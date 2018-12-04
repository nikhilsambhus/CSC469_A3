// Copyright (C) 2016, 2017 Alexey Khrabrov, Bogdan Simion
//
// Distributed under the terms of the GNU General Public License.
//
// This file is part of Assignment 3, CSC469, Fall 2017.
//
// This is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This file is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this file.  If not, see <http://www.gnu.org/licenses/>.


// The metadata server implementation

#include <assert.h>
#include <errno.h>
#include <limits.h>
#include <pthread.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

#include <sys/types.h>
#include <sys/socket.h>

#include "defs.h"
#include "util.h"


// Program arguments

// Ports for listening to incoming connections from clients and servers
static uint16_t clients_port = 0;
static uint16_t servers_port = 0;

// Server configuration file name
static char cfg_file_name[PATH_MAX] = "";

// Timeout for detecting server failures; you might want to adjust this default value
static const int default_server_timeout = 5;
static int server_timeout = 0;

// Log file name
static char log_file_name[PATH_MAX] = "";


static void usage(char **argv)
{
	printf("usage: %s -c <client port> -s <servers port> -C <config file> "
	       "[-t <timeout (seconds)> -l <log file>]\n", argv[0]);
	printf("Default timeout is %d seconds\n", default_server_timeout);
	printf("If the log file (-l) is not specified, log output is written to stdout\n");
}

// Returns false if the arguments are invalid
static bool parse_args(int argc, char **argv)
{
	char option;
	while ((option = getopt(argc, argv, "c:s:C:l:t:")) != -1) {
		switch(option) {
			case 'c': clients_port = atoi(optarg); break;
			case 's': servers_port = atoi(optarg); break;
			case 'l': strncpy(log_file_name, optarg, PATH_MAX); break;
			case 'C': strncpy(cfg_file_name, optarg, PATH_MAX); break;
			case 't': server_timeout = atoi(optarg); break;
			default:
				fprintf(stderr, "Invalid option: -%c\n", option);
				return false;
		}
	}

	server_timeout = (server_timeout != 0) ? server_timeout : default_server_timeout;

	return (clients_port != 0) && (servers_port != 0) && (cfg_file_name[0] != '\0');
}


// Current machine host name
static char mserver_host_name[HOST_NAME_MAX] = "";

// Sockets for incoming connections from clients and servers
static int clients_fd = -1;
static int servers_fd = -1;

// Store socket fds for all connected clients, up to MAX_CLIENT_SESSIONS
#define MAX_CLIENT_SESSIONS 1000
static int client_fd_table[MAX_CLIENT_SESSIONS];


// Structure describing a key-value server state
typedef struct _server_node {
	// Server host name, possibly prefixed by "user@" (for starting servers remotely via ssh)
	char host_name[HOST_NAME_MAX];
	// Servers/client/mserver port numbers
	uint16_t sport;
	uint16_t cport;
	uint16_t mport;
	// Server ID
	int sid;
	// Socket for receiving requests from the server
	int socket_fd_in;
	// Socket for sending requests to the server
	int socket_fd_out;
	// Server process PID (it is a child process of mserver)
	pid_t pid;

	time_t latest_alive;
	// TODO: add fields for necessary additional server state information
	// ...

} server_node;

// Total number of servers
static int num_servers = 0;
// Server state information
static server_node *server_nodes = NULL;

static int failed_server_id = -1;

// Read the configuration file, fill in the server_nodes array
// Returns false if the configuration is invalid
static bool read_config_file()
{
	FILE *cfg_file = fopen(cfg_file_name, "r");
	if (cfg_file == NULL) {
		perror(cfg_file_name);
		return false;
	}
	bool result = false;

	// The first line contains the number of servers
	if (fscanf(cfg_file, "%d\n", &num_servers) < 1) {
		goto end;
	}

	// Need at least 3 servers to avoid cross-replication
	if (num_servers < 3) {
		log_error("Invalid number of servers: %d\n", num_servers);
		goto end;
	}

	if ((server_nodes = calloc(num_servers, sizeof(server_node))) == NULL) {
		log_perror("calloc");
		goto end;
	}

	for (int i = 0; i < num_servers; i++) {
		server_node *node = &(server_nodes[i]);

		// Format: <host_name> <clients port> <servers port> <mservers_port>
		if ((fscanf(cfg_file, "%s %hu %hu %hu\n", node->host_name,
		            &(node->cport), &(node->sport), &(node->mport)) < 4) ||
		    ((strcmp(node->host_name, "localhost") != 0) && (strchr(node->host_name, '@') == NULL)) ||
		    (node->cport == 0) || (node->sport == 0) || (node->mport == 0))
		{
			free(server_nodes);
			server_nodes = NULL;
			goto end;
		}

		node->sid = i;
		node->socket_fd_in = -1;
		node->socket_fd_out = -1;
		node->pid = 0;
	}

	// Print server configuration
	printf("Key-value servers configuration:\n");
	for (int i = 0; i < num_servers; i++) {
		server_node *node = &(server_nodes[i]);
		printf("\thost: %s, client port: %d, server port: %d\n", node->host_name, node->cport, node->sport);
	}
	result = true;

end:
	fclose(cfg_file);
	return result;
}


static void cleanup();
static bool init_servers();

// Initialize and start the metadata server
static bool init_mserver()
{
	for (int i = 0; i < MAX_CLIENT_SESSIONS; i++) {
		client_fd_table[i] = -1;
	}

	// Get the host name that server is running on
	if (get_local_host_name(mserver_host_name, sizeof(mserver_host_name)) < 0) {
		return false;
	}
	log_write("%s Metadata server starts on host: %s\n", current_time_str(), mserver_host_name);

	// Create sockets for incoming connections from servers
	if ((servers_fd = create_server(servers_port, num_servers + 1, NULL)) < 0) {
		goto cleanup;
	}

	// Start key-value servers
	if (!init_servers()) {
		goto cleanup;
	}

	// Create sockets for incoming connections from clients
	if ((clients_fd = create_server(clients_port, MAX_CLIENT_SESSIONS, NULL)) < 0) {
		goto cleanup;
	}

	log_write("Metadata server initialized\n");
	return true;

cleanup:
	cleanup();
	return false;
}

// Cleanup and release all the resources
static void cleanup()
{
	close_safe(&clients_fd);
	close_safe(&servers_fd);

	// Close all client connections
	for (int i = 0; i < MAX_CLIENT_SESSIONS; i++) {
		close_safe(&(client_fd_table[i]));
	}

	if (server_nodes != NULL) {
		for (int i = 0; i < num_servers; i++) {
			server_node *node = &(server_nodes[i]);

			if (node->socket_fd_out != -1 && failed_server_id != i) {
				// Request server shutdown
				server_ctrl_request request = {0};
				request.hdr.type = MSG_SERVER_CTRL_REQ;
				request.type = SHUTDOWN;
				send_msg(node->socket_fd_out, &request, sizeof(request));
			}

			// Close the connections
			close_safe(&(server_nodes[i].socket_fd_out));
			close_safe(&(server_nodes[i].socket_fd_in));

			// Wait with timeout (or kill if timeout expires) for the server process
			if (server_nodes[i].pid > 0) {
				kill_safe(&(server_nodes[i].pid), 5);
			}
		}

		free(server_nodes);
		server_nodes = NULL;
	}
}


static const int max_cmd_length = 32;

static const char *remote_path = "csc469_a3/";

// Generate a command to start a key-value server (see server.c for arguments description)
static char **get_spawn_cmd(int sid)
{
	char **cmd = calloc(max_cmd_length, sizeof(char*));
	assert(cmd != NULL);

	server_node *node = &(server_nodes[sid]);
	int i = -1;

	if (strcmp(node->host_name, "localhost") != 0) {
		// Remote server, host_name format is "user@host"
		assert(strchr(node->host_name, '@') != NULL);

		// Use ssh to run the command on a remote machine
		cmd[++i] = strdup("ssh");
		cmd[++i] = strdup("-o");
		cmd[++i] = strdup("StrictHostKeyChecking=no");
		cmd[++i] = strdup(node->host_name);
		cmd[++i] = strdup("cd");
		cmd[++i] = strdup(remote_path);
		cmd[++i] = strdup("&&");
	}

	cmd[++i] = strdup("./server\0");

	cmd[++i] = strdup("-h");
	cmd[++i] = strdup(mserver_host_name);

	cmd[++i] = strdup("-m");
	cmd[++i] = malloc(8); sprintf(cmd[i], "%hu", servers_port);

	cmd[++i] = strdup("-c");
	cmd[++i] = malloc(8); sprintf(cmd[i], "%hu", node->cport);

	cmd[++i] = strdup("-s");
	cmd[++i] = malloc(8); sprintf(cmd[i], "%hu", node->sport);

	cmd[++i] = strdup("-M");
	cmd[++i] = malloc(8); sprintf(cmd[i], "%hu", node->mport);

	cmd[++i] = strdup("-S");
	cmd[++i] = malloc(8); sprintf(cmd[i], "%d", sid);

	cmd[++i] = strdup("-n");
	cmd[++i] = malloc(8); sprintf(cmd[i], "%d", num_servers);

	cmd[++i] = strdup("-l");
	cmd[++i] = malloc(20); sprintf(cmd[i], "server_%d.log", sid);

	cmd[++i] = NULL;
	assert(i < max_cmd_length);
	return cmd;
}

static void free_cmd(char **cmd)
{
	assert(cmd != NULL);

	for (int i = 0; i < max_cmd_length; i++) {
		if (cmd[i] != NULL) {
			free(cmd[i]);
		}
	}
	free(cmd);
}

// Start a key-value server with given id
static int spawn_server(int sid)
{
	server_node *node = &(server_nodes[sid]);

	close_safe(&(node->socket_fd_in));
	close_safe(&(node->socket_fd_out));
	kill_safe(&(node->pid), 0);

	// Spawn the server as a process on either the local machine or a remote machine (using ssh)
	pid_t pid = fork();
	switch (pid) {
		case -1:
			log_perror("fork");
			return -1;
		case 0: {
			char **cmd = get_spawn_cmd(sid);
			execvp(cmd[0], cmd);
			// If exec returns, some error happened
			perror(cmd[0]);
			free_cmd(cmd);
			_exit(1);
		}
		default:
			node->pid = pid;
			break;
	}

	// Wait for the server to connect
	int fd_idx = accept_connection(servers_fd, &(node->socket_fd_in), 1);
	if (fd_idx < 0) {
		// Something went wrong, kill the server process
		kill_safe(&(node->pid), 1);
		return -1;
	}
	assert(fd_idx == 0);

	// Extract the host name from "user@host"
	char *at = strchr(node->host_name, '@');
	char *host = (at == NULL) ? node->host_name : (at + 1);

	// Connect to the server
	if ((node->socket_fd_out = connect_to_server(host, node->mport)) < 0) {
		// Something went wrong, kill the server process
		close_safe(&(node->socket_fd_in));
		kill_safe(&(node->pid), 1);
		return -1;
	}

	return 0;
}

// Send the initial SET-SECONDARY message to a newly created server; returns true on success
static bool send_set_secondary(int sid)
{
	char buffer[MAX_MSG_LEN] = {0};
	server_ctrl_request *request = (server_ctrl_request*)buffer;

	// Fill in the request parameters
	request->hdr.type = MSG_SERVER_CTRL_REQ;
	request->type = SET_SECONDARY;
	server_node *secondary_node = &(server_nodes[secondary_server_id(sid, num_servers)]);
	request->port = secondary_node->sport;

	// Extract the host name from "user@host"
	char *at = strchr(secondary_node->host_name, '@');
	char *host = (at == NULL) ? secondary_node->host_name : (at + 1);

	int host_name_len = strlen(host) + 1;
	strncpy(request->host_name, host, host_name_len);

	// Send the request and receive the response
	server_ctrl_response response = {0};
	if (!send_msg(server_nodes[sid].socket_fd_out, request, sizeof(*request) + host_name_len) ||
	    !recv_msg(server_nodes[sid].socket_fd_out, &response, sizeof(response), MSG_SERVER_CTRL_RESP))
	{
		return false;
	}

	if (response.status != CTRLREQ_SUCCESS) {
		log_error("Server %d failed SET-SECONDARY\n", sid);
		return false;
	}
	return true;
}

// Start all key-value servers
static bool init_servers()
{
	// Spawn all the servers
	for (int i = 0; i < num_servers; i++) {
		if (spawn_server(i) < 0) {
			return false;
		}
	}

	// Let each server know the location of its secondary replica
	for (int i = 0; i < num_servers; i++) {
		if (!send_set_secondary(i)) {
			return false;
		}
	}

	return true;
}


// Connection will be closed after calling this function regardless of result
static void process_client_message(int fd)
{
	log_write("%s Receiving a client message\n", current_time_str());

	// Read and parse the message
	locate_request request = {0};
	if (!recv_msg(fd, &request, sizeof(request), MSG_LOCATE_REQ)) {
		return;
	}

	// Determine which server is responsible for the requested key
	int server_id = key_server_id(request.key, num_servers);

	// TODO: redirect client requests to the secondary replica while the primary is being recovered
	// ...

	// Fill in the response with the key-value server location information
	char buffer[MAX_MSG_LEN] = {0};
	locate_response *response = (locate_response*)buffer;
	response->hdr.type = MSG_LOCATE_RESP;
	response->port = server_nodes[server_id].cport;

	// Extract the host name from "user@host"
	char *at = strchr(server_nodes[server_id].host_name, '@');
	char *host = (at == NULL) ? server_nodes[server_id].host_name : (at + 1);

	int host_name_len = strlen(host) + 1;
	strncpy(response->host_name, host, host_name_len);

	// Reply to the client
	send_msg(fd, response, sizeof(*response) + host_name_len);
}


// Returns false if the message was invalid (so the connection will be closed)
static bool process_server_message(int fd)
{
	log_write("%s Receiving a server message\n", current_time_str());

	// TODO: read and process the message
	// ...
	char req_buffer[MAX_MSG_LEN] = {0};

	if(!recv_msg(fd, req_buffer, MAX_MSG_LEN, MSG_MSERVER_CTRL_REQ)) {
		log_write("Error server message, closing connection\n");
		return false;
	}

	mserver_ctrl_request *request = (mserver_ctrl_request *)req_buffer; 

	switch(request->type) {
		case HEARTBEAT:
			server_nodes[request->server_id].latest_alive = time(NULL);
			return true;
			break;
		default:
			log_write("Server message Invalid command\n");
	}
	
	return false;
}


static const int select_timeout_interval = 1;// seconds

static time_t hbeat_timer = 0;


int monitor_heartbeat(int *sid) {

	if(hbeat_timer == 0) { //initialization
		hbeat_timer = time(NULL);
	}
	else if((time(NULL) - hbeat_timer) >= default_server_timeout) {
		for (int i = 0; i < num_servers; i++) {
			if(server_nodes[i].latest_alive <= hbeat_timer) {
				hbeat_timer = time(NULL); //reset
				*sid = i;
				failed_server_id = i;	
				log_write("Server %d is dead\n", i);
				return -1;
			}
		}
		hbeat_timer = time(NULL); //reset
	}
	return 0;	
}

// Returns false if stopped due to errors, true if shutdown was requested
static bool run_mserver_loop()
{
	// Usual preparation stuff for select()
	fd_set rset, allset;
	FD_ZERO(&allset);
	// End-of-file on stdin (e.g. Ctrl+D in a terminal) is used to request shutdown
	FD_SET(fileno(stdin), &allset);
	FD_SET(servers_fd, &allset);
	FD_SET(clients_fd, &allset);

	int max_server_fd = -1;
	for (int i = 0; i < num_servers; i++) {
		FD_SET(server_nodes[i].socket_fd_in, &allset);
		max_server_fd = max(max_server_fd, server_nodes[i].socket_fd_in);
		server_nodes[i].latest_alive = time(NULL);
	}

	int maxfd = max(clients_fd, servers_fd);
	maxfd = max(maxfd,  max_server_fd);

	// Metadata server sits in an infinite loop waiting for incoming connections from clients
	// and for incoming messages from already connected servers and clients
	for (;;) {
		rset = allset;

		struct timeval time_out;
		time_out.tv_sec = select_timeout_interval;
		time_out.tv_usec = 0;
		
		int sid;
		if(monitor_heartbeat(&sid) == -1) {
			log_write("Server failure detected, server id %d\n", sid);
			log_error("Server failure detected, server id %d\n", sid);
		}
		// Wait with timeout (in order to be able to handle asynchronous events such as heartbeat messages)
		int num_ready_fds = select(maxfd + 1, &rset, NULL, NULL, &time_out);
		if (num_ready_fds < 0) {
			log_perror("select");
			return false;
		}
		if (num_ready_fds <= 0 ) {
			// Due to time out
			continue;
		}

		// Stop if detected EOF on stdin
		if (FD_ISSET(fileno(stdin), &rset)) {
			char buffer[1024];
			if (fgets(buffer, sizeof(buffer), stdin) == NULL) {
				return true;
			}
		}

		// Check for any messages from connected servers
		for (int i = 0; i < num_servers; i++) {
			server_node *node = &(server_nodes[i]);
			if ((node->socket_fd_in != -1) && FD_ISSET(node->socket_fd_in, &rset)) {
				if (!process_server_message(node->socket_fd_in)) {
					// Received an invalid message, close the connection
					log_error("Closing server %d connection\n", i);
					FD_CLR(node->socket_fd_in, &allset);
					close_safe(&(node->socket_fd_in));
				}

				if (--num_ready_fds <= 0) {
					break;
				}
			}
		}

		// TODO: implement failure detection and recovery
		// Need to go through the list of servers and figure out which servers have not sent a heartbeat message yet
		// within the timeout interval. Keep information in the server_node structure regarding when was the last
		// heartbeat received from a server and compare to current time. Initiate recovery if discovered a failure.
		// ...

		if (num_ready_fds <= 0) {
			continue;
		}

		// Incoming connection from a client
		if (FD_ISSET(clients_fd, &rset)) {
			int fd_idx = accept_connection(clients_fd, client_fd_table, MAX_CLIENT_SESSIONS);
			if (fd_idx >= 0) {
				FD_SET(client_fd_table[fd_idx], &allset);
				maxfd = max(maxfd, client_fd_table[fd_idx]);
			}

			if (--num_ready_fds <= 0) {
				continue;
			}
		}

		// Check for any messages from connected clients
		for (int i = 0; i < MAX_CLIENT_SESSIONS; i++) {
			if ((client_fd_table[i] != -1) && FD_ISSET(client_fd_table[i], &rset)) {
				process_client_message(client_fd_table[i]);
				// Close connection after processing (semantics are "one connection per request")
				FD_CLR(client_fd_table[i], &allset);
				close_safe(&(client_fd_table[i]));

				if (--num_ready_fds <= 0 ) {
					break;
				}
			}
		}
	}
}


int main(int argc, char **argv)
{
	signal(SIGPIPE, SIG_IGN);

	if (!parse_args(argc, argv)) {
		usage(argv);
		return 1;
	}

	open_log(log_file_name);

	if (!read_config_file()) {
		log_error("Invalid configuraion file\n");
		return 1;
	}

	if (!init_mserver()) {
		return 1;
	}

	bool result = run_mserver_loop();

	cleanup();
	return result ? 0 : 1;
}
