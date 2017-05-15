/* 
 * tsh - A tiny shell program with job control
 * 
 * Matthew Turnshek
 */

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include <ctype.h>
#include <signal.h>
#include <sys/types.h>
#include <fcntl.h>
#include <sys/wait.h>
#include <errno.h>

/* Misc manifest constants */
#define MAXLINE    1024   /* max line size */
#define MAXARGS     128   /* max args on a command line */
#define MAXJOBS      16   /* max jobs at any point in time */
#define MAXJID    1<<16   /* max job ID */

/* Job states */
#define UNDEF         0   /* undefined */
#define FG            1   /* running in foreground */
#define BG            2   /* running in background */
#define ST            3   /* stopped */

/* 
 * Jobs states: FG (foreground), BG (background), ST (stopped)
 * Job state transitions and enabling actions:
 *     FG -> ST  : ctrl-z
 *     ST -> FG  : fg command
 *     ST -> BG  : bg command
 *     BG -> FG  : fg command
 * At most 1 job can be in the FG state.
 */

/* Parsing states */
#define ST_NORMAL   0x0   /* next token is an argument */
#define ST_INFILE   0x1   /* next token is the input file */
#define ST_OUTFILE  0x2   /* next token is the output file */


/* Global variables */
extern char **environ;      /* defined in libc */
char prompt[] = "tsh> ";    /* command line prompt (DO NOT CHANGE) */
int verbose = 0;            /* if true, print additional output */
int nextjid = 1;            /* next job ID to allocate */
char sbuf[MAXLINE];         /* for composing sprintf messages */

struct job_t {              /* The job struct */
    pid_t pid;              /* job PID */
    int jid;                /* job ID [1, 2, ...] */
    int state;              /* UNDEF, BG, FG, or ST */
    char cmdline[MAXLINE];  /* command line */
};
struct job_t job_list[MAXJOBS]; /* The job list */

struct cmdline_tokens {
    int argc;               /* Number of arguments */
    char *argv[MAXARGS];    /* The arguments list */
    char *infile;           /* The input file */
    char *outfile;          /* The output file */
    enum builtins_t {       /* Indicates if argv[0] is a builtin command */
        BUILTIN_NONE,
        BUILTIN_QUIT,
        BUILTIN_JOBS,
        BUILTIN_BG,
        BUILTIN_FG} builtins;
};

/* End global variables */


/* Function prototypes */
void eval(char *cmdline);

void sigchld_handler(int sig);
void sigtstp_handler(int sig);
void sigint_handler(int sig);

/* Here are some functions I've written myself to help */
int builtin_commands(char** argv);
int ioredirection(char* infile, char* outfile);

/* Here are helper routines that we've provided for you */
int parseline(const char *cmdline, struct cmdline_tokens *tok); 
void sigquit_handler(int sig);

void clearjob(struct job_t *job);
void initjobs(struct job_t *job_list);
int maxjid(struct job_t *job_list); 
int addjob(struct job_t *job_list, pid_t pid, int state, char *cmdline);
int deletejob(struct job_t *job_list, pid_t pid); 
pid_t fgpid(struct job_t *job_list);
struct job_t *getjobpid(struct job_t *job_list, pid_t pid);
struct job_t *getjobjid(struct job_t *job_list, int jid); 
int pid2jid(pid_t pid); 
void listjobs(struct job_t *job_list, int output_fd);

void usage(void);
void unix_error(char *msg);
void app_error(char *msg);
typedef void handler_t(int);
handler_t *Signal(int signum, handler_t *handler);


//////////////////////////////////////
// Error checking wrapper functions //
//////////////////////////////////////

// System functions

// These functions will all automatically report errors is something goes wrong.
pid_t Fork(void);
void Execve(const char* filename, char* const argv[], char* const envp[]);
void Kill(pid_t pid, int signum);
void Setpgid(pid_t pid, pid_t pgid);

pid_t Fork(void) 
{
    pid_t pid;

    if ((pid = fork()) < 0)
    unix_error("Fork error");
    return pid;
}

void Execve(const char *filename, char *const argv[], char *const envp[]) 
{
    if (execve(filename, argv, envp) < 0)
    unix_error("Execve error");
}

void Kill(pid_t pid, int signum) 
{
    int rc;

    if ((rc = kill(pid, signum)) < 0)
    unix_error("Kill error");
}
 
void Setpgid(pid_t pid, pid_t pgid) {
    int rc;

    if ((rc = setpgid(pid, pgid)) < 0)
    unix_error("Setpgid error");
    return;
}

// Signal functions

void Sigprocmask(int how, const sigset_t* set, sigset_t* oldet);
void Sigemptyset(sigset_t *set);
void Sigaddset(sigset_t* set, int signum);

void Sigprocmask(int how, const sigset_t *set, sigset_t *oldset)
{
    if (sigprocmask(how, set, oldset) < 0)
    unix_error("Sigprocmask error");
    return;
}

void Sigemptyset(sigset_t *set)
{
    if (sigemptyset(set) < 0)
    unix_error("Sigemptyset error");
    return;
}

void Sigaddset(sigset_t *set, int signum)
{
    if (sigaddset(set, signum) < 0)
    unix_error("Sigaddset error");
    return;
}

////////////////////////////////
// End error wrapper function //
////////////////////////////////



/*
 * main - The shell's main routine 
 */
int 
main(int argc, char **argv) 
{
    char c;
    char cmdline[MAXLINE];    /* cmdline for fgets */
    int emit_prompt = 1; /* emit prompt (default) */

    /* Redirect stderr to stdout (so that driver will get all output
     * on the pipe connected to stdout) */
    dup2(1, 2);

    /* Parse the command line */
    while ((c = getopt(argc, argv, "hvp")) != EOF) {
        switch (c) {
        case 'h':             /* print help message */
            usage();
            break;
        case 'v':             /* emit additional diagnostic info */
            verbose = 1;
            break;
        case 'p':             /* don't print a prompt */
            emit_prompt = 0;  /* handy for automatic testing */
            break;
        default:
            usage();
        }
    }

    /* Install the signal handlers */

    /* These are the ones you will need to implement */
    Signal(SIGINT,  sigint_handler);   /* ctrl-c */
    Signal(SIGTSTP, sigtstp_handler);  /* ctrl-z */
    Signal(SIGCHLD, sigchld_handler);  /* Terminated or stopped child */
    Signal(SIGTTIN, SIG_IGN);
    Signal(SIGTTOU, SIG_IGN);

    /* This one provides a clean way to kill the shell */
    Signal(SIGQUIT, sigquit_handler); 

    /* Initialize the job list */
    initjobs(job_list);


    /* Execute the shell's read/eval loop */
    while (1) {

        if (emit_prompt) {
            printf("%s", prompt);
            fflush(stdout);
        }
        if ((fgets(cmdline, MAXLINE, stdin) == NULL) && ferror(stdin))
            app_error("fgets error");
        if (feof(stdin)) { 
            /* End of file (ctrl-d) */
            printf ("\n");
            fflush(stdout);
            fflush(stderr);
            exit(0);
        }
        
        /* Remove the trailing newline */
        cmdline[strlen(cmdline)-1] = '\0';
        
        /* Evaluate the command line */
        eval(cmdline);
        
        fflush(stdout);
        fflush(stdout);
    } 
    
    exit(0); /* control never reaches here */
}

// Given an argument variable list, checks if the first argument is a builtin
// command. If it is, executes it and returns true. Otherwise returns false.
int builtin_command(struct cmdline_tokens tok) {
    char** argv = tok.argv;
    int i, given_id;
    struct job_t* target_job;
    sigset_t sigsuspend_mask;
    Sigemptyset(&sigsuspend_mask);

    // For redirection
    int outfile_descriptor;
    FILE* working_outfile;

    // Tells the terminal to stop.
    if (!strcmp(argv[0], "quit")) {
        exit(0);
    }


    // Ignore a singleton &. 
    else if (!strcmp(argv[0], "&")) {
        return 1;
    }

    
    // Print the jobs list.
    else if (!strcmp(argv[0], "jobs")) {
        // We have no output redirection
        if (tok.outfile == NULL) {
            listjobs(job_list, STDOUT_FILENO); // 2 is stdout.
        }
        // There is output redirection
        else {
            // Opening
            working_outfile = fopen(tok.outfile, "r");
            outfile_descriptor = open(tok.outfile, O_RDWR);

            // Writing
            listjobs(job_list, outfile_descriptor);

            // Closing
            close(outfile_descriptor);
            fclose(working_outfile);
        }

        
        return 1;
    }


    // Takes an ID and runs that process in the foreground.

    // Takes a JID or PID as arguments. If JID, must be in the format fg %n
    // where n is the JID. If PID, must be in the format fg n. 
    else if (!strcmp(argv[0], "fg")) {
        // If they didn't put an argument, let them know. 
        if (argv[1] == NULL) {
            printf("bg command requires PID or %%jobid argument\n");
            return 1;
        }

        // Compares first char of argv[1] with %
        // If it's there, it's a JID
        if (argv[1][0] == '%') {
            given_id = atoi(&argv[1][1]); // Ignore the first char, %
            // We now have the JID
            // We use a loop to extract the PID using our JID.
            for (i = 0; i < MAXJOBS; i++) {
                if ((job_list[i].jid) == given_id) {
                    given_id = job_list[i].pid;
                }
            }
        }

        // If it's not there, it's a PID
        else {
            given_id = atoi(argv[1]);
        }

        target_job = getjobpid(job_list, given_id);
        if (target_job == NULL) {
            printf("Not a valid ID.\n");
            return 1;
        }
        
        target_job->state = FG; // Change job state to FG
        Kill(given_id, SIGCONT); // Restarts the specific process

        // Now we wait to move on until recieiving some signal, like in eval.
        sigsuspend(&sigsuspend_mask);
        return 1;
    }


    // Takes an ID and runs that process in the background.

    // Takes a JID or PID as arguments. If JID, must be in the format bg %n
    // where n is the JID. If PID, must be in the format bg n. 
    else if (!strcmp(argv[0], "bg")) {
        // If they didn't put an argument, let them know.
        if (argv[1] == NULL) {
            printf("bg command requires PID or %%jobid argument\n");
            return 1;
        }

        // Compares first char of argv[1] with %
        // If it's there, it's a JID
        if (argv[1][0] == '%') {
            given_id = atoi(&argv[1][1]); // Ignore the first char, %
            // We now have the JID
            // We use a loop to extract the PID using our JID.
            for (i = 0; i < MAXJOBS; i++) {
                if ((job_list[i].jid) == given_id) {
                    given_id = job_list[i].pid;
                }
            }
        }

        // If it's not there, it's a PID
        else {
            given_id = atoi(argv[1]);
        }

        target_job = getjobpid(job_list, given_id);
        if (target_job == NULL) {
            printf("Not a valid ID.\n");
            return 1;
        }
        
        target_job->state = BG; // Change job state to BG
        Kill(given_id, SIGCONT); // Restarts the specific process

        printf("[%d] (%d) %s\n", target_job->jid,
                                 target_job->pid,
                                 target_job->cmdline);
        return 1;
    }
    return 0;
}

int ioredirection(char* infile, char* outfile) {
    int infile_descriptor, outfile_descriptor;
    FILE* working_infile;
    FILE* working_outfile;

    // Input Redirection
    if (infile != NULL) {
        // Opening
        working_infile = fopen(infile, "r");
        infile_descriptor = open(infile, O_RDONLY);

        // Redirecting
        dup2(infile_descriptor, STDIN_FILENO);

        // Closing
        close(infile_descriptor);
        fclose(working_infile);
    }


    // Output Redirection
    if (outfile != NULL) {
        // Opening
        working_outfile = fopen(outfile, "r");
        outfile_descriptor = open(outfile, O_RDWR);

        // Redirecting
        dup2(outfile_descriptor, STDOUT_FILENO);

        // Closing
        close(outfile_descriptor);
        fclose(working_outfile);
    }

    return 0;
}


/* 
 * eval - Evaluate the command line that the user has just typed in
 * 
 * If the user has requested a built-in command (quit, jobs, bg or fg)
 * then execute it immediately. Otherwise, fork a child process and
 * run the job in the context of the child. If the job is running in
 * the foreground, wait for it to terminate and then return.  Note:
 * each child process must have a unique process group ID so that our
 * background children don't receive SIGINT (SIGTSTP) from the kernel
 * when we type ctrl-c (ctrl-z) at the keyboard.  
 */
void 
eval(char *cmdline) 
{

    // Setup
    int bg;     /* should the job run in bg or fg? */
    struct cmdline_tokens tok;
    pid_t pid;
    int job_id;
    int state;
    sigset_t sigsuspend_mask;
    Sigemptyset(&sigsuspend_mask);
    sigset_t mask;

    /* Parse command line */
    bg = parseline(cmdline, &tok); 

    if (bg == -1) /* parsing error */
        return;

    if (tok.argv[0] == NULL) /* ignore empty lines */
        return;


    // The following block of code will execute our command
    // If it's a builtin_command we'll run it and end the loop.
    if (!builtin_command(tok)) {

        // Signal blocking
        Sigemptyset(&mask);
        Sigaddset(&mask, SIGCHLD);
        Sigaddset(&mask, SIGINT);
        Sigaddset(&mask, SIGTSTP);
        Sigprocmask(SIG_BLOCK, &mask, NULL); // Blocks sigchld, sigint, sigtstp

        // Fork and execve //
        // Here we fork the new process we're running.
        if ((pid = Fork()) == 0) {

            ioredirection(tok.infile, tok.outfile);

            Setpgid(0, 0); // No process will be in the same process group
                           // as the shell.
            Sigprocmask(SIG_UNBLOCK, &mask, NULL); // Unblocks signals
            if (execve(tok.argv[0], tok.argv, environ) < 0) {
                printf("%s: Command not found.\n", tok.argv[0]);
                exit(0);
            }
        }


        // Job list //
        // First we prepare the job id and state in case we are running a job.
        job_id = nextjid;
        if (bg) {
            state = BG;
        }
        else {
            state = FG;
        } 
        // Now our shell (the parent) adds the job if the process is running.
        addjob(job_list, pid, state, cmdline);

        // Now, since we've added our job we no longer have a race condition
        // if we unblock signals.
        Sigprocmask(SIG_UNBLOCK, &mask, NULL); // Unblocks signals


        // Foreground waiting //


        if (!bg) {
            while (fgpid(job_list) != 0) {
                sigsuspend(&sigsuspend_mask);
            }
        }

        // Background info output //
        // If it's a background process, our shell just prints some information
        // and lets the main loop continue.
        else {
            // Job ID in brackets, then process ID in parens, followed by input
            printf("[%d] (%d) %s\n", job_id, pid, cmdline);
        }
    }

    return;
}

/* 
 * parseline - Parse the command line and build the argv array.
 * 
 * Parameters:
 *   cmdline:  The command line, in the form:
 *
 *                command [arguments...] [< infile] [> oufile] [&]
 *
 *   tok:      Pointer to a cmdline_tokens structure. The elements of this
 *             structure will be populated with the parsed tokens. Characters 
 *             enclosed in single or double quotes are treated as a single
 *             argument. 
 * Returns:
 *   1:        if the user has requested a BG job
 *   0:        if the user has requested a FG job  
 *  -1:        if cmdline is incorrectly formatted
 * 
 * Note:       The string elements of tok (e.g., argv[], infile, outfile) 
 *             are statically allocated inside parseline() and will be 
 *             overwritten the next time this function is invoked.
 */
int 
parseline(const char *cmdline, struct cmdline_tokens *tok) 
{

    static char array[MAXLINE];          /* holds local copy of command line */
    const char delims[10] = " \t\r\n";   /* argument delimiters (white-space) */
    char *buf = array;                   /* ptr that traverses command line */
    char *next;                          /* ptr to the end of the current arg */
    char *endbuf;                        /* ptr to end of cmdline string */
    int is_bg;                           /* background job? */

    int parsing_state;                   /* indicates if the next token is the
                                            input or output file */

    if (cmdline == NULL) {
        (void) fprintf(stderr, "Error: command line is NULL\n");
        return -1;
    }

    (void) strncpy(buf, cmdline, MAXLINE);
    endbuf = buf + strlen(buf);

    tok->infile = NULL;
    tok->outfile = NULL;

    /* Build the argv list */
    parsing_state = ST_NORMAL;
    tok->argc = 0;

    while (buf < endbuf) {
        /* Skip the white-spaces */
        buf += strspn (buf, delims);
        if (buf >= endbuf) break;

        /* Check for I/O redirection specifiers */
        if (*buf == '<') {
            if (tok->infile) {
                (void) fprintf(stderr, "Error: Ambiguous I/O redirection\n");
                return -1;
            }
            parsing_state |= ST_INFILE;
            buf++;
            continue;
        }
        if (*buf == '>') {
            if (tok->outfile) {
                (void) fprintf(stderr, "Error: Ambiguous I/O redirection\n");
                return -1;
            }
            parsing_state |= ST_OUTFILE;
            buf ++;
            continue;
        }

        if (*buf == '\'' || *buf == '\"') {
            /* Detect quoted tokens */
            buf++;
            next = strchr (buf, *(buf-1));
        } else {
            /* Find next delimiter */
            next = buf + strcspn (buf, delims);
        }
        
        if (next == NULL) {
            /* Returned by strchr(); this means that the closing
               quote was not found. */
            (void) fprintf (stderr, "Error: unmatched %c.\n", *(buf-1));
            return -1;
        }

        /* Terminate the token */
        *next = '\0';

        /* Record the token as either the next argument or the i/o file */
        switch (parsing_state) {
        case ST_NORMAL:
            tok->argv[tok->argc++] = buf;
            break;
        case ST_INFILE:
            tok->infile = buf;
            break;
        case ST_OUTFILE:
            tok->outfile = buf;
            break;
        default:
            (void) fprintf(stderr, "Error: Ambiguous I/O redirection\n");
            return -1;
        }
        parsing_state = ST_NORMAL;

        /* Check if argv is full */
        if (tok->argc >= MAXARGS-1) break;

        buf = next + 1;
    }

    if (parsing_state != ST_NORMAL) {
        (void) fprintf(stderr,
                       "Error: must provide file name for redirection\n");
        return -1;
    }

    /* The argument list must end with a NULL pointer */
    tok->argv[tok->argc] = NULL;

    if (tok->argc == 0)  /* ignore blank line */
        return 1;

    if (!strcmp(tok->argv[0], "quit")) {                 /* quit command */
        tok->builtins = BUILTIN_QUIT;
    } else if (!strcmp(tok->argv[0], "jobs")) {          /* jobs command */
        tok->builtins = BUILTIN_JOBS;
    } else if (!strcmp(tok->argv[0], "bg")) {            /* bg command */
        tok->builtins = BUILTIN_BG;
    } else if (!strcmp(tok->argv[0], "fg")) {            /* fg command */
        tok->builtins = BUILTIN_FG;
    } else {
        tok->builtins = BUILTIN_NONE;
    }

    /* Should the job run in the background? */
    if ((is_bg = (*tok->argv[tok->argc-1] == '&')) != 0)
        tok->argv[--tok->argc] = NULL;

    return is_bg;
}


/*****************
 * Signal handlers
 *****************/

/* 
 * sigchld_handler - The kernel sends a SIGCHLD to the shell whenever
 *     a child job terminates (becomes a zombie), or stops because it
 *     received a SIGSTOP, SIGTSTP, SIGTTIN or SIGTTOU signal. The 
 *     handler reaps all available zombie children, but doesn't wait 
 *     for any other currently running children to terminate.  
 */
void sigchld_handler(int sig) {
    int status;
    pid_t pid;
    struct job_t* target_job;

    // We loop until there are no children left. This is because multiple
    // signals may have been sent and we want to deal with all children.
    while ((pid = waitpid(-1, &status, WNOHANG | WUNTRACED)) > 0) {
        // If the child terminated normally, delete its job.
        if WIFEXITED(status) {
            deletejob(job_list, pid);
        }
        // If the child was stopped, we recieve it here because of WUNTRACED.
        else if WIFSTOPPED(status) {
            // Print some info about the job that was stopped
            target_job = getjobpid(job_list, pid);
            printf("Job [%d] (%d) stopped by signal %d\n", 
                    target_job->jid, pid, SIGTSTP);
            // Record the stop on the jobs list
            target_job->state = ST;
        }
        // We also want to delete from the jobs list if the child was terminated
        // by a SIGINT.
        else if WIFSIGNALED(status) {
            target_job = getjobpid(job_list, pid);
            printf("Job [%d] (%d) terminated by signal %d\n", 
                    target_job->jid, pid, SIGINT);
            deletejob(job_list, pid);
        }
        else {
            unix_error("Error in waitpid loop in sigchld_handler\n");
        }
    }

    return;
}

/* 
 * sigint_handler - The kernel sends a SIGINT to the shell whenver the
 *    user types ctrl-c at the keyboard.  Catch it and send it along
 *    to the foreground job.  
 */
void 
sigint_handler(int sig) 
{
    pid_t foreground_pid = fgpid(job_list);

    // Passes the signal on to the foreground job group.
    Kill(-foreground_pid, sig);

    return;
}

/*
 * sigtstp_handler - The kernel sends a SIGTSTP to the shell whenever
 *     the user types ctrl-z at the keyboard. Catch it and suspend the
 *     foreground job by sending it a SIGTSTP.  
 */
void 
sigtstp_handler(int sig) 
{
    pid_t foreground_pid = fgpid(job_list);

    // Passes the signal on to the foreground job group.
    Kill(-foreground_pid, sig);

    return;
}

/*********************
 * End signal handlers
 *********************/

/***********************************************
 * Helper routines that manipulate the job list
 **********************************************/

/* clearjob - Clear the entries in a job struct */
void 
clearjob(struct job_t *job) {
    job->pid = 0;
    job->jid = 0;
    job->state = UNDEF;
    job->cmdline[0] = '\0';
}

/* initjobs - Initialize the job list */
void 
initjobs(struct job_t *job_list) {
    int i;

    for (i = 0; i < MAXJOBS; i++)
        clearjob(&job_list[i]);
}

/* maxjid - Returns largest allocated job ID */
int 
maxjid(struct job_t *job_list) 
{
    int i, max=0;

    for (i = 0; i < MAXJOBS; i++)
        if (job_list[i].jid > max)
            max = job_list[i].jid;
    return max;
}

/* addjob - Add a job to the job list */
int 
addjob(struct job_t *job_list, pid_t pid, int state, char *cmdline) 
{
    int i;

    if (pid < 1)
        return 0;

    for (i = 0; i < MAXJOBS; i++) {
        if (job_list[i].pid == 0) {
            job_list[i].pid = pid;
            job_list[i].state = state;
            job_list[i].jid = nextjid++;
            if (nextjid > MAXJOBS)
                nextjid = 1;
            strcpy(job_list[i].cmdline, cmdline);
            if(verbose){
                printf("Added job [%d] %d %s\n",
                       job_list[i].jid,
                       job_list[i].pid,
                       job_list[i].cmdline);
            }
            return 1;
        }
    }
    printf("Tried to create too many jobs\n");
    return 0;
}

/* deletejob - Delete a job whose PID=pid from the job list */
int 
deletejob(struct job_t *job_list, pid_t pid) 
{
    int i;

    if (pid < 1)
        return 0;

    for (i = 0; i < MAXJOBS; i++) {
        if (job_list[i].pid == pid) {
            clearjob(&job_list[i]);
            nextjid = maxjid(job_list)+1;
            return 1;
        }
    }
    return 0;
}

/* fgpid - Return PID of current foreground job, 0 if no such job */
pid_t 
fgpid(struct job_t *job_list) {
    int i;

    for (i = 0; i < MAXJOBS; i++)
        if (job_list[i].state == FG)
            return job_list[i].pid;
    return 0;
}

/* getjobpid  - Find a job (by PID) on the job list */
struct job_t 
*getjobpid(struct job_t *job_list, pid_t pid) {
    int i;

    if (pid < 1)
        return NULL;
    for (i = 0; i < MAXJOBS; i++)
        if (job_list[i].pid == pid)
            return &job_list[i];
    return NULL;
}

/* getjobjid  - Find a job (by JID) on the job list */
struct job_t *getjobjid(struct job_t *job_list, int jid) 
{
    int i;

    if (jid < 1)
        return NULL;
    for (i = 0; i < MAXJOBS; i++)
        if (job_list[i].jid == jid)
            return &job_list[i];
    return NULL;
}

/* pid2jid - Map process ID to job ID */
int 
pid2jid(pid_t pid) 
{
    int i;

    if (pid < 1)
        return 0;
    for (i = 0; i < MAXJOBS; i++)
        if (job_list[i].pid == pid) {
            return job_list[i].jid;
        }
    return 0;
}

/* listjobs - Print the job list */
void 
listjobs(struct job_t *job_list, int output_fd) 
{
    int i;
    char buf[MAXLINE];

    for (i = 0; i < MAXJOBS; i++) {
        memset(buf, '\0', MAXLINE);
        if (job_list[i].pid != 0) {
            sprintf(buf, "[%d] (%d) ", job_list[i].jid, job_list[i].pid);
            if(write(output_fd, buf, strlen(buf)) < 0) {
                fprintf(stderr, "Error writing to output file\n");
                exit(1);
            }
            memset(buf, '\0', MAXLINE);
            switch (job_list[i].state) {
            case BG:
                sprintf(buf, "Running    ");
                break;
            case FG:
                sprintf(buf, "Foreground ");
                break;
            case ST:
                sprintf(buf, "Stopped    ");
                break;
            default:
                sprintf(buf, "listjobs: Internal error: job[%d].state=%d ",
                        i, job_list[i].state);
            }
            if(write(output_fd, buf, strlen(buf)) < 0) {
                fprintf(stderr, "Error writing to output file\n");
                exit(1);
            }
            memset(buf, '\0', MAXLINE);
            sprintf(buf, "%s\n", job_list[i].cmdline);
            if(write(output_fd, buf, strlen(buf)) < 0) {
                fprintf(stderr, "Error writing to output file\n");
                exit(1);
            }
        }
    }
}
/******************************
 * end job list helper routines
 ******************************/


/***********************
 * Other helper routines
 ***********************/

/*
 * usage - print a help message
 */
void 
usage(void) 
{
    printf("Usage: shell [-hvp]\n");
    printf("   -h   print this message\n");
    printf("   -v   print additional diagnostic information\n");
    printf("   -p   do not emit a command prompt\n");
    exit(1);
}

/*
 * unix_error - unix-style error routine
 */
void 
unix_error(char *msg)
{
    fprintf(stdout, "%s: %s\n", msg, strerror(errno));
    exit(1);
}

/*
 * app_error - application-style error routine
 */
void 
app_error(char *msg)
{
    fprintf(stdout, "%s\n", msg);
    exit(1);
}

/*
 * Signal - wrapper for the sigaction function
 */
handler_t 
*Signal(int signum, handler_t *handler) 
{
    struct sigaction action, old_action;

    action.sa_handler = handler;  
    sigemptyset(&action.sa_mask); /* block sigs of type being handled */
    action.sa_flags = SA_RESTART; /* restart syscalls if possible */

    if (sigaction(signum, &action, &old_action) < 0)
        unix_error("Signal error");
    return (old_action.sa_handler);
}

/*
 * sigquit_handler - The driver program can gracefully terminate the
 *    child shell by sending it a SIGQUIT signal.
 */
void 
sigquit_handler(int sig) 
{
    printf("Terminating after receipt of SIGQUIT signal\n");
    exit(1);
}