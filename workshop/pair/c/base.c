/* base: a small .ath prompt. Plain C, no windows, no hidden behaviour.
   It prints "ath> ", reads one line, and runs what the line names:
     :big      run big.ath through asteroid (--no-lean, so it needs no Lean)
     :hello    run hello.ath through asteroid
     :quit     leave
   Anything else prints a short help line. Build: gcc -O2 -static -s -o base base.c
   The asteroid binary is the ASTEROID environment variable, or else dist/linux/asteroid relative to the
   CURRENT directory (run it from the repository root). big.ath and hello.ath are also read from the current directory. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/wait.h>

static int run(const char *prog, const char *program) {
    pid_t pid = fork();
    if (pid < 0) { perror("fork"); return 1; }
    if (pid == 0) {
        execl(prog, prog, "--no-lean", program, (char *)NULL);
        perror("exec");
        _exit(127);
    }
    int status = 0;
    waitpid(pid, &status, 0);
    return WIFEXITED(status) ? WEXITSTATUS(status) : 1;
}

int main(void) {
    const char *prog = getenv("ASTEROID");
    if (!prog || !*prog) prog = "dist/linux/asteroid";
    char line[256];
    printf("ath> (:big :hello :quit)\n");
    for (;;) {
        printf("ath> "); fflush(stdout);
        if (!fgets(line, sizeof line, stdin)) { printf("\n"); return 0; }
        line[strcspn(line, "\n")] = 0;
        if (!strcmp(line, ":quit")) return 0;
        if (!strcmp(line, ":big")) printf("exit %d\n", run(prog, "big.ath"));
        else if (!strcmp(line, ":hello")) printf("exit %d\n", run(prog, "hello.ath"));
        else printf("commands: :big :hello :quit\n");
    }
}
