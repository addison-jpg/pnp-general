/* base_win: the Windows version of the base prompt. Plain C, Win32 only, no Python.
   Commands: :hello runs hello.ath, :big runs big.ath, :bus runs workshop/bus/bus.ath, :quit leaves.
   The engine is the program named by the ASTEROID environment variable, else asteroid.exe then ast.exe
   in the current folder. Build: x86_64-w64-mingw32-gcc -O2 -s -o base.exe base_win.c   */
#include <windows.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>

static int run(const char *engine, const char *program) {
    char cmd[1024];
    snprintf(cmd, sizeof cmd, "\"%s\" --no-lean %s", engine, program);
    STARTUPINFOA si; PROCESS_INFORMATION pi;
    ZeroMemory(&si, sizeof si); si.cb = sizeof si;
    ZeroMemory(&pi, sizeof pi);
    if (!CreateProcessA(NULL, cmd, NULL, NULL, TRUE, 0, NULL, NULL, &si, &pi)) {
        printf("could not start %s (error %lu)\n", engine, GetLastError());
        return 1;
    }
    WaitForSingleObject(pi.hProcess, INFINITE);
    DWORD code = 1;
    GetExitCodeProcess(pi.hProcess, &code);
    CloseHandle(pi.hProcess); CloseHandle(pi.hThread);
    return (int)code;
}

static const char *engine(void) {
    const char *env = getenv("ASTEROID");
    if (env && *env) return env;
    if (GetFileAttributesA("asteroid.exe") != INVALID_FILE_ATTRIBUTES) return "asteroid.exe";
    return "ast.exe";
}

int main(void) {
    char line[256];
    printf("ath> (:big :hello :bus :quit)\n");
    for (;;) {
        printf("ath> "); fflush(stdout);
        if (!fgets(line, sizeof line, stdin)) { printf("\n"); return 0; }
        line[strcspn(line, "\r\n")] = 0;
        if (!strcmp(line, ":quit")) return 0;
        if (!strcmp(line, ":hello")) printf("exit %d\n", run(engine(), "hello.ath"));
        else if (!strcmp(line, ":big")) printf("exit %d\n", run(engine(), "big.ath"));
        else if (!strcmp(line, ":bus")) printf("exit %d\n", run(engine(), "workshop/bus/bus.ath"));
        else printf("commands: :big :hello :bus :quit\n");
    }
}
