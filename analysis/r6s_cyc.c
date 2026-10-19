// usage: r6s_cyc <cmd> [args...]
// Counts user-mode cycles, instructions and branch misses of the command and
// all its threads, and prints them to stderr. Build: gcc -O2 -o r6s_cyc r6s_cyc.c
#define _GNU_SOURCE
#include <linux/perf_event.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/syscall.h>
#include <sys/wait.h>
#include <unistd.h>

static int open_ev(uint64_t config) {
    struct perf_event_attr a;
    memset(&a, 0, sizeof a);
    a.size = sizeof a;
    a.type = PERF_TYPE_HARDWARE;
    a.config = config;
    a.disabled = 1;
    a.exclude_kernel = 1;
    a.exclude_hv = 1;
    a.inherit = 1;
    a.enable_on_exec = 1;
    int fd = syscall(SYS_perf_event_open, &a, 0, -1, -1, 0);
    if (fd < 0) {
        perror("perf_event_open");
        exit(1);
    }
    return fd;
}

int main(int argc, char **argv) {
    int fc = open_ev(PERF_COUNT_HW_CPU_CYCLES);
    int fi = open_ev(PERF_COUNT_HW_INSTRUCTIONS);
    int fb = open_ev(PERF_COUNT_HW_BRANCH_MISSES);
    pid_t p = fork();
    if (p == 0) {
        execvp(argv[1], argv + 1);
        perror("exec");
        _exit(127);
    }
    int st;
    waitpid(p, &st, 0);
    uint64_t c = 0, i = 0, b = 0;
    if (read(fc, &c, 8) != 8 || read(fi, &i, 8) != 8 || read(fb, &b, 8) != 8) {
        perror("read");
    }
    fprintf(stderr, "cycles %.4f G instructions %.4f G branch-misses %.4f G\n", c / 1e9, i / 1e9, b / 1e9);
    return WEXITSTATUS(st);
}
