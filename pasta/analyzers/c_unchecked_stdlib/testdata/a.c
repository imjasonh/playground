#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void f(char *dst, const char *src, const char *n) {
    system("ls");           // want "`system` is easy to misuse"
    strcpy(dst, src);       // want "`strcpy` is easy to misuse"
    strcat(dst, src);       // want "`strcat` is easy to misuse"
    sprintf(dst, "%s", src); // want "`sprintf` is easy to misuse"
    atoi(n);                // want "`atoi` is easy to misuse"
    strtol(n, NULL, 10);
    snprintf(dst, 8, "%s", src);
}
