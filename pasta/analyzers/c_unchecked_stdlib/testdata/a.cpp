#include <cstdlib>
#include <cstring>

void f(char *dst, const char *src) {
    std::strcpy(dst, src); // qualified; identifier is strcpy still? leave as OK if it's field_expression
    system("ls");          // want "`system` is easy to misuse"
}
