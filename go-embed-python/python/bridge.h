// C side of package python: thin helpers over the CPython C API.
//
// bridge_start and bridge_stop must run on the same OS thread. Every other
// helper takes the GIL itself, so Go can call it from any goroutine. On
// failure, *err receives a malloc'd description of the Python exception,
// including its traceback. The caller frees it.

#ifndef GO_EMBED_PYTHON_BRIDGE_H_
#define GO_EMBED_PYTHON_BRIDGE_H_

int bridge_start(const char* home, char** err);
int bridge_stop(void);
int bridge_load_module(const char* name, const char* source,
                       const char* filename, char** err);
void* bridge_lookup(const char* module, const char* attr, char** err);
char* bridge_call(void* callable, const char* arg, char** err);

#endif  // GO_EMBED_PYTHON_BRIDGE_H_
