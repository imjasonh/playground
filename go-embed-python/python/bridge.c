// C side of package python. These helpers make the CPython C API calls that
// the Go code needs, and define gohost, the module Python code imports to call
// functions registered in Go.

#define PY_SSIZE_T_CLEAN
#include <Python.h>
#include <stdlib.h>
#include <string.h>

#include "_cgo_export.h"
#include "bridge.h"

// Saved when bridge_start releases the GIL, and restored by bridge_stop on the
// same OS thread before finalizing.
static PyThreadState* main_thread_state;

// gohost.call(name, arg) runs the Go function registered as name. It runs
// with the GIL held, on the OS thread of the goroutine that called into Python.
static PyObject* gohost_call(PyObject* self, PyObject* args) {
  const char* name;
  const char* arg;
  if (!PyArg_ParseTuple(args, "ss", &name, &arg)) return NULL;
  char* err = NULL;
  char* result = goCall((char*)name, (char*)arg, &err);
  if (err != NULL) {
    PyErr_SetString(PyExc_RuntimeError, err);
    free(err);
    free(result);
    return NULL;
  }
  if (result == NULL) return PyErr_NoMemory();
  PyObject* str = PyUnicode_FromString(result);
  free(result);
  return str;
}

static PyMethodDef gohost_methods[] = {
    {"call", gohost_call, METH_VARARGS,
     "call(name, arg) -> str\n\nRuns the Go function registered as name."},
    {NULL, NULL, 0, NULL},
};

static struct PyModuleDef gohost_module = {
    PyModuleDef_HEAD_INIT, "gohost", "Functions provided by the Go program.",
    -1, gohost_methods,
};

static PyObject* init_gohost(void) { return PyModule_Create(&gohost_module); }

// Formats the pending Python exception, traceback included, and clears it.
// Returns NULL only if memory runs out.
static char* take_error(void) {
  PyObject* exc = PyErr_GetRaisedException();
  PyObject* traceback = PyImport_ImportModule("traceback");
  PyObject* lines = NULL;
  if (exc != NULL && traceback != NULL) {
    lines = PyObject_CallMethod(traceback, "format_exception", "O", exc);
  }
  PyObject* empty = PyUnicode_FromString("");
  PyObject* text = NULL;
  if (lines != NULL && empty != NULL) text = PyUnicode_Join(empty, lines);
  const char* utf8 = text != NULL ? PyUnicode_AsUTF8(text) : NULL;
  char* out = strdup(utf8 != NULL ? utf8 : "Python exception (unformattable)");
  Py_XDECREF(text);
  Py_XDECREF(empty);
  Py_XDECREF(lines);
  Py_XDECREF(traceback);
  Py_XDECREF(exc);
  PyErr_Clear();
  return out;
}

int bridge_start(const char* home, char** err) {
  // Built-in modules must be registered before initialization.
  if (PyImport_AppendInittab("gohost", init_gohost) == -1) {
    *err = strdup("could not register the gohost module");
    return -1;
  }

  PyConfig config;
  PyConfig_InitPythonConfig(&config);
  // The Go runtime already owns signal handling. Python's handlers would
  // replace Go's, for example turning SIGINT into KeyboardInterrupt.
  config.install_signal_handlers = 0;
  config.parse_argv = 0;
  PyStatus status = PyStatus_Ok();
  if (home[0] != '\0') {
    status = PyConfig_SetBytesString(&config, &config.home, home);
  }
  if (!PyStatus_Exception(status)) status = Py_InitializeFromConfig(&config);
  PyConfig_Clear(&config);
  if (PyStatus_Exception(status)) {
    *err = strdup(status.err_msg != NULL ? status.err_msg
                                         : "Python initialization failed");
    return -1;
  }

  // Initialization leaves this thread holding the GIL. Release it so that
  // other OS threads can take it with PyGILState_Ensure.
  main_thread_state = PyEval_SaveThread();
  return 0;
}

int bridge_stop(void) {
  PyEval_RestoreThread(main_thread_state);
  return Py_FinalizeEx();
}

int bridge_load_module(const char* name, const char* source,
                       const char* filename, char** err) {
  PyGILState_STATE gil = PyGILState_Ensure();
  PyObject* code = Py_CompileString(source, filename, Py_file_input);
  PyObject* module = NULL;
  if (code != NULL) module = PyImport_ExecCodeModuleEx(name, code, filename);
  int rc = 0;
  if (module == NULL) {
    *err = take_error();
    rc = -1;
  }
  Py_XDECREF(module);
  Py_XDECREF(code);
  PyGILState_Release(gil);
  return rc;
}

void* bridge_lookup(const char* module, const char* attr, char** err) {
  PyGILState_STATE gil = PyGILState_Ensure();
  PyObject* mod = PyImport_ImportModule(module);
  PyObject* callable = NULL;
  if (mod != NULL) callable = PyObject_GetAttrString(mod, attr);
  if (callable == NULL) *err = take_error();
  Py_XDECREF(mod);
  PyGILState_Release(gil);
  return callable;
}

char* bridge_call(void* callable, const char* arg, char** err) {
  PyGILState_STATE gil = PyGILState_Ensure();
  PyObject* result = PyObject_CallFunction((PyObject*)callable, "s", arg);
  const char* utf8 = result != NULL ? PyUnicode_AsUTF8(result) : NULL;
  char* out = NULL;
  if (utf8 != NULL) {
    out = strdup(utf8);
  } else {
    *err = take_error();
  }
  Py_XDECREF(result);
  PyGILState_Release(gil);
  return out;
}
