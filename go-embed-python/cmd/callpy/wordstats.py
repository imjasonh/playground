"""Word statistics for callpy. The Go binary embeds this file with go:embed."""

import json
import os
import sys
import threading

import gohost  # Built into the process by package python (python/bridge.c).


def summarize(payload):
    """Returns statistics about a JSON object such as {"words": [...]}."""
    words = json.loads(payload)["words"]
    gohost.call("log", f"summarize() received {len(words)} words")
    return json.dumps({
        "count": len(words),
        "longest": max(words, key=len),
        "python_version": sys.version.split()[0],
        "go_version": gohost.call("go_version", ""),
        "pid": os.getpid(),
        "module_file": __file__,
        "executable": sys.executable,
    })


def square(n):
    return str(int(n) ** 2)


def thread_id(_):
    return str(threading.get_ident())


def fail(message):
    raise ValueError(message)
