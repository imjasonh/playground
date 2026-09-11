#!/usr/bin/env python3
"""Relay bytes between a child pty and a JSON-lines parent.

The parent writes JSON lines on stdin and reads JSON lines on stdout.
This process does not interpret the child.
"""

from __future__ import annotations

import base64
import errno
import json
import os
import pty
import select
import signal
import struct
import sys
import termios
import tty
import fcntl


def write_msg(obj: dict) -> None:
    sys.stdout.write(json.dumps(obj, separators=(",", ":")) + "\n")
    sys.stdout.flush()


def set_winsize(fd: int, rows: int, cols: int) -> None:
    packed = struct.pack("HHHH", rows, cols, 0, 0)
    fcntl.ioctl(fd, termios.TIOCSWINSZ, packed)


def main() -> int:
    if len(sys.argv) < 2:
        print("usage: pty_bridge.py COMMAND [ARGS...]", file=sys.stderr)
        return 2

    cmd = sys.argv[1:]
    rows = int(os.environ.get("PTY_ROWS", "24"))
    cols = int(os.environ.get("PTY_COLS", "80"))

    pid, fd = pty.fork()
    if pid == 0:
        os.environ["TERM"] = os.environ.get("TERM") or "xterm-256color"
        os.environ.setdefault("LANG", "C.UTF-8")
        try:
            tty.setraw(0)
        except tty.error:
            pass
        try:
            os.execvp(cmd[0], cmd)
        except OSError as exc:
            print(f"exec failed: {exc}", file=sys.stderr)
            os._exit(127)

    try:
        set_winsize(fd, rows, cols)
        os.kill(pid, signal.SIGWINCH)
    except OSError:
        pass

    stdin_buf = b""
    stdin_open = True
    child_done = False
    exit_code = 0

    def reap() -> None:
        nonlocal child_done, exit_code
        try:
            waited, status = os.waitpid(pid, os.WNOHANG)
        except ChildProcessError:
            child_done = True
            return
        if waited == 0:
            return
        child_done = True
        if os.WIFEXITED(status):
            exit_code = os.WEXITSTATUS(status)
        elif os.WIFSIGNALED(status):
            exit_code = 128 + os.WTERMSIG(status)
        else:
            exit_code = status

    try:
        while True:
            watch = [fd]
            if stdin_open:
                watch.append(sys.stdin.fileno())
            try:
                readable, _, _ = select.select(watch, [], [], 0.05)
            except InterruptedError:
                readable = []

            if fd in readable:
                try:
                    data = os.read(fd, 4096)
                except OSError as exc:
                    if exc.errno not in (errno.EIO, errno.EBADF):
                        raise
                    data = b""
                if data:
                    write_msg(
                        {
                            "type": "bytes",
                            "b64": base64.b64encode(data).decode("ascii"),
                        }
                    )
                else:
                    reap()

            reap()

            if stdin_open and sys.stdin.fileno() in readable:
                try:
                    chunk = os.read(sys.stdin.fileno(), 4096)
                except OSError:
                    chunk = b""
                if not chunk:
                    stdin_open = False
                else:
                    stdin_buf += chunk
                    while b"\n" in stdin_buf:
                        line, stdin_buf = stdin_buf.split(b"\n", 1)
                        if not line.strip():
                            continue
                        try:
                            msg = json.loads(line.decode("utf-8"))
                        except (UnicodeDecodeError, json.JSONDecodeError):
                            continue
                        kind = msg.get("type")
                        if kind == "write":
                            raw = base64.b64decode(msg.get("b64", ""))
                            if raw:
                                try:
                                    os.write(fd, raw)
                                except OSError:
                                    child_done = True
                        elif kind == "close":
                            try:
                                os.kill(pid, signal.SIGHUP)
                            except OSError:
                                pass

            if child_done:
                # One last non-blocking drain.
                try:
                    leftover = os.read(fd, 4096)
                except OSError:
                    leftover = b""
                if leftover:
                    write_msg(
                        {
                            "type": "bytes",
                            "b64": base64.b64encode(leftover).decode("ascii"),
                        }
                    )
                write_msg({"type": "exit", "code": exit_code})
                break
    finally:
        try:
            os.close(fd)
        except OSError:
            pass
        if not child_done:
            try:
                os.kill(pid, signal.SIGHUP)
            except OSError:
                pass
            try:
                os.waitpid(pid, 0)
            except ChildProcessError:
                pass

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
