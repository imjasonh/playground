package bot

import (
	"context"
	"log/slog"
	"os"
	"os/exec"
	"strings"
	"syscall"
)

// launcherArg, as the first argument of the program that runs a Bot, makes
// the program a launcher: it changes to a directory and replaces itself with
// an action's command.
const launcherArg = "-ci-substrate-launch-in"

// RunLauncher turns the process into a launcher when its arguments ask for
// one, and otherwise returns. A program that runs a Bot calls it first thing
// in main, and a test binary that runs one calls it in TestMain.
//
// The bot never starts an action directly in its exec root. On Linux, Go
// starts a child with vfork, and the parent's thread can't be preempted
// until the child calls execve. A child that changes into an exec root
// served by FUSE from this process waits for the FUSE server, and a garbage
// collection that is stopping the world never lets the server answer, so
// the process deadlocks. The child execs the launcher instead, whose binary
// is not on the mount, and the launcher enters the exec root as a process of
// its own.
func RunLauncher() {
	if len(os.Args) < 5 || os.Args[1] != launcherArg {
		return
	}
	dir, path, argv := os.Args[2], os.Args[3], os.Args[4:]
	if err := syscall.Chdir(dir); err != nil {
		slog.Error("launcher: entering the exec root", "dir", dir, "err", err)
		os.Exit(127)
	}
	err := syscall.Exec(path, argv, os.Environ())
	slog.Error("launcher: starting the command", "path", path, "err", err)
	os.Exit(127)
}

// command returns the command that runs args in dir through the launcher.
// A program name with no slash is looked up on the bot's PATH, as
// exec.Command does; a relative path is relative to dir.
func (b *Bot) command(ctx context.Context, dir string, args []string) (*exec.Cmd, error) {
	path := args[0]
	if !strings.Contains(path, "/") {
		lp, err := exec.LookPath(path)
		if err != nil {
			return nil, err
		}
		path = lp
	}
	return exec.CommandContext(ctx, b.launcher, append([]string{launcherArg, dir, path}, args...)...), nil
}
