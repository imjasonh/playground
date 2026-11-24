package bot

import (
	"context"
	"os/exec"
	"strings"
	"syscall"
	"time"
)

// command returns the command that runs args in dir.
//
// The bot never starts an action directly in its exec root. On Linux, Go
// starts a child with vfork, and the parent's thread can't be preempted
// until the child calls execve. A child that changes into an exec root
// served by FUSE from this process waits for the FUSE server, and a garbage
// collection that is stopping the world never lets the server answer, so
// the process deadlocks. The child execs bash instead, which is not on the
// mount, and bash enters the exec root as a process of its own.
//
// Each action runs in its own process group so timeout or lease cancellation
// terminates the entire process tree instead of leaving grandchild processes
// behind.
//
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
	// $1 is the directory, $2 the argv[0] the action asked for, $3 the
	// resolved program. exec -a keeps that argv[0]; bash can, and the
	// runner image's shell is bash.
	const script = `cd "$1" || exit 127; shift; name=$1; shift; prog=$1; shift; exec -a "$name" "$prog" "$@"`
	argv := append([]string{"-c", script, "bash", dir, args[0], path}, args[1:]...)
	cmd := exec.CommandContext(ctx, b.shell, argv...)
	cmd.SysProcAttr = &syscall.SysProcAttr{Setpgid: true}
	cmd.Cancel = func() error {
		if cmd.Process == nil {
			return nil
		}
		return syscall.Kill(-cmd.Process.Pid, syscall.SIGKILL)
	}
	cmd.WaitDelay = 5 * time.Second
	return cmd, nil
}
