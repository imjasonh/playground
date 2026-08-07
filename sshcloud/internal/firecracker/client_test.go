package firecracker

import (
	"os/exec"
	"testing"
	"time"
)

func TestMachineAliveDetectsRunningAndExitedProcesses(t *testing.T) {
	t.Parallel()
	runningCmd := exec.Command("sh", "-c", "sleep 30")
	if err := runningCmd.Start(); err != nil {
		t.Fatal(err)
	}
	running := &Machine{cmd: runningCmd}
	if !running.Alive() {
		t.Fatal("running process reported dead")
	}
	if err := running.Kill(); err != nil {
		t.Fatal(err)
	}
	if running.Alive() {
		t.Fatal("killed process reported alive")
	}

	exitedCmd := exec.Command("sh", "-c", "exit 0")
	if err := exitedCmd.Start(); err != nil {
		t.Fatal(err)
	}
	exited := &Machine{cmd: exitedCmd}
	deadline := time.Now().Add(2 * time.Second)
	for exited.Alive() && time.Now().Before(deadline) {
		time.Sleep(5 * time.Millisecond)
	}
	if exited.Alive() {
		_ = exitedCmd.Process.Kill()
		_ = exitedCmd.Wait()
		t.Fatal("exited-but-unreaped process reported alive")
	}
	_ = exitedCmd.Wait()
}
