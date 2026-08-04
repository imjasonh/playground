package firecracker

import (
	"fmt"
	"os"
	"os/exec"
	"strings"
)

// Tap holds a host TAP device used by a microVM.
type Tap struct {
	Name    string
	HostIP  string // e.g. 172.16.0.1
	GuestIP string // e.g. 172.16.0.2
	Prefix  int    // e.g. 24
}

// ipCommand runs `ip` as root via sudo when the current process is unprivileged.
func ipCommand(args ...string) *exec.Cmd {
	if os.Geteuid() == 0 {
		return exec.Command("ip", args...)
	}
	return exec.Command("sudo", append([]string{"-n", "ip"}, args...)...)
}

// CreateTap creates and configures a TAP device (requires CAP_NET_ADMIN).
// When not root, the TAP is owned by the current uid so Firecracker can open it.
// Idempotent if the device already exists.
func CreateTap(name, hostIP string, prefix int) error {
	if !tapExists(name) {
		args := []string{"tuntap", "add", "dev", name, "mode", "tap"}
		if os.Geteuid() != 0 {
			args = append(args, "user", fmt.Sprintf("%d", os.Getuid()))
		}
		if out, err := ipCommand(args...).CombinedOutput(); err != nil {
			if !tapExists(name) && !strings.Contains(string(out), "exists") {
				return fmt.Errorf("tuntap add: %v\n%s", err, out)
			}
		}
	}
	cidr := fmt.Sprintf("%s/%d", hostIP, prefix)
	_ = ipCommand("addr", "flush", "dev", name).Run()
	if out, err := ipCommand("addr", "add", cidr, "dev", name).CombinedOutput(); err != nil {
		if !strings.Contains(string(out), "File exists") {
			return fmt.Errorf("addr add: %v\n%s", err, out)
		}
	}
	if out, err := ipCommand("link", "set", "dev", name, "up").CombinedOutput(); err != nil {
		return fmt.Errorf("link up: %v\n%s", err, out)
	}
	return nil
}

// DeleteTap removes a TAP device.
func DeleteTap(name string) error {
	if !tapExists(name) {
		return nil
	}
	if out, err := ipCommand("link", "del", "dev", name).CombinedOutput(); err != nil {
		return fmt.Errorf("link del: %v\n%s", err, out)
	}
	return nil
}

func tapExists(name string) bool {
	return ipCommand("link", "show", "dev", name).Run() == nil
}

// GuestBootArgs returns kernel IP config for a static virtio-net address.
// Format: ip=<client-IP>::<gw-IP>:<netmask>:<hostname>:<device>:off
func GuestBootArgs(guestIP, gatewayIP, netmask, hostname string) string {
	if hostname == "" {
		hostname = "app"
	}
	if netmask == "" {
		netmask = "255.255.255.0"
	}
	return fmt.Sprintf("ip=%s::%s:%s:%s:eth0:off", guestIP, gatewayIP, netmask, hostname)
}
