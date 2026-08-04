package firecracker

import (
	"fmt"
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

// CreateTap creates and configures a TAP device (requires CAP_NET_ADMIN).
func CreateTap(name, hostIP string, prefix int) error {
	if out, err := exec.Command("ip", "tuntap", "add", "dev", name, "mode", "tap").CombinedOutput(); err != nil {
		// already exists?
		if !strings.Contains(string(out), "File exists") && !strings.Contains(string(out), "exists") {
			return fmt.Errorf("tuntap add: %v\n%s", err, out)
		}
	}
	cidr := fmt.Sprintf("%s/%d", hostIP, prefix)
	_ = exec.Command("ip", "addr", "flush", "dev", name).Run()
	if out, err := exec.Command("ip", "addr", "add", cidr, "dev", name).CombinedOutput(); err != nil {
		if !strings.Contains(string(out), "File exists") {
			return fmt.Errorf("addr add: %v\n%s", err, out)
		}
	}
	if out, err := exec.Command("ip", "link", "set", "dev", name, "up").CombinedOutput(); err != nil {
		return fmt.Errorf("link up: %v\n%s", err, out)
	}
	return nil
}

// DeleteTap removes a TAP device.
func DeleteTap(name string) error {
	if out, err := exec.Command("ip", "link", "del", "dev", name).CombinedOutput(); err != nil {
		return fmt.Errorf("link del: %v\n%s", err, out)
	}
	return nil
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
