package firecracker

import (
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
)

// Tap holds a host TAP device used by a microVM.
type Tap struct {
	Name    string
	HostIP  string // e.g. 172.16.0.1
	GuestIP string // e.g. 172.16.0.2
	Prefix  int    // e.g. 24
}

// ipCommand runs `ip` directly as root or when systemd supplied CAP_NET_ADMIN.
// Local unprivileged development/CI retains the passwordless-sudo fallback.
func ipCommand(args ...string) *exec.Cmd {
	if os.Geteuid() == 0 || os.Getenv("SSHCLOUD_IP_DIRECT") == "1" {
		return exec.Command("ip", args...)
	}
	return exec.Command("sudo", append([]string{"-n", "ip"}, args...)...)
}

func netfilterCommand(binary string, args ...string) *exec.Cmd {
	if os.Geteuid() == 0 || os.Getenv("SSHCLOUD_IP_DIRECT") == "1" {
		return exec.Command(binary, args...)
	}
	return exec.Command("sudo", append([]string{"-n", binary}, args...)...)
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
	if err := isolateTap(name); err != nil {
		_ = ipCommand("link", "del", "dev", name).Run()
		return err
	}
	return nil
}

// DeleteTap removes a TAP device.
func DeleteTap(name string) error {
	deleteIsolationRules(name)
	if !tapExists(name) {
		return nil
	}
	if out, err := ipCommand("link", "del", "dev", name).CombinedOutput(); err != nil {
		return fmt.Errorf("link del: %v\n%s", err, out)
	}
	return nil
}

func isolateTap(name string) error {
	_ = os.WriteFile(filepath.Join("/proc/sys/net/ipv6/conf", name, "disable_ipv6"), []byte("1\n"), 0o644)
	for _, binary := range []string{"iptables", "ip6tables"} {
		if err := installIsolationRules(binary, name); err != nil {
			deleteIsolationRules(name)
			return err
		}
	}
	return nil
}

func installIsolationRules(binary, name string) error {
	rules := [][]string{
		{"INPUT", "-i", name, "-j", "DROP"},
		{"INPUT", "-i", name, "-m", "conntrack", "--ctstate", "ESTABLISHED,RELATED", "-j", "ACCEPT"},
		{"FORWARD", "-i", name, "-j", "DROP"},
	}
	for _, rule := range rules {
		check := append([]string{"-C"}, rule...)
		if netfilterCommand(binary, check...).Run() == nil {
			continue
		}
		add := append([]string{"-I", rule[0], "1"}, rule[1:]...)
		if out, err := netfilterCommand(binary, add...).CombinedOutput(); err != nil {
			return fmt.Errorf("isolate TAP %s with %s: %v\n%s", name, binary, err, out)
		}
	}
	return nil
}

func deleteIsolationRules(name string) {
	rules := [][]string{
		{"INPUT", "-i", name, "-j", "DROP"},
		{"INPUT", "-i", name, "-m", "conntrack", "--ctstate", "ESTABLISHED,RELATED", "-j", "ACCEPT"},
		{"FORWARD", "-i", name, "-j", "DROP"},
	}
	for _, binary := range []string{"iptables", "ip6tables"} {
		for _, rule := range rules {
			del := append([]string{"-D"}, rule...)
			for netfilterCommand(binary, del...).Run() == nil {
			}
		}
	}
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
