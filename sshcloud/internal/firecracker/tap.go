package firecracker

import (
	"fmt"
	"net"
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

// ipCommand is used only by the explicit direct local/KVM test runtime.
// Production delegates fixed operations to cmd/taphelper.
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
	if err := isolateTap(name, hostIP); err != nil {
		_ = ipCommand("link", "del", "dev", name).Run()
		return err
	}
	return nil
}

// DeleteTap removes a TAP device.
func DeleteTap(name, hostIP string) error {
	deleteIsolationRules(name, hostIP)
	if !tapExists(name) {
		return nil
	}
	if out, err := ipCommand("link", "del", "dev", name).CombinedOutput(); err != nil {
		return fmt.Errorf("link del: %v\n%s", err, out)
	}
	return nil
}

func isolateTap(name, hostIP string) error {
	_ = os.WriteFile(filepath.Join("/proc/sys/net/ipv6/conf", name, "disable_ipv6"), []byte("1\n"), 0o644)
	for _, binary := range []string{"iptables", "ip6tables"} {
		if err := installIsolationRules(binary, name, hostIP); err != nil {
			deleteIsolationRules(name, hostIP)
			return err
		}
	}
	return nil
}

func isolationRules(binary, name, hostIP string) ([][]string, error) {
	rules := [][]string{
		{"INPUT", "-i", name, "-j", "DROP"},
		{"FORWARD", "-i", name, "-j", "DROP"},
	}
	if binary == "ip6tables" {
		return rules, nil
	}
	host := net.ParseIP(hostIP)
	if host == nil || host.To4() == nil || host.String() != hostIP || host.To4()[3] != 1 {
		return nil, fmt.Errorf("invalid TAP host IPv4 address %q", hostIP)
	}
	host4 := host.To4()
	guestIP := net.IPv4(host4[0], host4[1], host4[2], 2).String()
	rules = append(rules, []string{
		"INPUT", "-i", name,
		"-s", guestIP + "/32",
		"-d", hostIP + "/32",
		"-m", "conntrack", "--ctstate", "ESTABLISHED,RELATED",
		"-j", "ACCEPT",
	})
	return rules, nil
}

func installIsolationRules(binary, name, hostIP string) error {
	rules, err := isolationRules(binary, name, hostIP)
	if err != nil {
		return err
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

func deleteIsolationRules(name, hostIP string) {
	for _, binary := range []string{"iptables", "ip6tables"} {
		rules, err := isolationRules(binary, name, hostIP)
		if err != nil {
			continue
		}
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
