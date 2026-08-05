package taphelper

import (
	"bytes"
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"net"
	"os"
	"os/exec"
	"path/filepath"
	"strconv"
	"strings"
	"syscall"
	"time"

	"github.com/imjasonh/playground/sshcloud/internal/helperrpc"
	"github.com/imjasonh/playground/sshcloud/internal/hostisolation"
	"golang.org/x/sys/unix"
)

const (
	defaultIPPath        = "/usr/sbin/ip"
	defaultIPTablesPath  = "/usr/sbin/iptables"
	defaultIP6TablesPath = "/usr/sbin/ip6tables"
	commandTimeout       = 10 * time.Second
	maxDeleteAttempts    = 16
)

// Runner executes helper-selected binaries and arguments.
type Runner interface {
	Run(ctx context.Context, path string, args ...string) ([]byte, error)
}

type execRunner struct{}

func (execRunner) Run(ctx context.Context, path string, args ...string) ([]byte, error) {
	return exec.CommandContext(ctx, path, args...).CombinedOutput()
}

// Config contains only operator-fixed values.
type Config struct {
	SubnetBase      string
	SandboxIDBase   uint32
	ExpectedPeerUID uint32
	IPPath          string
	IPTablesPath    string
	IP6TablesPath   string
	Runner          Runner
}

func (c *Config) defaults() {
	if c.SandboxIDBase == 0 {
		c.SandboxIDBase = hostisolation.DefaultSandboxIDBase
	}
	if c.IPPath == "" {
		c.IPPath = defaultIPPath
	}
	if c.IPTablesPath == "" {
		c.IPTablesPath = defaultIPTablesPath
	}
	if c.IP6TablesPath == "" {
		c.IP6TablesPath = defaultIP6TablesPath
	}
	if c.Runner == nil {
		c.Runner = execRunner{}
	}
}

func (c Config) validate() error {
	if c.ExpectedPeerUID == 0 {
		return fmt.Errorf("unprivileged agent UID required")
	}
	if err := hostisolation.ValidateHostIP(c.SubnetBase+".1.1", c.SubnetBase); err != nil {
		return fmt.Errorf("subnet base: %w", err)
	}
	if _, err := hostisolation.SandboxID("000000000000", c.SandboxIDBase); err != nil {
		return err
	}
	for label, command := range map[string]struct {
		path string
		base string
	}{
		"ip":        {path: c.IPPath, base: "ip"},
		"iptables":  {path: c.IPTablesPath, base: "iptables"},
		"ip6tables": {path: c.IP6TablesPath, base: "ip6tables"},
	} {
		if !filepath.IsAbs(command.path) || filepath.Clean(command.path) != command.path ||
			filepath.Base(command.path) != command.base {
			return fmt.Errorf("%s command must be a fixed absolute path", label)
		}
	}
	return nil
}

// Rule is one immutable netfilter rule shape.
type Rule struct {
	Chain          string
	InsertPosition int
	Match          []string
}

// IsolationRules returns the complete per-TAP deny-by-default ruleset.
func IsolationRules(tapName string) ([]Rule, error) {
	if _, err := hostisolation.VMIDFromTapName(tapName); err != nil {
		return nil, err
	}
	return []Rule{
		{
			Chain: "INPUT", InsertPosition: 1,
			Match: []string{"-i", tapName, "-m", "conntrack", "--ctstate", "ESTABLISHED,RELATED", "-j", "ACCEPT"},
		},
		{
			Chain: "INPUT", InsertPosition: 2,
			Match: []string{"-i", tapName, "-j", "DROP"},
		},
		{
			Chain: "FORWARD", InsertPosition: 1,
			Match: []string{"-i", tapName, "-j", "DROP"},
		},
	}, nil
}

// Server validates and constructs fixed TAP/network operations.
type Server struct {
	config Config
}

// NewServer applies fixed command paths and validates configuration.
func NewServer(config Config) (*Server, error) {
	config.defaults()
	if err := config.validate(); err != nil {
		return nil, err
	}
	return &Server{config: config}, nil
}

// Ready verifies that this separate process has only the capability it needs
// from the host network boundary's perspective.
func (s *Server) Ready(ctx context.Context) error {
	mask, err := effectiveCapabilities()
	if err != nil {
		return err
	}
	want := uint64(1) << uint(unix.CAP_NET_ADMIN)
	if mask != want {
		return fmt.Errorf("effective capabilities %#x, want CAP_NET_ADMIN only (%#x)", mask, want)
	}
	for _, path := range []string{s.config.IPPath, s.config.IPTablesPath, s.config.IP6TablesPath} {
		info, err := os.Stat(path)
		if err != nil {
			return err
		}
		if !info.Mode().IsRegular() || info.Mode().Perm()&0o111 == 0 {
			return fmt.Errorf("%q is not an executable regular file", path)
		}
		stat, ok := info.Sys().(*syscall.Stat_t)
		if !ok || stat.Uid != 0 || info.Mode().Perm()&0o022 != 0 {
			return fmt.Errorf("%q must be root-owned and not group/world writable", path)
		}
	}
	tunInfo, err := os.Stat("/dev/net/tun")
	if err != nil {
		return err
	}
	tunStat, ok := tunInfo.Sys().(*syscall.Stat_t)
	if !ok || !tunInfo.Mode().IsRegular() && tunInfo.Mode()&os.ModeDevice == 0 ||
		unix.Major(uint64(tunStat.Rdev)) != 10 || unix.Minor(uint64(tunStat.Rdev)) != 200 {
		return fmt.Errorf("/dev/net/tun has unexpected device type or number")
	}
	tunFD, err := unix.Open("/dev/net/tun", unix.O_RDWR|unix.O_CLOEXEC, 0)
	if err != nil {
		return fmt.Errorf("open /dev/net/tun through service device policy: %w", err)
	}
	_ = unix.Close(tunFD)
	if err := s.run(ctx, s.config.IPPath, "link", "show", "dev", "lo"); err != nil {
		return fmt.Errorf("netlink readiness: %w", err)
	}
	for _, binary := range []string{s.config.IPTablesPath, s.config.IP6TablesPath} {
		if err := s.run(ctx, binary, "-w", "2", "-n", "-L"); err != nil {
			return fmt.Errorf("netfilter readiness: %w", err)
		}
	}
	return nil
}

func effectiveCapabilities() (uint64, error) {
	content, err := os.ReadFile("/proc/self/status")
	if err != nil {
		return 0, err
	}
	for _, line := range strings.Split(string(content), "\n") {
		if !strings.HasPrefix(line, "CapEff:") {
			continue
		}
		value := strings.TrimSpace(strings.TrimPrefix(line, "CapEff:"))
		mask, err := strconv.ParseUint(value, 16, 64)
		if err != nil {
			return 0, err
		}
		return mask, nil
	}
	return 0, fmt.Errorf("CapEff missing from /proc/self/status")
}

// Serve authenticates each RPC connection independently.
func (s *Server) Serve(listener net.Listener) error {
	return helperrpc.Serve(listener, s.config.ExpectedPeerUID, s.handle)
}

func (s *Server) handle(ctx context.Context, operation string, payload json.RawMessage) (any, error) {
	switch operation {
	case operationReady:
		return nil, s.Ready(ctx)
	case operationCreate:
		var request CreateRequest
		if err := decodePayload(payload, &request); err != nil {
			return nil, err
		}
		return nil, s.Create(ctx, request)
	case operationDelete:
		var request vmRequest
		if err := decodePayload(payload, &request); err != nil {
			return nil, err
		}
		return nil, s.Delete(ctx, request.VMID)
	default:
		return nil, fmt.Errorf("unsupported operation %q", operation)
	}
}

func decodePayload(payload json.RawMessage, dst any) error {
	decoder := json.NewDecoder(bytes.NewReader(payload))
	decoder.DisallowUnknownFields()
	if err := decoder.Decode(dst); err != nil {
		return fmt.Errorf("decode payload: %w", err)
	}
	if decoder.Decode(&struct{}{}) != io.EOF {
		return fmt.Errorf("decode payload: trailing JSON")
	}
	return nil
}

func (s *Server) commandContext(parent context.Context) (context.Context, context.CancelFunc) {
	return context.WithTimeout(parent, commandTimeout)
}

func (s *Server) run(ctx context.Context, path string, args ...string) error {
	commandCtx, cancel := s.commandContext(ctx)
	defer cancel()
	output, err := s.config.Runner.Run(commandCtx, path, args...)
	if err != nil {
		return fmt.Errorf("%s %s: %w: %s", path, strings.Join(args, " "), err, bytes.TrimSpace(output))
	}
	return nil
}

func (s *Server) succeeds(ctx context.Context, path string, args ...string) bool {
	commandCtx, cancel := s.commandContext(ctx)
	defer cancel()
	_, err := s.config.Runner.Run(commandCtx, path, args...)
	return err == nil
}

// Create creates one fixed-name /24 TAP owned by the VM's derived jail UID,
// then installs the fixed IPv4 and IPv6 isolation rules.
func (s *Server) Create(ctx context.Context, request CreateRequest) (retErr error) {
	if err := hostisolation.ValidateVMID(request.VMID); err != nil {
		return err
	}
	if err := hostisolation.ValidateHostIP(request.HostIP, s.config.SubnetBase); err != nil {
		return err
	}
	tapName, _ := hostisolation.TapName(request.VMID)
	owner, err := hostisolation.SandboxID(request.VMID, s.config.SandboxIDBase)
	if err != nil {
		return err
	}
	prepared := false
	defer func() {
		if retErr != nil && prepared {
			_ = s.Delete(context.Background(), request.VMID)
		}
	}()
	if s.succeeds(ctx, s.config.IPPath, "link", "show", "dev", tapName) {
		// Never trust a stale fixed-name interface's type or owner. No VMM is
		// running when the manager asks Create during boot/restore, so replace
		// it with the helper-derived TAP instead of adopting it.
		if err := s.Delete(ctx, request.VMID); err != nil {
			return err
		}
	}
	if err := s.run(ctx, s.config.IPPath,
		"tuntap", "add", "dev", tapName, "mode", "tap", "user", strconv.FormatUint(uint64(owner), 10)); err != nil {
		return err
	}
	prepared = true
	if err := s.run(ctx, s.config.IPPath, "addr", "flush", "dev", tapName); err != nil {
		return err
	}
	if err := s.run(ctx, s.config.IPPath, "addr", "add", request.HostIP+"/24", "dev", tapName); err != nil {
		return err
	}
	if err := s.run(ctx, s.config.IPPath, "link", "set", "dev", tapName, "up"); err != nil {
		return err
	}
	if err := s.installRules(ctx, tapName); err != nil {
		return err
	}
	return nil
}

func (s *Server) installRules(ctx context.Context, tapName string) error {
	rules, err := IsolationRules(tapName)
	if err != nil {
		return err
	}
	for _, binary := range []string{s.config.IPTablesPath, s.config.IP6TablesPath} {
		for _, rule := range rules {
			check := append([]string{"-w", "2", "-C", rule.Chain}, rule.Match...)
			if s.succeeds(ctx, binary, check...) {
				continue
			}
			add := append([]string{"-w", "2", "-I", rule.Chain, strconv.Itoa(rule.InsertPosition)}, rule.Match...)
			if err := s.run(ctx, binary, add...); err != nil {
				return err
			}
		}
	}
	return nil
}

// Delete removes only the derived TAP and exact fixed rules.
func (s *Server) Delete(ctx context.Context, vmID string) error {
	if err := hostisolation.ValidateVMID(vmID); err != nil {
		return err
	}
	tapName, _ := hostisolation.TapName(vmID)
	rules, _ := IsolationRules(tapName)
	var errs []error
	for _, binary := range []string{s.config.IPTablesPath, s.config.IP6TablesPath} {
		for _, rule := range rules {
			del := append([]string{"-w", "2", "-D", rule.Chain}, rule.Match...)
			for attempt := 0; attempt < maxDeleteAttempts && s.succeeds(ctx, binary, del...); attempt++ {
			}
		}
	}
	if s.succeeds(ctx, s.config.IPPath, "link", "show", "dev", tapName) {
		if err := s.run(ctx, s.config.IPPath, "link", "del", "dev", tapName); err != nil {
			errs = append(errs, err)
		}
	}
	return errors.Join(errs...)
}
