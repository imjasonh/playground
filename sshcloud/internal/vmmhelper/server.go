package vmmhelper

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
	"sync"
	"syscall"
	"time"

	"github.com/imjasonh/playground/sshcloud/internal/helperrpc"
	"github.com/imjasonh/playground/sshcloud/internal/hostisolation"
	"github.com/imjasonh/playground/sshcloud/internal/observability"
	"golang.org/x/sys/unix"
)

const (
	apiReadyTimeout  = 5 * time.Second
	processStopWait  = 5 * time.Second
	maxBinaryBytes   = 256 << 20
	maxKernelBytes   = 256 << 20
	maxRootfsBytes   = 2 << 30
	maxStateBytes    = 128 << 20
	snapshotOverhead = 64 << 20
)

// Config contains operator-fixed paths and identities. No value is populated
// from an agent request.
type Config struct {
	WorkRoot       string
	ChrootBase     string
	Firecracker    string
	Jailer         string
	Kernel         string
	ProxyDir       string
	CgroupParent   string
	AgentUID       uint32
	AgentGID       uint32
	ExpectedPeerID uint32
	HostID         string
}

func normalizeHostID(value string) string {
	value = strings.TrimSpace(value)
	if value == "" {
		value, _ = os.Hostname()
	}
	if dot := strings.IndexByte(value, '.'); dot > 0 {
		value = value[:dot]
	}
	var clean strings.Builder
	for _, char := range value {
		if (char >= 'a' && char <= 'z') || (char >= 'A' && char <= 'Z') ||
			(char >= '0' && char <= '9') || char == '-' || char == '_' || char == '.' {
			clean.WriteRune(char)
		} else {
			clean.WriteByte('-')
		}
		if clean.Len() == 63 {
			break
		}
	}
	value = strings.TrimLeft(clean.String(), "._-")
	if value == "" {
		return "unknown"
	}
	return value
}

func (c Config) validate() error {
	for label, value := range map[string]string{
		"work root":     c.WorkRoot,
		"chroot base":   c.ChrootBase,
		"firecracker":   c.Firecracker,
		"jailer":        c.Jailer,
		"kernel":        c.Kernel,
		"API proxy dir": c.ProxyDir,
		"cgroup parent": c.CgroupParent,
	} {
		if value == "" {
			return fmt.Errorf("%s required", label)
		}
	}
	for label, value := range map[string]string{
		"work root":     c.WorkRoot,
		"chroot base":   c.ChrootBase,
		"firecracker":   c.Firecracker,
		"jailer":        c.Jailer,
		"kernel":        c.Kernel,
		"API proxy dir": c.ProxyDir,
	} {
		if !filepath.IsAbs(value) || filepath.Clean(value) != value {
			return fmt.Errorf("%s must be a clean absolute path", label)
		}
	}
	if filepath.Base(c.Firecracker) != "firecracker" {
		return fmt.Errorf("Firecracker executable must be named firecracker")
	}
	if filepath.Base(c.Jailer) != "jailer" {
		return fmt.Errorf("jailer executable must be named jailer")
	}
	if filepath.IsAbs(c.CgroupParent) || c.CgroupParent == "." ||
		strings.Contains(c.CgroupParent, "/") || strings.Contains(c.CgroupParent, "..") {
		return fmt.Errorf("cgroup parent must be one safe relative segment")
	}
	if c.AgentUID == 0 || c.AgentGID == 0 || c.ExpectedPeerID == 0 {
		return fmt.Errorf("unprivileged agent UID/GID required")
	}
	return nil
}

// JailerArgv returns the complete fixed jailer argument vector for a request.
// It is exported so the security-sensitive command shape has a direct unit
// test; production launch uses this function without appending arguments.
func JailerArgv(config Config, request LaunchRequest, uid, gid uint32) ([]string, error) {
	if err := config.validate(); err != nil {
		return nil, err
	}
	if err := request.validate(); err != nil {
		return nil, err
	}
	wantID, err := hostisolation.SandboxID(request.VMID)
	if err != nil {
		return nil, err
	}
	if uid != wantID || gid != wantID {
		return nil, fmt.Errorf("sandbox UID/GID must be helper-derived")
	}
	memoryMaxMiB := int64(512)
	if request.MemMiB == 512 {
		// Snapshot and restore can transiently account both guest memory and
		// filesystem page cache to the VMM cgroup.
		memoryMaxMiB = 1536
	}
	memoryMax := memoryMaxMiB << 20
	cpuQuota := request.VCPUs * 100_000
	fileSizeMax := (request.MemMiB + 1024) << 20
	return []string{
		"--id", request.VMID,
		"--exec-file", config.Firecracker,
		"--uid", strconv.FormatUint(uint64(uid), 10),
		"--gid", strconv.FormatUint(uint64(gid), 10),
		"--chroot-base-dir", config.ChrootBase,
		"--cgroup-version", "2",
		"--parent-cgroup", config.CgroupParent,
		"--cgroup", fmt.Sprintf("memory.max=%d", memoryMax),
		"--cgroup", "memory.swap.max=0",
		"--cgroup", "memory.oom.group=1",
		"--cgroup", fmt.Sprintf("cpu.max=%d 100000", cpuQuota),
		"--cgroup", "pids.max=64",
		"--resource-limit", "no-file=1024",
		"--resource-limit", fmt.Sprintf("fsize=%d", fileSizeMax),
		"--",
		"--api-sock", hostisolation.FirecrackerAPISocket,
	}, nil
}

type managedVM struct {
	id        string
	uid       uint32
	memMiB    int64
	cmd       *exec.Cmd
	done      chan struct{}
	jailDir   string
	apiSocket string
	proxyPath string
	output    *observability.ConsoleSink

	mu           sync.Mutex
	proxy        net.Listener
	terminated   bool
	rootfsSynced bool
	jailRemoved  bool
}

func (vm *managedVM) alive() bool {
	select {
	case <-vm.done:
		return false
	default:
		return true
	}
}

func (vm *managedVM) closeProxy() {
	vm.mu.Lock()
	defer vm.mu.Unlock()
	if vm.proxy != nil {
		_ = vm.proxy.Close()
		vm.proxy = nil
	}
	_ = os.Remove(vm.proxyPath)
}

func (vm *managedVM) markTerminated() {
	vm.mu.Lock()
	vm.terminated = true
	vm.mu.Unlock()
}

func (vm *managedVM) terminationWasConfirmed() bool {
	vm.mu.Lock()
	defer vm.mu.Unlock()
	return vm.terminated
}

// Server owns every jailer process it launches.
type Server struct {
	config Config
	// terminateCgroup is fixed to killCgroup in production and replaceable only
	// by same-package tests that exercise fail-closed teardown.
	terminateCgroup func(string) error

	mu              sync.Mutex
	vms             map[string]*managedVM
	operations      map[string]*sync.Mutex
	uidReservations map[uint32]string
	active          sync.WaitGroup
	closing         bool
}

// NewServer validates immutable helper configuration.
func NewServer(config Config) (*Server, error) {
	config.HostID = normalizeHostID(config.HostID)
	if err := config.validate(); err != nil {
		return nil, err
	}
	return &Server{
		config:          config,
		terminateCgroup: killCgroup,
		vms:             make(map[string]*managedVM),
		operations:      make(map[string]*sync.Mutex),
		uidReservations: make(map[uint32]string),
	}, nil
}

// Ready verifies root-only substrate and exact pinned binaries.
func (s *Server) Ready(ctx context.Context) error {
	if os.Geteuid() != 0 {
		return fmt.Errorf("VMM helper must run as root")
	}
	for label, asset := range map[string]struct {
		path  string
		limit int64
	}{
		"firecracker": {path: s.config.Firecracker, limit: maxBinaryBytes},
		"jailer":      {path: s.config.Jailer, limit: maxBinaryBytes},
		"kernel":      {path: s.config.Kernel, limit: maxKernelBytes},
	} {
		if err := validateRootAsset(asset.path, asset.limit); err != nil {
			return fmt.Errorf("%s asset: %w", label, err)
		}
		if label == "kernel" {
			continue
		}
		checkCtx, cancel := context.WithTimeout(ctx, 2*time.Second)
		output, err := exec.CommandContext(checkCtx, asset.path, "--version").CombinedOutput()
		cancel()
		if err != nil {
			return fmt.Errorf("%s --version: %w: %s", label, err, bytes.TrimSpace(output))
		}
		if !containsWord(output, hostisolation.FirecrackerVersion) {
			return fmt.Errorf("%s is not pinned %s: %s", label, hostisolation.FirecrackerVersion, bytes.TrimSpace(output))
		}
	}
	capabilities, err := effectiveCapabilities()
	if err != nil {
		return err
	}
	wantCapabilities := capabilityMask(
		unix.CAP_CHOWN,
		unix.CAP_DAC_OVERRIDE,
		unix.CAP_FOWNER,
		unix.CAP_KILL,
		unix.CAP_SETGID,
		unix.CAP_SETUID,
		unix.CAP_SYS_CHROOT,
		unix.CAP_SYS_ADMIN,
		unix.CAP_SYS_RESOURCE,
		unix.CAP_MKNOD,
	)
	if capabilities != wantCapabilities {
		return fmt.Errorf("effective capabilities %#x, want fixed VMM helper set %#x", capabilities, wantCapabilities)
	}
	for _, device := range []struct {
		path         string
		major, minor uint32
	}{
		{path: "/dev/kvm", major: 10, minor: 232},
		{path: "/dev/net/tun", major: 10, minor: 200},
	} {
		info, err := os.Stat(device.path)
		if err != nil {
			return fmt.Errorf("%s: %w", device.path, err)
		}
		if info.Mode()&os.ModeDevice == 0 {
			return fmt.Errorf("%s is not a device", device.path)
		}
		stat, ok := info.Sys().(*syscall.Stat_t)
		if !ok || unix.Major(uint64(stat.Rdev)) != device.major || unix.Minor(uint64(stat.Rdev)) != device.minor {
			return fmt.Errorf("%s has unexpected device number", device.path)
		}
		fd, err := unix.Open(device.path, unix.O_RDWR|unix.O_CLOEXEC, 0)
		if err != nil {
			return fmt.Errorf("open %s through service device policy: %w", device.path, err)
		}
		_ = unix.Close(fd)
	}
	if _, err := os.Stat("/sys/fs/cgroup/cgroup.controllers"); err != nil {
		return fmt.Errorf("cgroup v2 unified hierarchy: %w", err)
	}
	parent := filepath.Join("/sys/fs/cgroup", s.config.CgroupParent)
	for _, name := range []string{"cgroup.kill", "cgroup.events"} {
		if _, err := os.Stat(filepath.Join(parent, name)); err != nil {
			return fmt.Errorf("cgroup v2 recursive termination %s: %w", name, err)
		}
	}
	controllers, err := os.ReadFile(filepath.Join(parent, "cgroup.controllers"))
	if err != nil {
		return fmt.Errorf("cgroup v2 parent controllers: %w", err)
	}
	enabled, err := os.ReadFile(filepath.Join(parent, "cgroup.subtree_control"))
	if err != nil {
		return fmt.Errorf("cgroup v2 parent delegation: %w", err)
	}
	for _, controller := range []string{"cpu", "memory", "pids"} {
		if !containsWord(controllers, controller) || !containsWord(enabled, controller) {
			return fmt.Errorf("cgroup v2 controller %s is not delegated under %s", controller, parent)
		}
	}
	for _, dir := range []struct {
		path  string
		owner uint32
	}{
		{path: s.config.WorkRoot, owner: s.config.AgentUID},
		{path: s.config.ChrootBase, owner: 0},
		{path: s.config.ProxyDir, owner: 0},
	} {
		if err := validateDirectory(dir.path, dir.owner); err != nil {
			return err
		}
	}
	return nil
}

// CleanupOrphans kills and removes only validated VM cgroups/jails left by a
// previous helper process. Work directories are preserved, and the fixed
// jailed rootfs is synchronized back after stopping the orphan when possible.
func (s *Server) CleanupOrphans() error {
	ids := make(map[string]bool)
	for _, root := range []string{
		filepath.Join("/sys/fs/cgroup", s.config.CgroupParent),
		filepath.Join(s.config.ChrootBase, "firecracker"),
	} {
		entries, err := os.ReadDir(root)
		if err != nil {
			if os.IsNotExist(err) {
				continue
			}
			return err
		}
		for _, entry := range entries {
			if entry.IsDir() && hostisolation.ValidateVMID(entry.Name()) == nil {
				ids[entry.Name()] = true
			}
		}
	}
	var errs []error
	for id := range ids {
		cgroupDir := filepath.Join("/sys/fs/cgroup", s.config.CgroupParent, id)
		if err := killCgroup(cgroupDir); err != nil {
			errs = append(errs, fmt.Errorf("kill orphan %s: %w", id, err))
			continue
		}
		jailDir := filepath.Join(s.config.ChrootBase, "firecracker", id, "root")
		uid, err := hostisolation.SandboxID(id)
		if err != nil {
			errs = append(errs, fmt.Errorf("derive orphan %s identity: %w", id, err))
			continue
		}
		vm := &managedVM{id: id, uid: uid, jailDir: jailDir}
		jailRootFD, jailErr := s.openJailRoot(id)
		switch {
		case jailErr == nil:
			rootfs, _, rootfsErr := s.openJailFile(jailRootFD, vm, "rootfs.ext4", maxRootfsBytes)
			_ = unix.Close(jailRootFD)
			if rootfsErr == nil {
				_ = rootfs.Close()
				relativeDir, _ := hostisolation.WorkRelativePath(id)
				workFD, workErr := openBeneath(s.config.WorkRoot, relativeDir, unix.O_RDONLY|unix.O_DIRECTORY)
				if workErr == nil {
					_ = unix.Close(workFD)
					if err := s.syncRootfs(vm); err != nil {
						errs = append(errs, fmt.Errorf("sync orphan %s rootfs: %w", id, err))
						continue
					}
				} else if !os.IsNotExist(workErr) {
					errs = append(errs, fmt.Errorf("inspect orphan %s work directory: %w", id, workErr))
					continue
				}
			} else if !os.IsNotExist(rootfsErr) {
				errs = append(errs, fmt.Errorf("inspect orphan %s rootfs: %w", id, rootfsErr))
				continue
			}
		case !os.IsNotExist(jailErr):
			errs = append(errs, fmt.Errorf("open orphan %s jail: %w", id, jailErr))
			continue
		}
		if err := os.RemoveAll(filepath.Dir(jailDir)); err != nil {
			errs = append(errs, err)
		}
		if err := os.Remove(cgroupDir); err != nil && !os.IsNotExist(err) {
			errs = append(errs, err)
		}
		_ = os.Remove(filepath.Join(s.config.ProxyDir, id+".sock"))
	}
	return errors.Join(errs...)
}

func killCgroup(cgroupDir string) error {
	return killCgroupWithin(cgroupDir, processStopWait)
}

func killCgroupWithin(cgroupDir string, wait time.Duration) error {
	info, err := os.Stat(cgroupDir)
	if err != nil {
		return fmt.Errorf("open derived cgroup: %w", err)
	}
	if !info.IsDir() {
		return fmt.Errorf("derived cgroup is not a directory")
	}
	if err := os.WriteFile(filepath.Join(cgroupDir, "cgroup.kill"), []byte("1\n"), 0o600); err != nil {
		return fmt.Errorf("kill complete derived cgroup: %w", err)
	}
	deadline := time.Now().Add(wait)
	for {
		content, err := os.ReadFile(filepath.Join(cgroupDir, "cgroup.events"))
		if err != nil {
			return fmt.Errorf("prove derived cgroup empty: %w", err)
		}
		populated, err := cgroupPopulated(content)
		if err != nil {
			return err
		}
		if !populated {
			return nil
		}
		if time.Now().After(deadline) {
			return fmt.Errorf("derived cgroup remains populated")
		}
		time.Sleep(20 * time.Millisecond)
	}
}

func cgroupPopulated(content []byte) (bool, error) {
	for _, line := range bytes.Split(content, []byte{'\n'}) {
		fields := bytes.Fields(line)
		if len(fields) != 2 || string(fields[0]) != "populated" {
			continue
		}
		switch string(fields[1]) {
		case "0":
			return false, nil
		case "1":
			return true, nil
		default:
			return false, fmt.Errorf("invalid populated value in cgroup.events")
		}
	}
	return false, fmt.Errorf("populated is missing from cgroup.events")
}

func containsWord(content []byte, word string) bool {
	for _, field := range bytes.Fields(content) {
		if string(field) == word {
			return true
		}
	}
	return false
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

func capabilityMask(capabilities ...int) uint64 {
	var mask uint64
	for _, capability := range capabilities {
		mask |= uint64(1) << uint(capability)
	}
	return mask
}

func validateRootAsset(path string, maxBytes int64) error {
	info, err := os.Lstat(path)
	if err != nil {
		return err
	}
	if !info.Mode().IsRegular() {
		return fmt.Errorf("%q is not a regular file", path)
	}
	stat, ok := info.Sys().(*syscall.Stat_t)
	if !ok || stat.Uid != 0 || stat.Gid != 0 {
		return fmt.Errorf("%q must be owned by root:root", path)
	}
	if info.Mode().Perm()&0o022 != 0 {
		return fmt.Errorf("%q must not be group/world writable", path)
	}
	if info.Size() <= 0 || info.Size() > maxBytes {
		return fmt.Errorf("%q size %d is outside 1..%d", path, info.Size(), maxBytes)
	}
	return nil
}

func validateDirectory(path string, owner uint32) error {
	info, err := os.Lstat(path)
	if err != nil {
		return fmt.Errorf("directory %q: %w", path, err)
	}
	if !info.IsDir() {
		return fmt.Errorf("%q is not a directory", path)
	}
	stat, ok := info.Sys().(*syscall.Stat_t)
	if !ok || stat.Uid != owner {
		return fmt.Errorf("%q must be owned by UID %d", path, owner)
	}
	if info.Mode().Perm()&0o022 != 0 {
		return fmt.Errorf("%q must not be group/world writable", path)
	}
	return nil
}

// Serve authenticates every RPC connection with SO_PEERCRED.
func (s *Server) Serve(listener net.Listener) error {
	return helperrpc.Serve(listener, s.config.ExpectedPeerID, s.handle)
}

func (s *Server) handle(ctx context.Context, operation string, payload json.RawMessage) (any, error) {
	s.mu.Lock()
	if s.closing {
		s.mu.Unlock()
		return nil, fmt.Errorf("VMM helper is shutting down")
	}
	s.active.Add(1)
	s.mu.Unlock()
	defer s.active.Done()

	switch operation {
	case operationReady:
		return nil, s.Ready(ctx)
	case operationLaunch:
		var request LaunchRequest
		if err := decodePayload(payload, &request); err != nil {
			return nil, err
		}
		return s.launch(ctx, request)
	case operationAlive:
		var request vmRequest
		if err := decodePayload(payload, &request); err != nil {
			return nil, err
		}
		alive, err := s.alive(request.VMID)
		return aliveResponse{Alive: alive}, err
	case operationKill:
		var request vmRequest
		if err := decodePayload(payload, &request); err != nil {
			return nil, err
		}
		return s.kill(request.VMID)
	case operationExportSnapshot:
		var request vmRequest
		if err := decodePayload(payload, &request); err != nil {
			return nil, err
		}
		return nil, s.exportSnapshot(request.VMID)
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

func (s *Server) launch(ctx context.Context, request LaunchRequest) (response LaunchResponse, retErr error) {
	if err := request.validate(); err != nil {
		return LaunchResponse{}, err
	}
	startedAt := time.Now()
	identity := request.Identity
	identity.Host = s.config.HostID
	operation := "boot"
	if request.Mode == LaunchRestore {
		operation = "restore"
	}
	defer func() {
		outcome := observability.OutcomeSuccess
		state := "running"
		if retErr != nil {
			outcome = observability.OutcomeFailure
			state = "failed"
		}
		observability.Emit(observability.LifecycleEvent{
			Identity: identity, Operation: operation, State: state,
			Outcome: outcome, Duration: time.Since(startedAt),
		})
	}()
	uid, err := hostisolation.SandboxID(request.VMID)
	if err != nil {
		return LaunchResponse{}, err
	}
	args, err := JailerArgv(s.config, request, uid, uid)
	if err != nil {
		return LaunchResponse{}, err
	}

	operationLock := s.operationLock(request.VMID)
	operationLock.Lock()
	defer operationLock.Unlock()

	s.mu.Lock()
	if existing := s.vms[request.VMID]; existing != nil {
		s.mu.Unlock()
		return LaunchResponse{}, fmt.Errorf("VM %s is already tracked", request.VMID)
	}
	if owner, reserved := s.uidReservations[uid]; reserved {
		s.mu.Unlock()
		return LaunchResponse{}, fmt.Errorf("sandbox identity collision between %s and %s", request.VMID, owner)
	}
	for id, existing := range s.vms {
		if existing.uid == uid {
			s.mu.Unlock()
			return LaunchResponse{}, fmt.Errorf("sandbox identity collision between %s and %s", request.VMID, id)
		}
	}
	s.uidReservations[uid] = request.VMID
	s.mu.Unlock()
	reserved := true
	defer func() {
		if !reserved {
			return
		}
		s.mu.Lock()
		if s.uidReservations[uid] == request.VMID {
			delete(s.uidReservations, uid)
		}
		s.mu.Unlock()
	}()

	jailDir, err := s.prepareJail(request, uid)
	if err != nil {
		return LaunchResponse{}, err
	}
	output, err := observability.NewConsoleSink(observability.ConsoleConfig{
		Identity: identity,
	})
	if err != nil {
		_ = os.RemoveAll(filepath.Dir(jailDir))
		return LaunchResponse{}, err
	}
	cmd := exec.Command(s.config.Jailer, args...)
	cmd.Stdout = output.AppWriter()
	cmd.Stderr = output.DiagnosticsWriter()
	if err := cmd.Start(); err != nil {
		output.Close()
		_ = os.RemoveAll(filepath.Dir(jailDir))
		return LaunchResponse{}, fmt.Errorf("start pinned jailer: %w", err)
	}

	vm := &managedVM{
		id:        request.VMID,
		uid:       uid,
		memMiB:    request.MemMiB,
		cmd:       cmd,
		done:      make(chan struct{}),
		jailDir:   jailDir,
		apiSocket: filepath.Join(jailDir, strings.TrimPrefix(hostisolation.FirecrackerAPISocket, "/")),
		proxyPath: filepath.Join(s.config.ProxyDir, request.VMID+".sock"),
		output:    output,
	}
	s.mu.Lock()
	delete(s.uidReservations, uid)
	reserved = false
	s.vms[request.VMID] = vm
	s.mu.Unlock()

	go func() {
		_ = cmd.Wait()
		close(vm.done)
		output.Close()
		vm.closeProxy()
	}()

	if err := waitUnixSocket(ctx, vm.apiSocket, vm.done, vm.uid); err != nil {
		_, _ = s.killLocked(request.VMID)
		return LaunchResponse{}, fmt.Errorf("jailed Firecracker API: %w", err)
	}
	if err := s.sealJailRun(vm); err != nil {
		_, _ = s.killLocked(request.VMID)
		return LaunchResponse{}, fmt.Errorf("seal jailed API directory: %w", err)
	}
	if err := s.startProxy(vm); err != nil {
		_, _ = s.killLocked(request.VMID)
		return LaunchResponse{}, err
	}
	return LaunchResponse{APISocket: vm.proxyPath, UID: uid, GID: uid}, nil
}

func (s *Server) operationLock(vmID string) *sync.Mutex {
	s.mu.Lock()
	defer s.mu.Unlock()
	lock := s.operations[vmID]
	if lock == nil {
		lock = &sync.Mutex{}
		s.operations[vmID] = lock
	}
	return lock
}

func (s *Server) prepareJail(request LaunchRequest, uid uint32) (_ string, retErr error) {
	instanceDir := filepath.Join(s.config.ChrootBase, "firecracker", request.VMID)
	jailDir := filepath.Join(instanceDir, "root")
	if _, err := os.Lstat(instanceDir); err == nil {
		return "", fmt.Errorf("fixed jail path for VM %s already exists", request.VMID)
	} else if !os.IsNotExist(err) {
		return "", err
	}
	if err := os.MkdirAll(jailDir, 0o755); err != nil {
		return "", err
	}
	defer func() {
		if retErr != nil {
			_ = os.RemoveAll(instanceDir)
		}
	}()
	if err := os.Chown(jailDir, 0, 0); err != nil {
		return "", err
	}
	if err := os.Chmod(jailDir, 0o755); err != nil {
		return "", err
	}
	for _, dir := range []string{
		filepath.Join(jailDir, "run"),
		filepath.Join(jailDir, strings.TrimPrefix(hostisolation.JailedSnapshotDir, "/")),
	} {
		if err := os.Mkdir(dir, 0o700); err != nil {
			return "", err
		}
		if err := os.Chown(dir, int(uid), int(uid)); err != nil {
			return "", err
		}
		if err := os.Chmod(dir, 0o700); err != nil {
			return "", err
		}
	}
	jailRootFD, err := s.openJailRoot(request.VMID)
	if err != nil {
		return "", err
	}
	defer unix.Close(jailRootFD)
	if err := copyFixedAsset(
		s.config.Kernel,
		jailRootFD, strings.TrimPrefix(hostisolation.JailedKernelPath, "/"),
		0o400, uid, uid, maxKernelBytes,
	); err != nil {
		// The configured kernel is deliberately not request-selectable. It is
		// expected beside Firecracker in the immutable asset directory.
		return "", fmt.Errorf("stage fixed kernel: %w", err)
	}

	rootfsParts := []string{"rootfs.ext4"}
	if request.Mode == LaunchRestore {
		rootfsParts = []string{hostisolation.HostRestoreDir, "rootfs.ext4"}
	}
	rootfsRel, _ := hostisolation.WorkRelativePath(request.VMID, rootfsParts...)
	if err := s.copyWorkFile(rootfsRel, jailRootFD, "rootfs.ext4", 0o600, uid, maxRootfsBytes); err != nil {
		return "", fmt.Errorf("stage fixed rootfs: %w", err)
	}
	if request.Mode == LaunchRestore {
		for _, artifact := range []struct {
			name  string
			limit int64
		}{
			{name: "vm.state", limit: maxStateBytes},
			{name: "vm.mem", limit: (request.MemMiB << 20) + snapshotOverhead},
		} {
			rel, _ := hostisolation.WorkRelativePath(request.VMID, hostisolation.HostRestoreDir, artifact.name)
			dst := filepath.Join(strings.TrimPrefix(hostisolation.JailedSnapshotDir, "/"), artifact.name)
			if err := s.copyWorkFile(rel, jailRootFD, dst, 0o600, uid, artifact.limit); err != nil {
				return "", fmt.Errorf("stage fixed snapshot %s: %w", artifact.name, err)
			}
		}
	}
	return jailDir, nil
}

func copyFixedAsset(srcPath string, dstRootFD int, dstRelative string, mode os.FileMode, uid, gid uint32, maxBytes int64) error {
	fd, err := unix.Open(srcPath, unix.O_RDONLY|unix.O_CLOEXEC|unix.O_NOFOLLOW, 0)
	if err != nil {
		return err
	}
	src := os.NewFile(uintptr(fd), srcPath)
	if src == nil {
		_ = unix.Close(fd)
		return fmt.Errorf("open fixed asset %q", srcPath)
	}
	defer src.Close()
	info, err := src.Stat()
	if err != nil {
		return err
	}
	stat, ok := info.Sys().(*syscall.Stat_t)
	if !ok || !info.Mode().IsRegular() || stat.Uid != 0 || stat.Gid != 0 ||
		info.Mode().Perm()&0o022 != 0 {
		return fmt.Errorf("%q must be a root-owned, non-writable regular file", srcPath)
	}
	return copyFileAt(src, dstRootFD, dstRelative, mode, uid, gid, maxBytes)
}

func (s *Server) copyWorkFile(relativePath string, dstRootFD int, dstRelative string, mode os.FileMode, uid uint32, maxBytes int64) error {
	fd, err := openBeneath(s.config.WorkRoot, relativePath, unix.O_RDONLY)
	if err != nil {
		return err
	}
	src := os.NewFile(uintptr(fd), relativePath)
	if src == nil {
		_ = unix.Close(fd)
		return fmt.Errorf("open %s", relativePath)
	}
	defer src.Close()
	if err := validateOpenRegularFile(src, s.config.AgentUID, s.config.AgentGID, maxBytes); err != nil {
		return fmt.Errorf("fixed work path %q: %w", relativePath, err)
	}
	return copyFileAt(src, dstRootFD, dstRelative, mode, uid, uid, maxBytes)
}

func validateOpenRegularFile(file *os.File, uid, gid uint32, maxBytes int64) error {
	info, err := file.Stat()
	if err != nil {
		return err
	}
	stat, ok := info.Sys().(*syscall.Stat_t)
	if !ok || !info.Mode().IsRegular() {
		return fmt.Errorf("source is not a regular file")
	}
	if stat.Uid != uid || stat.Gid != gid {
		return fmt.Errorf("source owner is %d:%d, want %d:%d", stat.Uid, stat.Gid, uid, gid)
	}
	if info.Size() <= 0 || info.Size() > maxBytes {
		return fmt.Errorf("source size %d is outside 1..%d", info.Size(), maxBytes)
	}
	return nil
}

func copyFileAt(src *os.File, dstRootFD int, dstRelative string, mode os.FileMode, uid, gid uint32, maxBytes int64) error {
	info, err := src.Stat()
	if err != nil {
		return err
	}
	if !info.Mode().IsRegular() {
		return fmt.Errorf("source is not a regular file")
	}
	if info.Size() <= 0 || info.Size() > maxBytes {
		return fmt.Errorf("source size %d is outside 1..%d", info.Size(), maxBytes)
	}
	fd, err := openAtBeneath(
		dstRootFD, dstRelative,
		unix.O_WRONLY|unix.O_CREAT|unix.O_EXCL,
		uint32(mode.Perm()),
	)
	if err != nil {
		return err
	}
	dst := os.NewFile(uintptr(fd), dstRelative)
	if dst == nil {
		_ = unix.Close(fd)
		return fmt.Errorf("open destination %q", dstRelative)
	}
	ok := false
	defer func() {
		_ = dst.Close()
		if !ok {
			_ = unix.Unlinkat(dstRootFD, dstRelative, 0)
		}
	}()
	copied, err := io.Copy(dst, io.LimitReader(src, maxBytes+1))
	if err != nil {
		return err
	}
	if copied > maxBytes {
		return fmt.Errorf("source exceeds maximum size %d", maxBytes)
	}
	if copied != info.Size() {
		return fmt.Errorf("source size changed while staging: copied %d, expected %d", copied, info.Size())
	}
	if err := dst.Chmod(mode); err != nil {
		return err
	}
	if err := dst.Chown(int(uid), int(gid)); err != nil {
		return err
	}
	if err := dst.Sync(); err != nil {
		return err
	}
	if err := dst.Close(); err != nil {
		return err
	}
	ok = true
	return nil
}

func openBeneath(root, relativePath string, flags int) (int, error) {
	rootFD, err := unix.Open(root, unix.O_PATH|unix.O_DIRECTORY|unix.O_CLOEXEC|unix.O_NOFOLLOW, 0)
	if err != nil {
		return -1, err
	}
	defer unix.Close(rootFD)
	fd, err := openAtBeneath(rootFD, relativePath, flags, 0)
	if err != nil {
		return -1, fmt.Errorf("open fixed path %q beneath %q: %w", relativePath, root, err)
	}
	return fd, nil
}

func openAtBeneath(rootFD int, relativePath string, flags int, mode uint32) (int, error) {
	if relativePath == "" || filepath.IsAbs(relativePath) || filepath.Clean(relativePath) != relativePath {
		return -1, fmt.Errorf("invalid relative path %q", relativePath)
	}
	how := &unix.OpenHow{
		Flags: uint64(flags | unix.O_CLOEXEC | unix.O_NOFOLLOW),
		Mode:  uint64(mode),
		Resolve: unix.RESOLVE_BENEATH |
			unix.RESOLVE_NO_SYMLINKS |
			unix.RESOLVE_NO_MAGICLINKS,
	}
	fd, err := unix.Openat2(rootFD, relativePath, how)
	if err != nil {
		return -1, err
	}
	var stat unix.Stat_t
	if err := unix.Fstat(fd, &stat); err != nil {
		_ = unix.Close(fd)
		return -1, err
	}
	if flags&unix.O_DIRECTORY == 0 && stat.Mode&unix.S_IFMT != unix.S_IFREG {
		_ = unix.Close(fd)
		return -1, fmt.Errorf("fixed path %q is not regular", relativePath)
	}
	return fd, nil
}

func (s *Server) openJailRoot(vmID string) (int, error) {
	if err := hostisolation.ValidateVMID(vmID); err != nil {
		return -1, err
	}
	relative := filepath.Join("firecracker", vmID, "root")
	fd, err := openBeneath(s.config.ChrootBase, relative, unix.O_RDONLY|unix.O_DIRECTORY)
	if err != nil {
		return -1, err
	}
	var stat unix.Stat_t
	if err := unix.Fstat(fd, &stat); err != nil {
		_ = unix.Close(fd)
		return -1, err
	}
	sandboxID, _ := hostisolation.SandboxID(vmID)
	rootOwned := stat.Uid == 0 && stat.Gid == 0
	sandboxOwned := stat.Uid == sandboxID && stat.Gid == sandboxID
	if (!rootOwned && !sandboxOwned) || stat.Mode&0o022 != 0 {
		_ = unix.Close(fd)
		return -1, fmt.Errorf("fixed jail root has unexpected ownership or group/world write access")
	}
	return fd, nil
}

func (s *Server) openJailFile(jailRootFD int, vm *managedVM, relativePath string, maxBytes int64) (*os.File, int64, error) {
	fd, err := openAtBeneath(jailRootFD, relativePath, unix.O_RDONLY, 0)
	if err != nil {
		return nil, 0, fmt.Errorf("open fixed jail path %q: %w", relativePath, err)
	}
	file := os.NewFile(uintptr(fd), relativePath)
	if file == nil {
		_ = unix.Close(fd)
		return nil, 0, fmt.Errorf("open fixed jail path %q", relativePath)
	}
	if err := validateOpenRegularFile(file, vm.uid, vm.uid, maxBytes); err != nil {
		_ = file.Close()
		return nil, 0, fmt.Errorf("fixed jail path %q: %w", relativePath, err)
	}
	info, err := file.Stat()
	if err != nil {
		_ = file.Close()
		return nil, 0, err
	}
	return file, info.Size(), nil
}

func waitUnixSocket(ctx context.Context, path string, processDone <-chan struct{}, expectedUID uint32) error {
	timer := time.NewTimer(apiReadyTimeout)
	defer timer.Stop()
	ticker := time.NewTicker(20 * time.Millisecond)
	defer ticker.Stop()
	for {
		conn, err := net.DialTimeout("unix", path, 100*time.Millisecond)
		if err == nil {
			_, authErr := helperrpc.AuthorizePeer(conn, expectedUID)
			_ = conn.Close()
			if authErr != nil {
				return fmt.Errorf("API socket peer: %w", authErr)
			}
			return nil
		}
		select {
		case <-ctx.Done():
			return ctx.Err()
		case <-processDone:
			return fmt.Errorf("jailer exited before creating API socket")
		case <-timer.C:
			return fmt.Errorf("timeout waiting for %s", path)
		case <-ticker.C:
		}
	}
}

func (s *Server) sealJailRun(vm *managedVM) error {
	jailRootFD, err := s.openJailRoot(vm.id)
	if err != nil {
		return err
	}
	defer unix.Close(jailRootFD)
	runFD, err := openAtBeneath(jailRootFD, "run", unix.O_RDONLY|unix.O_DIRECTORY, 0)
	if err != nil {
		return fmt.Errorf("open fixed /run: %w", err)
	}
	defer unix.Close(runFD)
	var runStat unix.Stat_t
	if err := unix.Fstat(runFD, &runStat); err != nil {
		return err
	}
	if runStat.Uid != vm.uid || runStat.Gid != vm.uid {
		return fmt.Errorf("jailed /run owner is %d:%d, want %d:%d", runStat.Uid, runStat.Gid, vm.uid, vm.uid)
	}
	if err := unix.Fchown(runFD, 0, 0); err != nil {
		return err
	}
	if err := unix.Fchmod(runFD, 0o555); err != nil {
		return err
	}
	if err := unix.Fstat(runFD, &runStat); err != nil {
		return err
	}
	if runStat.Uid != 0 || runStat.Gid != 0 || runStat.Mode&0o222 != 0 {
		return fmt.Errorf("jailed /run remains writable by sandbox")
	}
	if err := unix.Fchown(jailRootFD, 0, 0); err != nil {
		return err
	}
	if err := unix.Fchmod(jailRootFD, 0o555); err != nil {
		return err
	}
	var rootStat unix.Stat_t
	if err := unix.Fstat(jailRootFD, &rootStat); err != nil {
		return err
	}
	if rootStat.Uid != 0 || rootStat.Gid != 0 || rootStat.Mode&0o222 != 0 {
		return fmt.Errorf("jailed root remains writable by sandbox")
	}
	var socketStat unix.Stat_t
	if err := unix.Fstatat(runFD, "firecracker.socket", &socketStat, unix.AT_SYMLINK_NOFOLLOW); err != nil {
		return err
	}
	if socketStat.Mode&unix.S_IFMT != unix.S_IFSOCK ||
		socketStat.Uid != vm.uid || socketStat.Gid != vm.uid {
		return fmt.Errorf("jailed API path is not the sandbox-owned fixed Unix socket")
	}
	return nil
}

func (s *Server) startProxy(vm *managedVM) error {
	_ = os.Remove(vm.proxyPath)
	listener, err := net.Listen("unix", vm.proxyPath)
	if err != nil {
		return err
	}
	cleanup := func(cause error) error {
		_ = listener.Close()
		_ = os.Remove(vm.proxyPath)
		return cause
	}
	if err := os.Chmod(vm.proxyPath, 0o600); err != nil {
		return cleanup(err)
	}
	if err := os.Chown(vm.proxyPath, int(s.config.AgentUID), int(s.config.AgentGID)); err != nil {
		return cleanup(err)
	}
	vm.mu.Lock()
	if !vm.alive() {
		vm.mu.Unlock()
		return cleanup(fmt.Errorf("jailer exited before API proxy was ready"))
	}
	vm.proxy = listener
	vm.mu.Unlock()
	go s.proxyLoop(vm, listener)
	return nil
}

func (s *Server) proxyLoop(vm *managedVM, listener net.Listener) {
	for {
		client, err := listener.Accept()
		if err != nil {
			return
		}
		go s.proxyConn(vm, client)
	}
}

func (s *Server) proxyConn(vm *managedVM, client net.Conn) {
	defer client.Close()
	if _, err := helperrpc.AuthorizePeer(client, s.config.ExpectedPeerID); err != nil {
		return
	}
	upstream, err := net.DialTimeout("unix", vm.apiSocket, time.Second)
	if err != nil {
		return
	}
	defer upstream.Close()
	if _, err := helperrpc.AuthorizePeer(upstream, vm.uid); err != nil {
		return
	}
	done := make(chan struct{}, 2)
	copyOneWay := func(dst, src net.Conn) {
		_, _ = io.Copy(dst, src)
		if unixConn, ok := dst.(*net.UnixConn); ok {
			_ = unixConn.CloseWrite()
		}
		done <- struct{}{}
	}
	go copyOneWay(upstream, client)
	go copyOneWay(client, upstream)
	<-done
}

func (s *Server) alive(vmID string) (bool, error) {
	if err := hostisolation.ValidateVMID(vmID); err != nil {
		return false, err
	}
	operationLock := s.operationLock(vmID)
	operationLock.Lock()
	defer operationLock.Unlock()
	s.mu.Lock()
	vm := s.vms[vmID]
	s.mu.Unlock()
	return vm != nil && vm.alive(), nil
}

func (s *Server) kill(vmID string) (killResponse, error) {
	if err := hostisolation.ValidateVMID(vmID); err != nil {
		return killResponse{}, err
	}
	operationLock := s.operationLock(vmID)
	operationLock.Lock()
	defer operationLock.Unlock()
	return s.killLocked(vmID)
}

func (s *Server) killLocked(vmID string) (killResponse, error) {
	s.mu.Lock()
	vm := s.vms[vmID]
	s.mu.Unlock()
	if vm == nil {
		cgroupDir := filepath.Join("/sys/fs/cgroup", s.config.CgroupParent, vmID)
		if _, err := os.Stat(cgroupDir); err == nil {
			terminate := s.terminateCgroup
			if terminate == nil {
				terminate = killCgroup
			}
			if err := terminate(cgroupDir); err != nil {
				return killResponse{}, fmt.Errorf("terminate untracked VM %s cgroup: %w", vmID, err)
			}
			response := killResponse{Terminated: true}
			if err := os.Remove(cgroupDir); err != nil && !os.IsNotExist(err) {
				response.CleanupError = fmt.Sprintf("remove untracked VM %s cgroup: %v", vmID, err)
			}
			return response, nil
		} else if !os.IsNotExist(err) {
			return killResponse{}, fmt.Errorf("inspect untracked VM %s cgroup: %w", vmID, err)
		}
		return killResponse{Terminated: true}, nil
	}

	vm.closeProxy()
	if !vm.terminationWasConfirmed() {
		terminate := s.terminateCgroup
		if terminate == nil {
			terminate = killCgroup
		}
		cgroupDir := filepath.Join("/sys/fs/cgroup", s.config.CgroupParent, vmID)
		if err := terminate(cgroupDir); err != nil {
			return killResponse{}, fmt.Errorf("terminate VM %s cgroup: %w", vmID, err)
		}
		vm.markTerminated()
	}
	response := killResponse{Terminated: true}
	select {
	case <-vm.done:
	case <-time.After(processStopWait):
		response.CleanupError = fmt.Sprintf("timeout reaping VM %s after cgroup termination", vmID)
		return response, nil
	}
	if !vm.rootfsSynced {
		if err := s.syncRootfs(vm); err != nil {
			response.CleanupError = fmt.Sprintf("synchronize VM %s rootfs: %v", vmID, err)
			return response, nil
		}
		vm.rootfsSynced = true
	}
	if !vm.jailRemoved {
		if err := os.RemoveAll(filepath.Dir(vm.jailDir)); err != nil {
			response.CleanupError = fmt.Sprintf("remove VM %s jail: %v", vmID, err)
			return response, nil
		}
		vm.jailRemoved = true
	}
	cgroupDir := filepath.Join("/sys/fs/cgroup", s.config.CgroupParent, vmID)
	if err := os.Remove(cgroupDir); err != nil && !os.IsNotExist(err) {
		response.CleanupError = fmt.Sprintf("remove VM %s cgroup: %v", vmID, err)
		return response, nil
	}
	s.mu.Lock()
	if s.vms[vmID] == vm {
		delete(s.vms, vmID)
	}
	s.mu.Unlock()
	return response, nil
}

func (s *Server) syncRootfs(vm *managedVM) error {
	relativeDir, _ := hostisolation.WorkRelativePath(vm.id)
	dirFD, err := openBeneath(s.config.WorkRoot, relativeDir, unix.O_RDONLY|unix.O_DIRECTORY)
	if err != nil {
		return err
	}
	defer unix.Close(dirFD)
	jailRootFD, err := s.openJailRoot(vm.id)
	if err != nil {
		return err
	}
	defer unix.Close(jailRootFD)
	source, size, err := s.openJailFile(jailRootFD, vm, "rootfs.ext4", maxRootfsBytes)
	if err != nil {
		return err
	}
	defer source.Close()
	return s.copySnapshotOutput(dirFD, source, size, "rootfs.ext4", maxRootfsBytes)
}

func (s *Server) exportSnapshot(vmID string) error {
	if err := hostisolation.ValidateVMID(vmID); err != nil {
		return err
	}
	operationLock := s.operationLock(vmID)
	operationLock.Lock()
	defer operationLock.Unlock()
	s.mu.Lock()
	vm := s.vms[vmID]
	s.mu.Unlock()
	if vm == nil || !vm.alive() {
		return fmt.Errorf("VM %s is not running", vmID)
	}
	relativeDir, _ := hostisolation.WorkRelativePath(vmID, hostisolation.HostSnapshotDir)
	dirFD, err := openBeneath(s.config.WorkRoot, relativeDir, unix.O_RDONLY|unix.O_DIRECTORY)
	if err != nil {
		return err
	}
	defer unix.Close(dirFD)
	jailRootFD, err := s.openJailRoot(vm.id)
	if err != nil {
		return err
	}
	defer unix.Close(jailRootFD)

	files := []struct {
		src   string
		name  string
		limit int64
	}{
		{src: "snapshot/vm.state", name: "vm.state", limit: maxStateBytes},
		{src: "snapshot/vm.mem", name: "vm.mem", limit: (vm.memMiB << 20) + snapshotOverhead},
		{src: "rootfs.ext4", name: "rootfs.ext4", limit: maxRootfsBytes},
	}
	for _, file := range files {
		source, size, err := s.openJailFile(jailRootFD, vm, file.src, file.limit)
		if err != nil {
			return fmt.Errorf("export %s: %w", file.name, err)
		}
		copyErr := s.copySnapshotOutput(dirFD, source, size, file.name, file.limit)
		_ = source.Close()
		if copyErr != nil {
			return fmt.Errorf("export %s: %w", file.name, copyErr)
		}
	}
	return nil
}

func (s *Server) copySnapshotOutput(dirFD int, source *os.File, sourceSize int64, name string, maxBytes int64) error {
	tmpName := ".vmmhelper-" + name
	_ = unix.Unlinkat(dirFD, tmpName, 0)
	fd, err := unix.Openat(dirFD, tmpName, unix.O_WRONLY|unix.O_CREAT|unix.O_EXCL|unix.O_CLOEXEC|unix.O_NOFOLLOW, 0o600)
	if err != nil {
		return err
	}
	tmp := os.NewFile(uintptr(fd), tmpName)
	ok := false
	defer func() {
		_ = tmp.Close()
		if !ok {
			_ = unix.Unlinkat(dirFD, tmpName, 0)
		}
	}()
	copied, err := io.Copy(tmp, io.LimitReader(source, maxBytes+1))
	if err != nil {
		return err
	}
	if copied > maxBytes {
		return fmt.Errorf("fixed snapshot source exceeds maximum size %d", maxBytes)
	}
	if copied != sourceSize {
		return fmt.Errorf("fixed snapshot source size changed: copied %d, expected %d", copied, sourceSize)
	}
	info, err := source.Stat()
	if err != nil {
		return err
	}
	if !info.Mode().IsRegular() || info.Size() != sourceSize {
		return fmt.Errorf("fixed snapshot source changed while copying")
	}
	if err := unix.Fchown(fd, int(s.config.AgentUID), int(s.config.AgentGID)); err != nil {
		return err
	}
	if err := tmp.Sync(); err != nil {
		return err
	}
	if err := tmp.Close(); err != nil {
		return err
	}
	if err := unix.Renameat(dirFD, tmpName, dirFD, name); err != nil {
		return err
	}
	ok = true
	return nil
}

// Close kills every child before the root helper exits.
func (s *Server) Close() error {
	s.mu.Lock()
	s.closing = true
	s.mu.Unlock()
	s.active.Wait()

	s.mu.Lock()
	ids := make([]string, 0, len(s.vms))
	for id := range s.vms {
		ids = append(ids, id)
	}
	s.mu.Unlock()
	var first error
	for _, id := range ids {
		response, err := s.kill(id)
		if err == nil && response.CleanupError != "" {
			err = errors.New(response.CleanupError)
		}
		if err != nil && first == nil {
			first = err
		}
	}
	return first
}
