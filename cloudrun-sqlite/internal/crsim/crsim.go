// Package crsim runs a local stand-in for a Cloud Run service: it starts
// container processes on demand when requests arrive, gives each one a fresh
// scratch directory, stops idle ones with SIGTERM and a grace period before
// SIGKILL, can freeze instances between requests the way request-based
// billing throttles CPU, and can deploy a new revision while the old one is
// still serving.
package crsim

import (
	"bufio"
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"io/fs"
	"log/slog"
	"math/rand/v2"
	"net"
	"net/http"
	"net/http/httputil"
	"net/url"
	"os"
	"os/exec"
	"path/filepath"
	"strconv"
	"strings"
	"sync"
	"syscall"
	"time"
)

// Config configures a simulated service.
type Config struct {
	// Command is the container entrypoint and its arguments.
	Command []string
	// Env is added to each instance's environment, after PORT, K_SERVICE,
	// K_REVISION, and TMPDIR.
	Env []string
	// IdleTimeout scales an instance to zero after this long without
	// requests. Zero disables it. Cloud Run waits up to 15 minutes.
	IdleTimeout time.Duration
	// GracePeriod is the time between SIGTERM and SIGKILL. Cloud Run gives
	// 10 seconds.
	GracePeriod time.Duration
	// Throttle freezes instances with SIGSTOP whenever no request is in
	// flight, like request-based billing, which allocates CPU only while
	// requests are being handled.
	Throttle bool
	// StartTimeout bounds how long an instance has to start listening.
	StartTimeout time.Duration
	// Output receives instance stdout and stderr, prefixed by instance ID.
	Output io.Writer
	Logger *slog.Logger
}

// Sim is a simulated Cloud Run service. It is an http.Handler: requests
// under /_crsim/ control the simulator, and everything else is proxied to an
// instance.
type Sim struct {
	cfg Config

	mu       sync.Mutex
	revision int
	seq      int
	active   *instance   // receives new requests
	overlap  *instance   // also receives requests until overlapUntil
	overlapT time.Time   // end of the overlap window
	all      []*instance // every instance ever started
	starting chan struct{}
	closed   bool
}

type instance struct {
	sim      *Sim
	id       string
	revision int
	cmd      *exec.Cmd
	port     int
	dir      string
	proxy    *httputil.ReverseProxy
	ready    chan struct{}
	readyErr error
	exited   chan struct{}

	// Guarded by sim.mu.
	inflight   int
	frozen     bool
	lastActive time.Time
	stopping   bool

	Stats InstanceStats
}

// InstanceStats describes one instance's lifetime.
type InstanceStats struct {
	ID          string     `json:"id"`
	Revision    int        `json:"revision"`
	StartedAt   time.Time  `json:"started_at"`
	ReadyMillis float64    `json:"ready_ms"`
	Requests    int64      `json:"requests"`
	PeakRSS     int64      `json:"peak_rss_bytes"`
	PeakDisk    int64      `json:"peak_disk_bytes"`
	ExitedAt    *time.Time `json:"exited_at,omitempty"`
	Exit        string     `json:"exit,omitempty"` // "sigterm", "sigkill-after-grace", "killed", "crashed"
	ExitCode    int        `json:"exit_code"`
}

// New returns a simulator. Call Close to stop every instance.
func New(cfg Config) *Sim {
	if cfg.GracePeriod == 0 {
		cfg.GracePeriod = 10 * time.Second
	}
	if cfg.StartTimeout == 0 {
		cfg.StartTimeout = 4 * time.Minute
	}
	if cfg.Output == nil {
		cfg.Output = os.Stderr
	}
	if cfg.Logger == nil {
		cfg.Logger = slog.Default()
	}
	s := &Sim{cfg: cfg, revision: 1}
	go s.monitor()
	return s
}

func (s *Sim) ServeHTTP(w http.ResponseWriter, r *http.Request) {
	if strings.HasPrefix(r.URL.Path, "/_crsim/") {
		s.admin(w, r)
		return
	}
	inst, err := s.acquire(r.Context())
	if err != nil {
		http.Error(w, "crsim: "+err.Error(), http.StatusServiceUnavailable)
		return
	}
	defer s.release(inst)
	inst.proxy.ServeHTTP(w, r)
}

// acquire returns a ready instance with the request counted as in flight,
// starting one if the service is scaled to zero.
func (s *Sim) acquire(ctx context.Context) (*instance, error) {
	for {
		s.mu.Lock()
		if s.closed {
			s.mu.Unlock()
			return nil, errors.New("simulator closed")
		}
		inst := s.active
		if s.overlap != nil && time.Now().Before(s.overlapT) && rand.IntN(2) == 0 {
			inst = s.overlap
		}
		if inst == nil {
			if s.starting == nil {
				s.starting = make(chan struct{})
				go s.coldStart()
			}
			wait := s.starting
			s.mu.Unlock()
			select {
			case <-wait:
				continue
			case <-ctx.Done():
				return nil, ctx.Err()
			}
		}
		inst.inflight++
		inst.Stats.Requests++
		if inst.frozen {
			inst.frozen = false
			inst.signal(syscall.SIGCONT)
		}
		s.mu.Unlock()
		return inst, nil
	}
}

func (s *Sim) release(inst *instance) {
	s.mu.Lock()
	defer s.mu.Unlock()
	inst.inflight--
	inst.lastActive = time.Now()
	if inst.inflight == 0 && s.cfg.Throttle && !inst.stopping {
		inst.frozen = true
		inst.signal(syscall.SIGSTOP)
	}
}

func (s *Sim) coldStart() {
	inst, err := s.start()
	s.mu.Lock()
	defer s.mu.Unlock()
	if err == nil {
		s.active = inst
	} else {
		s.cfg.Logger.Error("cold start failed", "error", err)
	}
	close(s.starting)
	s.starting = nil
}

// start launches an instance of the current revision and waits until it
// accepts TCP connections on PORT, which is Cloud Run's default startup
// probe.
func (s *Sim) start() (*instance, error) {
	s.mu.Lock()
	s.seq++
	rev := s.revision
	id := fmt.Sprintf("rev%d-%d", rev, s.seq)
	s.mu.Unlock()

	port, err := freePort()
	if err != nil {
		return nil, err
	}
	dir, err := os.MkdirTemp("", "crsim-"+id+"-")
	if err != nil {
		return nil, err
	}
	cmd := exec.Command(s.cfg.Command[0], s.cfg.Command[1:]...)
	cmd.Env = append(os.Environ(),
		"PORT="+strconv.Itoa(port),
		"K_SERVICE=crsim",
		"K_REVISION=rev"+strconv.Itoa(rev),
		"TMPDIR="+dir,
	)
	cmd.Env = append(cmd.Env, s.cfg.Env...)
	cmd.SysProcAttr = &syscall.SysProcAttr{Setpgid: true}
	out, err := cmd.StdoutPipe()
	if err != nil {
		return nil, err
	}
	cmd.Stderr = cmd.Stdout

	target, _ := url.Parse("http://127.0.0.1:" + strconv.Itoa(port))
	inst := &instance{
		sim:      s,
		id:       id,
		revision: rev,
		cmd:      cmd,
		port:     port,
		dir:      dir,
		proxy:    httputil.NewSingleHostReverseProxy(target),
		ready:    make(chan struct{}),
		exited:   make(chan struct{}),
		Stats:    InstanceStats{ID: id, Revision: rev, StartedAt: time.Now()},
	}
	inst.proxy.ErrorHandler = func(w http.ResponseWriter, r *http.Request, err error) {
		http.Error(w, "crsim: instance "+id+": "+err.Error(), http.StatusBadGateway)
	}
	if err := cmd.Start(); err != nil {
		os.RemoveAll(dir)
		return nil, err
	}
	s.mu.Lock()
	s.all = append(s.all, inst)
	s.mu.Unlock()
	s.cfg.Logger.Info("instance starting", "id", id)

	go inst.copyOutput(out)
	go inst.wait()

	deadline := time.Now().Add(s.cfg.StartTimeout)
	for {
		if conn, err := net.DialTimeout("tcp", target.Host, 100*time.Millisecond); err == nil {
			conn.Close()
			break
		}
		select {
		case <-inst.exited:
			return nil, fmt.Errorf("instance %s exited during startup", id)
		case <-time.After(5 * time.Millisecond):
		}
		if time.Now().After(deadline) {
			inst.kill("killed")
			return nil, fmt.Errorf("instance %s did not listen within %s", id, s.cfg.StartTimeout)
		}
	}
	s.mu.Lock()
	inst.Stats.ReadyMillis = float64(time.Since(inst.Stats.StartedAt).Microseconds()) / 1000
	inst.lastActive = time.Now()
	s.mu.Unlock()
	close(inst.ready)
	s.cfg.Logger.Info("instance ready", "id", id, "ready_ms", inst.Stats.ReadyMillis)
	return inst, nil
}

func (inst *instance) copyOutput(r io.Reader) {
	sc := bufio.NewScanner(r)
	sc.Buffer(make([]byte, 64<<10), 1<<20)
	for sc.Scan() {
		fmt.Fprintf(inst.sim.cfg.Output, "[%s] %s\n", inst.id, sc.Text())
	}
}

func (inst *instance) wait() {
	err := inst.cmd.Wait()
	s := inst.sim
	s.mu.Lock()
	now := time.Now()
	inst.Stats.ExitedAt = &now
	inst.Stats.ExitCode = inst.cmd.ProcessState.ExitCode()
	if inst.Stats.Exit == "" {
		inst.Stats.Exit = "crashed"
	}
	if s.active == inst {
		s.active = nil
	}
	if s.overlap == inst {
		s.overlap = nil
	}
	s.mu.Unlock()
	s.cfg.Logger.Info("instance exited", "id", inst.id, "how", inst.Stats.Exit, "code", inst.Stats.ExitCode, "error", err)
	os.RemoveAll(inst.dir)
	close(inst.exited)
}

func (inst *instance) signal(sig syscall.Signal) {
	if inst.cmd.Process != nil {
		inst.cmd.Process.Signal(sig)
	}
}

// terminate does what Cloud Run does when it shuts an instance down: thaw
// it, send SIGTERM, and SIGKILL it if it hasn't exited after the grace
// period.
func (inst *instance) terminate() {
	s := inst.sim
	s.mu.Lock()
	if inst.stopping {
		s.mu.Unlock()
		<-inst.exited
		return
	}
	inst.stopping = true
	inst.frozen = false
	if s.active == inst {
		s.active = nil
	}
	if s.overlap == inst {
		s.overlap = nil
	}
	inst.Stats.Exit = "sigterm"
	s.mu.Unlock()

	inst.signal(syscall.SIGCONT)
	inst.signal(syscall.SIGTERM)
	select {
	case <-inst.exited:
	case <-time.After(s.cfg.GracePeriod):
		s.mu.Lock()
		inst.Stats.Exit = "sigkill-after-grace"
		s.mu.Unlock()
		inst.signal(syscall.SIGKILL)
		<-inst.exited
	}
}

// kill stops an instance without warning, like a host failure.
func (inst *instance) kill(how string) {
	s := inst.sim
	s.mu.Lock()
	inst.stopping = true
	inst.Stats.Exit = how
	if s.active == inst {
		s.active = nil
	}
	if s.overlap == inst {
		s.overlap = nil
	}
	s.mu.Unlock()
	inst.signal(syscall.SIGKILL)
	<-inst.exited
}

// monitor scales idle instances to zero and records peak memory and
// scratch-directory use. Cloud Run counts files written to the container
// filesystem against the memory limit.
func (s *Sim) monitor() {
	for range time.Tick(250 * time.Millisecond) {
		s.mu.Lock()
		if s.closed {
			s.mu.Unlock()
			return
		}
		var idle []*instance
		var live []*instance
		for _, inst := range s.all {
			if inst.Stats.ExitedAt != nil || inst.stopping {
				continue
			}
			live = append(live, inst)
			if s.cfg.IdleTimeout > 0 && inst.inflight == 0 && !inst.lastActive.IsZero() && time.Since(inst.lastActive) > s.cfg.IdleTimeout {
				idle = append(idle, inst)
			}
		}
		s.mu.Unlock()
		for _, inst := range live {
			rss := readRSS(inst.cmd.Process.Pid)
			disk := dirSize(inst.dir)
			s.mu.Lock()
			inst.Stats.PeakRSS = max(inst.Stats.PeakRSS, rss)
			inst.Stats.PeakDisk = max(inst.Stats.PeakDisk, disk)
			s.mu.Unlock()
		}
		for _, inst := range idle {
			s.cfg.Logger.Info("scaling idle instance to zero", "id", inst.id)
			go inst.terminate()
		}
	}
}

// ScaleToZero gracefully stops every running instance.
func (s *Sim) ScaleToZero() {
	for _, inst := range s.running() {
		inst.terminate()
	}
}

// Crash SIGKILLs every running instance.
func (s *Sim) Crash() {
	for _, inst := range s.running() {
		inst.kill("killed")
	}
}

// Deploy starts an instance of a new revision and moves traffic to it once
// it is ready. For the overlap duration, requests are split between the old
// and new instance, so two instances serve at once. The old instance is
// then stopped with SIGTERM.
func (s *Sim) Deploy(overlap time.Duration) error {
	s.mu.Lock()
	s.revision++
	s.mu.Unlock()
	inst, err := s.start()
	if err != nil {
		return err
	}
	s.mu.Lock()
	old := s.active
	s.active = inst
	if old != nil && overlap > 0 {
		s.overlap = old
		s.overlapT = time.Now().Add(overlap)
	}
	s.mu.Unlock()
	if old != nil {
		go func() {
			time.Sleep(overlap)
			old.terminate()
		}()
	}
	return nil
}

func (s *Sim) running() []*instance {
	s.mu.Lock()
	defer s.mu.Unlock()
	var out []*instance
	for _, inst := range s.all {
		if inst.Stats.ExitedAt == nil {
			out = append(out, inst)
		}
	}
	return out
}

// Instances returns stats for every instance started so far.
func (s *Sim) Instances() []InstanceStats {
	s.mu.Lock()
	defer s.mu.Unlock()
	out := make([]InstanceStats, len(s.all))
	for i, inst := range s.all {
		out[i] = inst.Stats
	}
	return out
}

// Close gracefully stops every instance.
func (s *Sim) Close() {
	s.ScaleToZero()
	s.mu.Lock()
	s.closed = true
	s.mu.Unlock()
}

func (s *Sim) admin(w http.ResponseWriter, r *http.Request) {
	switch r.URL.Path {
	case "/_crsim/stats":
		w.Header().Set("Content-Type", "application/json")
		json.NewEncoder(w).Encode(s.Instances())
	case "/_crsim/scale-to-zero":
		s.ScaleToZero()
	case "/_crsim/crash":
		s.Crash()
	case "/_crsim/deploy":
		overlap, _ := time.ParseDuration(r.URL.Query().Get("overlap"))
		if err := s.Deploy(overlap); err != nil {
			http.Error(w, err.Error(), http.StatusInternalServerError)
		}
	default:
		http.NotFound(w, r)
	}
}

func freePort() (int, error) {
	ln, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		return 0, err
	}
	defer ln.Close()
	return ln.Addr().(*net.TCPAddr).Port, nil
}

func readRSS(pid int) int64 {
	b, err := os.ReadFile(fmt.Sprintf("/proc/%d/status", pid))
	if err != nil {
		return 0
	}
	for _, line := range strings.Split(string(b), "\n") {
		if rest, ok := strings.CutPrefix(line, "VmRSS:"); ok {
			kb, _ := strconv.ParseInt(strings.TrimSuffix(strings.TrimSpace(rest), " kB"), 10, 64)
			return kb << 10
		}
	}
	return 0
}

func dirSize(dir string) int64 {
	var n int64
	filepath.WalkDir(dir, func(_ string, d fs.DirEntry, err error) error {
		if err == nil && !d.IsDir() {
			if fi, err := d.Info(); err == nil {
				n += fi.Size()
			}
		}
		return nil
	})
	return n
}
