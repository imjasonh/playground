package encoder

import (
	"bytes"
	"context"
	"errors"
	"fmt"
	"io"
	"log/slog"
	"os"
	"os/exec"
	"path/filepath"
	"slices"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"testing"
	"time"

	"github.com/chainguard-dev/clog"
)

// TestMain lets the test binary stand in for ffmpeg. With FAKE_FFMPEG set,
// it reads frames like ffmpeg does and behaves as the mode says.
func TestMain(m *testing.M) {
	if mode := os.Getenv("FAKE_FFMPEG"); mode != "" {
		os.Exit(fakeFFmpeg(mode, os.Args[1:], os.Stdout, os.Stderr))
	}
	os.Exit(m.Run())
}

// fakeFFmpeg reads video frames from stdin and audio from fd 3, reports
// progress, and appends one line describing the run to $FAKE_FFMPEG_OUT.
// Modes:
//
//	ok        read until stdin closes, then exit 0
//	crash:N   exit 1 after N frames
//	stall     read one frame, then stop reading and reporting
//	echo      print the output URL to stderr, then behave like ok
func fakeFFmpeg(mode string, args []string, stdout, stderr io.Writer) int {
	var w, h int
	if i := slices.Index(args, "-video_size"); i >= 0 {
		fmt.Sscanf(args[i+1], "%dx%d", &w, &h)
	}
	url := args[len(args)-1]
	record := func(s string) {
		if f, err := os.OpenFile(os.Getenv("FAKE_FFMPEG_OUT"), os.O_APPEND|os.O_CREATE|os.O_WRONLY, 0o644); err == nil {
			fmt.Fprintln(f, s)
			f.Close()
		}
	}
	if mode == "echo" {
		fmt.Fprintf(stderr, "[flv @ 0x1] Opening '%s' for writing\n", url)
		mode = "ok"
	}
	crashAt := -1
	if n, ok := strings.CutPrefix(mode, "crash:"); ok {
		crashAt, _ = strconv.Atoi(n)
	}

	var audioBytes atomic.Int64
	go func() {
		n, _ := io.Copy(io.Discard, os.NewFile(3, "audio"))
		audioBytes.Add(n)
	}()
	frame := make([]byte, w*h*3/2)
	frames := 0
	for {
		if _, err := io.ReadFull(os.Stdin, frame); err != nil {
			break
		}
		frames++
		fmt.Fprintf(stdout, "frame=%d\nspeed=1x\nprogress=continue\n", frames)
		if frames == crashAt {
			record(fmt.Sprintf("crashed frames=%d", frames))
			return 1
		}
		if mode == "stall" {
			record("stalled")
			select {}
		}
	}
	// Give the audio reader a moment to see EOF too.
	time.Sleep(50 * time.Millisecond)
	record(fmt.Sprintf("clean frames=%d audio=%d url=%s", frames, audioBytes.Load(), url))
	return 0
}

type syncBuffer struct {
	mu  sync.Mutex
	buf bytes.Buffer
}

func (b *syncBuffer) Write(p []byte) (int, error) {
	b.mu.Lock()
	defer b.mu.Unlock()
	return b.buf.Write(p)
}

func (b *syncBuffer) String() string {
	b.mu.Lock()
	defer b.mu.Unlock()
	return b.buf.String()
}

type harness struct {
	t       *testing.T
	enc     *Encoder
	out     string
	logs    *syncBuffer
	urls    atomic.Int32
	cancel  context.CancelFunc
	done    chan error
	release atomic.Int64
}

const testW, testH = 64, 32

func start(t *testing.T, mode string, tweak func(*Config)) *harness {
	t.Helper()
	h := &harness{t: t, out: filepath.Join(t.TempDir(), "runs"), logs: &syncBuffer{}, done: make(chan error, 1)}
	t.Setenv("FAKE_FFMPEG", mode)
	t.Setenv("FAKE_FFMPEG_OUT", h.out)
	cfg := Config{
		FFmpeg: os.Args[0], Width: testW, Height: testH, FPS: 30, SampleRate: 48000,
		VideoBitrate: 1000000, Preset: "veryfast",
		URL: func(context.Context) (string, error) {
			n := h.urls.Add(1)
			return fmt.Sprintf("rtmp://ingest.example/live2/secret-key-%04d", n), nil
		},
		MinBackoff: 10 * time.Millisecond, MaxBackoff: 50 * time.Millisecond,
		StopTimeout: 5 * time.Second, QueueFrames: 4,
	}
	if tweak != nil {
		tweak(&cfg)
	}
	h.enc = New(cfg)
	ctx, cancel := context.WithCancel(clog.WithLogger(t.Context(), clog.New(slog.NewTextHandler(h.logs, nil))))
	h.cancel = cancel
	go func() { h.done <- h.enc.Run(ctx) }()
	t.Cleanup(func() {
		cancel()
		<-h.done
	})
	return h
}

func (h *harness) job() Job {
	return Job{
		Video:   make([]byte, testW*testH*3/2),
		Audio:   make([]byte, 1600*4),
		Release: func() { h.release.Add(1) },
	}
}

// submit submits n jobs, waiting for room as needed, and returns how many
// were attempted including drops.
func (h *harness) submit(n int) int {
	h.t.Helper()
	attempts := 0
	deadline := time.Now().Add(10 * time.Second)
	for sent := 0; sent < n; {
		attempts++
		if h.enc.Submit(h.job()) {
			sent++
			continue
		}
		if time.Now().After(deadline) {
			h.t.Fatalf("submitted %d of %d jobs before the deadline", sent, n)
		}
		time.Sleep(time.Millisecond)
	}
	return attempts
}

func (h *harness) stop() {
	h.t.Helper()
	h.cancel()
	select {
	case err := <-h.done:
		if err != nil {
			h.t.Fatalf("Run returned %v", err)
		}
		h.done <- nil
	case <-time.After(10 * time.Second):
		h.t.Fatal("Run did not return after cancel")
	}
}

func (h *harness) runs() []string {
	b, err := os.ReadFile(h.out)
	if errors.Is(err, os.ErrNotExist) {
		return nil
	}
	if err != nil {
		h.t.Fatal(err)
	}
	return strings.Split(strings.TrimSpace(string(b)), "\n")
}

func waitFor(t *testing.T, what string, cond func() bool) {
	t.Helper()
	deadline := time.Now().Add(10 * time.Second)
	for !cond() {
		if time.Now().After(deadline) {
			t.Fatalf("timed out waiting for %s", what)
		}
		time.Sleep(5 * time.Millisecond)
	}
}

func TestStreamsAndStopsCleanly(t *testing.T) {
	h := start(t, "ok", nil)
	attempts := h.submit(100)
	h.stop()
	runs := h.runs()
	want := fmt.Sprintf("clean frames=100 audio=%d url=rtmp://ingest.example/live2/secret-key-0001", 100*1600*4)
	if len(runs) != 1 || runs[0] != want {
		t.Errorf("runs = %q, want [%q]", runs, want)
	}
	if got := h.release.Load(); got != int64(attempts) {
		t.Errorf("released %d jobs, want %d", got, attempts)
	}
	if s := h.enc.Stats(); s.Running || s.Restarts != 0 {
		t.Errorf("stats after stop = %+v", s)
	}
}

func TestRestartsAfterCrashWithFreshURL(t *testing.T) {
	h := start(t, "crash:5", nil)
	waitFor(t, "three restarts", func() bool {
		h.enc.Submit(h.job())
		return h.enc.Stats().Restarts >= 3
	})
	h.stop()
	runs := h.runs()
	if len(runs) < 3 {
		t.Fatalf("runs = %q, want at least 3", runs)
	}
	for _, r := range runs[:3] {
		if r != "crashed frames=5" {
			t.Errorf("run = %q, want a crash after 5 frames", r)
		}
	}
	if n := h.urls.Load(); n < 3 {
		t.Errorf("URL fetched %d times, want once per start", n)
	}
}

func TestKillsStalledFFmpeg(t *testing.T) {
	h := start(t, "stall", func(c *Config) { c.StallTimeout = 200 * time.Millisecond; c.StopTimeout = 200 * time.Millisecond })
	waitFor(t, "a restart after a stall", func() bool {
		h.enc.Submit(h.job())
		return h.urls.Load() >= 2
	})
	h.stop()
	if !strings.Contains(h.logs.String(), "ffmpeg stalled") {
		t.Errorf("logs don't mention the stall:\n%s", h.logs)
	}
}

func TestNeverLogsStreamKey(t *testing.T) {
	h := start(t, "echo", nil)
	h.submit(3)
	waitFor(t, "ffmpeg's message", func() bool { return strings.Contains(h.logs.String(), "Opening") })
	h.stop()
	logs := h.logs.String()
	if strings.Contains(logs, "secret-key") {
		t.Errorf("logs contain the stream key:\n%s", logs)
	}
	if !strings.Contains(logs, "[REDACTED]") {
		t.Errorf("logs don't show where the key was removed:\n%s", logs)
	}
}

func TestURLErrorRetries(t *testing.T) {
	var calls atomic.Int32
	h := start(t, "ok", func(c *Config) {
		c.URL = func(context.Context) (string, error) {
			calls.Add(1)
			return "", errors.New("secret manager unavailable")
		}
	})
	waitFor(t, "retries", func() bool { return calls.Load() >= 3 })
	if h.enc.Submit(h.job()) {
		t.Error("Submit succeeded with no ffmpeg running")
	}
	if h.release.Load() != 1 {
		t.Error("dropped job was not released")
	}
	h.stop()
}

func TestBackoffGrowsAndCaps(t *testing.T) {
	var mu sync.Mutex
	var times []time.Time
	h := start(t, "ok", func(c *Config) {
		c.MinBackoff, c.MaxBackoff = 20*time.Millisecond, 80*time.Millisecond
		c.URL = func(context.Context) (string, error) {
			mu.Lock()
			times = append(times, time.Now())
			mu.Unlock()
			return "", errors.New("down")
		}
	})
	waitFor(t, "six attempts", func() bool {
		mu.Lock()
		defer mu.Unlock()
		return len(times) >= 6
	})
	h.stop()
	mu.Lock()
	defer mu.Unlock()
	want := []time.Duration{20, 40, 80, 80, 80}
	for i, w := range want {
		gap := times[i+1].Sub(times[i])
		if gap < w*time.Millisecond || gap > w*time.Millisecond+200*time.Millisecond {
			t.Errorf("wait before attempt %d = %v, want about %v", i+2, gap, w*time.Millisecond)
		}
	}
}

func TestLineWriter(t *testing.T) {
	var got []string
	w := &lineWriter{fn: func(s string) { got = append(got, s) }}
	for _, chunk := range []string{"frame=1\nfps=", "60\r\n", "\n  speed=1x  \rpartial"} {
		w.Write([]byte(chunk))
	}
	want := []string{"frame=1", "fps=60", "speed=1x"}
	if !slices.Equal(got, want) {
		t.Errorf("lines = %q, want %q", got, want)
	}
}

func TestRedactor(t *testing.T) {
	for _, tc := range []struct{ url, in, want string }{
		{"rtmps://h/live2/abcd-efgh-ijkl", "rtmps://h/live2/abcd-efgh-ijkl: 403", "[REDACTED]: 403"},
		{"rtmps://h/live2/abcd-efgh-ijkl", "key abcd-efgh-ijkl rejected", "key [REDACTED] rejected"},
		{"file:///tmp/out.flv", "out.flv: ok", "out.flv: ok"},
	} {
		if got := redactor(tc.url)(tc.in); got != tc.want {
			t.Errorf("redactor(%q)(%q) = %q, want %q", tc.url, tc.in, got, tc.want)
		}
	}
}

func TestFFmpegArgs(t *testing.T) {
	cfg := Config{Width: 1920, Height: 1080, FPS: 60, SampleRate: 48000, VideoBitrate: 12000000, Preset: "veryfast", Format: "flv"}
	args := ffmpegArgs(cfg, "rtmps://a.rtmps.youtube.com:443/live2/key")
	joined := strings.Join(args, " ")
	for _, want := range []string{
		"-video_size 1920x1080 -framerate 60",
		"-i pipe:0",
		"-i pipe:3",
		"-preset veryfast",
		"-g 120 -keyint_min 120 -sc_threshold 0",
		"-b:v 12000000 -maxrate 12000000 -bufsize 24000000",
		"-f flv rtmps://a.rtmps.youtube.com:443/live2/key",
	} {
		if !strings.Contains(joined, want) {
			t.Errorf("args lack %q:\n%s", want, joined)
		}
	}
	if args[len(args)-1] != "rtmps://a.rtmps.youtube.com:443/live2/key" {
		t.Errorf("last arg = %q, want the URL", args[len(args)-1])
	}
}

// TestRealFFmpeg encodes a short stream with the ffmpeg on PATH, if any,
// and checks every frame made it into the file.
func TestRealFFmpeg(t *testing.T) {
	ffmpeg, err := exec.LookPath("ffmpeg")
	if err != nil {
		t.Skip("ffmpeg not on PATH")
	}
	ffprobe, err := exec.LookPath("ffprobe")
	if err != nil {
		t.Skip("ffprobe not on PATH")
	}
	out := filepath.Join(t.TempDir(), "out.flv")
	enc := New(Config{
		FFmpeg: ffmpeg, Width: 320, Height: 180, FPS: 30, SampleRate: 48000,
		VideoBitrate: 500000, Preset: "ultrafast", Format: "flv",
		URL:         func(context.Context) (string, error) { return out, nil },
		QueueFrames: 4, StopTimeout: 20 * time.Second,
	})
	ctx, cancel := context.WithCancel(t.Context())
	done := make(chan error, 1)
	go func() { done <- enc.Run(ctx) }()
	video := make([]byte, 320*180*3/2)
	audio := make([]byte, 1600*4)
	deadline := time.Now().Add(30 * time.Second)
	for sent := 0; sent < 60; {
		for i := range video[:320*180] {
			video[i] = byte(16 + (i+sent)%200)
		}
		if enc.Submit(Job{Video: slices.Clone(video), Audio: audio}) {
			sent++
		} else {
			if time.Now().After(deadline) {
				t.Fatalf("sent %d frames before the deadline", sent)
			}
			time.Sleep(2 * time.Millisecond)
		}
	}
	cancel()
	if err := <-done; err != nil {
		t.Fatal(err)
	}
	b, err := exec.Command(ffprobe, "-v", "error", "-count_frames", "-select_streams", "v:0",
		"-show_entries", "stream=nb_read_frames", "-of", "csv=p=0", out).CombinedOutput()
	if err != nil {
		t.Fatalf("ffprobe: %v\n%s", err, b)
	}
	if got := strings.TrimSpace(string(b)); got != "60" {
		t.Errorf("file has %s video frames, want 60", got)
	}
}
