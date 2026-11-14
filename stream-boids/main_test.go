package main

import (
	"context"
	"net/http/httptest"
	"os"
	"os/exec"
	"path/filepath"
	"strconv"
	"strings"
	"testing"
	"time"

	"github.com/sethvargo/go-envconfig"

	"github.com/imjasonh/playground/stream-boids/internal/fakeyt"
)

func load(t *testing.T, vars map[string]string) config {
	t.Helper()
	var cfg config
	if err := envconfig.ProcessWith(t.Context(), &envconfig.Config{
		Target:   &cfg,
		Lookuper: envconfig.MapLookuper(vars),
	}); err != nil {
		t.Fatal(err)
	}
	return cfg
}

func TestValidate(t *testing.T) {
	for _, tc := range []struct {
		name string
		vars map[string]string
		want string
	}{
		{"defaults with output", map[string]string{"OUTPUT_URL": "out.flv"}, ""},
		{"stream key file", map[string]string{"STREAM_KEY_FILE": "/run/key"}, ""},
		{"no output", map[string]string{}, "OUTPUT_URL"},
		{"odd size", map[string]string{"OUTPUT_URL": "x", "WIDTH": "641"}, "even"},
		{"fps", map[string]string{"OUTPUT_URL": "x", "FPS": "7"}, "FPS"},
		{"min over cap", map[string]string{"OUTPUT_URL": "x", "MIN_BOIDS": "5", "BOID_CAP": "2"}, "MIN_BOIDS"},
		{"two stream keys", map[string]string{"STREAM_KEY_FILE": "a", "STREAM_KEY_SECRET": "b"}, "not both"},
		{"real API without key", map[string]string{"OUTPUT_URL": "x", "VIDEO_ID": "v"}, "YOUTUBE_API_KEY"},
		{"fake API without key", map[string]string{"OUTPUT_URL": "x", "VIDEO_ID": "v", "YOUTUBE_API_BASE": "http://127.0.0.1:8090/youtube/v3"}, ""},
	} {
		t.Run(tc.name, func(t *testing.T) {
			err := load(t, tc.vars).validate()
			switch {
			case tc.want == "" && err != nil:
				t.Fatalf("validate() = %v, want nil", err)
			case tc.want != "" && (err == nil || !strings.Contains(err.Error(), tc.want)):
				t.Fatalf("validate() = %v, want an error mentioning %q", err, tc.want)
			}
		})
	}
}

func TestStreamsToFile(t *testing.T) {
	if _, err := exec.LookPath("ffmpeg"); err != nil {
		t.Skip("ffmpeg not installed")
	}
	if _, err := exec.LookPath("ffprobe"); err != nil {
		t.Skip("ffprobe not installed")
	}

	yt := fakeyt.New()
	yt.PollInterval = 50 * time.Millisecond
	yt.SetViewers(40)
	srv := httptest.NewServer(yt)
	defer srv.Close()

	out := filepath.Join(t.TempDir(), "out.flv")
	cfg := load(t, map[string]string{
		"WIDTH":            "320",
		"HEIGHT":           "180",
		"FPS":              "30",
		"BOID_CAP":         "100",
		"OUTPUT_URL":       out,
		"X264_PRESET":      "ultrafast",
		"VIDEO_BITRATE":    "500000",
		"YOUTUBE_API_BASE": srv.URL + "/youtube/v3",
		"VIDEO_ID":         fakeyt.VideoID,
		"VIEWER_POLL":      "50ms",
		"CHAT_POLL":        "50ms",
		"METRICS_INTERVAL": "500ms",
	})

	ctx, cancel := context.WithCancel(t.Context())
	done := make(chan error, 1)
	go func() { done <- run(ctx, cfg) }()

	time.Sleep(time.Second)
	yt.NewMember("Ada")
	yt.SuperChat("Grace", true, 20, "hello")
	time.Sleep(2 * time.Second)
	cancel()
	select {
	case err := <-done:
		if err != nil {
			t.Fatalf("run() = %v", err)
		}
	case <-time.After(30 * time.Second):
		t.Fatal("run() did not return after cancel")
	}

	if yt.Calls("videos") == 0 || yt.Calls("liveChatMessages") == 0 {
		t.Errorf("calls: videos=%d chat=%d, want both > 0", yt.Calls("videos"), yt.Calls("liveChatMessages"))
	}
	if fi, err := os.Stat(out); err != nil || fi.Size() == 0 {
		t.Fatalf("output: %v, %v", fi, err)
	}
	probe, err := exec.Command("ffprobe", "-v", "error", "-count_frames", "-select_streams", "v:0",
		"-show_entries", "stream=nb_read_frames,width,height", "-of", "csv=p=0", out).Output()
	if err != nil {
		t.Fatalf("ffprobe: %v", err)
	}
	fields := strings.Split(strings.TrimSpace(string(probe)), ",")
	if len(fields) != 3 || fields[0] != "320" || fields[1] != "180" {
		t.Fatalf("ffprobe = %q, want 320,180,<frames>", probe)
	}
	// Three seconds at 30 fps, less ffmpeg's startup.
	if n, _ := strconv.Atoi(fields[2]); n < 50 {
		t.Errorf("encoded %d frames, want at least 50", n)
	}
}
