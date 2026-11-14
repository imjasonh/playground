// Command stream-boids renders a flock of boids, one per viewer, and
// streams it with a soundtrack to YouTube Live through ffmpeg.
package main

import (
	"context"
	"errors"
	"fmt"
	"os"
	"os/signal"
	"runtime"
	"strings"
	"sync"
	"syscall"
	"time"

	"github.com/chainguard-dev/clog"
	_ "github.com/chainguard-dev/clog/gcp/init"
	"github.com/sethvargo/go-envconfig"

	"github.com/imjasonh/playground/stream-boids/internal/audio"
	"github.com/imjasonh/playground/stream-boids/internal/encoder"
	"github.com/imjasonh/playground/stream-boids/internal/flock"
	"github.com/imjasonh/playground/stream-boids/internal/frame"
	"github.com/imjasonh/playground/stream-boids/internal/secret"
	"github.com/imjasonh/playground/stream-boids/internal/show"
	"github.com/imjasonh/playground/stream-boids/internal/youtube"
)

const sampleRate = 48000

type config struct {
	Width    int `env:"WIDTH, default=1920"`
	Height   int `env:"HEIGHT, default=1080"`
	FPS      int `env:"FPS, default=60"`
	BoidCap  int `env:"BOID_CAP, default=10000"`
	MinBoids int `env:"MIN_BOIDS, default=1"`
	// Workers is how many goroutines simulate and render. Zero means
	// GOMAXPROCS.
	Workers int `env:"WORKERS"`
	// StaticViewers is the viewer count when no YouTube video or channel
	// is set.
	StaticViewers int `env:"STATIC_VIEWERS"`

	// OutputURL replaces YouTube ingest, for a file or a local RTMP server.
	OutputURL    string `env:"OUTPUT_URL"`
	OutputFormat string `env:"OUTPUT_FORMAT, default=flv"`
	IngestURL    string `env:"INGEST_URL, default=rtmps://a.rtmps.youtube.com:443/live2"`
	FFmpeg       string `env:"FFMPEG, default=ffmpeg"`
	VideoBitrate int    `env:"VIDEO_BITRATE, default=12000000"`
	X264Preset   string `env:"X264_PRESET, default=veryfast"`

	// Secrets come from Secret Manager or a file, never from the
	// environment itself.
	StreamKeySecret     string `env:"STREAM_KEY_SECRET"`
	StreamKeyFile       string `env:"STREAM_KEY_FILE"`
	YouTubeAPIKeySecret string `env:"YOUTUBE_API_KEY_SECRET"`
	YouTubeAPIKeyFile   string `env:"YOUTUBE_API_KEY_FILE"`

	YouTubeAPIBase string        `env:"YOUTUBE_API_BASE, default=https://www.googleapis.com/youtube/v3"`
	VideoID        string        `env:"VIDEO_ID"`
	ChannelID      string        `env:"CHANNEL_ID"`
	ViewerPoll     time.Duration `env:"VIEWER_POLL, default=60s"`
	ChatPoll       time.Duration `env:"CHAT_POLL, default=75s"`
	SearchInterval time.Duration `env:"SEARCH_INTERVAL, default=30m"`
	MemberWindow   time.Duration `env:"MEMBER_WINDOW, default=30m"`
	QuotaPause     time.Duration `env:"QUOTA_PAUSE, default=1h"`

	MetricsInterval time.Duration `env:"METRICS_INTERVAL, default=60s"`
}

var env = envconfig.MustProcess(context.Background(), &config{})

func main() {
	ctx, stop := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
	defer stop()
	if err := run(ctx, *env); err != nil {
		clog.Fatal("stream-boids failed", "error", err)
	}
}

func (c config) validate() error {
	var errs []error
	if c.Width <= 0 || c.Height <= 0 || c.Width%2 != 0 || c.Height%2 != 0 {
		errs = append(errs, fmt.Errorf("WIDTH and HEIGHT must be positive and even, got %dx%d", c.Width, c.Height))
	}
	if c.FPS <= 0 || sampleRate%c.FPS != 0 {
		errs = append(errs, fmt.Errorf("FPS must divide %d, got %d", sampleRate, c.FPS))
	}
	if c.BoidCap < 0 || c.MinBoids < 0 || c.MinBoids > c.BoidCap {
		errs = append(errs, fmt.Errorf("want 0 <= MIN_BOIDS <= BOID_CAP, got %d and %d", c.MinBoids, c.BoidCap))
	}
	if c.StreamKeySecret != "" && c.StreamKeyFile != "" {
		errs = append(errs, errors.New("set STREAM_KEY_SECRET or STREAM_KEY_FILE, not both"))
	}
	if c.OutputURL == "" && c.StreamKeySecret == "" && c.StreamKeyFile == "" {
		errs = append(errs, errors.New("set STREAM_KEY_SECRET or STREAM_KEY_FILE to stream to YouTube, or OUTPUT_URL to stream elsewhere"))
	}
	if c.YouTubeAPIKeySecret != "" && c.YouTubeAPIKeyFile != "" {
		errs = append(errs, errors.New("set YOUTUBE_API_KEY_SECRET or YOUTUBE_API_KEY_FILE, not both"))
	}
	if (c.VideoID != "" || c.ChannelID != "") && c.YouTubeAPIKeySecret == "" && c.YouTubeAPIKeyFile == "" &&
		c.YouTubeAPIBase == youtube.DefaultBase {
		errs = append(errs, errors.New("the YouTube API needs YOUTUBE_API_KEY_SECRET or YOUTUBE_API_KEY_FILE"))
	}
	return errors.Join(errs...)
}

// secrets returns the secret Funcs that cfg names, sharing one Secret
// Manager client.
func (c config) secrets() (streamKey, apiKey secret.Func) {
	sm := &secret.Manager{}
	pick := func(name, file string) secret.Func {
		switch {
		case name != "":
			return sm.Secret(name)
		case file != "":
			return secret.File(file)
		}
		return nil
	}
	streamKey = pick(c.StreamKeySecret, c.StreamKeyFile)
	if k := pick(c.YouTubeAPIKeySecret, c.YouTubeAPIKeyFile); k != nil {
		apiKey = secret.Cached(k, 10*time.Minute)
	}
	return streamKey, apiKey
}

// buffer is one frame's video and audio, recycled through a pool.
type buffer struct {
	video *frame.Frame
	audio []byte
}

func run(ctx context.Context, cfg config) error {
	if err := cfg.validate(); err != nil {
		return err
	}
	ctx = clog.WithLogger(ctx, clog.FromContext(ctx).With("video", cfg.VideoID))
	log := clog.FromContext(ctx)
	workers := cfg.Workers
	if workers <= 0 {
		workers = runtime.GOMAXPROCS(0)
	}

	fl := flock.New(float32(cfg.Width), float32(cfg.Height), flock.DefaultParams(), workers, uint32(time.Now().UnixNano()))
	synth := audio.New(sampleRate)
	sh := show.New(show.Config{Cap: cfg.BoidCap, Min: cfg.MinBoids}, fl, synth)
	rend, err := frame.NewRenderer(cfg.Width, cfg.Height, workers)
	if err != nil {
		return err
	}

	streamKey, apiKey := cfg.secrets()
	url := func(ctx context.Context) (string, error) {
		if cfg.OutputURL != "" {
			return cfg.OutputURL, nil
		}
		key, err := streamKey(ctx)
		if err != nil {
			return "", fmt.Errorf("reading stream key: %w", err)
		}
		return strings.TrimSuffix(cfg.IngestURL, "/") + "/" + key, nil
	}
	const queue = 2
	enc := encoder.New(encoder.Config{
		FFmpeg: cfg.FFmpeg, Width: cfg.Width, Height: cfg.Height, FPS: cfg.FPS, SampleRate: sampleRate,
		VideoBitrate: cfg.VideoBitrate, Preset: cfg.X264Preset, Format: cfg.OutputFormat, URL: url,
		QueueFrames: queue,
	})

	var wg sync.WaitGroup
	defer wg.Wait()
	ctx, cancel := context.WithCancel(ctx)
	defer cancel()
	wg.Go(func() {
		if err := enc.Run(ctx); err != nil {
			log.Error("encoder stopped", "error", err)
		}
	})

	var watcher *youtube.Watcher
	var events <-chan youtube.Message
	if cfg.VideoID != "" || cfg.ChannelID != "" {
		watcher = youtube.NewWatcher(&youtube.Client{Base: cfg.YouTubeAPIBase, Key: apiKey}, youtube.WatcherConfig{
			VideoID: cfg.VideoID, ChannelID: cfg.ChannelID,
			ViewerPoll: cfg.ViewerPoll, ChatPoll: cfg.ChatPoll, SearchInterval: cfg.SearchInterval,
			MemberWindow: cfg.MemberWindow, QuotaPause: cfg.QuotaPause,
		})
		events = watcher.Events()
		wg.Go(func() {
			if err := watcher.Run(ctx); err != nil {
				log.Error("YouTube watcher stopped", "error", err)
			}
		})
	} else {
		log.Info("no YouTube video or channel set; showing a fixed viewer count", "viewers", cfg.StaticViewers)
		sh.Update(youtube.State{Viewers: cfg.StaticViewers, ViewersKnown: true})
	}

	// The encoder holds up to queue frames plus one per pipe it is
	// writing, and the loop renders one more.
	pool := make(chan *buffer, queue+3)
	for range cap(pool) {
		f, err := frame.New(cfg.Width, cfg.Height)
		if err != nil {
			return err
		}
		pool <- &buffer{video: f, audio: make([]byte, sampleRate/cfg.FPS*audio.BytesPerFrame)}
	}

	log.Info("streaming", "size", fmt.Sprintf("%dx%d", cfg.Width, cfg.Height), "fps", cfg.FPS,
		"boidCap", cfg.BoidCap, "workers", workers, "preset", cfg.X264Preset, "bitrate", cfg.VideoBitrate)

	period := time.Second / time.Duration(cfg.FPS)
	dt := 1 / float64(cfg.FPS)
	start := time.Now()
	var m metrics
	nextMetrics := start.Add(cfg.MetricsInterval)
	for n := int64(0); ; n++ {
		deadline := start.Add(time.Duration(n) * period)
		if wait := time.Until(deadline); wait > 0 {
			select {
			case <-ctx.Done():
				return nil
			case <-time.After(wait):
			}
		} else if ctx.Err() != nil {
			return nil
		} else if -wait > 5*period {
			// Far behind: skip ahead rather than stream slower than real
			// time.
			behind := int64(-wait / period)
			m.skipped += behind
			n += behind
		}

		if watcher != nil {
			if n%int64(cfg.FPS) == 0 {
				sh.Update(watcher.State())
			}
		drain:
			for {
				select {
				case ev := <-events:
					log.Info("chat event", "type", ev.Type, "tier", ev.Tier)
					sh.Event(ev)
				default:
					break drain
				}
			}
		}

		t0 := time.Now()
		sc := sh.Step(dt)
		if !enc.Stats().Running {
			m.idle++
			continue
		}
		var b *buffer
		select {
		case b = <-pool:
		default:
			m.skipped++
			continue
		}
		if err := rend.Render(sc, b.video); err != nil {
			return err
		}
		synth.Fill(b.audio)
		m.observe(time.Since(t0))
		enc.Submit(encoder.Job{Video: b.video.Bytes(), Audio: b.audio, Release: func() { pool <- b }})

		if now := time.Now(); now.After(nextMetrics) {
			nextMetrics = now.Add(cfg.MetricsInterval)
			s := enc.Stats()
			log.Info("metrics",
				"boids", fl.Len(), "target", sh.Target(), "viewers", sc.HUD.Viewers, "members", sc.HUD.Members,
				"frameAvg", m.avg().String(), "frameMax", m.max.String(), "skipped", m.skipped, "idle", m.idle,
				"ffmpegRunning", s.Running, "uptime", s.Uptime.Round(time.Second).String(), "restarts", s.Restarts,
				"dropped", s.Dropped, "encoded", s.Encoded, "speed", s.Speed)
			m = metrics{}
		}
	}
}

// metrics summarizes the frames since the last metrics log.
type metrics struct {
	frames  int64
	total   time.Duration
	max     time.Duration
	skipped int64
	idle    int64
}

func (m *metrics) observe(d time.Duration) {
	m.frames++
	m.total += d
	m.max = max(m.max, d)
}

func (m *metrics) avg() time.Duration {
	if m.frames == 0 {
		return 0
	}
	return m.total / time.Duration(m.frames)
}
