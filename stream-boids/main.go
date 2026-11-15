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

// secrets returns the encoder's output URL and the YouTube API key, read
// through one Secret Manager client. apiKey is nil when no key is set.
func (c config) secrets() (outputURL func(context.Context) (string, error), apiKey secret.Func) {
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
	streamKey := pick(c.StreamKeySecret, c.StreamKeyFile)
	outputURL = func(ctx context.Context) (string, error) {
		if c.OutputURL != "" {
			return c.OutputURL, nil
		}
		key, err := streamKey(ctx)
		if err != nil {
			return "", fmt.Errorf("reading stream key: %w", err)
		}
		return strings.TrimSuffix(c.IngestURL, "/") + "/" + key, nil
	}
	if k := pick(c.YouTubeAPIKeySecret, c.YouTubeAPIKeyFile); k != nil {
		apiKey = secret.Cached(k, 10*time.Minute)
	}
	return outputURL, apiKey
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
	rend, err := frame.NewRenderer(cfg.Width, cfg.Height, workers)
	if err != nil {
		return err
	}
	outputURL, apiKey := cfg.secrets()
	enc := encoder.New(encoder.Config{
		FFmpeg: cfg.FFmpeg, Width: cfg.Width, Height: cfg.Height, FPS: cfg.FPS, SampleRate: sampleRate,
		VideoBitrate: cfg.VideoBitrate, Preset: cfg.X264Preset, Format: cfg.OutputFormat, URL: outputURL,
	})
	// The loop renders one frame while the encoder holds the rest.
	pool := make(chan *buffer, enc.Capacity()+1)
	for range cap(pool) {
		f, err := frame.New(cfg.Width, cfg.Height)
		if err != nil {
			return err
		}
		pool <- &buffer{video: f, audio: make([]byte, sampleRate/cfg.FPS*audio.BytesPerFrame)}
	}

	s := &streamer{
		cfg:      cfg,
		flock:    fl,
		synth:    synth,
		show:     show.New(show.Config{Cap: cfg.BoidCap, Min: cfg.MinBoids}, fl, synth),
		rend:     rend,
		pool:     pool,
		enc:      enc,
		audience: func() youtube.State { return youtube.State{Viewers: cfg.StaticViewers, ViewersKnown: true} },
	}

	var wg sync.WaitGroup
	defer wg.Wait()
	ctx, cancel := context.WithCancel(ctx)
	defer cancel()
	wg.Go(func() {
		if err := s.enc.Run(ctx); err != nil {
			log.Error("encoder stopped", "error", err)
		}
	})
	if cfg.VideoID != "" || cfg.ChannelID != "" {
		w := youtube.NewWatcher(&youtube.Client{Base: cfg.YouTubeAPIBase, Key: apiKey}, youtube.WatcherConfig{
			VideoID: cfg.VideoID, ChannelID: cfg.ChannelID,
			ViewerPoll: cfg.ViewerPoll, ChatPoll: cfg.ChatPoll, SearchInterval: cfg.SearchInterval,
			MemberWindow: cfg.MemberWindow, QuotaPause: cfg.QuotaPause,
		})
		s.audience, s.events = w.State, w.Events()
		wg.Go(func() {
			if err := w.Run(ctx); err != nil {
				log.Error("YouTube watcher stopped", "error", err)
			}
		})
	} else {
		log.Info("no YouTube video or channel set; showing a fixed viewer count", "viewers", cfg.StaticViewers)
	}

	log.Info("streaming", "size", fmt.Sprintf("%dx%d", cfg.Width, cfg.Height), "fps", cfg.FPS,
		"boidCap", cfg.BoidCap, "workers", workers, "preset", cfg.X264Preset, "bitrate", cfg.VideoBitrate)
	return s.run(ctx)
}

// buffer is one frame's video and audio, recycled through a pool.
type buffer struct {
	video *frame.Frame
	audio []byte
}

// streamer renders the show one frame at a time, in real time, and hands
// each frame to the encoder.
type streamer struct {
	cfg   config
	flock *flock.Flock
	synth *audio.Synth
	show  *show.Show
	rend  *frame.Renderer
	enc   *encoder.Encoder
	pool  chan *buffer

	// audience is read once a second. events delivers chat events, and is
	// nil when nothing sends them.
	audience func() youtube.State
	events   <-chan youtube.Message
}

func (s *streamer) run(ctx context.Context) error {
	log := clog.FromContext(ctx)
	clk := clock{start: time.Now(), period: time.Second / time.Duration(s.cfg.FPS)}
	dt := 1 / float64(s.cfg.FPS)
	var m metrics
	nextMetrics := clk.start.Add(s.cfg.MetricsInterval)
	for n := int64(0); ; n++ {
		due, ok := clk.wait(ctx, n)
		if !ok {
			return nil
		}
		m.skipped += due - n
		n = due

		if n%int64(s.cfg.FPS) == 0 {
			s.show.Update(s.audience())
		}
	drain:
		for {
			select {
			case ev := <-s.events:
				log.Info("chat event", "type", ev.Type, "tier", ev.Tier)
				s.show.Event(ev)
			default:
				break drain
			}
		}

		t0 := time.Now()
		sc := s.show.Step(dt)
		if !s.enc.Stats().Running {
			m.idle++
			continue
		}
		var b *buffer
		select {
		case b = <-s.pool:
		default:
			m.skipped++
			continue
		}
		if err := s.rend.Render(sc, b.video); err != nil {
			return err
		}
		s.synth.Fill(b.audio)
		m.observe(time.Since(t0))
		s.enc.Submit(encoder.Job{Video: b.video.Bytes(), Audio: b.audio, Release: func() { s.pool <- b }})

		if now := time.Now(); now.After(nextMetrics) {
			nextMetrics = now.Add(s.cfg.MetricsInterval)
			st := s.enc.Stats()
			log.Info("metrics",
				"boids", s.flock.Len(), "target", s.show.Target(), "viewers", sc.HUD.Viewers, "members", sc.HUD.Members,
				"frameAvg", m.avg().String(), "frameMax", m.max.String(), "skipped", m.skipped, "idle", m.idle,
				"ffmpegRunning", st.Running, "uptime", st.Uptime.Round(time.Second).String(), "restarts", st.Restarts,
				"dropped", st.Dropped, "encoded", st.Encoded, "speed", st.Speed)
			m = metrics{}
		}
	}
}

// clock schedules frame n at start + n*period.
type clock struct {
	start  time.Time
	period time.Duration
}

// wait sleeps until frame n is due and returns the frame to render: n, or
// a later frame when more than five frames behind, so the stream skips
// ahead rather than run slower than real time. It returns false once ctx
// is done.
func (c clock) wait(ctx context.Context, n int64) (int64, bool) {
	wait := time.Until(c.start.Add(time.Duration(n) * c.period))
	if wait <= 0 {
		if -wait > 5*c.period {
			n += int64(-wait / c.period)
		}
		return n, ctx.Err() == nil
	}
	t := time.NewTimer(wait)
	defer t.Stop()
	select {
	case <-ctx.Done():
		return n, false
	case <-t.C:
		return n, true
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
