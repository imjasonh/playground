// Package encoder supervises the ffmpeg process that encodes frames and
// streams them to an ingest URL.
//
// ffmpeg reads raw yuv420p video on stdin and s16le audio on file
// descriptor 3. When it exits, stalls, or loses the connection, the
// encoder starts a new one after a backoff, asking for the URL again so a
// rotated stream key takes effect. Frames submitted while no ffmpeg is
// running, or while its queue is full, are dropped so the render loop never
// waits on the network.
package encoder

import (
	"bytes"
	"context"
	"errors"
	"fmt"
	"os"
	"os/exec"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"time"

	"github.com/chainguard-dev/clog"
)

// Config configures an Encoder.
type Config struct {
	// FFmpeg is the path to the ffmpeg binary.
	FFmpeg string

	Width, Height, FPS int
	// SampleRate is the audio sample rate. Audio is stereo s16le.
	SampleRate int

	// VideoBitrate is the target video bitrate in bits per second.
	VideoBitrate int
	// Preset is the x264 preset, such as "veryfast".
	Preset string
	// Format is the output container, such as "flv" for RTMP.
	Format string

	// URL returns the output URL. It is called before each ffmpeg start.
	// The URL is a secret: the encoder never logs it, and removes it and
	// its last path segment (the stream key) from ffmpeg's messages.
	URL func(ctx context.Context) (string, error)

	// StallTimeout is how long ffmpeg may go without encoding a frame
	// before the encoder kills it.
	StallTimeout time.Duration
	// MinBackoff and MaxBackoff bound the wait between restarts. The wait
	// doubles after each failure and starts over once ffmpeg has run for
	// a minute.
	MinBackoff, MaxBackoff time.Duration
	// StopTimeout is how long ffmpeg has to flush and exit after its input
	// closes before the encoder kills it.
	StopTimeout time.Duration
}

// Job is one video frame and the audio that plays during it.
type Job struct {
	Video, Audio []byte
	// Release is called once ffmpeg has read both buffers or the job was
	// dropped, after which the caller may reuse them.
	Release func()
}

// Stats describes the encoder's state.
type Stats struct {
	Running  bool
	Uptime   time.Duration
	Restarts int64
	Dropped  int64
	// Encoded is the number of frames the current ffmpeg reported encoding.
	Encoded int64
	// Speed is ffmpeg's encoding speed relative to real time, such as
	// "1x".
	Speed string
}

// Encoder runs ffmpeg and feeds it frames.
type Encoder struct {
	cfg   Config
	queue int

	mu  sync.Mutex
	cur *proc

	restarts atomic.Int64
	dropped  atomic.Int64
}

// New returns an encoder. Call Run to start it.
func New(cfg Config) *Encoder {
	if cfg.StallTimeout <= 0 {
		cfg.StallTimeout = 20 * time.Second
	}
	if cfg.MinBackoff <= 0 {
		cfg.MinBackoff = time.Second
	}
	if cfg.MaxBackoff < cfg.MinBackoff {
		cfg.MaxBackoff = max(30*time.Second, cfg.MinBackoff)
	}
	if cfg.StopTimeout <= 0 {
		cfg.StopTimeout = 10 * time.Second
	}
	if cfg.Format == "" {
		cfg.Format = "flv"
	}
	// ffmpeg's raw PCM demuxer passes audio on about a tenth of a second
	// at a time, and stops reading video until it has that much. A frame
	// is dropped whole when either queue is full, so the queue must hold
	// more than a tenth of a second of frames or the pipes deadlock.
	return &Encoder{cfg: cfg, queue: (cfg.FPS+9)/10 + 2}
}

// Capacity is the most jobs the encoder holds at once: its queue, plus
// one being written to each pipe.
func (e *Encoder) Capacity() int { return e.queue + 2 }

type job struct {
	Job
	refs atomic.Int32
}

func (j *job) done() {
	if j.refs.Add(-1) == 0 && j.Release != nil {
		j.Release()
	}
}

// Submit queues a job for the running ffmpeg. It never blocks. It returns
// false, after releasing the job, when no ffmpeg is running or its queue is
// full. Submit must not be called concurrently with itself.
func (e *Encoder) Submit(j Job) bool {
	jb := &job{Job: j}
	jb.refs.Store(2)
	e.mu.Lock()
	defer e.mu.Unlock()
	p := e.cur
	if p == nil || len(p.video) == cap(p.video) || len(p.audio) == cap(p.audio) {
		e.dropped.Add(1)
		if j.Release != nil {
			j.Release()
		}
		return false
	}
	p.video <- jb
	p.audio <- jb
	return true
}

// Stats returns the encoder's current state.
func (e *Encoder) Stats() Stats {
	s := Stats{Restarts: e.restarts.Load(), Dropped: e.dropped.Load()}
	e.mu.Lock()
	p := e.cur
	e.mu.Unlock()
	if p != nil {
		s.Running = true
		s.Uptime = time.Since(p.started)
		s.Encoded = p.frames.Load()
		if sp, ok := p.speed.Load().(string); ok {
			s.Speed = sp
		}
	}
	return s
}

// Run starts ffmpeg and restarts it whenever it exits, until ctx is done.
// Then it closes ffmpeg's input, waits for it to finish the stream, and
// returns.
func (e *Encoder) Run(ctx context.Context) error {
	log := clog.FromContext(ctx)
	backoff := e.cfg.MinBackoff
	for {
		started := time.Now()
		err := e.runOnce(ctx)
		if ctx.Err() != nil {
			return nil
		}
		e.restarts.Add(1)
		if time.Since(started) > time.Minute {
			backoff = e.cfg.MinBackoff
		}
		log.Warn("ffmpeg stopped; restarting", "error", err, "uptime", time.Since(started).Round(time.Millisecond), "backoff", backoff)
		select {
		case <-ctx.Done():
			return nil
		case <-time.After(backoff):
		}
		backoff = min(backoff*2, e.cfg.MaxBackoff)
	}
}

// proc is one running ffmpeg.
type proc struct {
	started      time.Time
	video        chan *job
	audio        chan *job
	frames       atomic.Int64
	speed        atomic.Value
	lastProgress atomic.Int64
}

// progress records a line of ffmpeg's -progress output.
func (p *proc) progress(line string) {
	k, v, ok := strings.Cut(line, "=")
	if !ok {
		return
	}
	switch k {
	case "frame":
		n, err := strconv.ParseInt(strings.TrimSpace(v), 10, 64)
		if err == nil && n > p.frames.Load() {
			p.frames.Store(n)
			p.lastProgress.Store(time.Now().UnixNano())
		}
	case "speed":
		p.speed.Store(strings.TrimSpace(v))
	}
}

// redactor returns a func that removes url, and its last path segment when
// that looks like a stream key, from a string.
func redactor(url string) func(string) string {
	secrets := []string{url}
	if i := strings.LastIndexByte(url, '/'); i >= 0 && len(url)-i > 8 {
		secrets = append(secrets, url[i+1:])
	}
	return func(s string) string {
		for _, sec := range secrets {
			s = strings.ReplaceAll(s, sec, "[REDACTED]")
		}
		return s
	}
}

func (e *Encoder) runOnce(ctx context.Context) error {
	log := clog.FromContext(ctx)
	url, err := e.cfg.URL(ctx)
	if err != nil {
		return fmt.Errorf("getting output URL: %w", err)
	}
	redact := redactor(url)

	videoR, videoW, err := os.Pipe()
	if err != nil {
		return err
	}
	audioR, audioW, err := os.Pipe()
	if err != nil {
		videoR.Close()
		videoW.Close()
		return err
	}

	p := &proc{
		started: time.Now(),
		video:   make(chan *job, e.queue),
		audio:   make(chan *job, e.queue),
	}
	p.lastProgress.Store(p.started.UnixNano())

	var msgs messages
	// exec.Command, not CommandContext: cancellation must close ffmpeg's
	// input so it finishes the stream, not kill it.
	cmd := exec.Command(e.cfg.FFmpeg, ffmpegArgs(e.cfg, url)...)
	cmd.Stdin = videoR
	cmd.ExtraFiles = []*os.File{audioR}
	cmd.Stdout = &lineWriter{fn: p.progress}
	cmd.Stderr = &lineWriter{fn: func(line string) {
		line = redact(line)
		if msgs.add(line) {
			log.Warn("ffmpeg", "message", line)
		}
	}}
	err = cmd.Start()
	videoR.Close()
	audioR.Close()
	if err != nil {
		videoW.Close()
		audioW.Close()
		return fmt.Errorf("starting ffmpeg: %s", redact(err.Error()))
	}
	log.Info("ffmpeg started", "pid", cmd.Process.Pid, "args", redact(strings.Join(cmd.Args, " ")))

	exited := make(chan error, 1)
	go func() { exited <- cmd.Wait() }()

	// Each writer runs until its channel closes, so queued frames reach a
	// stopping ffmpeg before EOF. After a write fails it only releases jobs.
	var writers sync.WaitGroup
	write := func(f *os.File, ch chan *job, buf func(*job) []byte) {
		defer f.Close()
		ok := true
		for j := range ch {
			if ok {
				_, err := f.Write(buf(j))
				ok = err == nil
			}
			j.done()
		}
	}
	writers.Go(func() { write(videoW, p.video, func(j *job) []byte { return j.Video }) })
	writers.Go(func() { write(audioW, p.audio, func(j *job) []byte { return j.Audio }) })

	e.mu.Lock()
	e.cur = p
	e.mu.Unlock()

	tick := time.NewTicker(time.Second)
	defer tick.Stop()
	var exitErr error
	stopping := false
wait:
	for {
		select {
		case exitErr = <-exited:
			break wait
		case <-ctx.Done():
			stopping = true
			break wait
		case <-tick.C:
			idle := time.Since(time.Unix(0, p.lastProgress.Load()))
			if idle > e.cfg.StallTimeout {
				log.Warn("ffmpeg stalled; killing it", "idle", idle.Round(time.Second))
				cmd.Process.Kill()
			}
		}
	}

	// Submit sends while holding mu, so once cur is nil nothing else sends.
	e.mu.Lock()
	e.cur = nil
	e.mu.Unlock()
	close(p.video)
	close(p.audio)

	if stopping {
		select {
		case exitErr = <-exited:
		case <-time.After(e.cfg.StopTimeout):
			log.Warn("ffmpeg did not exit in time; killing it", "timeout", e.cfg.StopTimeout)
			cmd.Process.Kill()
			exitErr = <-exited
		}
		// A killed ffmpeg breaks the pipes, which unblocks the writers.
		writers.Wait()
		log.Info("ffmpeg stopped", "error", exitErr, "frames", p.frames.Load())
		return exitErr
	}
	writers.Wait()
	if exitErr == nil {
		exitErr = errors.New("ffmpeg exited")
	}
	return fmt.Errorf("%w; last messages:\n%s", exitErr, msgs.last())
}

// ffmpegArgs returns ffmpeg's arguments for streaming to url.
func ffmpegArgs(cfg Config, url string) []string {
	gop := strconv.Itoa(2 * cfg.FPS)
	rate := strconv.Itoa(cfg.VideoBitrate)
	return []string{
		"-hide_banner", "-loglevel", "warning", "-nostats", "-y",
		"-progress", "pipe:1",
		// ffmpeg opens the inputs one at a time and by default reads
		// seconds of each before opening the next, but frames arrive on
		// both pipes together. Both formats are fully specified, so skip
		// probing.
		"-probesize", "32", "-analyzeduration", "0",
		"-f", "rawvideo", "-pix_fmt", "yuv420p",
		"-video_size", fmt.Sprintf("%dx%d", cfg.Width, cfg.Height),
		"-framerate", strconv.Itoa(cfg.FPS),
		// The renderer draws BT.709 limited range. Without these tags
		// ffmpeg converts every frame through RGB to reach the output's.
		"-colorspace", "bt709", "-color_primaries", "bt709", "-color_trc", "bt709", "-color_range", "tv",
		// Each queued video packet is a whole raw frame, so keep the
		// queue short; frames wait in the encoder's queue instead.
		"-thread_queue_size", "8",
		"-i", "pipe:0",
		"-probesize", "32", "-analyzeduration", "0",
		"-f", "s16le", "-ar", strconv.Itoa(cfg.SampleRate), "-ch_layout", "stereo",
		"-thread_queue_size", "64",
		"-i", "pipe:3",
		"-map", "0:v", "-map", "1:a",
		"-c:v", "libx264", "-preset", cfg.Preset, "-profile:v", "high",
		"-pix_fmt", "yuv420p",
		"-b:v", rate, "-maxrate", rate, "-bufsize", strconv.Itoa(2 * cfg.VideoBitrate),
		// A keyframe every two seconds, as YouTube asks, and never between.
		"-g", gop, "-keyint_min", gop, "-sc_threshold", "0",
		// x264 otherwise holds back a frame per thread, plus lookahead,
		// before its first output. ffmpeg stops reading audio while it
		// waits, the audio pipe fills, and frames are dropped whole, so
		// with enough cores x264 never gets the frames it is waiting for.
		"-tune", "zerolatency",
		"-c:a", "aac", "-b:a", "160k", "-ar", strconv.Itoa(cfg.SampleRate),
		"-flvflags", "no_duration_filesize",
		// Give up on a connection that stops accepting data, in
		// microseconds, so the encoder can reconnect.
		"-rw_timeout", "15000000",
		"-f", cfg.Format, url,
	}
}

// lineWriter calls fn with each line written to it. ffmpeg ends progress
// lines with \n and some messages with \r.
type lineWriter struct {
	mu  sync.Mutex
	buf []byte
	fn  func(string)
}

func (w *lineWriter) Write(b []byte) (int, error) {
	w.mu.Lock()
	defer w.mu.Unlock()
	w.buf = append(w.buf, b...)
	for {
		i := bytes.IndexAny(w.buf, "\r\n")
		if i < 0 {
			break
		}
		if line := strings.TrimSpace(string(w.buf[:i])); line != "" {
			w.fn(line)
		}
		w.buf = w.buf[i+1:]
	}
	// A message without a newline shouldn't grow the buffer forever.
	if len(w.buf) > 64<<10 {
		w.fn(string(w.buf))
		w.buf = w.buf[:0]
	}
	return len(b), nil
}

// messages keeps ffmpeg's last messages for the error when it exits, and
// rate-limits logging them.
type messages struct {
	mu     sync.Mutex
	tail   []string
	window time.Time
	count  int
}

const (
	// tailLines is how many messages the exit error includes.
	tailLines = 12
	// logPerMinute is how many messages are logged as they arrive.
	logPerMinute = 10
)

// add records line and reports whether to log it.
func (m *messages) add(line string) bool {
	m.mu.Lock()
	defer m.mu.Unlock()
	m.tail = append(m.tail, line)
	if len(m.tail) > tailLines {
		m.tail = m.tail[1:]
	}
	if now := time.Now(); now.Sub(m.window) > time.Minute {
		m.window, m.count = now, 0
	}
	m.count++
	return m.count <= logPerMinute
}

func (m *messages) last() string {
	m.mu.Lock()
	defer m.mu.Unlock()
	return strings.Join(m.tail, "\n")
}
