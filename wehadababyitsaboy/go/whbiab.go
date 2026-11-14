// Package whbiab records one use of a command-line program in the
// wehadababyitsaboy bucket.
//
// A ping is an HTTPS GET for an object that does not exist:
//
//	https://storage.googleapis.com/wehadababyitsaboy/CLIENT/ARGS?bob=wehadababyitsaboy&v=VERSION&os=OS&arch=ARCH
//
// The bucket answers 403, and its hourly usage logs keep the request line, the
// client address, and the user agent. CLIENT is the program name. ARGS is the
// subcommand and the names of the flags the user set, joined with dots. A ping
// never carries a flag value or a positional argument, because a value can be a
// path, a query, or a token.
//
// Set DO_NOT_TRACK=1 or WHBIAB_DISABLE=1 to turn pings off. A test binary sends
// nothing unless WHBIAB_ENDPOINT names a server, so a CLI's tests need no setup.
package whbiab

import (
	"context"
	"flag"
	"io"
	"log/slog"
	"net/http"
	"net/url"
	"runtime"
	"runtime/debug"
	"strings"
	"testing"
	"time"

	"github.com/sethvargo/go-envconfig"
)

const (
	defaultEndpoint = "https://storage.googleapis.com/wehadababyitsaboy"

	// maxParts and maxPartLen bound the size of the object name.
	maxParts   = 16
	maxPartLen = 64

	// defaultArgs names a ping that has no subcommand and no flags.
	defaultArgs = "run"

	queryKey   = "bob"
	queryValue = "wehadababyitsaboy"
)

// requestTimeout bounds one ping, from connecting to reading the response.
// Tests shorten it.
var requestTimeout = 2 * time.Second

type config struct {
	DoNotTrack string `env:"DO_NOT_TRACK"`
	Disable    string `env:"WHBIAB_DISABLE"`
	Endpoint   string `env:"WHBIAB_ENDPOINT"`
	CI         string `env:"CI"`
}

func (c config) disabled() bool {
	return on(c.DoNotTrack) || on(c.Disable)
}

func (c config) endpoint() string {
	if c.Endpoint == "" {
		return defaultEndpoint
	}
	return c.Endpoint
}

func on(v string) bool {
	return v != "" && v != "0"
}

// Track sends a ping in the background and returns a function that waits for
// it. Call wait before the program exits, including before os.Exit and
// log.Fatal, or the process can end before the request leaves.
//
// client is the program name. parts name the subcommand and the flags the user
// set; see [Flags]. Each is lowercased, and every character outside a-z, 0-9,
// "-", and "_" becomes "-". Never pass a flag value or a positional argument.
//
// Track never fails the program. A disabled or failed ping is silent, and wait
// returns within about two seconds.
func Track(ctx context.Context, client string, parts ...string) (wait func()) {
	noop := func() {}
	var cfg config
	if err := envconfig.Process(ctx, &cfg); err != nil {
		slog.DebugContext(ctx, "usage ping skipped", "error", err)
		return noop
	}
	if cfg.disabled() || (testing.Testing() && cfg.Endpoint == "") {
		return noop
	}
	target, ok := pingURL(cfg, client, parts)
	if !ok {
		return noop
	}
	agent := clean(client) + "/" + version() + " (whbiab)"
	done := make(chan struct{})
	go func() {
		defer close(done)
		send(ctx, target, agent)
	}()
	return func() { <-done }
}

// Flags returns the names of the flags that fs set, in lexicographic order.
// It leaves out their values. Pass flag.CommandLine for the default flag set.
func Flags(fs *flag.FlagSet) []string {
	var names []string
	fs.Visit(func(f *flag.Flag) {
		names = append(names, f.Name)
	})
	return names
}

func pingURL(cfg config, client string, parts []string) (string, bool) {
	name := clean(client)
	if name == "" {
		return "", false
	}
	var args []string
	for _, p := range parts {
		if p = clean(p); p != "" {
			args = append(args, p)
		}
		if len(args) == maxParts {
			break
		}
	}
	joined := strings.Join(args, ".")
	if joined == "" {
		joined = defaultArgs
	}

	extra := url.Values{}
	extra.Set("v", version())
	extra.Set("os", runtime.GOOS)
	extra.Set("arch", runtime.GOARCH)
	if on(cfg.CI) {
		extra.Set("ci", "1")
	}

	base := strings.TrimRight(cfg.endpoint(), "/")
	// bob goes first so that the usage-log filter matches it.
	return base + "/" + name + "/" + joined + "?" + queryKey + "=" + queryValue + "&" + extra.Encode(), true
}

func send(ctx context.Context, target, agent string) {
	ctx, cancel := context.WithTimeout(ctx, requestTimeout)
	defer cancel()
	req, err := http.NewRequestWithContext(ctx, http.MethodGet, target, nil)
	if err != nil {
		slog.DebugContext(ctx, "usage ping skipped", "error", err)
		return
	}
	req.Header.Set("User-Agent", agent)
	resp, err := http.DefaultClient.Do(req)
	if err != nil {
		slog.DebugContext(ctx, "usage ping failed", "error", err)
		return
	}
	defer resp.Body.Close()
	// The bucket answers 403 on purpose; only the request matters.
	_, _ = io.Copy(io.Discard, io.LimitReader(resp.Body, 4096))
}

// clean lowercases s and replaces every character that is not safe in an
// object name with "-".
func clean(s string) string {
	var b strings.Builder
	for _, r := range strings.ToLower(s) {
		switch {
		case r >= 'a' && r <= 'z', r >= '0' && r <= '9', r == '-', r == '_':
			b.WriteRune(r)
		default:
			b.WriteByte('-')
		}
	}
	out := strings.Trim(b.String(), "-")
	if len(out) > maxPartLen {
		out = strings.Trim(out[:maxPartLen], "-")
	}
	return out
}

// version names the build of the running program: its module version, or the
// short commit it was built from, or "dev".
func version() string {
	bi, ok := debug.ReadBuildInfo()
	if !ok {
		return "dev"
	}
	if v := bi.Main.Version; v != "" && v != "(devel)" {
		return v
	}
	var rev, dirty string
	for _, s := range bi.Settings {
		switch s.Key {
		case "vcs.revision":
			rev = s.Value
		case "vcs.modified":
			if s.Value == "true" {
				dirty = "-dirty"
			}
		}
	}
	if rev == "" {
		return "dev"
	}
	return rev[:min(len(rev), 12)] + dirty
}
