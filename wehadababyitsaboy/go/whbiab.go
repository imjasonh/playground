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
// The package works with programs built on [cobra]. Run the root command with
// [Execute] in place of its own Execute:
//
//	func main() {
//		if err := whbiab.Execute(context.Background(), rootCmd); err != nil {
//			os.Exit(1)
//		}
//	}
//
// Set DO_NOT_TRACK=1 or WHBIAB_DISABLE=1 to turn pings off. A test binary sends
// nothing unless WHBIAB_ENDPOINT names a server, so a CLI's tests need no setup.
package whbiab

import (
	"context"
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
	"github.com/spf13/cobra"
	"github.com/spf13/pflag"
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

// on reports whether an environment flag is set. "", "0", and "false" are off.
func on(v string) bool {
	return v != "" && v != "0" && !strings.EqualFold(v, "false")
}

// Execute runs root, as [cobra.Command.ExecuteContext] does, and sends a ping
// for the command that runs. The ping starts before the command's Run function,
// after cobra has parsed the flags, and Execute waits for it before it returns.
// It sends nothing for help, completion, or a command that fails to parse.
//
// CLIENT is the root command's name. ARGS is the names of the subcommands below
// the root and the names of the flags the user set, including flags that an
// ancestor declares as persistent. A flag's shorthand and its name count as the
// same flag.
//
// Execute sets [cobra.EnableTraverseRunHooks], so that a PersistentPreRun on a
// subcommand doesn't replace the one that sends the ping. The root's own
// PersistentPreRun or PersistentPreRunE still runs, after the ping starts.
//
// Execute never fails the program because of a ping. A disabled or failed ping
// is silent, and the wait is at most about two seconds.
func Execute(ctx context.Context, root *cobra.Command) error {
	cobra.EnableTraverseRunHooks = true
	var wait func()
	preRun, preRunE := root.PersistentPreRun, root.PersistentPreRunE
	root.PersistentPreRun, root.PersistentPreRunE = nil, func(cmd *cobra.Command, args []string) error {
		if wait == nil && !skipped(cmd) {
			client, parts := cobraParts(cmd)
			wait = track(ctx, client, parts...)
		}
		switch {
		case preRunE != nil:
			return preRunE(cmd, args)
		case preRun != nil:
			preRun(cmd, args)
		}
		return nil
	}
	err := root.ExecuteContext(ctx)
	if wait != nil {
		wait()
	}
	return err
}

// skipped reports whether cmd is one of cobra's built-in commands, which tell
// us nothing about how people use the program.
func skipped(cmd *cobra.Command) bool {
	for c := cmd; c.HasParent(); c = c.Parent() {
		switch c.Name() {
		case cobra.ShellCompRequestCmd, cobra.ShellCompNoDescRequestCmd, "completion", "help":
			return true
		}
	}
	return false
}

// cobraParts returns the program name and the parts of the object name for the
// command that is running: the subcommands below the root, then the names of
// the flags that were set.
func cobraParts(cmd *cobra.Command) (client string, parts []string) {
	client = cmd.Root().Name()
	if path := strings.Fields(cmd.CommandPath()); len(path) > 1 {
		parts = append(parts, path[1:]...)
	}
	cmd.Flags().Visit(func(f *pflag.Flag) {
		parts = append(parts, f.Name)
	})
	return client, parts
}

// track sends a ping in the background and returns a function that waits for
// it. client is the program name. parts name the subcommand and the flags the
// user set. Each is lowercased, and every character outside a-z, 0-9, "-", and
// "_" becomes "-".
func track(ctx context.Context, client string, parts ...string) (wait func()) {
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
