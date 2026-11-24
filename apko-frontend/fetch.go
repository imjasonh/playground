package main

import (
	"bytes"
	"context"
	"errors"
	"fmt"
	"io"
	"maps"
	"net/http"
	"net/url"
	"path"
	"strings"
	"sync"

	"github.com/chainguard-dev/clog"
	"github.com/moby/buildkit/client/llb"
	"github.com/moby/buildkit/frontend/gateway/client"
)

// buildContextHost is the host of the URLs that the fetcher reads from the
// build context instead of the network. The .invalid top-level domain never
// resolves (RFC 2606).
const buildContextHost = "build-context.invalid"

// errNotFound reports that a build-context file doesn't exist.
var errNotFound = errors.New("not found")

// readChunk bounds each ReadFile call so large indexes stay under the
// gateway's gRPC message limit.
const readChunk = 4 << 20

func isRemote(s string) bool {
	return strings.HasPrefix(s, "https://") || strings.HasPrefix(s, "http://")
}

// contextURL returns the URL that stands for path p in the build context.
// The path is cleaned so it can't leave the context.
func contextURL(p string) string {
	p = strings.TrimPrefix(p, "file://")
	return "http://" + buildContextHost + path.Clean("/"+p)
}

// fetcher downloads URLs through BuildKit and keeps each URL's LLB state,
// so the helper step can mount exactly the files that apko read in the
// frontend.
type fetcher struct {
	c client.Client
	// mainContext returns the build context, limited to the given paths.
	mainContext func(ctx context.Context, paths ...string) (llb.State, error)

	mu      sync.Mutex
	entries map[string]*fetchEntry
	// warned holds the hosts warnAuth has reported.
	warned map[string]bool
}

type fetchEntry struct {
	url   string
	key   string
	state llb.State
	// local is set for build-context files.
	local bool

	once sync.Once
	data []byte
	err  error
}

func newFetcher(c client.Client, mainContext func(context.Context, ...string) (llb.State, error)) *fetcher {
	return &fetcher{c: c, mainContext: mainContext, entries: map[string]*fetchEntry{}, warned: map[string]bool{}}
}

// warnAuth logs, once for each host, how to pass credentials for it.
func (f *fetcher) warnAuth(ctx context.Context, host string) {
	f.mu.Lock()
	seen := f.warned[host]
	f.warned[host] = true
	f.mu.Unlock()
	if seen {
		return
	}
	clog.FromContext(ctx).Warn(fmt.Sprintf("%s requires credentials; pass them with --secret id=%s%s,env=VAR, where VAR holds the whole Authorization header, such as \"Basic <base64 of user:password>\", or with --secret id=%s%s,env=VAR, where VAR holds a bearer token",
		host, authHeaderSecretPrefix, host, authTokenSecretPrefix, host))
}

// entry returns the entry for rawURL, creating its LLB state on first use.
// The state's output holds one file, named by fetchKey, at its root.
func (f *fetcher) entry(ctx context.Context, rawURL string) (*fetchEntry, error) {
	key, err := fetchKey(rawURL)
	if err != nil {
		return nil, err
	}
	f.mu.Lock()
	defer f.mu.Unlock()
	if e, ok := f.entries[key]; ok {
		return e, nil
	}
	u, err := url.Parse(rawURL)
	if err != nil {
		return nil, err
	}
	var st llb.State
	local := false
	switch {
	case u.Host == buildContextHost:
		p := strings.TrimPrefix(path.Clean(u.Path), "/")
		src, err := f.mainContext(ctx, p)
		if err != nil {
			return nil, err
		}
		// The wildcard options turn a missing file into an empty
		// result, which read reports as errNotFound.
		st = llb.Scratch().File(
			llb.Copy(src, "/"+p, "/"+key, &llb.CopyInfo{AllowWildcard: true, AllowEmptyWildcard: true}),
			llb.WithCustomNamef("[context] %s", p),
		)
		local = true
	case u.Scheme == "https" || u.Scheme == "http":
		name := "fetch " + u.Redacted()
		if path.Base(u.Path) == "apk-configuration" {
			name = "probe " + u.Redacted() + " for signing keys (only Chainguard repositories have one; a 404 is normal)"
		}
		st = llb.HTTP(u.String(), llb.Filename(key), llb.WithCustomName(name))
	default:
		return nil, fmt.Errorf("unsupported URL %s", u.Redacted())
	}
	e := &fetchEntry{url: u.String(), key: key, state: st, local: local}
	f.entries[key] = e
	return e, nil
}

// get solves the entry's state and reads its file. The result is cached for
// the life of the build.
func (f *fetcher) get(ctx context.Context, e *fetchEntry) ([]byte, error) {
	e.once.Do(func() {
		e.data, e.err = f.read(ctx, e)
	})
	return e.data, e.err
}

func (f *fetcher) read(ctx context.Context, e *fetchEntry) ([]byte, error) {
	def, err := e.state.Marshal(ctx)
	if err != nil {
		return nil, err
	}
	res, err := f.c.Solve(ctx, client.SolveRequest{Definition: def.ToPB()})
	if err != nil {
		return nil, err
	}
	ref, err := res.SingleRef()
	if err != nil {
		return nil, err
	}
	st, err := ref.StatFile(ctx, client.StatRequest{Path: e.key})
	if err != nil {
		if e.local {
			return nil, fmt.Errorf("%s: %w", e.url, errNotFound)
		}
		return nil, err
	}
	var buf bytes.Buffer
	buf.Grow(int(st.Size))
	for off := 0; off < int(st.Size); {
		n := min(readChunk, int(st.Size)-off)
		b, err := ref.ReadFile(ctx, client.ReadRequest{
			Filename: e.key,
			Range:    &client.FileRange{Offset: off, Length: n},
		})
		if err != nil {
			return nil, err
		}
		if len(b) == 0 {
			return nil, fmt.Errorf("reading %s: unexpected end of file at %d of %d bytes", e.url, off, st.Size)
		}
		buf.Write(b)
		off += len(b)
	}
	return buf.Bytes(), nil
}

// recorder is an http.RoundTripper for one platform's resolution. It
// fetches through the shared fetcher and remembers every URL it served, so
// the helper for that platform mounts the same files.
type recorder struct {
	f *fetcher

	mu   sync.Mutex
	used map[string]*fetchEntry
}

func (f *fetcher) recorder() *recorder {
	return &recorder{f: f, used: map[string]*fetchEntry{}}
}

func (r *recorder) RoundTrip(req *http.Request) (*http.Response, error) {
	if req.Body != nil {
		req.Body.Close()
	}
	if req.Method != http.MethodGet && req.Method != http.MethodHead {
		return textResponse(req, http.StatusMethodNotAllowed, req.Method+" is not supported"), nil
	}
	e, err := r.f.entry(req.Context(), req.URL.String())
	if err != nil {
		return nil, err
	}
	data, err := r.f.get(req.Context(), e)
	if err != nil {
		// BuildKit's HTTP source reports a status other than 200 as
		// "invalid response status". apko treats some 404s as "absent"
		// rather than as failures.
		if errors.Is(err, errNotFound) || strings.Contains(err.Error(), "invalid response status 404") {
			return textResponse(req, http.StatusNotFound, err.Error()), nil
		}
		// Return an authentication failure as a response, which apko's
		// client doesn't retry, and say which secret to pass.
		for _, code := range []int{http.StatusUnauthorized, http.StatusForbidden} {
			if strings.Contains(err.Error(), fmt.Sprintf("invalid response status %d", code)) {
				r.f.warnAuth(req.Context(), req.URL.Hostname())
				return textResponse(req, code, err.Error()), nil
			}
		}
		return nil, fmt.Errorf("fetching %s: %w", req.URL.Redacted(), err)
	}
	r.add(e)
	var body io.ReadCloser = io.NopCloser(bytes.NewReader(data))
	if req.Method == http.MethodHead {
		body = http.NoBody
	}
	return &http.Response{
		Status:        "200 OK",
		StatusCode:    http.StatusOK,
		Proto:         "HTTP/1.1",
		ProtoMajor:    1,
		ProtoMinor:    1,
		Header:        http.Header{"Content-Type": {"application/octet-stream"}},
		ContentLength: int64(len(data)),
		Body:          body,
		Request:       req,
	}, nil
}

// add records that the helper needs e, without fetching it in the frontend.
func (r *recorder) add(e *fetchEntry) {
	r.mu.Lock()
	defer r.mu.Unlock()
	r.used[e.key] = e
}

// entries returns a copy of the entries r served, keyed by fetchKey.
func (r *recorder) entries() map[string]*fetchEntry {
	r.mu.Lock()
	defer r.mu.Unlock()
	return maps.Clone(r.used)
}
