package main

import (
	"errors"
	"fmt"
	"io"
	"net/http"
	"net/http/httptest"
	"slices"
	"strings"
	"sync"
	"testing"
	"time"

	"golang.org/x/mod/module"
)

var (
	today   = time.Date(2026, 3, 1, 0, 0, 0, 0, time.UTC)
	longAgo = time.Date(2026, 1, 1, 0, 0, 0, 0, time.UTC)
)

// fakeProxy is a module proxy that serves lists, info, and go.mod files
// from memory.
type fakeProxy struct {
	URL string

	mu     sync.Mutex
	files  map[string]string
	status map[string]int
	hits   map[string]int
}

func newFakeProxy(t *testing.T) *fakeProxy {
	p := &fakeProxy{files: map[string]string{}, status: map[string]int{}, hits: map[string]int{}}
	hs := httptest.NewServer(p)
	t.Cleanup(hs.Close)
	p.URL = hs.URL
	return p
}

func (p *fakeProxy) ServeHTTP(w http.ResponseWriter, req *http.Request) {
	p.mu.Lock()
	defer p.mu.Unlock()
	p.hits[req.URL.Path]++
	if code := p.status[req.URL.Path]; code != 0 {
		http.Error(w, http.StatusText(code), code)
		return
	}
	body, ok := p.files[req.URL.Path]
	if !ok {
		http.NotFound(w, req)
		return
	}
	io.WriteString(w, body)
}

// path returns the URL path of a file in a module's @v directory.
func (p *fakeProxy) path(mod, file string) string {
	esc, err := module.EscapePath(mod)
	if err != nil {
		panic(err)
	}
	return "/" + esc + "/@v/" + file
}

// publish adds a version of a module from time t, whose go.mod file holds
// extra after its module line.
func (p *fakeProxy) publish(mod, version string, t time.Time, extra string) {
	p.list(mod, version)
	p.set(mod, version+".info", fmt.Sprintf(`{"Version":%q,"Time":%q}`, version, t.UTC().Format(time.RFC3339)))
	p.set(mod, version+".mod", "module "+mod+"\n"+extra)
}

// list adds lines to a module's list of versions.
func (p *fakeProxy) list(mod string, lines ...string) {
	p.mu.Lock()
	defer p.mu.Unlock()
	for _, l := range lines {
		p.files[p.path(mod, "list")] += l + "\n"
	}
}

func (p *fakeProxy) set(mod, file, body string) {
	p.mu.Lock()
	defer p.mu.Unlock()
	p.files[p.path(mod, file)] = body
}

// fail makes the proxy answer requests for a module's file with code.
func (p *fakeProxy) fail(mod, file string, code int) {
	p.mu.Lock()
	defer p.mu.Unlock()
	p.status[p.path(mod, file)] = code
}

func (p *fakeProxy) hitsOf(mod, file string) int {
	p.mu.Lock()
	defer p.mu.Unlock()
	return p.hits[p.path(mod, file)]
}

// listedLongAgo returns a proxy whose clock reads today and that first
// listed mod's versions long ago, so only the versions' times decide which
// ones are old enough. An error in listing them shows up again when the
// test asks for a target.
func listedLongAgo(t *testing.T, mod string, urls ...string) *proxy {
	clock := longAgo
	p := newProxy(urls, time.Hour, func() time.Time { return clock })
	if _, err := p.versions(t.Context(), mod); err != nil {
		t.Logf("listing %s long ago: %v", mod, err)
	}
	clock = today
	return p
}

type release struct {
	version string
	age     time.Duration
	mod     string
}

func TestTarget(t *testing.T) {
	const day = 24 * time.Hour
	for _, tc := range []struct {
		name     string
		releases []release
		// lines are more lines in the list of versions.
		lines    []string
		from     []string
		excluded []string
		minAge   time.Duration
		want     string
		wait     time.Duration
	}{{
		name:     "the newest release",
		releases: []release{{version: "v1.0.0"}, {version: "v1.1.1"}, {version: "v1.1.0"}, {version: "v1.2.0-rc.1"}},
		lines:    []string{"v1.3.0-0.20260101000000-abcdefabcdef", "v1.4", "not a version", "", "v1.1.1"},
		from:     []string{"v1.0.0"},
		want:     "v1.1.1",
	}, {
		name:     "not another major version",
		releases: []release{{version: "v1.0.0"}, {version: "v1.1.0"}, {version: "v2.0.0+incompatible"}},
		from:     []string{"v1.0.0"},
		want:     "v1.1.0",
	}, {
		name:     "an incompatible version's own major version",
		releases: []release{{version: "v2.0.0+incompatible"}, {version: "v2.1.0+incompatible"}, {version: "v3.0.0+incompatible"}},
		from:     []string{"v2.0.0+incompatible"},
		want:     "v2.1.0+incompatible",
	}, {
		name:     "not from v0 to v1",
		releases: []release{{version: "v0.1.0"}, {version: "v0.2.0"}, {version: "v1.0.0"}},
		from:     []string{"v0.1.0"},
		want:     "v0.2.0",
	}, {
		name:     "nothing newer",
		releases: []release{{version: "v1.0.0"}, {version: "v1.1.0-rc.1"}},
		from:     []string{"v1.0.0"},
	}, {
		name:     "the newest version that a file requires, for the others",
		releases: []release{{version: "v1.0.0"}, {version: "v1.1.0"}, {version: "v1.2.0"}},
		from:     []string{"v1.2.0", "v1.0.0"},
		want:     "v1.2.0",
	}, {
		name:     "every file requires the newest",
		releases: []release{{version: "v1.0.0"}, {version: "v1.2.0"}},
		from:     []string{"v1.2.0", "v1.2.0"},
	}, {
		name:     "an excluded version",
		releases: []release{{version: "v1.0.0"}, {version: "v1.1.0"}, {version: "v1.2.0"}},
		from:     []string{"v1.0.0"},
		excluded: []string{"v1.2.0"},
		want:     "v1.1.0",
	}, {
		name: "retracted versions",
		releases: []release{
			{version: "v1.0.0"}, {version: "v1.0.1"}, {version: "v1.1.0"},
			{version: "v1.1.1", mod: "retract [v1.1.0, v1.1.1]\n"},
		},
		from: []string{"v1.0.0"},
		want: "v1.0.1",
	}, {
		name: "retractions in the newest release, not a prerelease",
		releases: []release{
			{version: "v1.0.0"}, {version: "v1.1.0"}, {version: "v1.2.0", mod: "retract v1.2.0\n"},
			{version: "v1.3.0-rc.1"},
		},
		from: []string{"v1.0.0"},
		want: "v1.1.0",
	}, {
		name: "retractions in the newest compatible release",
		releases: []release{
			{version: "v1.0.0"}, {version: "v1.1.0"}, {version: "v1.2.0", mod: "retract v1.2.0\n"},
			{version: "v2.0.0+incompatible"},
		},
		from: []string{"v1.0.0"},
		want: "v1.1.0",
	}, {
		name:     "a version that's too young",
		releases: []release{{version: "v1.0.0"}, {version: "v1.1.0"}, {version: "v1.2.0", age: day}},
		from:     []string{"v1.0.0"},
		minAge:   3 * day,
		want:     "v1.1.0",
		wait:     2 * day,
	}, {
		name:     "every newer version is too young",
		releases: []release{{version: "v1.0.0"}, {version: "v1.1.0", age: day}, {version: "v1.2.0", age: 2 * day}},
		from:     []string{"v1.0.0"},
		minAge:   3 * day,
		wait:     day,
	}, {
		name:     "a version that's exactly old enough",
		releases: []release{{version: "v1.0.0"}, {version: "v1.1.0", age: 3 * day}},
		from:     []string{"v1.0.0"},
		minAge:   3 * day,
		want:     "v1.1.0",
	}, {
		name:     "no minimum age",
		releases: []release{{version: "v1.0.0"}, {version: "v1.1.0", age: time.Minute}},
		from:     []string{"v1.0.0"},
		want:     "v1.1.0",
	}} {
		t.Run(tc.name, func(t *testing.T) {
			fp := newFakeProxy(t)
			const mod = "example.com/greet"
			for _, r := range tc.releases {
				at := longAgo
				if r.age > 0 {
					at = today.Add(-r.age)
				}
				fp.publish(mod, r.version, at, r.mod)
			}
			fp.list(mod, tc.lines...)
			excluded := map[string]bool{}
			for _, v := range tc.excluded {
				excluded[v] = true
			}
			p := listedLongAgo(t, mod, fp.URL)
			got, wait, err := p.target(t.Context(), mod, tc.from, excluded, tc.minAge)
			if err != nil || got != tc.want || wait != tc.wait {
				t.Errorf("target() = %q, %v, %v, want %q, %v", got, wait, err, tc.want, tc.wait)
			}
			if tc.minAge == 0 && slices.ContainsFunc(tc.releases, func(r release) bool { return fp.hitsOf(mod, r.version+".info") > 0 }) {
				t.Error("without a minimum age, target read versions' info")
			}
		})
	}
}

func TestTargetCaches(t *testing.T) {
	fp := newFakeProxy(t)
	const mod = "example.com/greet"
	fp.publish(mod, "v1.0.0", longAgo, "")
	fp.publish(mod, "v1.1.0", longAgo, "")
	clock := today
	p := newProxy([]string{fp.URL}, time.Hour, func() time.Time { return clock })
	target := func() string {
		t.Helper()
		v, _, err := p.target(t.Context(), mod, []string{"v1.0.0"}, nil, 0)
		if err != nil {
			t.Fatal(err)
		}
		return v
	}
	if got := target(); got != "v1.1.0" {
		t.Fatalf("target() = %q, want v1.1.0", got)
	}

	t.Log("Within the TTL, a new version doesn't show.")
	fp.publish(mod, "v1.2.0", longAgo, "")
	clock = clock.Add(59 * time.Minute)
	if got := target(); got != "v1.1.0" {
		t.Errorf("target() = %q, want v1.1.0 from the cached list", got)
	}

	t.Log("After it, the list is read again; go.mod files stay cached.")
	clock = clock.Add(time.Minute)
	if got := target(); got != "v1.2.0" {
		t.Errorf("target() = %q, want v1.2.0", got)
	}
	if n := fp.hitsOf(mod, "list"); n != 2 {
		t.Errorf("the list was read %d times, want 2", n)
	}
	if n := fp.hitsOf(mod, "v1.1.0.mod"); n != 1 {
		t.Errorf("v1.1.0.mod was read %d times, want 1", n)
	}
}

func TestTargetWaitsFromWhenAVersionShowsUp(t *testing.T) {
	const (
		mod    = "example.com/greet"
		minAge = 72 * time.Hour
	)
	fp := newFakeProxy(t)
	fp.publish(mod, "v1.0.0", longAgo, "")
	clock := today
	p := newProxy([]string{fp.URL}, time.Hour, func() time.Time { return clock })
	target := func(p *proxy, want string, wantWait time.Duration) {
		t.Helper()
		got, wait, err := p.target(t.Context(), mod, []string{"v1.0.0"}, nil, minAge)
		if err != nil || got != want || wait != wantWait {
			t.Errorf("target() = %q, %v, %v, want %q, %v", got, wait, err, want, wantWait)
		}
	}

	t.Log("v1.1.0 comes out with a backdated commit, so the proxy reports a time long ago.")
	fp.publish(mod, "v1.1.0", longAgo, "")
	target(p, "", minAge)
	clock = clock.Add(minAge - time.Second)
	target(p, "", time.Second)
	clock = clock.Add(time.Second)
	target(p, "v1.1.0", 0)

	t.Log("Each version waits from when it showed up.")
	fp.publish(mod, "v1.2.0", longAgo, "")
	clock = clock.Add(time.Hour)
	target(p, "v1.1.0", minAge)
	clock = clock.Add(minAge)
	target(p, "v1.2.0", 0)

	t.Log("A version whose time is later than when it showed up waits from its time.")
	fp.publish(mod, "v1.3.0", clock.Add(24*time.Hour), "")
	clock = clock.Add(time.Hour)
	target(p, "v1.2.0", minAge+23*time.Hour)

	t.Log("After a restart, every version waits again.")
	restarted := newProxy([]string{fp.URL}, time.Hour, func() time.Time { return clock })
	target(restarted, "", minAge)
	if n := fp.hitsOf(mod, "v1.1.0.info"); n != 2 {
		t.Errorf("v1.1.0.info was read %d times, want once by each proxy", n)
	}
}

func TestTargetErrors(t *testing.T) {
	const mod = "example.com/greet"
	for _, tc := range []struct {
		name string
		// setup sets up the first proxy and the second.
		setup    func(a, b *fakeProxy)
		want     string
		notFound bool
	}{{
		name: "falls through 404 and 410",
		setup: func(a, b *fakeProxy) {
			a.fail(mod, "list", http.StatusGone)
			b.publish(mod, "v1.0.0", longAgo, "")
			b.publish(mod, "v1.1.0", longAgo, "")
		},
		want: "v1.1.0",
	}, {
		name: "stops at other errors",
		setup: func(a, b *fakeProxy) {
			a.fail(mod, "list", http.StatusInternalServerError)
			b.publish(mod, "v1.0.0", longAgo, "")
			b.publish(mod, "v1.1.0", longAgo, "")
		},
	}, {
		name:     "no proxy has the module",
		setup:    func(a, b *fakeProxy) {},
		notFound: true,
	}, {
		name: "no proxy has the version's info",
		setup: func(a, b *fakeProxy) {
			a.publish(mod, "v1.0.0", longAgo, "")
			a.publish(mod, "v1.1.0", longAgo, "")
			a.fail(mod, "v1.1.0.info", http.StatusNotFound)
		},
		notFound: true,
	}, {
		name: "info for another version",
		setup: func(a, b *fakeProxy) {
			a.publish(mod, "v1.0.0", longAgo, "")
			a.publish(mod, "v1.1.0", longAgo, "")
			a.set(mod, "v1.1.0.info", `{"Version":"v1.0.0","Time":"2026-01-01T00:00:00Z"}`)
		},
	}, {
		name: "info that's too large",
		setup: func(a, b *fakeProxy) {
			a.publish(mod, "v1.0.0", longAgo, "")
			a.publish(mod, "v1.1.0", longAgo, "")
			a.set(mod, "v1.1.0.info", `{"Version":"v1.1.0","Time":"2026-01-01T00:00:00Z"}`+strings.Repeat(" ", maxInfo))
		},
	}, {
		name: "a go.mod file that doesn't parse",
		setup: func(a, b *fakeProxy) {
			a.publish(mod, "v1.0.0", longAgo, "")
			a.publish(mod, "v1.1.0", longAgo, "require (\n")
		},
	}} {
		t.Run(tc.name, func(t *testing.T) {
			a, b := newFakeProxy(t), newFakeProxy(t)
			tc.setup(a, b)
			p := listedLongAgo(t, mod, a.URL, b.URL)
			got, _, err := p.target(t.Context(), mod, []string{"v1.0.0"}, nil, time.Hour)
			switch {
			case tc.want != "":
				if err != nil || got != tc.want {
					t.Errorf("target() = %q, %v, want %q", got, err, tc.want)
				}
			case err == nil || errors.Is(err, errNotFound) != tc.notFound:
				t.Errorf("target() = %q, %v, want an error, errNotFound: %v", got, err, tc.notFound)
			}
		})
	}
}

func TestParseProxies(t *testing.T) {
	got, err := parseProxies("https://proxy.golang.org, http://10.0.0.1:3000/proxy/")
	if want := []string{"https://proxy.golang.org", "http://10.0.0.1:3000/proxy"}; err != nil || !slices.Equal(got, want) {
		t.Errorf("parseProxies() = %q, %v, want %q", got, err, want)
	}
	for _, s := range []string{"", "direct", "https://proxy.golang.org,off", "https://a.example.com|https://b.example.com", "ftp://a.example.com", "https://", "proxy.golang.org", "https://a.example.com,"} {
		if got, err := parseProxies(s); err == nil {
			t.Errorf("parseProxies(%q) = %q, want an error", s, got)
		}
	}
}
