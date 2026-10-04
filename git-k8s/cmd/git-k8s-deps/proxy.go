package main

import (
	"cmp"
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"maps"
	"net/http"
	"net/url"
	"slices"
	"strings"
	"sync"
	"time"

	"golang.org/x/mod/modfile"
	"golang.org/x/mod/module"
	"golang.org/x/mod/semver"
)

// errNotFound means that no module proxy has a module or a version of it.
var errNotFound = errors.New("no module proxy has it")

// Limits on what the controller reads from a module proxy.
const (
	maxList = 1 << 20
	maxInfo = 64 << 10
	maxMod  = 4 << 20
)

// parseProxies parses the -goproxy flag, a comma-separated list of module
// proxy URLs. The controller and its Pods read modules only from proxies,
// so it rejects direct and off, and the | separator, which falls back on
// errors that a comma doesn't.
func parseProxies(s string) ([]string, error) {
	var urls []string
	for part := range strings.SplitSeq(s, ",") {
		part = strings.TrimSpace(part)
		u, err := url.Parse(part)
		switch {
		case part == "direct" || part == "off":
			return nil, fmt.Errorf("-goproxy holds %s, but git-k8s-deps reads modules only from module proxies", part)
		case strings.Contains(part, "|"):
			return nil, errors.New("-goproxy holds |, but git-k8s-deps needs proxies separated by commas")
		case err != nil || (u.Scheme != "https" && u.Scheme != "http") || u.Host == "":
			return nil, fmt.Errorf("-goproxy holds %q, which isn't an http or https URL", part)
		}
		urls = append(urls, strings.TrimSuffix(part, "/"))
	}
	return urls, nil
}

// proxy reads modules' versions from module proxies. Like the go command,
// it asks the next proxy only when one answers 404 or 410.
type proxy struct {
	urls   []string
	client *http.Client
	// ttl is how long a module's list of versions stays cached. A
	// version's time and go.mod file don't change, so they stay cached.
	ttl time.Duration
	now func() time.Time

	mu       sync.Mutex
	lists    map[string]versionList
	times    map[module.Version]time.Time
	retracts map[module.Version][]modfile.VersionInterval
	// seen holds when this process first saw each version that target
	// considered in its module's list, and stored holds the times that
	// load read last, which other processes may have written.
	seen, stored map[seenKey]time.Time
}

// seenKey is a version that a proxy listed.
type seenKey struct {
	proxy, path, version string
}

type versionList struct {
	versions []string
	// proxy is the URL of the proxy that listed the versions.
	proxy string
	at    time.Time
}

func newProxy(urls []string, ttl time.Duration, now func() time.Time) *proxy {
	return &proxy{
		urls: urls, client: &http.Client{Timeout: 30 * time.Second}, ttl: ttl, now: now,
		lists: map[string]versionList{}, times: map[module.Version]time.Time{}, retracts: map[module.Version][]modfile.VersionInterval{},
		seen: map[seenKey]time.Time{}, stored: map[seenKey]time.Time{},
	}
}

// get reads a file from a module's @v directory on the first proxy that
// has it, and returns that proxy's URL.
func (p *proxy) get(ctx context.Context, path, file string, limit int64) (body []byte, from string, err error) {
	esc, err := module.EscapePath(path)
	if err != nil {
		return nil, "", err
	}
	for _, base := range p.urls {
		u := base + "/" + esc + "/@v/" + file
		req, err := http.NewRequestWithContext(ctx, http.MethodGet, u, nil)
		if err != nil {
			return nil, "", err
		}
		resp, err := p.client.Do(req)
		if err != nil {
			return nil, "", err
		}
		body, err := io.ReadAll(io.LimitReader(resp.Body, limit+1))
		resp.Body.Close()
		switch {
		case resp.StatusCode == http.StatusNotFound || resp.StatusCode == http.StatusGone:
			continue
		case resp.StatusCode != http.StatusOK:
			return nil, "", fmt.Errorf("GET %s: %s", u, resp.Status)
		case err != nil:
			return nil, "", fmt.Errorf("GET %s: %w", u, err)
		case int64(len(body)) > limit:
			return nil, "", fmt.Errorf("GET %s: the response is larger than %d bytes", u, limit)
		}
		return body, base, nil
	}
	return nil, "", errNotFound
}

// versions returns a module's versions other than pseudo-versions, in
// semver order, from the first proxy that has the module. It forgets when
// this process first saw the versions that the proxy no longer lists.
func (p *proxy) versions(ctx context.Context, path string) (versionList, error) {
	p.mu.Lock()
	l, ok := p.lists[path]
	p.mu.Unlock()
	if ok && p.now().Sub(l.at) < p.ttl {
		return l, nil
	}
	body, from, err := p.get(ctx, path, "list", maxList)
	if err != nil {
		return versionList{}, err
	}
	var vs []string
	for line := range strings.Lines(string(body)) {
		f := strings.Fields(line)
		if len(f) == 0 {
			continue
		}
		if v := f[0]; module.Check(path, v) == nil && module.CanonicalVersion(v) == v && !module.IsPseudoVersion(v) && !slices.Contains(vs, v) {
			vs = append(vs, v)
		}
	}
	semver.Sort(vs)
	l = versionList{versions: vs, proxy: from, at: p.now()}
	p.mu.Lock()
	p.lists[path] = l
	maps.DeleteFunc(p.seen, func(k seenKey, _ time.Time) bool {
		return k.proxy == from && k.path == path && !slices.Contains(vs, k.version)
	})
	p.mu.Unlock()
	return l, nil
}

// time returns a version's time from the proxy's info about it.
func (p *proxy) time(ctx context.Context, path, version string) (time.Time, error) {
	key := module.Version{Path: path, Version: version}
	p.mu.Lock()
	t, ok := p.times[key]
	p.mu.Unlock()
	if ok {
		return t, nil
	}
	esc, err := module.EscapeVersion(version)
	if err != nil {
		return time.Time{}, err
	}
	body, _, err := p.get(ctx, path, esc+".info", maxInfo)
	if err != nil {
		return time.Time{}, err
	}
	var info struct {
		Version string
		Time    time.Time
	}
	if err := json.Unmarshal(body, &info); err != nil {
		return time.Time{}, fmt.Errorf("reading the info of %s: %w", key, err)
	}
	if info.Version != version || info.Time.IsZero() {
		return time.Time{}, fmt.Errorf("the info of %s has version %q and time %v", key, info.Version, info.Time)
	}
	p.mu.Lock()
	p.times[key] = info.Time
	p.mu.Unlock()
	return info.Time, nil
}

// retractions returns the versions that the go.mod file of a version
// retracts.
func (p *proxy) retractions(ctx context.Context, path, version string) ([]modfile.VersionInterval, error) {
	key := module.Version{Path: path, Version: version}
	p.mu.Lock()
	rs, ok := p.retracts[key]
	p.mu.Unlock()
	if ok {
		return rs, nil
	}
	esc, err := module.EscapeVersion(version)
	if err != nil {
		return nil, err
	}
	body, _, err := p.get(ctx, path, esc+".mod", maxMod)
	if err != nil {
		return nil, err
	}
	f, err := modfile.ParseLax(key.String()+"/go.mod", body, nil)
	if err != nil {
		return nil, err
	}
	rs = []modfile.VersionInterval{}
	for _, r := range f.Retract {
		rs = append(rs, r.VersionInterval)
	}
	p.mu.Lock()
	p.retracts[key] = rs
	p.mu.Unlock()
	return rs, nil
}

// target returns the version of a module to update to from the versions
// in from, or "" if there's none. That's the newest release with the same
// major version as the newest version in from that's newer than the oldest
// one, isn't in excluded, isn't retracted, and is at least minAge old, both
// by its time and since it showed up in the module's list, unless it's
// vetted, a version that was old enough before. wait is how long until a
// newer version is old enough.
func (p *proxy) target(ctx context.Context, path string, from []string, excluded map[string]bool, minAge time.Duration, vetted string) (version string, wait time.Duration, err error) {
	if len(from) == 0 {
		return "", 0, nil
	}
	list, err := p.versions(ctx, path)
	if err != nil {
		return "", 0, err
	}
	oldest := slices.MinFunc(from, semver.Compare)
	newest := slices.MaxFunc(from, semver.Compare)
	var candidates []string
	for _, v := range list.versions {
		if semver.Prerelease(v) == "" && semver.Major(v) == semver.Major(newest) && semver.Compare(v, oldest) > 0 && !excluded[v] {
			candidates = append(candidates, v)
		}
	}
	if len(candidates) == 0 {
		return "", 0, nil
	}
	var seen map[string]time.Time
	if minAge > 0 {
		seen = p.firstSeen(list.proxy, path, candidates)
	}
	retracted, err := p.retractions(ctx, path, latest(list.versions))
	if err != nil {
		return "", 0, err
	}
	now := p.now()
	for _, v := range slices.Backward(candidates) {
		if slices.ContainsFunc(retracted, func(r modfile.VersionInterval) bool {
			return semver.Compare(r.Low, v) <= 0 && semver.Compare(v, r.High) <= 0
		}) {
			continue
		}
		if minAge > 0 && v != vetted {
			t, err := p.time(ctx, path, v)
			if err != nil {
				return "", 0, err
			}
			// A proxy reports the time of the version's commit, which
			// whoever made the commit picks, so the version also waits
			// from when it showed up.
			if seen[v].After(t) {
				t = seen[v]
			}
			if d := t.Add(minAge).Sub(now); d > 0 {
				if wait == 0 || d < wait {
					wait = d
				}
				continue
			}
		}
		return v, wait, nil
	}
	return "", wait, nil
}

// latest returns the version whose go.mod file holds a module's
// retractions. Like the go command, that's the newest release, or the
// newest version if there's no release, leaving out +incompatible versions
// when the module has others.
func latest(list []string) string {
	compatible := slices.DeleteFunc(slices.Clone(list), func(v string) bool { return strings.HasSuffix(v, "+incompatible") })
	if len(compatible) > 0 {
		list = compatible
	}
	releases := slices.DeleteFunc(slices.Clone(list), func(v string) bool { return semver.Prerelease(v) != "" })
	if len(releases) > 0 {
		list = releases
	}
	return list[len(list)-1]
}

// firstSeen returns when each of versions first showed up in the list of a
// module from a proxy, by what this process saw and the times that load
// read, and remembers the times.
func (p *proxy) firstSeen(proxy, path string, versions []string) map[string]time.Time {
	now := p.now()
	p.mu.Lock()
	defer p.mu.Unlock()
	times := make(map[string]time.Time, len(versions))
	for _, v := range versions {
		k := seenKey{proxy: proxy, path: path, version: v}
		t := now
		for _, m := range []map[seenKey]time.Time{p.seen, p.stored} {
			if s, ok := m[k]; ok && s.Before(t) {
				t = s
			}
		}
		if s, ok := p.seen[k]; !ok || t.Before(s) {
			// path and v can be parts of larger strings, such as a
			// proxy's response, that the map mustn't keep.
			p.seen[seenKey{proxy: proxy, path: strings.Clone(path), version: strings.Clone(v)}] = t
		}
		times[v] = t
	}
	return times
}

// maxStored is the most bytes that encode returns. A ConfigMap holds at
// most 1 MiB.
var maxStored = 256 << 10

// encode returns the first-seen times that this process and the last load
// know, a line each, for load to read. It leaves out a version that a
// fresh list from its proxy doesn't have, and a version that only this
// process knows when there's no fresh list from its proxy: another process
// may have left that out for being unlisted. When the lines don't fit in
// maxStored bytes, encode leaves out the oldest times.
func (p *proxy) encode() string {
	now := p.now()
	p.mu.Lock()
	keep := func(k seenKey) bool {
		if l, ok := p.lists[k.path]; ok && l.proxy == k.proxy && now.Sub(l.at) < p.ttl {
			return slices.Contains(l.versions, k.version)
		}
		_, ok := p.stored[k]
		return ok
	}
	times := map[seenKey]time.Time{}
	for _, m := range []map[seenKey]time.Time{p.stored, p.seen} {
		for k, t := range m {
			if s, ok := times[k]; (!ok || t.Before(s)) && keep(k) {
				times[k] = t
			}
		}
	}
	p.mu.Unlock()
	keys := slices.SortedFunc(maps.Keys(times), func(a, b seenKey) int {
		return cmp.Or(times[b].Compare(times[a]), cmp.Compare(a.proxy, b.proxy), cmp.Compare(a.path, b.path), cmp.Compare(a.version, b.version))
	})
	var lines []string
	size := 0
	for _, k := range keys {
		line := fmt.Sprintf("%s %s %s %s\n", k.proxy, k.path, k.version, times[k].UTC().Format(time.RFC3339Nano))
		if size += len(line); size > maxStored {
			break
		}
		lines = append(lines, line)
	}
	slices.Sort(lines)
	return strings.Join(lines, "")
}

// load reads lines that encode returned, in place of the times that it
// read before. It skips lines for proxies that the controller doesn't read
// from and lines that it can't parse.
func (p *proxy) load(raw string) {
	stored := map[seenKey]time.Time{}
	for line := range strings.Lines(raw) {
		f := strings.Fields(line)
		if len(f) != 4 || !slices.Contains(p.urls, f[0]) || module.Check(f[1], f[2]) != nil {
			continue
		}
		t, err := time.Parse(time.RFC3339Nano, f[3])
		if err != nil {
			continue
		}
		k := seenKey{proxy: f[0], path: f[1], version: f[2]}
		if s, ok := stored[k]; !ok || t.Before(s) {
			stored[k] = t
		}
	}
	p.mu.Lock()
	p.stored = stored
	p.mu.Unlock()
}
