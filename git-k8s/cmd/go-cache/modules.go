package main

import (
	"context"
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"io"
	"net/http"
	"os"
	"path"
	"regexp"
	"strconv"
	"strings"
)

// maxModuleFile is the size of the largest module file that go-cache
// keeps. The go command doesn't accept larger module zips.
const maxModuleFile = 500 << 20

var (
	// Module paths and versions in requests are escaped: an uppercase
	// letter is "!" and the letter in lowercase.
	moduleElementRE = regexp.MustCompile(`^[a-z0-9._~!-]+$`)
	versionRE       = regexp.MustCompile(`^[a-z0-9._+~!-]+$`)
	// canonicalRE matches the files of a canonical version, which never
	// change, so go-cache keeps them.
	canonicalRE = regexp.MustCompile(`^@v/v(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)(-[0-9a-z!-]+(\.[0-9a-z!-]+)*)?(\+incompatible)?\.(info|mod|zip)$`)
)

// parseModuleRequest splits the path of a module proxy request, after
// /mod/, into the escaped module path and the file: @v/list,
// @v/VERSION.info, @v/VERSION.mod, @v/VERSION.zip, or @latest.
func parseModuleRequest(p string) (module, file string, ok bool) {
	if m, found := strings.CutSuffix(p, "/@latest"); found {
		module, file = m, "@latest"
	} else if i := strings.LastIndex(p, "/@v/"); i >= 0 {
		module, file = p[:i], p[i+1:]
		if version := strings.TrimPrefix(file, "@v/"); version != "list" {
			ext := path.Ext(version)
			v := strings.TrimSuffix(version, ext)
			if (ext != ".info" && ext != ".mod" && ext != ".zip") || !versionRE.MatchString(v) || strings.HasPrefix(v, ".") {
				return "", "", false
			}
		}
	} else {
		return "", "", false
	}
	for _, e := range strings.Split(module, "/") {
		if !moduleElementRE.MatchString(e) || e == "." || e == ".." {
			return "", "", false
		}
	}
	return module, file, true
}

func moduleContentType(file string) string {
	switch {
	case file == "@latest" || strings.HasSuffix(file, ".info"):
		return "application/json"
	case strings.HasSuffix(file, ".zip"):
		return "application/zip"
	}
	return "text/plain; charset=utf-8"
}

// module serves the module proxy.
func (s *server) module(w http.ResponseWriter, r *http.Request) {
	module, file, ok := parseModuleRequest(strings.TrimPrefix(r.URL.Path, "/mod/"))
	if !ok {
		s.metrics.moduleRequest("not_found")
		http.NotFound(w, r)
		return
	}
	var key string
	if canonicalRE.MatchString(file) {
		sum := sha256.Sum256([]byte(module + "/" + file))
		key = "mod/" + hex.EncodeToString(sum[:1]) + "/" + hex.EncodeToString(sum[:])
		if f, err := s.store.open(key); err == nil {
			defer f.Close()
			s.metrics.moduleRequest("hit")
			serveModuleFile(w, f, file)
			return
		}
	}
	resp, err := s.fetch(r.Context(), s.upstream+"/"+module+"/"+file)
	if err != nil {
		s.moduleFailed(w, err)
		return
	}
	defer resp.Body.Close()
	switch resp.StatusCode {
	case http.StatusOK:
	case http.StatusNotFound, http.StatusGone:
		s.metrics.moduleRequest("not_found")
		msg, _ := io.ReadAll(io.LimitReader(resp.Body, 4096))
		w.Header().Set("Content-Type", "text/plain; charset=utf-8")
		w.WriteHeader(resp.StatusCode)
		w.Write(msg)
		return
	default:
		s.moduleFailed(w, fmt.Errorf("GET %s: %s", resp.Request.URL, resp.Status))
		return
	}
	if key == "" {
		s.metrics.moduleRequest("passthrough")
		w.Header().Set("Content-Type", moduleContentType(file))
		io.Copy(w, resp.Body)
		return
	}
	_, err = s.store.put(key, func(f io.Writer) error {
		n, err := io.Copy(f, io.LimitReader(resp.Body, maxModuleFile+1))
		if err == nil && n > maxModuleFile {
			err = fmt.Errorf("it's larger than %d bytes", maxModuleFile)
		}
		return err
	})
	if err != nil {
		s.moduleFailed(w, fmt.Errorf("GET %s: %w", resp.Request.URL, err))
		return
	}
	f, err := s.store.open(key)
	if err != nil {
		s.moduleFailed(w, err)
		return
	}
	defer f.Close()
	s.metrics.moduleRequest("fetched")
	serveModuleFile(w, f, file)
}

func (s *server) fetch(ctx context.Context, url string) (*http.Response, error) {
	req, err := http.NewRequestWithContext(ctx, http.MethodGet, url, nil)
	if err != nil {
		return nil, err
	}
	return s.client.Do(req)
}

func (s *server) moduleFailed(w http.ResponseWriter, err error) {
	s.metrics.moduleRequest("error")
	s.log.Warn("module proxy", "err", err)
	http.Error(w, err.Error(), http.StatusBadGateway)
}

func serveModuleFile(w http.ResponseWriter, f *os.File, file string) {
	w.Header().Set("Content-Type", moduleContentType(file))
	if fi, err := f.Stat(); err == nil {
		w.Header().Set("Content-Length", strconv.FormatInt(fi.Size(), 10))
	}
	io.Copy(w, f)
}
