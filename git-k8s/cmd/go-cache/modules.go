package main

import (
	"context"
	"crypto/sha256"
	"encoding/hex"
	"errors"
	"fmt"
	"io"
	"io/fs"
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
	if !canonicalRE.MatchString(file) {
		s.passThrough(w, r, module, file, "passthrough")
		return
	}
	sum := sha256.Sum256([]byte(module + "/" + file))
	key := "mod/" + hex.EncodeToString(sum[:1]) + "/" + hex.EncodeToString(sum[:])
	result := "hit"
	f, err := s.store.open(key)
	if errors.Is(err, fs.ErrNotExist) {
		// Requests that miss at once share one fetch, which goes on if the
		// request that started it ends.
		v, ferr, _ := s.fetches.Do(key, func() (any, error) {
			result = "fetched"
			return s.fetchModule(context.WithoutCancel(r.Context()), module, file, key)
		})
		if why, ok := storeUnavailable(ferr); ok {
			// The go command doesn't retry a download, and a test Pod's
			// GOPROXY lists only go-cache, so an error would fail the Pod.
			s.passThrough(w, r, module, file, why)
			return
		}
		if ferr != nil {
			s.moduleFailed(w, ferr)
			return
		}
		if missing := v.(*upstreamMiss); missing != nil {
			s.metrics.moduleRequest("not_found")
			w.Header().Set("Content-Type", "text/plain; charset=utf-8")
			w.WriteHeader(missing.status)
			w.Write(missing.msg)
			return
		}
		f, err = s.store.open(key)
	}
	if err != nil {
		s.moduleFailed(w, err)
		return
	}
	defer f.Close()
	s.metrics.moduleRequest(result)
	serveModuleFile(w, f, file)
}

// upstreamMiss is the upstream's answer for a file that it doesn't have.
type upstreamMiss struct {
	status int
	msg    []byte
}

// fetchModule fetches a canonical version's file from the upstream into the
// store, if the store has a free slot for the write and room for the file.
// It returns the upstream's answer if the upstream doesn't have the file.
func (s *server) fetchModule(ctx context.Context, module, file, key string) (*upstreamMiss, error) {
	resp, err := s.fetch(ctx, s.upstream+"/"+module+"/"+file)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()
	switch resp.StatusCode {
	case http.StatusOK:
	case http.StatusNotFound, http.StatusGone:
		msg, _ := io.ReadAll(io.LimitReader(resp.Body, 4096))
		return &upstreamMiss{resp.StatusCode, msg}, nil
	default:
		return nil, fmt.Errorf("GET %s: %s", resp.Request.URL, resp.Status)
	}
	if resp.ContentLength > maxModuleFile {
		return nil, fmt.Errorf("GET %s: it's larger than %d bytes", resp.Request.URL, maxModuleFile)
	}
	_, err = s.store.tryPut(ctx, key, resp.ContentLength, func(f io.Writer) error {
		n, err := io.Copy(f, io.LimitReader(resp.Body, maxModuleFile+1))
		if err == nil && n > maxModuleFile {
			err = fmt.Errorf("it's larger than %d bytes", maxModuleFile)
		}
		return err
	})
	if err != nil {
		return nil, fmt.Errorf("GET %s: %w", resp.Request.URL, err)
	}
	return nil, nil
}

// passThrough serves a file from the upstream without keeping it, and counts
// the request under result. It serves files that can change, such as a
// module's list of versions, and files that the store can't take now.
func (s *server) passThrough(w http.ResponseWriter, r *http.Request, module, file, result string) {
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
	s.metrics.moduleRequest(result)
	w.Header().Set("Content-Type", moduleContentType(file))
	if resp.ContentLength >= 0 {
		w.Header().Set("Content-Length", strconv.FormatInt(resp.ContentLength, 10))
	}
	if _, err := io.Copy(w, resp.Body); err != nil {
		s.log.Warn("module proxy", "err", fmt.Errorf("GET %s: %w", resp.Request.URL, err))
		// Ending the response normally would give the client part of the
		// file as all of it.
		panic(http.ErrAbortHandler)
	}
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

// storeUnavailable returns the metrics result for an error that means the
// store can't take a write now.
func storeUnavailable(err error) (string, bool) {
	switch {
	case errors.Is(err, errFull):
		return "full", true
	case errors.Is(err, errBusy):
		return "busy", true
	}
	return "", false
}

func serveModuleFile(w http.ResponseWriter, f *os.File, file string) {
	w.Header().Set("Content-Type", moduleContentType(file))
	if fi, err := f.Stat(); err == nil {
		w.Header().Set("Content-Length", strconv.FormatInt(fi.Size(), 10))
	}
	io.Copy(w, f)
}
