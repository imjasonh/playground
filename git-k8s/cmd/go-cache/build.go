package main

import (
	"bytes"
	"crypto/sha256"
	"encoding/hex"
	"errors"
	"fmt"
	"io"
	"io/fs"
	"net/http"
	"os"
	"regexp"
	"strconv"
	"strings"

	"github.com/imjasonh/playground/git-k8s/internal/gocache"
)

var (
	namespaceRE  = regexp.MustCompile(`^[a-z0-9]([-a-z0-9]{0,61}[a-z0-9])?$`)
	repositoryRE = regexp.MustCompile(`^[a-z0-9]([-a-z0-9]*[a-z0-9])?(\.[a-z0-9]([-a-z0-9]*[a-z0-9])?)*$`)
)

// buildKey is where the store keeps a repository's output for an action:
// a line with the output ID and size, then the output.
func buildKey(ns, repo, action string) string {
	return "build/" + ns + "/" + repo + "/" + action[:2] + "/" + action
}

// authorize checks the path and token of a build cache request, and
// returns the key of the entry. If the request fails, authorize writes the
// response.
func (s *server) authorize(w http.ResponseWriter, r *http.Request, method string, audience func(ns, repo string) string) (string, bool) {
	ns, repo, action := r.PathValue("namespace"), r.PathValue("repository"), r.PathValue("action")
	if !namespaceRE.MatchString(ns) || len(repo) > 253 || !repositoryRE.MatchString(repo) || !gocache.IsID(action) {
		s.metrics.buildRequest(method, "invalid")
		http.Error(w, "want /cache/NAMESPACE/REPOSITORY/ACTION, with the action ID in lowercase hex", http.StatusBadRequest)
		return "", false
	}
	token, ok := strings.CutPrefix(r.Header.Get("Authorization"), "Bearer ")
	if !ok || token == "" {
		s.metrics.buildRequest(method, "denied")
		w.Header().Set("WWW-Authenticate", "Bearer")
		http.Error(w, "a service account token is required", http.StatusUnauthorized)
		return "", false
	}
	if s.reviewer == nil {
		s.metrics.buildRequest(method, "error")
		http.Error(w, "go-cache isn't running in a cluster, so it can't check tokens", http.StatusServiceUnavailable)
		return "", false
	}
	id, err := s.reviewer.review(r.Context(), token, audience(ns, repo))
	if err == nil && id.namespace == ns && method == "PUT" {
		err = s.reviewer.checkWriter(r.Context(), id)
	}
	switch {
	case errors.Is(err, errDenied):
		s.metrics.buildRequest(method, "denied")
		http.Error(w, err.Error(), http.StatusForbidden)
		return "", false
	case err != nil:
		s.metrics.buildRequest(method, "error")
		s.log.Error("checking a token", "err", err)
		http.Error(w, "couldn't check the token", http.StatusServiceUnavailable)
		return "", false
	case id.namespace != ns:
		s.metrics.buildRequest(method, "denied")
		http.Error(w, fmt.Sprintf("the token is from namespace %s, not %s", id.namespace, ns), http.StatusForbidden)
		return "", false
	}
	return buildKey(ns, repo, action), true
}

func (s *server) getOutput(w http.ResponseWriter, r *http.Request) {
	key, ok := s.authorize(w, r, "GET", gocache.ReadAudience)
	if !ok {
		return
	}
	f, err := s.store.open(key)
	if errors.Is(err, fs.ErrNotExist) {
		s.metrics.buildRequest("GET", "miss")
		http.NotFound(w, r)
		return
	} else if err != nil {
		s.buildFailed(w, "GET", err)
		return
	}
	defer f.Close()
	output, size, offset, err := readEntry(f)
	if err != nil {
		s.buildFailed(w, "GET", fmt.Errorf("reading %s: %w", key, err))
		return
	}
	s.metrics.buildRequest("GET", "hit")
	w.Header().Set(gocache.OutputIDHeader, output)
	w.Header().Set("Content-Type", "application/octet-stream")
	w.Header().Set("Content-Length", strconv.FormatInt(size, 10))
	io.Copy(w, io.NewSectionReader(f, offset, size))
}

var errMismatch = errors.New("the body doesn't match its length and output ID")

func (s *server) putOutput(w http.ResponseWriter, r *http.Request) {
	key, ok := s.authorize(w, r, "PUT", gocache.WriteAudience)
	if !ok {
		return
	}
	output, size := r.Header.Get(gocache.OutputIDHeader), r.ContentLength
	switch {
	case !gocache.IsID(output):
		s.metrics.buildRequest("PUT", "invalid")
		http.Error(w, gocache.OutputIDHeader+" must be the output ID in lowercase hex", http.StatusBadRequest)
		return
	case size < 0:
		s.metrics.buildRequest("PUT", "invalid")
		http.Error(w, "a Content-Length is required", http.StatusLengthRequired)
		return
	case size > gocache.MaxOutputSize:
		s.metrics.buildRequest("PUT", "invalid")
		http.Error(w, fmt.Sprintf("outputs can't be larger than %d bytes", gocache.MaxOutputSize), http.StatusRequestEntityTooLarge)
		return
	}
	// Answering before reading the body spares a client that sent
	// Expect: 100-continue from sending it.
	if s.answerExisting(w, key, output) {
		return
	}
	header := fmt.Sprintf("%s %d\n", output, size)
	created, err := s.store.put(r.Context(), key, int64(len(header))+size, func(f io.Writer) error {
		if _, err := io.WriteString(f, header); err != nil {
			return err
		}
		h := sha256.New()
		_, err := io.CopyN(io.MultiWriter(f, h), r.Body, size)
		switch {
		case errors.Is(err, io.EOF) || errors.Is(err, io.ErrUnexpectedEOF):
			return errMismatch
		case err != nil:
			return err
		case hex.EncodeToString(h.Sum(nil)) != output:
			return errMismatch
		}
		return nil
	})
	result, unavailable := storeUnavailable(err)
	switch {
	case errors.Is(err, errMismatch):
		s.metrics.buildRequest("PUT", "invalid")
		http.Error(w, err.Error(), http.StatusBadRequest)
	case unavailable:
		s.metrics.buildRequest("PUT", result)
		http.Error(w, err.Error(), http.StatusServiceUnavailable)
	case err != nil:
		s.buildFailed(w, "PUT", err)
	case created:
		s.metrics.buildRequest("PUT", "created")
		w.WriteHeader(http.StatusCreated)
	case !s.answerExisting(w, key, output):
		s.buildFailed(w, "PUT", fmt.Errorf("reading %s after another request wrote it", key))
	}
}

// answerExisting answers a PUT of output when the store already has an
// entry for key: with 200 if the entry holds output, or with 409 if it
// holds another output, which it keeps.
func (s *server) answerExisting(w http.ResponseWriter, key, output string) bool {
	f, err := s.store.open(key)
	if err != nil {
		return false
	}
	defer f.Close()
	have, _, _, err := readEntry(f)
	switch {
	case err != nil:
		return false
	case have == output:
		s.metrics.buildRequest("PUT", "exists")
		w.WriteHeader(http.StatusOK)
	default:
		s.metrics.buildRequest("PUT", "conflict")
		http.Error(w, "the cache has another output for this action: "+have, http.StatusConflict)
	}
	return true
}

func (s *server) buildFailed(w http.ResponseWriter, method string, err error) {
	s.metrics.buildRequest(method, "error")
	s.log.Error("build cache", "method", method, "err", err)
	http.Error(w, "go-cache couldn't serve the request", http.StatusInternalServerError)
}

// readEntry reads the line at the start of a build cache entry, and
// returns the output's ID and size, and where the output starts.
func readEntry(f *os.File) (output string, size, offset int64, err error) {
	buf := make([]byte, 128)
	n, err := f.ReadAt(buf, 0)
	if err != nil && !errors.Is(err, io.EOF) {
		return "", 0, 0, err
	}
	line, _, ok := bytes.Cut(buf[:n], []byte("\n"))
	fields := strings.Fields(string(line))
	if !ok || len(fields) != 2 || !gocache.IsID(fields[0]) {
		return "", 0, 0, errors.New("the entry doesn't start with an output ID and size")
	}
	size, err = strconv.ParseInt(fields[1], 10, 64)
	if err != nil {
		return "", 0, 0, err
	}
	fi, err := f.Stat()
	if err != nil {
		return "", 0, 0, err
	}
	offset = int64(len(line)) + 1
	if fi.Size() != offset+size {
		return "", 0, 0, fmt.Errorf("the entry has %d bytes, want %d", fi.Size(), offset+size)
	}
	return fields[0], size, offset, nil
}
