// Package fakegcs serves the part of the Cloud Storage JSON API that
// objstore uses (media get, conditional media upload, list, and delete)
// from a local directory. It can add latency and cap bandwidth the way
// cloudrun-sqlite's latproxy does, so measurements of the two services use
// the same model of Cloud Storage, and it counts requests by operation.
package fakegcs

import (
	"encoding/json/v2"
	"errors"
	"io"
	"math/rand/v2"
	"net/http"
	"path/filepath"
	"strconv"
	"sync"
	"sync/atomic"
	"time"

	"github.com/imjasonh/playground/cloudrun-duckdb/internal/objstore"
)

// Latency adds delay to each request. The zero value adds none.
type Latency struct {
	Get, List, Put, Delete time.Duration
	// Jitter is uniform jitter as a fraction of each latency.
	Jitter float64
	// Download and Upload cap each response or request body, in bytes per
	// second. Zero is unlimited.
	Download, Upload int64
}

// LatProxy is the model in cloudrun-sqlite's latproxy, plus the same cap on
// uploads, which matter more here because snapshots upload whole files.
var LatProxy = Latency{
	Get:      20 * time.Millisecond,
	List:     30 * time.Millisecond,
	Put:      50 * time.Millisecond,
	Delete:   20 * time.Millisecond,
	Jitter:   0.25,
	Download: 100 << 20,
	Upload:   100 << 20,
}

// Counts is how many requests of each kind the server answered. Cloud
// Storage bills creates and lists as Class A operations and gets as
// Class B. Deletes are free.
type Counts struct {
	Get      int64 `json:"get"`
	List     int64 `json:"list"`
	Create   int64 `json:"create"`
	Delete   int64 `json:"delete"`
	BytesIn  int64 `json:"bytes_in"`
	BytesOut int64 `json:"bytes_out"`
}

// Server is an http.Handler. Each bucket is a subdirectory of the root.
type Server struct {
	root    string
	latency Latency
	mux     *http.ServeMux

	mu      sync.Mutex
	buckets map[string]*objstore.File

	get, list, create, del, in, out atomic.Int64
}

// New returns a server for buckets under root.
func New(root string, latency Latency) *Server {
	s := &Server{root: root, latency: latency, buckets: map[string]*objstore.File{}}
	s.mux = http.NewServeMux()
	s.mux.HandleFunc("GET /storage/v1/b/{bucket}/o/{object...}", s.handleGet)
	s.mux.HandleFunc("GET /storage/v1/b/{bucket}/o", s.handleList)
	s.mux.HandleFunc("POST /upload/storage/v1/b/{bucket}/o", s.handleCreate)
	s.mux.HandleFunc("DELETE /storage/v1/b/{bucket}/o/{object...}", s.handleDelete)
	s.mux.HandleFunc("GET /_fakegcs/stats", func(w http.ResponseWriter, r *http.Request) {
		w.Header().Set("Content-Type", "application/json")
		json.MarshalWrite(w, s.Counts())
	})
	return s
}

// Counts returns the requests answered so far.
func (s *Server) Counts() Counts {
	return Counts{Get: s.get.Load(), List: s.list.Load(), Create: s.create.Load(), Delete: s.del.Load(), BytesIn: s.in.Load(), BytesOut: s.out.Load()}
}

func (s *Server) ServeHTTP(w http.ResponseWriter, r *http.Request) {
	s.mux.ServeHTTP(w, r)
}

func (s *Server) bucket(name string) (*objstore.File, error) {
	s.mu.Lock()
	defer s.mu.Unlock()
	if b, ok := s.buckets[name]; ok {
		return b, nil
	}
	if name == "" || name == "." || name == ".." || filepath.Base(name) != name {
		return nil, errors.New("bad bucket name")
	}
	b, err := objstore.NewFile(filepath.Join(s.root, name))
	if err != nil {
		return nil, err
	}
	s.buckets[name] = b
	return b, nil
}

func (s *Server) sleep(d time.Duration) {
	if d <= 0 {
		return
	}
	time.Sleep(time.Duration(float64(d) * (1 + s.latency.Jitter*(2*rand.Float64()-1))))
}

func (s *Server) handleGet(w http.ResponseWriter, r *http.Request) {
	s.get.Add(1)
	s.sleep(s.latency.Get)
	b, err := s.bucket(r.PathValue("bucket"))
	if err != nil {
		http.Error(w, err.Error(), http.StatusBadRequest)
		return
	}
	if r.URL.Query().Get("alt") != "media" {
		http.Error(w, "only alt=media is supported", http.StatusBadRequest)
		return
	}
	rc, err := b.Get(r.Context(), r.PathValue("object"))
	if errors.Is(err, objstore.ErrNotFound) {
		http.Error(w, "not found", http.StatusNotFound)
		return
	}
	if err != nil {
		http.Error(w, err.Error(), http.StatusInternalServerError)
		return
	}
	defer rc.Close()
	w.Header().Set("Content-Type", "application/octet-stream")
	n, _ := io.Copy(&paced{w: w, start: time.Now(), rate: s.latency.Download}, rc)
	s.out.Add(n)
}

type listItem struct {
	Name        string `json:"name"`
	Size        string `json:"size"`
	TimeCreated string `json:"timeCreated"`
}

func (s *Server) handleList(w http.ResponseWriter, r *http.Request) {
	s.list.Add(1)
	s.sleep(s.latency.List)
	b, err := s.bucket(r.PathValue("bucket"))
	if err != nil {
		http.Error(w, err.Error(), http.StatusBadRequest)
		return
	}
	q := r.URL.Query()
	all, err := b.List(r.Context(), q.Get("prefix"), q.Get("pageToken"))
	if err != nil {
		http.Error(w, err.Error(), http.StatusInternalServerError)
		return
	}
	// startOffset is inclusive.
	var objs []objstore.Object
	for _, o := range all {
		if o.Key >= q.Get("startOffset") {
			objs = append(objs, o)
		}
	}
	max := 1000
	if m, err := strconv.Atoi(q.Get("maxResults")); err == nil && m > 0 {
		max = m
	}
	page := struct {
		NextPageToken string     `json:"nextPageToken,omitempty"`
		Items         []listItem `json:"items,omitempty"`
	}{}
	for i, o := range objs {
		if i == max {
			page.NextPageToken = page.Items[len(page.Items)-1].Name
			break
		}
		page.Items = append(page.Items, listItem{Name: o.Key, Size: strconv.FormatInt(o.Size, 10), TimeCreated: o.Created.UTC().Format(time.RFC3339Nano)})
	}
	w.Header().Set("Content-Type", "application/json")
	json.MarshalWrite(w, page)
}

func (s *Server) handleCreate(w http.ResponseWriter, r *http.Request) {
	s.create.Add(1)
	s.sleep(s.latency.Put)
	b, err := s.bucket(r.PathValue("bucket"))
	if err != nil {
		http.Error(w, err.Error(), http.StatusBadRequest)
		return
	}
	q := r.URL.Query()
	if q.Get("uploadType") != "media" || q.Get("ifGenerationMatch") != "0" || q.Get("name") == "" {
		http.Error(w, "only conditional media uploads (ifGenerationMatch=0) are supported", http.StatusBadRequest)
		return
	}
	body := &pacedReader{r: r.Body, start: time.Now(), rate: s.latency.Upload}
	err = b.Create(r.Context(), q.Get("name"), body, r.ContentLength)
	s.in.Add(body.n)
	switch {
	case errors.Is(err, objstore.ErrExists):
		http.Error(w, "conditionNotMet", http.StatusPreconditionFailed)
	case err != nil:
		http.Error(w, err.Error(), http.StatusInternalServerError)
	default:
		w.Header().Set("Content-Type", "application/json")
		json.MarshalWrite(w, map[string]string{"name": q.Get("name")})
	}
}

func (s *Server) handleDelete(w http.ResponseWriter, r *http.Request) {
	s.del.Add(1)
	s.sleep(s.latency.Delete)
	b, err := s.bucket(r.PathValue("bucket"))
	if err != nil {
		http.Error(w, err.Error(), http.StatusBadRequest)
		return
	}
	if err := b.Delete(r.Context(), r.PathValue("object")); err != nil {
		http.Error(w, err.Error(), http.StatusInternalServerError)
		return
	}
	w.WriteHeader(http.StatusNoContent)
}

// paced writes no faster than rate bytes per second.
type paced struct {
	w     io.Writer
	start time.Time
	rate  int64
	n     int64
}

func (p *paced) Write(b []byte) (int, error) {
	n, err := p.w.Write(b)
	p.n += int64(n)
	if p.rate > 0 {
		if due := time.Duration(float64(p.n) / float64(p.rate) * float64(time.Second)); due > time.Since(p.start) {
			time.Sleep(due - time.Since(p.start))
		}
	}
	return n, err
}

// pacedReader reads no faster than rate bytes per second.
type pacedReader struct {
	r     io.Reader
	start time.Time
	rate  int64
	n     int64
}

func (p *pacedReader) Read(b []byte) (int, error) {
	n, err := p.r.Read(b)
	p.n += int64(n)
	if p.rate > 0 {
		if due := time.Duration(float64(p.n) / float64(p.rate) * float64(time.Second)); due > time.Since(p.start) {
			time.Sleep(due - time.Since(p.start))
		}
	}
	return n, err
}
