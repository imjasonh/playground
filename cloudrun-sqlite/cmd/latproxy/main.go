// Command latproxy is a reverse proxy for an S3-compatible server that adds
// per-request latency and caps download bandwidth, to approximate Cloud
// Storage or S3 as seen from Cloud Run in the same region.
//
//	latproxy -listen 127.0.0.1:9100 -target http://127.0.0.1:9000
package main

import (
	"flag"
	"math/rand/v2"
	"net/http"
	"net/http/httputil"
	"net/url"
	"sync/atomic"
	"time"

	"github.com/chainguard-dev/clog"
)

func main() {
	listen := flag.String("listen", "127.0.0.1:9100", "listen address")
	target := flag.String("target", "http://127.0.0.1:9000", "upstream server")
	get := flag.Duration("get", 20*time.Millisecond, "GET and HEAD latency")
	list := flag.Duration("list", 30*time.Millisecond, "LIST latency")
	put := flag.Duration("put", 50*time.Millisecond, "PUT and POST latency")
	del := flag.Duration("delete", 20*time.Millisecond, "DELETE latency")
	jitter := flag.Float64("jitter", 0.25, "uniform jitter, as a fraction of the latency")
	bw := flag.Int64("bw", 100<<20, "download bandwidth per response in bytes per second (0 is unlimited)")
	flag.Parse()

	u, err := url.Parse(*target)
	if err != nil {
		clog.Fatal("parse target", "error", err)
	}
	rp := httputil.NewSingleHostReverseProxy(u)
	var n atomic.Int64
	go func() {
		for range time.Tick(10 * time.Second) {
			clog.Info("requests", "count", n.Load())
		}
	}()
	clog.Fatal("serve", "error", http.ListenAndServe(*listen, http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		n.Add(1)
		d := *get
		switch {
		case r.Method == http.MethodPut || r.Method == http.MethodPost:
			d = *put
		case r.Method == http.MethodDelete:
			d = *del
		case r.URL.Query().Has("list-type") || r.URL.Query().Has("prefix"):
			d = *list
		}
		time.Sleep(time.Duration(float64(d) * (1 + *jitter*(2*rand.Float64()-1))))
		if *bw > 0 {
			w = &paced{ResponseWriter: w, start: time.Now(), rate: *bw}
		}
		rp.ServeHTTP(w, r)
	})))
}

// paced writes a response body no faster than rate bytes per second.
type paced struct {
	http.ResponseWriter
	start time.Time
	rate  int64
	n     int64
}

func (p *paced) Write(b []byte) (int, error) {
	n, err := p.ResponseWriter.Write(b)
	p.n += int64(n)
	if due := time.Duration(float64(p.n) / float64(p.rate) * float64(time.Second)); due > time.Since(p.start) {
		time.Sleep(due - time.Since(p.start))
	}
	return n, err
}

func (p *paced) Flush() {
	if f, ok := p.ResponseWriter.(http.Flusher); ok {
		f.Flush()
	}
}
