// Command orchestrator places microVMs and runs cross-host migrate.
//
//	go run ./cmd/orchestrator \
//	  -listen 127.0.0.1:8090 \
//	  -hosts host-a=http://127.0.0.1:8080,host-b=http://127.0.0.1:8081
package main

import (
	"context"
	"encoding/json"
	"flag"
	"fmt"
	"log"
	"net/http"
	"os"
	"os/signal"
	"strings"
	"syscall"
	"time"

	"github.com/imjasonh/playground/sshcloud/internal/backend"
	"github.com/imjasonh/playground/sshcloud/internal/migrate"
	"github.com/imjasonh/playground/sshcloud/internal/placement"
)

func main() {
	listen := flag.String("listen", "127.0.0.1:8090", "HTTP listen address")
	hostsFlag := flag.String("hosts", "", "comma-separated hostID=baseURL pairs")
	defaultHost := flag.String("default-host", "", "default placement host ID")
	flag.Parse()

	hosts, err := parseHosts(*hostsFlag)
	if err != nil {
		log.Fatal(err)
	}
	if len(hosts) == 0 {
		log.Fatal("-hosts is required (e.g. a=http://127.0.0.1:8080,b=http://127.0.0.1:8081)")
	}
	if *defaultHost == "" {
		for id := range hosts {
			*defaultHost = id
			break
		}
	}

	place := placement.NewMemory()
	mig := &migrate.Migrator{Placement: place, Hosts: hosts}
	dial := &backend.PlacedDial{Placement: place, Agents: hosts, DefaultHost: *defaultHost}

	mux := http.NewServeMux()
	mux.HandleFunc("GET /healthz", func(w http.ResponseWriter, _ *http.Request) {
		w.WriteHeader(http.StatusOK)
		_, _ = w.Write([]byte("ok"))
	})
	mux.HandleFunc("POST /v1/migrate", func(w http.ResponseWriter, r *http.Request) {
		var req struct {
			User string `json:"user"`
			App  string `json:"app"`
			To   string `json:"to"`
		}
		if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
			http.Error(w, err.Error(), http.StatusBadRequest)
			return
		}
		res, err := mig.Migrate(r.Context(), req.User, req.App, req.To)
		if err != nil {
			http.Error(w, err.Error(), http.StatusConflict)
			return
		}
		w.Header().Set("Content-Type", "application/json")
		_ = json.NewEncoder(w).Encode(res)
	})
	mux.HandleFunc("POST /v1/ensure", func(w http.ResponseWriter, r *http.Request) {
		var req struct {
			User string `json:"user"`
			App  string `json:"app"`
		}
		if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
			http.Error(w, err.Error(), http.StatusBadRequest)
			return
		}
		addr, err := dial.Addr(req.User, req.App)
		if err != nil {
			http.Error(w, err.Error(), http.StatusInternalServerError)
			return
		}
		w.Header().Set("Content-Type", "application/json")
		_ = json.NewEncoder(w).Encode(map[string]string{"addr": addr})
	})
	mux.HandleFunc("GET /v1/placement", func(w http.ResponseWriter, r *http.Request) {
		user := r.URL.Query().Get("user")
		app := r.URL.Query().Get("app")
		host, ok, err := place.Get(r.Context(), user, app)
		if err != nil {
			http.Error(w, err.Error(), http.StatusInternalServerError)
			return
		}
		if !ok {
			http.Error(w, "not found", http.StatusNotFound)
			return
		}
		w.Header().Set("Content-Type", "application/json")
		_ = json.NewEncoder(w).Encode(map[string]string{"user": user, "app": app, "host": host})
	})

	srv := &http.Server{Addr: *listen, Handler: mux, ReadHeaderTimeout: 10 * time.Second}
	go func() {
		log.Printf("sshcloud orchestrator on %s (hosts=%v default=%s)", *listen, hostIDs(hosts), *defaultHost)
		if err := srv.ListenAndServe(); err != nil && err != http.ErrServerClosed {
			log.Fatal(err)
		}
	}()

	ctx, stop := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
	defer stop()
	<-ctx.Done()
	_ = srv.Close()
}

func parseHosts(s string) (migrate.Hosts, error) {
	out := make(migrate.Hosts)
	s = strings.TrimSpace(s)
	if s == "" {
		return out, nil
	}
	for _, part := range strings.Split(s, ",") {
		part = strings.TrimSpace(part)
		if part == "" {
			continue
		}
		id, url, ok := strings.Cut(part, "=")
		if !ok || id == "" || url == "" {
			return nil, fmt.Errorf("invalid -hosts entry %q (want id=url)", part)
		}
		out[id] = &backend.AgentClient{BaseURL: strings.TrimRight(url, "/")}
	}
	return out, nil
}

func hostIDs(h migrate.Hosts) []string {
	ids := make([]string, 0, len(h))
	for id := range h {
		ids = append(ids, id)
	}
	return ids
}
