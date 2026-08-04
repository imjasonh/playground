// Command orchestrator places microVMs and runs cross-host migrate.
//
//	go run ./cmd/orchestrator \
//	  -listen 127.0.0.1:8090 \
//	  -hosts host-a=http://127.0.0.1:8080,host-b=http://127.0.0.1:8081
//
//	# GCE MIG: a timer rewrites -hosts-file; orchestrator reloads it.
//	go run ./cmd/orchestrator -hosts-file /var/lib/sshcloud/hosts
package main

import (
	"context"
	"encoding/json"
	"flag"
	"log"
	"net/http"
	"os"
	"os/signal"
	"syscall"
	"time"

	"github.com/imjasonh/playground/sshcloud/internal/backend"
	"github.com/imjasonh/playground/sshcloud/internal/migrate"
	"github.com/imjasonh/playground/sshcloud/internal/placement"
)

func main() {
	listen := flag.String("listen", "127.0.0.1:8090", "HTTP listen address")
	hostsFlag := flag.String("hosts", "", "comma-separated hostID=baseURL pairs")
	hostsFile := flag.String("hosts-file", "", "hosts file (id=url per line); reloaded every 30s")
	defaultHost := flag.String("default-host", "", "default placement host ID")
	firestoreProject := flag.String("firestore-project", "", "GCP project for Firestore placement (default: in-memory)")
	flag.Parse()

	initial, err := backend.ParseHostsSpec(*hostsFlag)
	if err != nil {
		log.Fatal(err)
	}
	if *hostsFile != "" {
		fromFile, err := backend.LoadHostsFile(*hostsFile)
		if err != nil {
			if len(initial) == 0 && !os.IsNotExist(err) {
				log.Fatalf("hosts-file: %v", err)
			}
			log.Printf("hosts-file: %v (starting with -hosts / empty)", err)
		} else {
			initial = fromFile
		}
	}
	if len(initial) == 0 && *hostsFile == "" {
		log.Fatal("-hosts or -hosts-file is required")
	}

	ctx, stop := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
	defer stop()

	var place placement.Store = placement.NewMemory()
	if *firestoreProject != "" {
		fs, err := placement.NewFirestore(ctx, *firestoreProject)
		if err != nil {
			log.Fatalf("firestore: %v", err)
		}
		defer fs.Close()
		place = fs
		log.Printf("placement: firestore project %s", *firestoreProject)
	} else {
		log.Printf("placement: in-memory")
	}

	hosts := backend.NewHostSet(initial, *defaultHost)
	mig := &migrate.Migrator{Placement: place, Hosts: hosts}
	dial := &backend.PlacedDial{Placement: place, Agents: hosts, DefaultHost: *defaultHost}

	if *hostsFile != "" {
		go watchHostsFile(ctx, *hostsFile, hosts)
	}

	mux := http.NewServeMux()
	mux.HandleFunc("GET /healthz", func(w http.ResponseWriter, _ *http.Request) {
		w.WriteHeader(http.StatusOK)
		_, _ = w.Write([]byte("ok"))
	})
	mux.HandleFunc("GET /v1/hosts", func(w http.ResponseWriter, _ *http.Request) {
		w.Header().Set("Content-Type", "application/json")
		_ = json.NewEncoder(w).Encode(map[string]any{
			"hosts":   hosts.IDs(),
			"default": hosts.DefaultHost(),
		})
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
		log.Printf("sshcloud orchestrator on %s (hosts=%v default=%s)", *listen, hosts.IDs(), hosts.DefaultHost())
		if err := srv.ListenAndServe(); err != nil && err != http.ErrServerClosed {
			log.Fatal(err)
		}
	}()

	<-ctx.Done()
	_ = srv.Close()
}

func watchHostsFile(ctx context.Context, path string, hosts *backend.HostSet) {
	tick := time.NewTicker(30 * time.Second)
	defer tick.Stop()
	for {
		select {
		case <-ctx.Done():
			return
		case <-tick.C:
			m, err := backend.LoadHostsFile(path)
			if err != nil {
				log.Printf("hosts-file reload: %v", err)
				continue
			}
			if len(m) == 0 {
				log.Printf("hosts-file reload: empty, keeping previous")
				continue
			}
			hosts.Replace(m)
			log.Printf("hosts-file reload: %v", hosts.IDs())
		}
	}
}
