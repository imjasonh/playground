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
	"fmt"
	"io"
	"log"
	"net/http"
	"os"
	"os/signal"
	"strings"
	"syscall"
	"time"

	"github.com/imjasonh/playground/sshcloud/internal/backend"
	"github.com/imjasonh/playground/sshcloud/internal/controlauth"
	"github.com/imjasonh/playground/sshcloud/internal/genid"
	"github.com/imjasonh/playground/sshcloud/internal/image"
	"github.com/imjasonh/playground/sshcloud/internal/migrate"
	"github.com/imjasonh/playground/sshcloud/internal/names"
	"github.com/imjasonh/playground/sshcloud/internal/placement"
)

func main() {
	listen := flag.String("listen", "127.0.0.1:8090", "HTTP listen address")
	hostsFlag := flag.String("hosts", "", "comma-separated hostID=baseURL pairs")
	hostsFile := flag.String("hosts-file", "", "hosts file (id=url per line); reloaded every 30s")
	defaultHost := flag.String("default-host", "", "default placement host ID")
	firestoreProject := flag.String("firestore-project", "", "GCP project for Firestore placement (default: in-memory)")
	controlTokenFile := flag.String("control-token-file", "", "bearer token file required by orchestrator APIs (empty is local-dev only)")
	agentTokenFile := flag.String("agent-token-file", "", "bearer token file sent to host agents")
	flag.Parse()

	controlToken, err := controlauth.LoadFile(*controlTokenFile)
	if err != nil {
		log.Fatalf("control token: %v", err)
	}
	agentToken, err := controlauth.LoadFile(*agentTokenFile)
	if err != nil {
		log.Fatalf("agent token: %v", err)
	}
	if controlToken == "" || agentToken == "" {
		log.Printf("WARNING: internal API authentication is incomplete")
	}

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
	setAgentToken(initial, agentToken)
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
		go watchHostsFile(ctx, *hostsFile, hosts, agentToken)
	}

	mux := http.NewServeMux()
	api := http.NewServeMux()
	mux.HandleFunc("GET /healthz", func(w http.ResponseWriter, _ *http.Request) {
		w.WriteHeader(http.StatusOK)
		_, _ = w.Write([]byte("ok"))
	})
	api.HandleFunc("GET /v1/hosts", func(w http.ResponseWriter, _ *http.Request) {
		w.Header().Set("Content-Type", "application/json")
		_ = json.NewEncoder(w).Encode(map[string]any{
			"hosts":   hosts.IDs(),
			"default": hosts.DefaultHost(),
		})
	})
	api.HandleFunc("POST /v1/migrate", func(w http.ResponseWriter, r *http.Request) {
		var req struct {
			User string `json:"user"`
			App  string `json:"app"`
			Gen  string `json:"gen"`
			To   string `json:"to"`
		}
		if !decodeJSON(w, r, &req) {
			return
		}
		if err := validateIdentity(req.User, req.App, req.Gen); err != nil {
			http.Error(w, err.Error(), http.StatusBadRequest)
			return
		}
		res, err := mig.MigrateGeneration(r.Context(), req.User, req.App, req.Gen, req.To)
		if err != nil {
			http.Error(w, err.Error(), http.StatusConflict)
			return
		}
		w.Header().Set("Content-Type", "application/json")
		_ = json.NewEncoder(w).Encode(res)
	})
	api.HandleFunc("POST /v1/ensure", func(w http.ResponseWriter, r *http.Request) {
		var req struct {
			User   string `json:"user"`
			App    string `json:"app"`
			Gen    string `json:"gen"`
			Image  string `json:"image"`
			Tier   string `json:"tier"`
			NoIdle bool   `json:"no_idle"`
		}
		if !decodeJSON(w, r, &req) {
			return
		}
		if err := validateIdentity(req.User, req.App, req.Gen); err != nil {
			http.Error(w, err.Error(), http.StatusBadRequest)
			return
		}
		if req.Image = strings.TrimSpace(req.Image); req.Image != "" {
			if err := image.ValidateDigestPinned(req.Image); err != nil {
				http.Error(w, err.Error(), http.StatusBadRequest)
				return
			}
		}
		if req.Tier != "" && req.Tier != "tiny" && req.Tier != "small" {
			http.Error(w, "tier must be tiny or small", http.StatusBadRequest)
			return
		}
		addr, err := dial.EnsureAddrTier(r.Context(), req.User, req.App, req.Gen, req.Image, req.Tier, req.NoIdle)
		if err != nil {
			http.Error(w, err.Error(), http.StatusInternalServerError)
			return
		}
		w.Header().Set("Content-Type", "application/json")
		_ = json.NewEncoder(w).Encode(map[string]string{"addr": addr})
	})
	api.HandleFunc("POST /v1/stop", func(w http.ResponseWriter, r *http.Request) {
		var req struct {
			User string `json:"user"`
			App  string `json:"app"`
			Gen  string `json:"gen"`
		}
		if !decodeJSON(w, r, &req) {
			return
		}
		if err := validateIdentity(req.User, req.App, req.Gen); err != nil {
			http.Error(w, err.Error(), http.StatusBadRequest)
			return
		}
		if err := dial.Stop(r.Context(), req.User, req.App, req.Gen); err != nil {
			http.Error(w, err.Error(), http.StatusInternalServerError)
			return
		}
		w.WriteHeader(http.StatusNoContent)
	})
	api.HandleFunc("POST /v1/no-idle", func(w http.ResponseWriter, r *http.Request) {
		var req struct {
			User   string `json:"user"`
			App    string `json:"app"`
			Gen    string `json:"gen"`
			NoIdle bool   `json:"no_idle"`
		}
		if !decodeJSON(w, r, &req) {
			return
		}
		if err := validateIdentity(req.User, req.App, req.Gen); err != nil {
			http.Error(w, err.Error(), http.StatusBadRequest)
			return
		}
		if err := dial.SetNoIdle(r.Context(), req.User, req.App, req.Gen, req.NoIdle); err != nil {
			http.Error(w, err.Error(), http.StatusInternalServerError)
			return
		}
		w.WriteHeader(http.StatusNoContent)
	})
	api.HandleFunc("GET /v1/placement", func(w http.ResponseWriter, r *http.Request) {
		user := r.URL.Query().Get("user")
		app := r.URL.Query().Get("app")
		if err := validateIdentity(user, app, ""); err != nil {
			http.Error(w, err.Error(), http.StatusBadRequest)
			return
		}
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
	mux.Handle("/v1/", controlauth.Require(controlToken, api))

	srv := &http.Server{
		Addr:              *listen,
		Handler:           mux,
		ReadHeaderTimeout: 10 * time.Second,
		ReadTimeout:       30 * time.Second,
		WriteTimeout:      7 * time.Minute,
		IdleTimeout:       60 * time.Second,
	}
	go func() {
		log.Printf("sshcloud orchestrator on %s (hosts=%v default=%s)", *listen, hosts.IDs(), hosts.DefaultHost())
		if err := srv.ListenAndServe(); err != nil && err != http.ErrServerClosed {
			log.Fatal(err)
		}
	}()

	<-ctx.Done()
	_ = srv.Close()
}

func watchHostsFile(ctx context.Context, path string, hosts *backend.HostSet, agentToken string) {
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
			setAgentToken(m, agentToken)
			hosts.Replace(m)
			log.Printf("hosts-file reload: %v", hosts.IDs())
		}
	}
}

func setAgentToken(hosts map[string]*backend.AgentClient, token string) {
	for _, client := range hosts {
		client.Token = token
	}
}

func validateIdentity(user, app, gen string) error {
	if err := names.ValidateIdent(user); err != nil {
		return fmt.Errorf("invalid user: %w", err)
	}
	if err := names.ValidateIdent(app); err != nil {
		return fmt.Errorf("invalid app: %w", err)
	}
	if gen != "" {
		if err := genid.Validate(gen); err != nil {
			return err
		}
	}
	return nil
}

func decodeJSON(w http.ResponseWriter, r *http.Request, dst any) bool {
	r.Body = http.MaxBytesReader(w, r.Body, 8<<10)
	dec := json.NewDecoder(r.Body)
	dec.DisallowUnknownFields()
	if err := dec.Decode(dst); err != nil {
		http.Error(w, "invalid JSON: "+err.Error(), http.StatusBadRequest)
		return false
	}
	if err := dec.Decode(&struct{}{}); err != io.EOF {
		http.Error(w, "request body must contain one JSON object", http.StatusBadRequest)
		return false
	}
	return true
}
