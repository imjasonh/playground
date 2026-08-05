// Command orchestrator places microVMs and runs cross-host migrate.
//
//	go run ./cmd/orchestrator \
//	  -control-insecure-loopback \
//	  -listen 127.0.0.1:8090 \
//	  -admin-socket /tmp/sshcloud-orchestrator-admin.sock \
//	  -hosts host-a=http://127.0.0.1:8080,host-b=http://127.0.0.1:8081
//
//	# GCE MIG: a timer rewrites -hosts-file; orchestrator reloads it.
//	go run ./cmd/orchestrator -hosts-file /var/lib/sshcloud/hosts
package main

import (
	"context"
	"crypto/tls"
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	"io"
	"log"
	"net"
	"net/http"
	"os"
	"os/signal"
	"path/filepath"
	"strings"
	"syscall"
	"time"

	"github.com/imjasonh/playground/sshcloud/internal/agent"
	"github.com/imjasonh/playground/sshcloud/internal/backend"
	"github.com/imjasonh/playground/sshcloud/internal/controlauth"
	"github.com/imjasonh/playground/sshcloud/internal/drain"
	"github.com/imjasonh/playground/sshcloud/internal/genid"
	"github.com/imjasonh/playground/sshcloud/internal/image"
	"github.com/imjasonh/playground/sshcloud/internal/migrate"
	"github.com/imjasonh/playground/sshcloud/internal/names"
	"github.com/imjasonh/playground/sshcloud/internal/observability"
	"github.com/imjasonh/playground/sshcloud/internal/placement"
	"github.com/imjasonh/playground/sshcloud/internal/quota"
	hostreconcile "github.com/imjasonh/playground/sshcloud/internal/reconcile"
)

func main() {
	observability.Configure("orchestrator")
	listen := flag.String("listen", "127.0.0.1:8090", "gateway-service HTTPS listen address")
	healthListen := flag.String("health-listen", "127.0.0.1:8091", "unauthenticated health-only HTTP listen address")
	adminSocket := flag.String("admin-socket", "", "root-owned Unix socket for the admin HTTPS API")
	hostsFlag := flag.String("hosts", "", "comma-separated hostID[@instance-id]=baseURL pairs")
	hostsFile := flag.String("hosts-file", "", "hosts file (name@instance-id=url per line in production); reloaded every 30s")
	defaultHost := flag.String("default-host", "", "default placement host ID")
	firestoreProject := flag.String("firestore-project", "", "GCP project for Firestore placement (default: in-memory)")
	firestorePrefix := flag.String("firestore-prefix", "sshcloud", "Firestore collection prefix")
	firestoreDatabase := flag.String("firestore-database", "sshcloud", "Firestore database ID")
	controlCert := flag.String("control-cert", "", "reloadable orchestrator control certificate PEM")
	controlKey := flag.String("control-key", "", "reloadable orchestrator control private-key PEM")
	controlCACurrent := flag.String("control-ca-current", "", "reloadable current control CA PEM")
	controlCAPrevious := flag.String("control-ca-previous", "", "reloadable previous control CA PEM")
	controlProjectID := flag.String("control-project-id", "", "expected GCE identity-token project ID")
	controlProjectNumber := flag.String("control-project-number", "", "expected GCE identity-token project number")
	gatewayServiceAccount := flag.String("gateway-service-account", "", "exact gateway service-account email")
	orchestratorServiceAccount := flag.String("orchestrator-service-account", "", "exact orchestrator service-account email")
	insecureControl := flag.Bool("control-insecure-loopback", false, "explicitly allow unauthenticated plaintext control traffic on loopback only")
	gatewayURL := flag.String("gateway-url", "", "gateway migration control base URL")
	freezeTimeout := flag.Duration("freeze-timeout", 30*time.Second, "maximum outer-session freeze before forced reconnect")
	maxAwakePerUser := flag.Int("max-awake-per-user", 2, "maximum running VMs per user (deploy gets one temporary burst)")
	wakesPerHour := flag.Int("wakes-per-hour", 30, "wake/start admissions per user per hour")
	flag.Parse()

	controlFiles := controlauth.TLSFiles{
		CertFile: *controlCert, KeyFile: *controlKey,
		CurrentCAFile: *controlCACurrent, PreviousCAFile: *controlCAPrevious,
	}
	if *insecureControl {
		if err := controlauth.ValidateLoopbackListen(*listen); err != nil {
			log.Fatal(err)
		}
		log.Printf("WARNING: orchestrator control uses explicit loopback-only insecure mode")
	} else {
		if *controlProjectID == "" || *controlProjectNumber == "" ||
			*gatewayServiceAccount == "" || *orchestratorServiceAccount == "" {
			log.Fatal("production control requires project identity and exact gateway/orchestrator service accounts")
		}
		if *adminSocket == "" {
			log.Fatal("production control requires -admin-socket")
		}
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
	var agentControlClient *controlauth.Client
	if !*insecureControl {
		agentControlClient, err = controlauth.NewClient(
			controlFiles, controlauth.RoleOrchestrator, controlauth.RoleAgent,
			controlauth.MetadataTokenSource{}, controlauth.AudienceAgent, 20*time.Minute,
		)
		if err != nil {
			log.Fatalf("agent control client: %v", err)
		}
	}
	configureAgentClients(initial, agentControlClient, *insecureControl)
	if !*insecureControl {
		if err := requireHostInstanceIDs(initial); err != nil {
			log.Fatal(err)
		}
	}
	if len(initial) == 0 && *hostsFile == "" {
		log.Fatal("-hosts or -hosts-file is required")
	}

	ctx, stop := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
	defer stop()

	var place placement.Store = placement.NewMemory()
	var quotaStore quota.Store = quota.NewMemory()
	if *firestoreProject != "" {
		fs, err := placement.NewFirestoreDatabase(ctx, *firestoreProject, *firestoreDatabase, *firestorePrefix)
		if err != nil {
			log.Fatalf("firestore: %v", err)
		}
		defer fs.Close()
		place = fs
		quotaStore, err = quota.NewFirestoreDatabase(ctx, *firestoreProject, *firestoreDatabase, *firestorePrefix)
		if err != nil {
			log.Fatalf("quota firestore: %v", err)
		}
		defer quotaStore.Close()
		log.Printf("placement: firestore project %s", *firestoreProject)
	} else {
		log.Printf("placement: in-memory")
	}

	hosts := backend.NewHostSet(initial, *defaultHost)
	mig := &migrate.Migrator{Placement: place, Hosts: hosts}
	dial := &backend.PlacedDial{
		Placement: place, Agents: hosts,
		Quotas: quotaStore, MaxAwakePerUser: *maxAwakePerUser, WakesPerHour: *wakesPerHour,
	}
	var gatewayClient *backend.GatewayClient
	if *gatewayURL != "" {
		gatewayClient = &backend.GatewayClient{
			BaseURL: *gatewayURL, InsecureLoopback: *insecureControl,
		}
		if !*insecureControl {
			client, err := controlauth.NewClient(
				controlFiles, controlauth.RoleOrchestrator, controlauth.RoleGateway,
				controlauth.MetadataTokenSource{}, controlauth.AudienceGatewayMigration, 45*time.Second,
			)
			if err != nil {
				log.Fatalf("gateway control client: %v", err)
			}
			gatewayClient.ControlClient = client
		}
	}
	mig.Gateway = gatewayClient
	mig.FreezeWindow = *freezeTimeout
	drainer := &drain.Controller{
		Placement: place, Hosts: hosts, Gateway: gatewayClient, FreezeWindow: *freezeTimeout,
	}

	if *hostsFile != "" {
		go watchHostsFile(ctx, *hostsFile, hosts, agentControlClient, *insecureControl)
	}
	go reconcilePlacementLeases(ctx, place, hosts)

	healthMux := http.NewServeMux()
	api := http.NewServeMux()
	healthMux.HandleFunc("GET /livez", func(w http.ResponseWriter, _ *http.Request) {
		w.WriteHeader(http.StatusOK)
		_, _ = w.Write([]byte("ok"))
	})
	ready := func(w http.ResponseWriter, r *http.Request) {
		if hosts.Len() == 0 {
			http.Error(w, "unavailable", http.StatusServiceUnavailable)
			return
		}
		if _, err := place.ListRecords(r.Context()); err != nil {
			http.Error(w, "unavailable", http.StatusServiceUnavailable)
			return
		}
		if _, err := hosts.Candidates(r.Context(), "tiny", nil); err != nil {
			http.Error(w, "unavailable", http.StatusServiceUnavailable)
			return
		}
		w.WriteHeader(http.StatusOK)
		_, _ = w.Write([]byte("ok"))
	}
	healthMux.HandleFunc("GET /readyz", ready)
	healthMux.HandleFunc("GET /healthz", ready)
	healthMux.Handle("GET /metrics", observability.MetricsHandler())
	api.HandleFunc("GET /v1/hosts", func(w http.ResponseWriter, r *http.Request) {
		type hostView struct {
			ID       string         `json:"id"`
			Capacity agent.Capacity `json:"capacity"`
			Error    string         `json:"error,omitempty"`
		}
		var views []hostView
		for _, id := range hosts.IDs() {
			client, _ := hosts.Get(id)
			capacity, err := client.Capacity(r.Context())
			view := hostView{ID: id, Capacity: capacity}
			if err != nil {
				view.Error = err.Error()
			}
			views = append(views, view)
		}
		w.Header().Set("Content-Type", "application/json")
		_ = json.NewEncoder(w).Encode(map[string]any{
			"hosts":   views,
			"default": hosts.DefaultHost(),
		})
	})
	api.HandleFunc("POST /v1/hosts/cordon", func(w http.ResponseWriter, r *http.Request) {
		var req struct {
			Host        string `json:"host"`
			Cordoned    *bool  `json:"cordoned"`
			CordonEpoch string `json:"cordon_epoch"`
		}
		if !decodeJSON(w, r, &req) {
			return
		}
		client, ok := hosts.Get(req.Host)
		if !ok {
			http.Error(w, "unknown host", http.StatusNotFound)
			return
		}
		cordoned := true
		if req.Cordoned != nil {
			cordoned = *req.Cordoned
		}
		var err error
		if cordoned {
			var epoch string
			epoch, err = client.Cordon(r.Context())
			if err == nil {
				w.Header().Set("Content-Type", "application/json")
				_ = json.NewEncoder(w).Encode(map[string]string{"cordon_epoch": epoch})
				return
			}
		} else {
			err = client.Uncordon(r.Context(), req.CordonEpoch)
		}
		if err != nil {
			http.Error(w, err.Error(), http.StatusBadGateway)
			return
		}
		w.WriteHeader(http.StatusNoContent)
	})
	api.HandleFunc("POST /v1/hosts/drain", func(w http.ResponseWriter, r *http.Request) {
		var req struct {
			Host string `json:"host"`
		}
		if !decodeJSON(w, r, &req) {
			return
		}
		result, err := drainer.DrainHost(r.Context(), req.Host)
		if err != nil {
			http.Error(w, err.Error(), http.StatusConflict)
			return
		}
		w.Header().Set("Content-Type", "application/json")
		_ = json.NewEncoder(w).Encode(result)
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
			User      string `json:"user"`
			App       string `json:"app"`
			Gen       string `json:"gen"`
			Image     string `json:"image"`
			Tier      string `json:"tier"`
			NoIdle    bool   `json:"no_idle"`
			Purpose   string `json:"purpose"`
			RequestID string `json:"request_id"`
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
		if req.Purpose == "" {
			req.Purpose = "session"
		}
		addr, err := dial.EnsureAddrTierWithOptions(
			r.Context(), req.User, req.App, req.Gen, req.Image, req.Tier, req.NoIdle,
			backend.StartOptions{Purpose: req.Purpose, RequestID: req.RequestID},
		)
		if err != nil {
			writeControlError(w, err)
			return
		}
		view, found, err := dial.StatusView(r.Context(), req.User, req.App, req.Gen)
		if err != nil || !found || view.SSHHostPublicKey == "" {
			if err == nil {
				err = fmt.Errorf("ensured generation has no SSH host identity")
			}
			writeControlError(w, err)
			return
		}
		w.Header().Set("Content-Type", "application/json")
		_ = json.NewEncoder(w).Encode(map[string]string{
			"addr": addr, "ssh_host_public_key": view.SSHHostPublicKey,
		})
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
			writeControlError(w, err)
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
			writeControlError(w, err)
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
		record, ok, err := place.GetRecord(r.Context(), user, app)
		if err != nil {
			http.Error(w, err.Error(), http.StatusInternalServerError)
			return
		}
		if !ok {
			http.Error(w, "not found", http.StatusNotFound)
			return
		}
		w.Header().Set("Content-Type", "application/json")
		_ = json.NewEncoder(w).Encode(record)
	})
	api.HandleFunc("GET /v1/placements", func(w http.ResponseWriter, r *http.Request) {
		records, err := place.ListRecords(r.Context())
		if err != nil {
			http.Error(w, err.Error(), http.StatusInternalServerError)
			return
		}
		w.Header().Set("Content-Type", "application/json")
		_ = json.NewEncoder(w).Encode(map[string]any{"placements": records})
	})
	api.HandleFunc("GET /v1/diagnostics", func(w http.ResponseWriter, r *http.Request) {
		records, err := place.ListRecords(r.Context())
		if err != nil {
			http.Error(w, err.Error(), http.StatusInternalServerError)
			return
		}
		hostDiagnostics := hosts.Diagnostics(r.Context())
		placementTotal := len(records)
		if len(records) > maxDiagnosticPlacements {
			records = records[:maxDiagnosticPlacements]
		}
		hostTotal := len(hostDiagnostics)
		instanceTotal := 0
		for _, diagnostic := range hostDiagnostics {
			instanceTotal += len(diagnostic.Instances)
		}
		if len(hostDiagnostics) > maxDiagnosticHosts {
			hostDiagnostics = hostDiagnostics[:maxDiagnosticHosts]
		}
		instanceReturned := 0
		for index := range hostDiagnostics {
			if len(hostDiagnostics[index].Instances) > maxDiagnosticInstancesPerHost {
				hostDiagnostics[index].Instances = hostDiagnostics[index].Instances[:maxDiagnosticInstancesPerHost]
			}
			instanceReturned += len(hostDiagnostics[index].Instances)
			hostDiagnostics[index].Error = boundedDiagnosticText(hostDiagnostics[index].Error)
		}
		w.Header().Set("Content-Type", "application/json")
		_ = json.NewEncoder(w).Encode(map[string]any{
			"placements": records, "hosts": hostDiagnostics,
			"bounds": map[string]int{
				"placements_total": placementTotal, "placements_returned": len(records),
				"hosts_total": hostTotal, "hosts_returned": len(hostDiagnostics),
				"instances_total": instanceTotal, "instances_returned": instanceReturned,
			},
		})
	})

	gatewayHandler := gatewayServiceRoutes(api)
	adminHandler := adminRoutes(api)
	var serverTLS *tls.Config
	if !*insecureControl {
		verifier := &controlauth.GCEVerifier{
			ProjectID: *controlProjectID, ProjectNumber: *controlProjectNumber,
		}
		gatewayHandler = controlauth.Require(verifier, controlauth.VerificationPolicy{
			CallerRole: controlauth.RoleGateway, ServiceAccount: *gatewayServiceAccount,
			Audience: controlauth.AudienceOrchestratorGateway,
		}, gatewayHandler)
		adminHandler = controlauth.Require(verifier, controlauth.VerificationPolicy{
			CallerRole: controlauth.RoleOrchestrator, ServiceAccount: *orchestratorServiceAccount,
			Audience: controlauth.AudienceOrchestratorAdmin,
		}, adminHandler)
		serverTLS, err = controlauth.ServerTLSConfig(controlFiles, controlauth.RoleOrchestrator)
		if err != nil {
			log.Fatalf("orchestrator control TLS: %v", err)
		}
	}

	gatewayServer := &http.Server{
		Addr:              *listen,
		Handler:           gatewayHandler,
		ReadHeaderTimeout: 10 * time.Second,
		ReadTimeout:       30 * time.Second,
		WriteTimeout:      35 * time.Minute,
		IdleTimeout:       60 * time.Second,
	}
	gatewayListener, err := net.Listen("tcp", *listen)
	if err != nil {
		log.Fatalf("orchestrator gateway-service listen: %v", err)
	}
	if serverTLS != nil {
		gatewayListener = tls.NewListener(gatewayListener, serverTLS)
	}
	go func() {
		log.Printf("sshcloud orchestrator gateway service on %s (hosts=%v default=%s)", *listen, hosts.IDs(), hosts.DefaultHost())
		if err := gatewayServer.Serve(gatewayListener); err != nil && err != http.ErrServerClosed {
			log.Fatal(err)
		}
	}()

	var adminServer *http.Server
	if *adminSocket != "" {
		adminListener, err := listenAdminSocket(*adminSocket, !*insecureControl)
		if err != nil {
			log.Fatalf("orchestrator admin socket: %v", err)
		}
		if serverTLS != nil {
			adminListener = tls.NewListener(adminListener, serverTLS)
		}
		adminServer = &http.Server{
			Handler:           adminHandler,
			ReadHeaderTimeout: 10 * time.Second, ReadTimeout: 30 * time.Second,
			WriteTimeout: 35 * time.Minute, IdleTimeout: 60 * time.Second,
		}
		go func() {
			log.Printf("sshcloud orchestrator admin service on unix://%s", *adminSocket)
			if err := adminServer.Serve(adminListener); err != nil && err != http.ErrServerClosed {
				log.Fatal(err)
			}
		}()
	}

	var healthServer *http.Server
	if *healthListen != "" {
		healthServer = &http.Server{
			Addr: *healthListen, Handler: healthMux,
			ReadHeaderTimeout: 5 * time.Second, ReadTimeout: 5 * time.Second,
			WriteTimeout: 5 * time.Second, IdleTimeout: 30 * time.Second,
		}
		go func() {
			log.Printf("sshcloud orchestrator health HTTP on %s", *healthListen)
			if err := healthServer.ListenAndServe(); err != nil && err != http.ErrServerClosed {
				log.Fatal(err)
			}
		}()
	}

	<-ctx.Done()
	_ = gatewayServer.Close()
	if adminServer != nil {
		_ = adminServer.Close()
		_ = os.Remove(*adminSocket)
	}
	if healthServer != nil {
		_ = healthServer.Close()
	}
}

const (
	maxDiagnosticPlacements       = 200
	maxDiagnosticHosts            = 100
	maxDiagnosticInstancesPerHost = 100
	maxDiagnosticErrorBytes       = 512
)

func boundedDiagnosticText(value string) string {
	if len(value) <= maxDiagnosticErrorBytes {
		return value
	}
	return value[:maxDiagnosticErrorBytes]
}

func watchHostsFile(ctx context.Context, path string, hosts *backend.HostSet, controlClient *controlauth.Client, insecureLoopback bool) {
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
			configureAgentClients(m, controlClient, insecureLoopback)
			if !insecureLoopback {
				if err := requireHostInstanceIDs(m); err != nil {
					log.Printf("hosts-file reload: %v", err)
					continue
				}
			}
			hosts.Replace(m)
			log.Printf("hosts-file reload: %v", hosts.IDs())
		}
	}
}

func reconcilePlacementLeases(ctx context.Context, store placement.Store, hosts *backend.HostSet) {
	ticker := time.NewTicker(30 * time.Second)
	defer ticker.Stop()
	reconciler := &hostreconcile.Controller{Placement: store, Hosts: hosts}
	for {
		if err := reconciler.RunOnce(ctx); err != nil && ctx.Err() == nil {
			log.Printf("placement operation reconcile: %v", err)
		}
		records, err := store.ListRecords(ctx)
		if err != nil {
			log.Printf("placement reconcile: %v", err)
		} else {
			now := time.Now()
			for _, record := range records {
				if record.Operation.Kind == "" && record.LeaseOwner != "" && record.LeaseUntilUnix <= now.UnixNano() {
					lease, err := store.Acquire(ctx, record.User, record.App, placement.NewLeaseOwner("reconcile"), placement.DefaultLeaseTTL, now)
					if err == nil {
						_ = store.Release(ctx, lease)
					}
				}
				if record.HostID != "" {
					if _, ok := hosts.Get(record.HostID); !ok {
						log.Printf("placement reconcile: %s/%s waits for lazy recovery from missing host %s", record.User, record.App, record.HostID)
					}
				}
			}
		}
		select {
		case <-ctx.Done():
			return
		case <-ticker.C:
		}
	}
}

func configureAgentClients(hosts map[string]*backend.AgentClient, controlClient *controlauth.Client, insecureLoopback bool) {
	for _, client := range hosts {
		client.ControlClient = controlClient
		client.InsecureLoopback = insecureLoopback
	}
}

func requireHostInstanceIDs(hosts map[string]*backend.AgentClient) error {
	for name, client := range hosts {
		if client == nil || client.InstanceID == "" {
			return fmt.Errorf("production host %q is missing its immutable GCE instance ID", name)
		}
	}
	return nil
}

func gatewayServiceRoutes(next http.Handler) http.Handler {
	return exactRoutes(next, map[string]struct{}{
		"POST /v1/ensure":  {},
		"POST /v1/stop":    {},
		"POST /v1/no-idle": {},
	})
}

func adminRoutes(next http.Handler) http.Handler {
	return exactRoutes(next, map[string]struct{}{
		"GET /v1/hosts":         {},
		"POST /v1/hosts/cordon": {},
		"POST /v1/hosts/drain":  {},
		"POST /v1/migrate":      {},
		"GET /v1/placement":     {},
		"GET /v1/placements":    {},
		"GET /v1/diagnostics":   {},
	})
}

func exactRoutes(next http.Handler, allowed map[string]struct{}) http.Handler {
	return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if _, ok := allowed[r.Method+" "+r.URL.Path]; !ok {
			http.NotFound(w, r)
			return
		}
		next.ServeHTTP(w, r)
	})
}

func listenAdminSocket(path string, requireRoot bool) (net.Listener, error) {
	if path == "" {
		return nil, fmt.Errorf("admin socket path is required")
	}
	if requireRoot && os.Geteuid() != 0 {
		return nil, fmt.Errorf("production admin socket requires root")
	}
	parent := filepath.Dir(path)
	if err := os.MkdirAll(parent, 0o755); err != nil {
		return nil, err
	}
	parentInfo, err := os.Stat(parent)
	if err != nil {
		return nil, err
	}
	if requireRoot {
		stat, ok := parentInfo.Sys().(*syscall.Stat_t)
		if !ok || stat.Uid != 0 || parentInfo.Mode().Perm()&0o022 != 0 {
			return nil, fmt.Errorf("admin socket directory %s must be root-owned and not group/world-writable", parent)
		}
	}
	if info, err := os.Lstat(path); err == nil {
		if info.Mode()&os.ModeSocket == 0 {
			return nil, fmt.Errorf("refusing to replace non-socket admin path %s", path)
		}
		if requireRoot {
			stat, ok := info.Sys().(*syscall.Stat_t)
			if !ok || stat.Uid != 0 {
				return nil, fmt.Errorf("refusing to replace admin socket not owned by root")
			}
		}
		if err := os.Remove(path); err != nil {
			return nil, err
		}
	} else if !os.IsNotExist(err) {
		return nil, err
	}
	listener, err := net.Listen("unix", path)
	if err != nil {
		return nil, err
	}
	cleanup := func(err error) (net.Listener, error) {
		_ = listener.Close()
		_ = os.Remove(path)
		return nil, err
	}
	if err := os.Chmod(path, 0o600); err != nil {
		return cleanup(err)
	}
	if requireRoot {
		info, err := os.Stat(path)
		if err != nil {
			return cleanup(err)
		}
		stat, ok := info.Sys().(*syscall.Stat_t)
		if !ok || stat.Uid != 0 || stat.Gid != 0 {
			return cleanup(fmt.Errorf("admin socket is not owned by root"))
		}
	}
	return listener, nil
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

func writeControlError(w http.ResponseWriter, err error) {
	var held placement.ErrLeaseHeld
	var lost placement.ErrLeaseLost
	var recovery placement.ErrRecoveryRequired
	var capacity backend.ErrAgentCapacity
	var exceeded quota.ErrExceeded
	switch {
	case errors.As(err, &exceeded):
		http.Error(w, err.Error(), http.StatusTooManyRequests)
	case errors.As(err, &held), errors.As(err, &lost), errors.As(err, &recovery):
		http.Error(w, err.Error(), http.StatusConflict)
	case errors.As(err, &capacity):
		http.Error(w, err.Error(), http.StatusServiceUnavailable)
	default:
		http.Error(w, err.Error(), http.StatusInternalServerError)
	}
}
