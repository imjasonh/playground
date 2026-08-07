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
	"flag"
	"log"
	"net"
	"net/http"
	"os"
	"os/signal"
	"syscall"
	"time"

	"github.com/imjasonh/playground/sshcloud/internal/backend"
	"github.com/imjasonh/playground/sshcloud/internal/controlauth"
	"github.com/imjasonh/playground/sshcloud/internal/drain"
	"github.com/imjasonh/playground/sshcloud/internal/healthhttp"
	"github.com/imjasonh/playground/sshcloud/internal/migrate"
	"github.com/imjasonh/playground/sshcloud/internal/observability"
	"github.com/imjasonh/playground/sshcloud/internal/placement"
	"github.com/imjasonh/playground/sshcloud/internal/quota"
)

func main() {
	observability.Configure("orchestrator")
	listen := flag.String("listen", "127.0.0.1:8090", "gateway-service HTTPS listen address")
	healthListen := flag.String("health-listen", "127.0.0.1:8091", "unauthenticated health-only HTTP listen address")
	adminSocket := flag.String("admin-socket", "", "root-owned Unix socket for the admin HTTPS API")
	hostsFlag := flag.String("hosts", "", "comma-separated hostID[@instance-id]=baseURL pairs")
	hostsFile := flag.String("hosts-file", "", "hosts file (name@instance-id=url per line in production); reloaded every 30s")
	gceZone := flag.String("gce-zone", "", "GCE zone used for immutable instance tombstone checks")
	firestoreProject := flag.String("firestore-project", "", "GCP project for Firestore placement (default: in-memory)")
	firestorePrefix := flag.String("firestore-prefix", "sshcloud", "Firestore collection prefix")
	userFirestoreDatabase := flag.String("user-firestore-database", "sshcloud-user", "user/app/quota Firestore database ID")
	placementFirestoreDatabase := flag.String("placement-firestore-database", "sshcloud-placement", "placement/operation Firestore database ID")
	controlTLS := controlauth.RegisterTLSFlags(flag.CommandLine, controlauth.RoleOrchestrator)
	controlProjectID := flag.String("control-project-id", "", "expected GCE identity-token project ID")
	controlProjectNumber := flag.String("control-project-number", "", "expected GCE identity-token project number")
	gatewayServiceAccount := flag.String("gateway-service-account", "", "exact gateway service-account email")
	orchestratorServiceAccount := flag.String("orchestrator-service-account", "", "exact orchestrator service-account email")
	agentServiceAccount := flag.String("agent-service-account", "", "exact agent service-account email for server proofs")
	insecureControl := flag.Bool("control-insecure-loopback", false, "explicitly allow unauthenticated plaintext control traffic on loopback only")
	gatewayURL := flag.String("gateway-url", "", "gateway migration control base URL")
	freezeTimeout := flag.Duration("freeze-timeout", 30*time.Second, "maximum outer-session freeze before forced reconnect")
	maxAwakePerUser := flag.Int("max-awake-per-user", 2, "maximum running VMs per user (deploy gets one temporary burst)")
	wakesPerHour := flag.Int("wakes-per-hour", 30, "wake/start admissions per user per hour")
	flag.Parse()

	controlFiles := controlTLS.Files()
	if *insecureControl {
		if err := controlauth.ValidateLoopbackListen(*listen); err != nil {
			log.Fatal(err)
		}
		log.Printf("WARNING: orchestrator control uses explicit loopback-only insecure mode")
	} else {
		if *controlProjectID == "" || *controlProjectNumber == "" ||
			*gatewayServiceAccount == "" || *orchestratorServiceAccount == "" ||
			*agentServiceAccount == "" || *gceZone == "" {
			log.Fatal("production control requires project identity, GCE zone, and exact gateway/orchestrator/agent service accounts")
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
	var agentServerVerifier controlauth.IdentityTokenVerifier
	if !*insecureControl {
		agentControlClient, err = controlauth.NewClient(
			controlFiles, controlauth.RoleOrchestrator, controlauth.RoleAgent,
			controlauth.MetadataTokenSource{}, controlauth.AudienceAgent, 20*time.Minute,
		)
		if err != nil {
			log.Fatalf("agent control client: %v", err)
		}
		agentServerVerifier = &controlauth.GCEVerifier{
			ProjectID: *controlProjectID, ProjectNumber: *controlProjectNumber,
		}
	}
	configureAgentClients(
		initial, agentControlClient, *insecureControl,
		agentServerVerifier, *agentServiceAccount,
	)
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
	var tombstones backend.InstanceTombstones
	if !*insecureControl {
		gceTombstones, err := backend.NewGCEInstanceTombstones(ctx, *controlProjectID, *gceZone)
		if err != nil {
			log.Fatalf("GCE instance tombstone verifier: %v", err)
		}
		tombstones = gceTombstones
	}

	var place placement.Store = placement.NewMemory()
	var quotaStore quota.Store = quota.NewMemory()
	if *firestoreProject != "" {
		fs, err := placement.NewFirestoreDatabase(ctx, *firestoreProject, *placementFirestoreDatabase, *firestorePrefix)
		if err != nil {
			log.Fatalf("firestore: %v", err)
		}
		defer fs.Close()
		place = fs
		quotaStore, err = quota.NewFirestoreDatabase(ctx, *firestoreProject, *userFirestoreDatabase, *firestorePrefix)
		if err != nil {
			log.Fatalf("quota firestore: %v", err)
		}
		defer quotaStore.Close()
		log.Printf("placement: firestore project %s", *firestoreProject)
	} else {
		log.Printf("placement: in-memory")
	}

	hosts := backend.NewHostSet(initial)
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
		go watchHostsFile(
			ctx, *hostsFile, hosts, agentControlClient, *insecureControl,
			agentServerVerifier, *agentServiceAccount,
		)
	}
	go reconcilePlacementLeases(ctx, place, hosts, tombstones)

	api, ready := buildAPIRoutes(controlTLS, hosts, place, drainer, mig, dial)
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
		log.Printf("sshcloud orchestrator gateway service on %s (hosts=%v)", *listen, hosts.IDs())
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
		healthServer = healthhttp.NewServer(*healthListen, func(mux *http.ServeMux) {
			healthhttp.Mount(mux, ready)
		})
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
