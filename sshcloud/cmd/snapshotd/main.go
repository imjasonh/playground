// Command snapshotd is the only production workload with snapshot-bucket and
// snapshot-KEK access. Agents proxy fixed packages through its authenticated
// internal API.
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
	"path/filepath"
	"strings"
	"syscall"
	"time"

	"github.com/imjasonh/playground/sshcloud/internal/controlauth"
	"github.com/imjasonh/playground/sshcloud/internal/healthhttp"
	"github.com/imjasonh/playground/sshcloud/internal/hostisolation"
	"github.com/imjasonh/playground/sshcloud/internal/observability"
	"github.com/imjasonh/playground/sshcloud/internal/placement"
	"github.com/imjasonh/playground/sshcloud/internal/snapshot"
	"github.com/imjasonh/playground/sshcloud/internal/snapshotd"
)

func main() {
	observability.Configure("snapshotd")
	listen := flag.String("listen", "", "snapshot API HTTPS listen address")
	healthListen := flag.String("health-listen", "", "health-only HTTP listen address")
	tempDir := flag.String("temp-dir", "/var/lib/sshcloud/snapshotd", "package staging directory")
	bucket := flag.String("gcs-bucket", "", "CMEK-backed snapshot bucket")
	prefix := flag.String("gcs-prefix", "sshcloud/snaps", "server-owned object prefix")
	kmsKey := flag.String("kms-key", "", "Cloud KMS snapshot KEK resource name")
	firestoreProject := flag.String("firestore-project", "", "placement Firestore project")
	firestorePrefix := flag.String("firestore-prefix", "sshcloud", "placement collection prefix")
	placementFirestoreDatabase := flag.String("placement-firestore-database", "sshcloud-placement", "placement/operation database")
	expectedLayout := flag.String("layout-version", hostisolation.SnapshotLayoutJailer, "only accepted snapshot layout")
	stagingMaxBytes := flag.Int64("staging-max-bytes", 10<<30, "global reserved plaintext staging bytes")
	stagingMaxOperations := flag.Int("staging-max-operations", 2, "global concurrent plaintext staging operations")
	stagingMaxPerAgent := flag.Int("staging-max-per-agent", 1, "concurrent staging operations per exact agent incarnation")
	controlTLS := controlauth.RegisterTLSFlags(flag.CommandLine, controlauth.RoleSnapshot)
	controlProjectID := flag.String("control-project-id", "", "expected GCE token project ID")
	controlProjectNumber := flag.String("control-project-number", "", "expected GCE token project number")
	agentServiceAccount := flag.String("agent-service-account", "", "exact agent service-account email")
	flag.Parse()

	for name, value := range map[string]string{
		"listen": *listen, "health-listen": *healthListen, "gcs-bucket": *bucket,
		"kms-key": *kmsKey, "firestore-project": *firestoreProject,
		"control-project-id": *controlProjectID, "control-project-number": *controlProjectNumber,
		"agent-service-account": *agentServiceAccount,
	} {
		if strings.TrimSpace(value) == "" {
			log.Fatalf("-%s is required", name)
		}
	}

	ctx, stop := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
	defer stop()
	if err := prepareTempDir(*tempDir); err != nil {
		log.Fatalf("snapshot staging directory: %v", err)
	}
	if *stagingMaxBytes < snapshot.MaxPackageBytes {
		log.Fatalf("-staging-max-bytes must fit one maximum package (%d bytes)", snapshot.MaxPackageBytes)
	}
	staging, err := snapshotd.NewStagingGuard(snapshotd.StagingLimits{
		MaxBytes: *stagingMaxBytes, MaxConcurrent: *stagingMaxOperations,
		MaxPerAgent: *stagingMaxPerAgent, MaxRequestBytes: snapshot.MaxRequestBytes,
	})
	if err != nil {
		log.Fatalf("snapshot staging limits: %v", err)
	}
	observability.DefaultMetrics().RegisterCollector(func() {
		usage := staging.Usage()
		observability.DefaultMetrics().SetSnapshotStaging(
			usage.MaxBytes,
			usage.UsedBytes,
			usage.RetainedBytes,
			usage.MaxConcurrent,
			usage.Active,
			usage.MaxPerAgent,
		)
	})
	place, err := placement.NewFirestoreDatabase(ctx, *firestoreProject, *placementFirestoreDatabase, *firestorePrefix)
	if err != nil {
		log.Fatalf("placement firestore: %v", err)
	}
	defer place.Close()
	store, err := snapshot.NewGCSStore(ctx, *bucket, *prefix, *kmsKey, *expectedLayout)
	if err != nil {
		log.Fatalf("snapshot store: %v", err)
	}
	defer store.Close()

	handler := &snapshotd.Handler{
		Store: store, Authorizer: &snapshotd.Authorizer{Placement: place},
		ExpectedLayout: *expectedLayout, TempDir: *tempDir, Staging: staging,
		Readiness: func() error {
			return controlTLS.Fresh()
		},
	}
	api := http.NewServeMux()
	handler.Mount(api)
	verifier := &controlauth.GCEVerifier{
		ProjectID: *controlProjectID, ProjectNumber: *controlProjectNumber,
	}
	authenticated := controlauth.RequireIdentity(verifier, controlauth.VerificationPolicy{
		CallerRole: controlauth.RoleAgent, ServiceAccount: *agentServiceAccount,
		Audience: controlauth.AudienceSnapshot,
	}, api)
	tlsConfig, err := controlauth.ServerTLSConfig(controlTLS.Files(), controlauth.RoleSnapshot)
	if err != nil {
		log.Fatalf("snapshot control TLS: %v", err)
	}
	server := &http.Server{
		Addr: *listen, Handler: authenticated,
		ReadHeaderTimeout: 10 * time.Second, ReadTimeout: 20 * time.Minute,
		WriteTimeout: 20 * time.Minute, IdleTimeout: 30 * time.Second,
		MaxHeaderBytes: 32 << 10,
	}
	listener, err := net.Listen("tcp", *listen)
	if err != nil {
		log.Fatalf("snapshot listen: %v", err)
	}
	listener = tls.NewListener(listener, tlsConfig)
	go func() {
		log.Printf("sshcloud snapshotd on %s", *listen)
		if err := server.Serve(listener); err != nil && err != http.ErrServerClosed {
			log.Fatal(err)
		}
	}()

	healthServer := healthhttp.NewServer(*healthListen, handler.MountHealth)
	healthServer.MaxHeaderBytes = 8 << 10
	go func() {
		log.Printf("sshcloud snapshotd health on %s", *healthListen)
		if err := healthServer.ListenAndServe(); err != nil && err != http.ErrServerClosed {
			log.Fatal(err)
		}
	}()

	<-ctx.Done()
	shutdown, cancel := context.WithTimeout(context.Background(), 30*time.Second)
	defer cancel()
	_ = server.Shutdown(shutdown)
	_ = healthServer.Shutdown(shutdown)
}

func prepareTempDir(dir string) error {
	if err := os.MkdirAll(dir, 0o700); err != nil {
		return err
	}
	if err := os.Chmod(dir, 0o700); err != nil {
		return err
	}
	entries, err := os.ReadDir(dir)
	if err != nil {
		return err
	}
	for _, entry := range entries {
		if err := os.RemoveAll(filepath.Join(dir, entry.Name())); err != nil {
			return err
		}
	}
	return nil
}
