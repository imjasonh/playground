package main

import (
	"context"
	"fmt"
	"log"
	"time"

	"github.com/imjasonh/playground/sshcloud/internal/backend"
	"github.com/imjasonh/playground/sshcloud/internal/controlauth"
	"github.com/imjasonh/playground/sshcloud/internal/placement"
	hostreconcile "github.com/imjasonh/playground/sshcloud/internal/reconcile"
)

func watchHostsFile(
	ctx context.Context,
	path string,
	hosts *backend.HostSet,
	controlClient *controlauth.Client,
	insecureLoopback bool,
	serverVerifier controlauth.IdentityTokenVerifier,
	agentServiceAccount string,
) {
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
			configureAgentClients(m, controlClient, insecureLoopback, serverVerifier, agentServiceAccount)
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

func reconcilePlacementLeases(
	ctx context.Context,
	store placement.Store,
	hosts *backend.HostSet,
	tombstones backend.InstanceTombstones,
) {
	ticker := time.NewTicker(30 * time.Second)
	defer ticker.Stop()
	reconciler := &hostreconcile.Controller{
		Placement: store, Hosts: hosts, Tombstones: tombstones,
	}
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

func configureAgentClients(
	hosts map[string]*backend.AgentClient,
	controlClient *controlauth.Client,
	insecureLoopback bool,
	serverVerifier controlauth.IdentityTokenVerifier,
	agentServiceAccount string,
) {
	for _, client := range hosts {
		client.ControlClient = controlClient
		client.InsecureLoopback = insecureLoopback
		client.ServerVerifier = serverVerifier
		client.ServerPolicy = controlauth.VerificationPolicy{
			ServiceAccount: agentServiceAccount,
			Audience:       controlauth.AudienceAgentServer,
		}
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
