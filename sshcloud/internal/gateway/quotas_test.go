package gateway

import (
	"context"
	"strings"
	"testing"

	"github.com/imjasonh/playground/sshcloud/internal/quota"
	"github.com/imjasonh/playground/sshcloud/internal/store"
)

func TestJoinAndDeployQuotaDefaults(t *testing.T) {
	t.Parallel()
	ctx := context.Background()
	hub := &Hub{Store: store.NewMemory(), Quotas: quota.NewMemory(), Limits: Limits{
		JoinsPerIPDay: 1, JoinsPerNetDay: 10, DeploysPerHour: 1, AppsPerUser: 1,
	}}
	if err := hub.allowJoin(ctx, "192.0.2.1", "alice", "key-a"); err != nil {
		t.Fatal(err)
	}
	if err := hub.allowJoin(ctx, "192.0.2.1", "bob", "key-b"); err == nil {
		t.Fatal("second join from IP was admitted")
	}
	if err := hub.Store.CreateUser(ctx, "alice", "key-a"); err != nil {
		t.Fatal(err)
	}
	imageA := "ghcr.io/example/a@sha256:" + strings.Repeat("a", 64)
	imageB := "ghcr.io/example/b@sha256:" + strings.Repeat("b", 64)
	if _, err := applyDeploy(ctx, hub, "key-a", "alice", DeployArgs{
		Name: "appone", Image: imageA, Tier: "tiny", Strategy: store.StrategyKick, Yes: true,
	}, true); err != nil {
		t.Fatal(err)
	}
	if _, err := applyDeploy(ctx, hub, "key-a", "alice", DeployArgs{
		Name: "apptwo", Image: imageB, Tier: "tiny", Strategy: store.StrategyKick, Yes: true,
	}, true); err == nil {
		t.Fatal("second app was admitted above app quota")
	}
	if _, err := applyDeploy(ctx, hub, "key-a", "alice", DeployArgs{
		Name: "appone", Image: imageB, Tier: "tiny", Strategy: store.StrategyKick, Yes: true,
	}, true); err == nil {
		t.Fatal("second distinct deploy event was admitted above hourly quota")
	}
}
