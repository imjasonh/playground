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

func TestDeployQuotaSkipsExactNoOpAndCountsTierChange(t *testing.T) {
	t.Parallel()
	ctx := context.Background()
	st := store.NewMemory()
	if err := st.CreateUser(ctx, "alice", "key-a"); err != nil {
		t.Fatal(err)
	}
	image := "ghcr.io/example/a@sha256:" + strings.Repeat("a", 64)
	if err := st.UpsertApp(ctx, store.App{
		Owner: "alice", Name: "appone", Image: image, Tier: "tiny",
		SessionStrategy: store.StrategyKick, ActiveGen: "g1",
	}); err != nil {
		t.Fatal(err)
	}
	hub := &Hub{
		Store: st, Quotas: quota.NewMemory(),
		Limits: Limits{DeploysPerHour: 1, AppsPerUser: 5},
	}

	if _, err := applyDeploy(ctx, hub, "key-a", "alice", DeployArgs{
		Name: "appone", Image: image, Tier: "tiny", Strategy: store.StrategyDrain, Yes: true,
	}, true); err != nil {
		t.Fatalf("exact no-op: %v", err)
	}
	unchanged, _ := st.GetApp(ctx, "alice", "appone")
	if unchanged.Tier != "tiny" || unchanged.SessionStrategy != store.StrategyKick {
		t.Fatalf("exact no-op mutated app: %+v", unchanged)
	}

	if _, err := applyDeploy(ctx, hub, "key-a", "alice", DeployArgs{
		Name: "appone", Image: image, Tier: "small", Strategy: store.StrategyKick, Yes: true,
	}, true); err != nil {
		t.Fatalf("tier change should consume first deploy admission: %v", err)
	}
	if _, err := applyDeploy(ctx, hub, "key-a", "alice", DeployArgs{
		Name: "appone", Image: image, Tier: "tiny", Strategy: store.StrategyKick, Yes: true,
	}, true); err == nil {
		t.Fatal("second tier change did not consume a distinct deploy admission")
	}
}

func TestDeployQuotaRetriesUseOneOperationIdentity(t *testing.T) {
	t.Parallel()
	hub := &Hub{
		Quotas: quota.NewMemory(),
		Limits: Limits{DeploysPerHour: 1},
	}
	for attempt := 0; attempt < 2; attempt++ {
		if err := hub.allowDeploy(t.Context(), "alice", "deploy-stable"); err != nil {
			t.Fatalf("retry %d with stable deploy operation ID: %v", attempt, err)
		}
	}
	if err := hub.allowDeploy(t.Context(), "alice", "deploy-separate"); err == nil {
		t.Fatal("separate deploy operation did not consume a distinct admission")
	}
}
