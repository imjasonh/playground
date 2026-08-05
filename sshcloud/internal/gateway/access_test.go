package gateway

import (
	"context"
	"crypto/ed25519"
	"crypto/rand"
	"encoding/json"
	"strings"
	"testing"

	"golang.org/x/crypto/ssh"

	"github.com/imjasonh/playground/sshcloud/internal/access"
	"github.com/imjasonh/playground/sshcloud/internal/session"
	"github.com/imjasonh/playground/sshcloud/internal/store"
)

func TestApplyDeployEnforcesAccessPolicy(t *testing.T) {
	t.Parallel()
	_, privateKey, err := ed25519.GenerateKey(rand.Reader)
	if err != nil {
		t.Fatal(err)
	}
	publicKey, err := ssh.NewPublicKey(privateKey.Public())
	if err != nil {
		t.Fatal(err)
	}
	line := strings.TrimSpace(string(ssh.MarshalAuthorizedKey(publicKey)))
	fingerprint := ssh.FingerprintSHA256(publicKey)
	data, err := json.Marshal(map[string]any{
		"version":                  1,
		"join_mode":                "allowlist",
		"deploy_mode":              "allowlist",
		"member_ssh_public_keys":   []string{line},
		"deployer_ssh_public_keys": []string{},
	})
	if err != nil {
		t.Fatal(err)
	}
	policy, err := access.ParseJSON(data)
	if err != nil {
		t.Fatal(err)
	}

	ctx := context.Background()
	st := store.NewMemory()
	if err := st.CreateUser(ctx, "alice", fingerprint); err != nil {
		t.Fatal(err)
	}
	hub := &Hub{
		Store:    st,
		Sessions: session.NewRegistry(),
		Access:   access.StaticSource{Policy: policy},
	}
	_, err = applyDeploy(ctx, hub, fingerprint, "alice", DeployArgs{
		Name:     "myapp",
		Image:    "ghcr.io/example/app@sha256:" + strings.Repeat("a", 64),
		Tier:     "tiny",
		Strategy: store.StrategyKick,
		Yes:      true,
	}, true)
	if err == nil || !isForbidden(err) {
		t.Fatalf("applyDeploy error = %v, want forbidden", err)
	}
	app, getErr := st.GetApp(ctx, "alice", "myapp")
	if getErr != nil || app != nil {
		t.Fatalf("forbidden deploy persisted app: %+v, %v", app, getErr)
	}
}
