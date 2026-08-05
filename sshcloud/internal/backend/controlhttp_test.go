package backend

import (
	"context"
	"fmt"
	"net/http"
	"net/http/httptest"
	"strings"
	"sync/atomic"
	"testing"
	"time"

	"github.com/imjasonh/playground/sshcloud/internal/agent"
	"github.com/imjasonh/playground/sshcloud/internal/controlauth"
)

type staticIdentityVerifier struct {
	token    string
	identity controlauth.Identity
}

func (v staticIdentityVerifier) VerifyIdentity(
	_ context.Context,
	token string,
	policy controlauth.VerificationPolicy,
) (controlauth.Identity, error) {
	if token != v.token || policy.Audience != controlauth.AudienceAgentServer {
		return controlauth.Identity{}, fmt.Errorf("unexpected server proof")
	}
	return v.identity, nil
}

func TestControlHTTPKernelDeniesRedirects(t *testing.T) {
	t.Parallel()
	var followed atomic.Int32
	target := httptest.NewServer(http.HandlerFunc(func(http.ResponseWriter, *http.Request) {
		followed.Add(1)
	}))
	defer target.Close()
	redirect := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		http.Redirect(w, r, target.URL, http.StatusTemporaryRedirect)
	}))
	defer redirect.Close()

	client := &GatewayClient{BaseURL: redirect.URL, InsecureLoopback: true}
	if err := client.Thaw(context.Background(), "token"); err == nil {
		t.Fatal("redirect response was accepted")
	}
	if followed.Load() != 0 {
		t.Fatal("control client followed a redirect")
	}
}

func TestControlHTTPKernelRequiresBoundedExactJSON(t *testing.T) {
	t.Parallel()
	for name, response := range map[string]string{
		"unknown field":  `{"addr":"127.0.0.1:22","ssh_host_public_key":"key","extra":true}`,
		"trailing value": `{"addr":"127.0.0.1:22","ssh_host_public_key":"key"} {}`,
		"oversized":      strings.Repeat(" ", maxControlJSONBytes+1),
	} {
		t.Run(name, func(t *testing.T) {
			server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, _ *http.Request) {
				_, _ = w.Write([]byte(response))
			}))
			defer server.Close()
			client := &OrchestratorClient{BaseURL: server.URL, InsecureLoopback: true}
			if _, err := client.TargetTierContext(
				context.Background(), "alice", "app", "g1", "", "tiny", false,
			); err == nil {
				t.Fatal("invalid control JSON response was accepted")
			}
		})
	}
}

func TestGatewayFreezeModelsCompleteStrictResponse(t *testing.T) {
	t.Parallel()
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, _ *http.Request) {
		_, _ = w.Write([]byte(
			`{"token":"freeze-token","sessions":2,"deadline":"2026-08-05T22:00:00Z"}`,
		))
	}))
	defer server.Close()
	client := &GatewayClient{BaseURL: server.URL, InsecureLoopback: true}
	token, sessions, err := client.Freeze(
		context.Background(), "alice", "app", "g1", time.Second,
	)
	if err != nil {
		t.Fatal(err)
	}
	if token != "freeze-token" || sessions != 2 {
		t.Fatalf("Freeze = %q, %d", token, sessions)
	}
}

func TestControlHTTPKernelRejectsNonLoopbackInsecureURL(t *testing.T) {
	t.Parallel()
	client := &GatewayClient{BaseURL: "http://192.0.2.1", InsecureLoopback: true}
	if err := client.Abort(context.Background(), "token"); err == nil {
		t.Fatal("insecure non-loopback control URL was accepted")
	}
}

func TestAgentMutationsCarryImmutableTargetIdentity(t *testing.T) {
	t.Parallel()
	target := make(chan [2]string, 1)
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		target <- [2]string{
			r.Header.Get(agent.TargetInstanceNameHeader),
			r.Header.Get(agent.TargetInstanceIDHeader),
		}
		w.WriteHeader(http.StatusNoContent)
	}))
	defer server.Close()
	client := &AgentClient{
		BaseURL: server.URL, InsecureLoopback: true,
		InstanceName: "agent-a", InstanceID: "123456789",
	}
	if err := client.StopContext(context.Background(), "alice", "app", "g1"); err != nil {
		t.Fatal(err)
	}
	got := <-target
	if got != [2]string{client.InstanceName, client.InstanceID} {
		t.Fatalf("target headers = %q@%q", got[0], got[1])
	}
}

func TestAgentServerProofStillBindsDiscoveredIncarnation(t *testing.T) {
	t.Parallel()
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, _ *http.Request) {
		_, _ = w.Write([]byte(`{"token":"server-proof"}`))
	}))
	defer server.Close()
	client := &AgentClient{
		BaseURL: server.URL, InsecureLoopback: true,
		InstanceName: "agent-a", InstanceID: "123456789",
		ServerVerifier: staticIdentityVerifier{
			token: "server-proof",
			identity: controlauth.Identity{
				InstanceName: "agent-a", InstanceID: "123456789",
			},
		},
		ServerPolicy: controlauth.VerificationPolicy{
			Audience: controlauth.AudienceAgentServer,
		},
	}
	if err := client.VerifyServerIdentity(context.Background()); err != nil {
		t.Fatal(err)
	}
	client.InstanceID = "987654321"
	if err := client.VerifyServerIdentity(context.Background()); err == nil {
		t.Fatal("server proof for a different immutable instance was accepted")
	}
}
