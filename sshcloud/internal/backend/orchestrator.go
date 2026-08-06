package backend

import (
	"context"
	"fmt"
	"net/http"
	"time"

	"github.com/imjasonh/playground/sshcloud/internal/controlauth"
	"github.com/imjasonh/playground/sshcloud/internal/placement"
)

// OrchestratorClient talks to cmd/orchestrator for placement-aware Ensure.
type OrchestratorClient struct {
	BaseURL          string
	ControlClient    *controlauth.Client
	HTTPClient       *http.Client
	InsecureLoopback bool
}

func (c *OrchestratorClient) kernel() controlHTTPKernel {
	return controlHTTPKernel{
		baseURL: c.BaseURL, controlClient: c.ControlClient, httpClient: c.HTTPClient,
		insecureLoopback: c.InsecureLoopback, timeout: 6 * time.Minute,
	}
}

type orchEnsureBody struct {
	User      string `json:"user"`
	App       string `json:"app"`
	Gen       string `json:"gen,omitempty"`
	Image     string `json:"image,omitempty"`
	Tier      string `json:"tier,omitempty"`
	NoIdle    bool   `json:"no_idle,omitempty"`
	Purpose   string `json:"purpose,omitempty"`
	RequestID string `json:"request_id,omitempty"`
}

type OrchestratorTarget struct {
	Addr             string
	SSHHostPublicKey string
}

type TemporaryError struct{ Err error }

func (e TemporaryError) Error() string   { return e.Err.Error() }
func (e TemporaryError) Unwrap() error   { return e.Err }
func (e TemporaryError) Temporary() bool { return true }

// Addr implements gateway dial via POST /v1/ensure.
func (c *OrchestratorClient) Addr(user, app, gen, image string) (string, error) {
	return c.AddrContext(context.Background(), user, app, gen, image)
}

// AddrContext is Addr with cancellation propagated to the orchestrator.
func (c *OrchestratorClient) AddrContext(ctx context.Context, user, app, gen, image string) (string, error) {
	return c.AddrTierContext(ctx, user, app, gen, image, "", false)
}

// AddrTierContext ensures an instance with tier/no-idle settings.
func (c *OrchestratorClient) AddrTierContext(ctx context.Context, user, app, gen, image, tier string, noIdle bool) (string, error) {
	target, err := c.TargetTierContext(ctx, user, app, gen, image, tier, noIdle)
	return target.Addr, err
}

func (c *OrchestratorClient) TargetTierContext(ctx context.Context, user, app, gen, image, tier string, noIdle bool) (OrchestratorTarget, error) {
	return c.TargetTierRequest(
		ctx, user, app, gen, image, tier, noIdle,
		"session", placement.NewLeaseOwner("session"),
	)
}

func (c *OrchestratorClient) TargetTierRequest(ctx context.Context, user, app, gen, image, tier string, noIdle bool, purpose, requestID string) (OrchestratorTarget, error) {
	return c.ensure(ctx, orchEnsureBody{
		User: user, App: app, Gen: gen, Image: image, Tier: tier, NoIdle: noIdle,
		Purpose: purpose, RequestID: requestID,
	})
}

func (c *OrchestratorClient) ensure(ctx context.Context, body orchEnsureBody) (OrchestratorTarget, error) {
	var out struct {
		Addr             string `json:"addr"`
		SSHHostPublicKey string `json:"ssh_host_public_key"`
	}
	err := c.kernel().json(
		ctx, http.MethodPost, "/v1/ensure", "orchestrator ensure", body, &out, nil,
	)
	if err != nil {
		if statusErr, ok := statusError(err); ok &&
			(statusErr.StatusCode == http.StatusConflict ||
				statusErr.StatusCode == http.StatusServiceUnavailable) {
			return OrchestratorTarget{}, TemporaryError{Err: err}
		}
		return OrchestratorTarget{}, err
	}
	if out.Addr == "" {
		return OrchestratorTarget{}, fmt.Errorf("orchestrator returned empty addr")
	}
	if out.SSHHostPublicKey == "" {
		return OrchestratorTarget{}, fmt.Errorf("orchestrator returned empty SSH host key")
	}
	return OrchestratorTarget{Addr: out.Addr, SSHHostPublicKey: out.SSHHostPublicKey}, nil
}

// Ready verifies the authenticated placement backend without starting a VM.
func (c *OrchestratorClient) Ready(ctx context.Context) error {
	return c.kernel().json(
		ctx, http.MethodGet, "/v1/readyz", "orchestrator readiness", nil, nil, nil,
	)
}

// Ensure implements cutover.Instances via POST /v1/ensure.
func (c *OrchestratorClient) Ensure(ctx context.Context, user, app, gen, image, tier string, noIdle bool) error {
	return c.EnsureTier(ctx, user, app, gen, image, tier, noIdle)
}

// EnsureTier is Ensure with an explicit resource tier.
func (c *OrchestratorClient) EnsureTier(ctx context.Context, user, app, gen, image, tier string, noIdle bool) error {
	_, err := c.ensure(ctx, orchEnsureBody{
		User: user, App: app, Gen: gen, Image: image, Tier: tier, NoIdle: noIdle,
		Purpose: "deploy", RequestID: gen,
	})
	return err
}

// Stop implements cutover.Instances via POST /v1/stop.
func (c *OrchestratorClient) Stop(ctx context.Context, user, app, gen string) error {
	return c.kernel().json(
		ctx, http.MethodPost, "/v1/stop", "orchestrator stop",
		instanceBody{User: user, App: app, Gen: gen}, nil, nil,
	)
}

// SetNoIdle changes an instance's active-operation hold through placement.
func (c *OrchestratorClient) SetNoIdle(ctx context.Context, user, app, gen string, noIdle bool) error {
	return c.kernel().json(
		ctx, http.MethodPost, "/v1/no-idle", "orchestrator no-idle",
		instanceBody{User: user, App: app, Gen: gen, NoIdle: noIdle}, nil, nil,
	)
}
