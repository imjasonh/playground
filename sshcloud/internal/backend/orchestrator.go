package backend

import (
	"bytes"
	"context"
	"encoding/json"
	"fmt"
	"net/http"
	"strings"
	"time"

	"github.com/imjasonh/playground/sshcloud/internal/controlauth"
)

// OrchestratorClient talks to cmd/orchestrator for placement-aware Ensure.
type OrchestratorClient struct {
	BaseURL          string
	ControlClient    *controlauth.Client
	HTTPClient       *http.Client
	InsecureLoopback bool
}

func (c *OrchestratorClient) client() *http.Client {
	if c.HTTPClient != nil {
		return c.HTTPClient
	}
	// Ensure may cold-boot or wake a snapshot; allow a long wait.
	return &http.Client{Timeout: 6 * time.Minute}
}

func (c *OrchestratorClient) do(req *http.Request) (*http.Response, error) {
	if c.ControlClient != nil {
		return c.ControlClient.Do(req)
	}
	if err := controlauth.PrepareRequest(req, nil, c.InsecureLoopback); err != nil {
		return nil, err
	}
	return c.client().Do(req)
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
	return c.TargetTierRequest(ctx, user, app, gen, image, tier, noIdle, "session", gen+"\x00"+image)
}

func (c *OrchestratorClient) TargetTierRequest(ctx context.Context, user, app, gen, image, tier string, noIdle bool, purpose, requestID string) (OrchestratorTarget, error) {
	return c.ensure(ctx, orchEnsureBody{
		User: user, App: app, Gen: gen, Image: image, Tier: tier, NoIdle: noIdle,
		Purpose: purpose, RequestID: requestID,
	})
}

func (c *OrchestratorClient) ensure(ctx context.Context, body orchEnsureBody) (OrchestratorTarget, error) {
	base := strings.TrimRight(c.BaseURL, "/")
	b, err := json.Marshal(body)
	if err != nil {
		return OrchestratorTarget{}, err
	}
	req, err := http.NewRequestWithContext(ctx, http.MethodPost, base+"/v1/ensure", bytes.NewReader(b))
	if err != nil {
		return OrchestratorTarget{}, err
	}
	req.Header.Set("Content-Type", "application/json")
	res, err := c.do(req)
	if err != nil {
		return OrchestratorTarget{}, err
	}
	defer res.Body.Close()
	if res.StatusCode >= 300 {
		err := fmt.Errorf("orchestrator ensure: %s: %s", res.Status, readErr(res.Body))
		if res.StatusCode == http.StatusConflict || res.StatusCode == http.StatusServiceUnavailable {
			return OrchestratorTarget{}, TemporaryError{Err: err}
		}
		return OrchestratorTarget{}, err
	}
	var out struct {
		Addr             string `json:"addr"`
		SSHHostPublicKey string `json:"ssh_host_public_key"`
	}
	if err := json.NewDecoder(res.Body).Decode(&out); err != nil {
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
	base := strings.TrimRight(c.BaseURL, "/")
	b, err := json.Marshal(instanceBody{User: user, App: app, Gen: gen})
	if err != nil {
		return err
	}
	req, err := http.NewRequestWithContext(ctx, http.MethodPost, base+"/v1/stop", bytes.NewReader(b))
	if err != nil {
		return err
	}
	req.Header.Set("Content-Type", "application/json")
	res, err := c.do(req)
	if err != nil {
		return err
	}
	defer res.Body.Close()
	if res.StatusCode >= 300 {
		return fmt.Errorf("orchestrator stop: %s: %s", res.Status, readErr(res.Body))
	}
	return nil
}

// SetNoIdle changes an instance's active-operation hold through placement.
func (c *OrchestratorClient) SetNoIdle(ctx context.Context, user, app, gen string, noIdle bool) error {
	base := strings.TrimRight(c.BaseURL, "/")
	b, err := json.Marshal(instanceBody{User: user, App: app, Gen: gen, NoIdle: noIdle})
	if err != nil {
		return err
	}
	req, err := http.NewRequestWithContext(ctx, http.MethodPost, base+"/v1/no-idle", bytes.NewReader(b))
	if err != nil {
		return err
	}
	req.Header.Set("Content-Type", "application/json")
	res, err := c.do(req)
	if err != nil {
		return err
	}
	defer res.Body.Close()
	if res.StatusCode >= 300 {
		return fmt.Errorf("orchestrator no-idle: %s: %s", res.Status, readErr(res.Body))
	}
	return nil
}
