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
	BaseURL    string
	Token      string
	HTTPClient *http.Client
}

func (c *OrchestratorClient) client() *http.Client {
	if c.HTTPClient != nil {
		return c.HTTPClient
	}
	// Ensure may cold-boot or wake a snapshot; allow a long wait.
	return &http.Client{Timeout: 120 * time.Second}
}

type orchEnsureBody struct {
	User   string `json:"user"`
	App    string `json:"app"`
	Gen    string `json:"gen,omitempty"`
	Image  string `json:"image,omitempty"`
	Tier   string `json:"tier,omitempty"`
	NoIdle bool   `json:"no_idle,omitempty"`
}

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
	return c.ensure(ctx, orchEnsureBody{
		User: user, App: app, Gen: gen, Image: image, Tier: tier, NoIdle: noIdle,
	})
}

func (c *OrchestratorClient) ensure(ctx context.Context, body orchEnsureBody) (string, error) {
	base := strings.TrimRight(c.BaseURL, "/")
	b, err := json.Marshal(body)
	if err != nil {
		return "", err
	}
	req, err := http.NewRequestWithContext(ctx, http.MethodPost, base+"/v1/ensure", bytes.NewReader(b))
	if err != nil {
		return "", err
	}
	req.Header.Set("Content-Type", "application/json")
	controlauth.Add(req, c.Token)
	res, err := c.client().Do(req)
	if err != nil {
		return "", err
	}
	defer res.Body.Close()
	if res.StatusCode >= 300 {
		return "", fmt.Errorf("orchestrator ensure: %s: %s", res.Status, readErr(res.Body))
	}
	var out struct {
		Addr string `json:"addr"`
	}
	if err := json.NewDecoder(res.Body).Decode(&out); err != nil {
		return "", err
	}
	if out.Addr == "" {
		return "", fmt.Errorf("orchestrator returned empty addr")
	}
	return out.Addr, nil
}

// Ensure implements cutover.Instances via POST /v1/ensure.
func (c *OrchestratorClient) Ensure(ctx context.Context, user, app, gen, image, tier string, noIdle bool) error {
	return c.EnsureTier(ctx, user, app, gen, image, tier, noIdle)
}

// EnsureTier is Ensure with an explicit resource tier.
func (c *OrchestratorClient) EnsureTier(ctx context.Context, user, app, gen, image, tier string, noIdle bool) error {
	_, err := c.ensure(ctx, orchEnsureBody{
		User: user, App: app, Gen: gen, Image: image, Tier: tier, NoIdle: noIdle,
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
	controlauth.Add(req, c.Token)
	res, err := c.client().Do(req)
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
	controlauth.Add(req, c.Token)
	res, err := c.client().Do(req)
	if err != nil {
		return err
	}
	defer res.Body.Close()
	if res.StatusCode >= 300 {
		return fmt.Errorf("orchestrator no-idle: %s: %s", res.Status, readErr(res.Body))
	}
	return nil
}
