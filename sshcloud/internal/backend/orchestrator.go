package backend

import (
	"bytes"
	"context"
	"encoding/json"
	"fmt"
	"net/http"
	"strings"
	"time"
)

// OrchestratorClient talks to cmd/orchestrator for placement-aware Ensure.
type OrchestratorClient struct {
	BaseURL    string
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
	NoIdle bool   `json:"no_idle,omitempty"`
}

// Addr implements gateway dial via POST /v1/ensure.
func (c *OrchestratorClient) Addr(user, app, gen, image string) (string, error) {
	return c.ensure(context.Background(), orchEnsureBody{
		User: user, App: app, Gen: gen, Image: image,
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
func (c *OrchestratorClient) Ensure(ctx context.Context, user, app, gen, image string, noIdle bool) error {
	_, err := c.ensure(ctx, orchEnsureBody{
		User: user, App: app, Gen: gen, Image: image, NoIdle: noIdle,
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
