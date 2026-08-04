package backend

import (
	"bytes"
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

// Addr implements gateway.DialFunc via POST /v1/ensure.
func (c *OrchestratorClient) Addr(user, app string) (string, error) {
	base := strings.TrimRight(c.BaseURL, "/")
	body, err := json.Marshal(map[string]string{"user": user, "app": app})
	if err != nil {
		return "", err
	}
	res, err := c.client().Post(base+"/v1/ensure", "application/json", bytes.NewReader(body))
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
