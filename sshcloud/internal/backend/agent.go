package backend

import (
	"bytes"
	"encoding/json"
	"fmt"
	"net/http"
	"time"
)

// AgentClient dials app instances via the host agent HTTP API.
type AgentClient struct {
	BaseURL    string
	HTTPClient *http.Client
}

// Addr implements gateway.DialFunc.
func (c *AgentClient) Addr(user, app string) (string, error) {
	hc := c.HTTPClient
	if hc == nil {
		hc = &http.Client{Timeout: 60 * time.Second}
	}
	body, _ := json.Marshal(map[string]string{"user": user, "app": app})
	res, err := hc.Post(c.BaseURL+"/v1/instances/ensure", "application/json", bytes.NewReader(body))
	if err != nil {
		return "", err
	}
	defer res.Body.Close()
	if res.StatusCode >= 300 {
		return "", fmt.Errorf("agent ensure: %s", res.Status)
	}
	var out struct {
		Addr string `json:"addr"`
	}
	if err := json.NewDecoder(res.Body).Decode(&out); err != nil {
		return "", err
	}
	if out.Addr == "" {
		return "", fmt.Errorf("agent returned empty addr")
	}
	return out.Addr, nil
}
