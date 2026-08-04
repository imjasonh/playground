package backend

import (
	"bytes"
	"encoding/json"
	"fmt"
	"io"
	"net/http"
	"net/url"
	"time"
)

// AgentClient talks to a host agent's HTTP API.
type AgentClient struct {
	BaseURL    string
	HTTPClient *http.Client
}

func (c *AgentClient) client() *http.Client {
	if c.HTTPClient != nil {
		return c.HTTPClient
	}
	return &http.Client{Timeout: 60 * time.Second}
}

func (c *AgentClient) post(path string, user, app string) (*http.Response, error) {
	body, _ := json.Marshal(map[string]string{"user": user, "app": app})
	return c.client().Post(c.BaseURL+path, "application/json", bytes.NewReader(body))
}

// Addr implements gateway.DialFunc via Ensure.
func (c *AgentClient) Addr(user, app string) (string, error) {
	in, err := c.Ensure(user, app)
	if err != nil {
		return "", err
	}
	return in.Addr, nil
}

// InstanceView is a subset of agent instance state.
type InstanceView struct {
	Addr    string `json:"addr"`
	GuestIP string `json:"guest_ip"`
	State   string `json:"state"`
}

// Ensure boots or wakes the instance on this host.
func (c *AgentClient) Ensure(user, app string) (InstanceView, error) {
	res, err := c.post("/v1/instances/ensure", user, app)
	if err != nil {
		return InstanceView{}, err
	}
	defer res.Body.Close()
	if res.StatusCode >= 300 {
		return InstanceView{}, fmt.Errorf("agent ensure: %s: %s", res.Status, readErr(res.Body))
	}
	var out InstanceView
	if err := json.NewDecoder(res.Body).Decode(&out); err != nil {
		return InstanceView{}, err
	}
	if out.Addr == "" {
		return InstanceView{}, fmt.Errorf("agent returned empty addr")
	}
	return out, nil
}

// Sleep snapshots and frees the VMM on this host.
func (c *AgentClient) Sleep(user, app string) error {
	res, err := c.post("/v1/instances/sleep", user, app)
	if err != nil {
		return err
	}
	defer res.Body.Close()
	if res.StatusCode >= 300 {
		return fmt.Errorf("agent sleep: %s: %s", res.Status, readErr(res.Body))
	}
	return nil
}

// Evict drops a sleeping instance without deleting the shared snapshot.
func (c *AgentClient) Evict(user, app string) error {
	res, err := c.post("/v1/instances/evict", user, app)
	if err != nil {
		return err
	}
	defer res.Body.Close()
	if res.StatusCode >= 300 {
		return fmt.Errorf("agent evict: %s: %s", res.Status, readErr(res.Body))
	}
	return nil
}

// Adopt restores an instance from the shared snapshot store onto this host.
func (c *AgentClient) Adopt(user, app string) (InstanceView, error) {
	res, err := c.post("/v1/instances/adopt", user, app)
	if err != nil {
		return InstanceView{}, err
	}
	defer res.Body.Close()
	if res.StatusCode >= 300 {
		return InstanceView{}, fmt.Errorf("agent adopt: %s: %s", res.Status, readErr(res.Body))
	}
	var out InstanceView
	if err := json.NewDecoder(res.Body).Decode(&out); err != nil {
		return InstanceView{}, err
	}
	return out, nil
}

// Status returns instance state, or ok=false when not found.
func (c *AgentClient) Status(user, app string) (InstanceView, bool, error) {
	u, err := url.Parse(c.BaseURL + "/v1/instances/status")
	if err != nil {
		return InstanceView{}, false, err
	}
	q := u.Query()
	q.Set("user", user)
	q.Set("app", app)
	u.RawQuery = q.Encode()
	req, err := http.NewRequest(http.MethodGet, u.String(), nil)
	if err != nil {
		return InstanceView{}, false, err
	}
	res, err := c.client().Do(req)
	if err != nil {
		return InstanceView{}, false, err
	}
	defer res.Body.Close()
	if res.StatusCode == http.StatusNotFound {
		return InstanceView{}, false, nil
	}
	if res.StatusCode >= 300 {
		return InstanceView{}, false, fmt.Errorf("agent status: %s: %s", res.Status, readErr(res.Body))
	}
	var out InstanceView
	if err := json.NewDecoder(res.Body).Decode(&out); err != nil {
		return InstanceView{}, false, err
	}
	return out, true, nil
}

// Stop destroys the instance and deletes its snapshot.
func (c *AgentClient) Stop(user, app string) error {
	res, err := c.post("/v1/instances/stop", user, app)
	if err != nil {
		return err
	}
	defer res.Body.Close()
	if res.StatusCode >= 300 {
		return fmt.Errorf("agent stop: %s: %s", res.Status, readErr(res.Body))
	}
	return nil
}

func readErr(r io.Reader) string {
	b, _ := io.ReadAll(io.LimitReader(r, 512))
	return string(bytes.TrimSpace(b))
}
