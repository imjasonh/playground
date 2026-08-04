package backend

import (
	"bytes"
	"context"
	"encoding/json"
	"fmt"
	"io"
	"net/http"
	"net/url"
	"time"

	"github.com/imjasonh/playground/sshcloud/internal/agent"
	"github.com/imjasonh/playground/sshcloud/internal/controlauth"
)

// AgentClient talks to a host agent's HTTP API.
type AgentClient struct {
	BaseURL    string
	Token      string
	HTTPClient *http.Client
}

func (c *AgentClient) client() *http.Client {
	if c.HTTPClient != nil {
		return c.HTTPClient
	}
	// Pulling, unpacking, building ext4, and booting a cold image can be slow.
	// Callers still provide cancellable request contexts.
	return &http.Client{Timeout: 5 * time.Minute}
}

type instanceBody struct {
	User        string `json:"user"`
	App         string `json:"app"`
	Gen         string `json:"gen,omitempty"`
	NoIdle      bool   `json:"no_idle,omitempty"`
	Image       string `json:"image,omitempty"`
	Tier        string `json:"tier,omitempty"`
	CordonEpoch string `json:"cordon_epoch,omitempty"`
}

func (c *AgentClient) postJSON(ctx context.Context, path string, body any) (*http.Response, error) {
	b, err := json.Marshal(body)
	if err != nil {
		return nil, err
	}
	req, err := http.NewRequestWithContext(ctx, http.MethodPost, c.BaseURL+path, bytes.NewReader(b))
	if err != nil {
		return nil, err
	}
	req.Header.Set("Content-Type", "application/json")
	controlauth.Add(req, c.Token)
	return c.client().Do(req)
}

func (c *AgentClient) postInstance(ctx context.Context, path, user, app, gen string) (*http.Response, error) {
	return c.postJSON(ctx, path, instanceBody{User: user, App: app, Gen: gen})
}

// Addr dials via Ensure (generation + optional digest-pinned image).
func (c *AgentClient) Addr(user, app, gen, image string) (string, error) {
	in, err := c.Ensure(user, app, gen, image, false)
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

// ErrAgentCapacity is returned when a host is full or cordoned.
type ErrAgentCapacity struct {
	HostStatus int
	Message    string
}

func (e ErrAgentCapacity) Error() string { return e.Message }

// Ensure boots or wakes the instance on this host.
func (c *AgentClient) Ensure(user, app, gen, image string, noIdle bool) (InstanceView, error) {
	return c.EnsureContext(context.Background(), user, app, gen, image, noIdle)
}

// EnsureContext is Ensure with cancellation propagated to the host agent.
func (c *AgentClient) EnsureContext(ctx context.Context, user, app, gen, image string, noIdle bool) (InstanceView, error) {
	return c.EnsureTierContext(ctx, user, app, gen, image, "", noIdle)
}

// EnsureTierContext is EnsureContext with an explicit resource tier.
func (c *AgentClient) EnsureTierContext(ctx context.Context, user, app, gen, image, tier string, noIdle bool) (InstanceView, error) {
	res, err := c.postJSON(ctx, "/v1/instances/ensure", instanceBody{
		User:   user,
		App:    app,
		Gen:    gen,
		Image:  image,
		Tier:   tier,
		NoIdle: noIdle,
	})
	if err != nil {
		return InstanceView{}, err
	}
	defer res.Body.Close()
	if res.StatusCode == http.StatusConflict || res.StatusCode == http.StatusServiceUnavailable {
		return InstanceView{}, ErrAgentCapacity{HostStatus: res.StatusCode, Message: readErr(res.Body)}
	}
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

// Capacity returns one host's allocatable resource view.
func (c *AgentClient) Capacity(ctx context.Context) (agent.Capacity, error) {
	req, err := http.NewRequestWithContext(ctx, http.MethodGet, c.BaseURL+"/v1/host/capacity", nil)
	if err != nil {
		return agent.Capacity{}, err
	}
	controlauth.Add(req, c.Token)
	res, err := c.client().Do(req)
	if err != nil {
		return agent.Capacity{}, err
	}
	defer res.Body.Close()
	if res.StatusCode >= 300 {
		return agent.Capacity{}, fmt.Errorf("agent capacity: %s: %s", res.Status, readErr(res.Body))
	}
	var capacity agent.Capacity
	if err := json.NewDecoder(res.Body).Decode(&capacity); err != nil {
		return agent.Capacity{}, err
	}
	return capacity, nil
}

// Instances returns host inventory for drain/reconciliation.
func (c *AgentClient) Instances(ctx context.Context) ([]agent.InstanceInfo, error) {
	req, err := http.NewRequestWithContext(ctx, http.MethodGet, c.BaseURL+"/v1/host/instances", nil)
	if err != nil {
		return nil, err
	}
	controlauth.Add(req, c.Token)
	res, err := c.client().Do(req)
	if err != nil {
		return nil, err
	}
	defer res.Body.Close()
	if res.StatusCode >= 300 {
		return nil, fmt.Errorf("agent instances: %s: %s", res.Status, readErr(res.Body))
	}
	var out struct {
		Instances []agent.InstanceInfo `json:"instances"`
	}
	if err := json.NewDecoder(res.Body).Decode(&out); err != nil {
		return nil, err
	}
	return out.Instances, nil
}

// SetCordoned toggles admission of new boots/restores on the host.
func (c *AgentClient) SetCordoned(ctx context.Context, cordoned bool) error {
	if cordoned {
		_, err := c.Cordon(ctx)
		return err
	}
	return fmt.Errorf("cordon epoch required; use Uncordon")
}

// Uncordon clears the exact epoch returned by Cordon.
func (c *AgentClient) Uncordon(ctx context.Context, epoch string) error {
	res, err := c.postJSON(ctx, "/v1/host/uncordon", map[string]string{"cordon_epoch": epoch})
	if err != nil {
		return err
	}
	defer res.Body.Close()
	if res.StatusCode >= 300 {
		return fmt.Errorf("agent cordon: %s: %s", res.Status, readErr(res.Body))
	}
	return nil
}

// Cordon rejects new lifecycle operations, waits for in-flight reservations,
// and returns the epoch required for rollback onto this host.
func (c *AgentClient) Cordon(ctx context.Context) (string, error) {
	res, err := c.postJSON(ctx, "/v1/host/cordon", struct{}{})
	if err != nil {
		return "", err
	}
	defer res.Body.Close()
	if res.StatusCode >= 300 {
		return "", fmt.Errorf("agent cordon: %s: %s", res.Status, readErr(res.Body))
	}
	var out struct {
		Epoch string `json:"cordon_epoch"`
	}
	if err := json.NewDecoder(res.Body).Decode(&out); err != nil {
		return "", err
	}
	if out.Epoch == "" {
		return "", fmt.Errorf("agent returned empty cordon epoch")
	}
	return out.Epoch, nil
}

// Sleep snapshots and frees the VMM on this host.
func (c *AgentClient) Sleep(user, app string) error {
	return c.SleepContext(context.Background(), user, app, "")
}

// SleepContext snapshots one generation. Empty gen selects the legacy instance.
func (c *AgentClient) SleepContext(ctx context.Context, user, app, gen string) error {
	return c.SleepWithEpoch(ctx, user, app, gen, "")
}

func (c *AgentClient) SleepWithEpoch(ctx context.Context, user, app, gen, cordonEpoch string) error {
	res, err := c.postJSON(ctx, "/v1/instances/sleep", instanceBody{
		User: user, App: app, Gen: gen, CordonEpoch: cordonEpoch,
	})
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
	return c.EvictContext(context.Background(), user, app, "")
}

// EvictContext evicts one sleeping generation.
func (c *AgentClient) EvictContext(ctx context.Context, user, app, gen string) error {
	return c.EvictWithEpoch(ctx, user, app, gen, "")
}

func (c *AgentClient) EvictWithEpoch(ctx context.Context, user, app, gen, cordonEpoch string) error {
	res, err := c.postJSON(ctx, "/v1/instances/evict", instanceBody{
		User: user, App: app, Gen: gen, CordonEpoch: cordonEpoch,
	})
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
	return c.AdoptContext(context.Background(), user, app, "")
}

// AdoptContext adopts one generation from the shared snapshot store.
func (c *AgentClient) AdoptContext(ctx context.Context, user, app, gen string) (InstanceView, error) {
	return c.adoptContext(ctx, user, app, gen, "")
}

// AdoptForcedContext permits rollback onto a cordoned source host.
func (c *AgentClient) AdoptForcedContext(ctx context.Context, user, app, gen, cordonEpoch string) (InstanceView, error) {
	return c.adoptContext(ctx, user, app, gen, cordonEpoch)
}

// PreflightSnapshot validates sleeping-snapshot compatibility without waking it.
func (c *AgentClient) PreflightSnapshot(ctx context.Context, user, app, gen string) (agent.InstanceInfo, error) {
	res, err := c.postInstance(ctx, "/v1/instances/preflight", user, app, gen)
	if err != nil {
		return agent.InstanceInfo{}, err
	}
	defer res.Body.Close()
	if res.StatusCode >= 300 {
		return agent.InstanceInfo{}, fmt.Errorf("agent preflight: %s: %s", res.Status, readErr(res.Body))
	}
	var info agent.InstanceInfo
	if err := json.NewDecoder(res.Body).Decode(&info); err != nil {
		return agent.InstanceInfo{}, err
	}
	return info, nil
}

// RegisterSleeping creates a durable host inventory claim without waking.
func (c *AgentClient) RegisterSleeping(ctx context.Context, user, app, gen string) (agent.InstanceInfo, error) {
	res, err := c.postInstance(ctx, "/v1/instances/register-sleeping", user, app, gen)
	if err != nil {
		return agent.InstanceInfo{}, err
	}
	defer res.Body.Close()
	if res.StatusCode >= 300 {
		return agent.InstanceInfo{}, fmt.Errorf("agent register sleeping: %s: %s", res.Status, readErr(res.Body))
	}
	var info agent.InstanceInfo
	if err := json.NewDecoder(res.Body).Decode(&info); err != nil {
		return agent.InstanceInfo{}, err
	}
	return info, nil
}

func (c *AgentClient) adoptContext(ctx context.Context, user, app, gen, cordonEpoch string) (InstanceView, error) {
	res, err := c.postJSON(ctx, "/v1/instances/adopt", instanceBody{
		User: user, App: app, Gen: gen, CordonEpoch: cordonEpoch,
	})
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
	return c.StatusContext(context.Background(), user, app, "")
}

// StatusGen is Status with an optional generation.
func (c *AgentClient) StatusGen(user, app, gen string) (InstanceView, bool, error) {
	return c.StatusContext(context.Background(), user, app, gen)
}

// StatusContext is StatusGen with cancellation.
func (c *AgentClient) StatusContext(ctx context.Context, user, app, gen string) (InstanceView, bool, error) {
	u, err := url.Parse(c.BaseURL + "/v1/instances/status")
	if err != nil {
		return InstanceView{}, false, err
	}
	q := u.Query()
	q.Set("user", user)
	q.Set("app", app)
	if gen != "" {
		q.Set("gen", gen)
	}
	u.RawQuery = q.Encode()
	req, err := http.NewRequestWithContext(ctx, http.MethodGet, u.String(), nil)
	if err != nil {
		return InstanceView{}, false, err
	}
	controlauth.Add(req, c.Token)
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
func (c *AgentClient) Stop(user, app, gen string) error {
	return c.StopContext(context.Background(), user, app, gen)
}

// StopContext destroys one generation with cancellation.
func (c *AgentClient) StopContext(ctx context.Context, user, app, gen string) error {
	res, err := c.postInstance(ctx, "/v1/instances/stop", user, app, gen)
	if err != nil {
		return err
	}
	defer res.Body.Close()
	if res.StatusCode >= 300 {
		return fmt.Errorf("agent stop: %s: %s", res.Status, readErr(res.Body))
	}
	return nil
}

// SetNoIdleContext changes the active-operation hold without booting or waking.
func (c *AgentClient) SetNoIdleContext(ctx context.Context, user, app, gen string, noIdle bool) error {
	return c.SetNoIdleWithEpoch(ctx, user, app, gen, noIdle, "")
}

func (c *AgentClient) SetNoIdleWithEpoch(ctx context.Context, user, app, gen string, noIdle bool, cordonEpoch string) error {
	res, err := c.postJSON(ctx, "/v1/instances/no-idle", instanceBody{
		User: user, App: app, Gen: gen, NoIdle: noIdle, CordonEpoch: cordonEpoch,
	})
	if err != nil {
		return err
	}
	defer res.Body.Close()
	if res.StatusCode >= 300 {
		return fmt.Errorf("agent no-idle: %s: %s", res.Status, readErr(res.Body))
	}
	return nil
}

// AgentControl adapts AgentClient to cutover.Instances.
type AgentControl struct {
	Client *AgentClient
}

// Ensure implements cutover.Instances.
func (a AgentControl) Ensure(ctx context.Context, user, app, gen, image, tier string, noIdle bool) error {
	if a.Client == nil {
		return fmt.Errorf("nil agent client")
	}
	_, err := a.Client.EnsureTierContext(ctx, user, app, gen, image, tier, noIdle)
	return err
}

// Stop implements cutover.Instances.
func (a AgentControl) Stop(ctx context.Context, user, app, gen string) error {
	if a.Client == nil {
		return fmt.Errorf("nil agent client")
	}
	return a.Client.StopContext(ctx, user, app, gen)
}

// SetNoIdle changes the active-operation hold.
func (a AgentControl) SetNoIdle(ctx context.Context, user, app, gen string, noIdle bool) error {
	if a.Client == nil {
		return fmt.Errorf("nil agent client")
	}
	return a.Client.SetNoIdleContext(ctx, user, app, gen, noIdle)
}

func readErr(r io.Reader) string {
	b, _ := io.ReadAll(io.LimitReader(r, 512))
	return string(bytes.TrimSpace(b))
}
