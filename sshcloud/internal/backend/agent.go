package backend

import (
	"context"
	"fmt"
	"net/http"
	"net/url"
	"time"

	"github.com/imjasonh/playground/sshcloud/internal/agent"
	"github.com/imjasonh/playground/sshcloud/internal/controlauth"
)

// AgentClient talks to a host agent's HTTP API.
type AgentClient struct {
	BaseURL          string
	InstanceName     string
	InstanceID       string
	ControlClient    *controlauth.Client
	HTTPClient       *http.Client
	InsecureLoopback bool
	ServerVerifier   controlauth.IdentityTokenVerifier
	ServerPolicy     controlauth.VerificationPolicy
}

func (c *AgentClient) kernel() controlHTTPKernel {
	return controlHTTPKernel{
		baseURL: c.BaseURL, controlClient: c.ControlClient, httpClient: c.HTTPClient,
		insecureLoopback: c.InsecureLoopback, timeout: 5 * time.Minute,
	}
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

func (c *AgentClient) postJSON(ctx context.Context, path, operation string, body, out any) error {
	headers := make(http.Header)
	if c.InstanceName == "" || c.InstanceID == "" {
		if !c.InsecureLoopback {
			return fmt.Errorf("expected agent instance name and ID are required")
		}
	} else {
		headers.Set(agent.TargetInstanceNameHeader, c.InstanceName)
		headers.Set(agent.TargetInstanceIDHeader, c.InstanceID)
	}
	return c.kernel().json(ctx, http.MethodPost, path, operation, body, out, headers)
}

// VerifyServerIdentity obtains a fresh audience-bound GCE identity document
// from the agent over the role-authenticated mTLS channel and binds the
// endpoint to the exact instance name and immutable numeric instance ID from
// host discovery. Mutations are bound to that identity in their own request;
// callers retain this independent server proof before committing placement.
func (c *AgentClient) VerifyServerIdentity(ctx context.Context) error {
	if c == nil {
		return fmt.Errorf("agent client is nil")
	}
	if c.InsecureLoopback && c.ServerVerifier == nil {
		return nil
	}
	if c.ServerVerifier == nil || c.ServerPolicy.ServiceAccount == "" ||
		c.ServerPolicy.Audience != controlauth.AudienceAgentServer {
		return fmt.Errorf("agent server identity verifier is not configured")
	}
	if c.InstanceName == "" || c.InstanceID == "" {
		return fmt.Errorf("expected agent instance name and ID are required")
	}
	var proof struct {
		Token string `json:"token"`
	}
	if err := c.kernel().json(
		ctx, http.MethodGet, "/v1/host/identity", "agent server identity", nil, &proof, nil,
	); err != nil {
		return err
	}
	identity, err := c.ServerVerifier.VerifyIdentity(ctx, proof.Token, c.ServerPolicy)
	if err != nil {
		return fmt.Errorf("verify agent server identity: %w", err)
	}
	if identity.InstanceName != c.InstanceName || identity.InstanceID != c.InstanceID {
		return fmt.Errorf(
			"agent endpoint identity is %s@%s, want %s@%s",
			identity.InstanceName, identity.InstanceID, c.InstanceName, c.InstanceID,
		)
	}
	return nil
}

func (c *AgentClient) postInstance(ctx context.Context, path, operation, user, app, gen string, out any) error {
	return c.postJSON(ctx, path, operation, instanceBody{User: user, App: app, Gen: gen}, out)
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
	User             string `json:"user,omitempty"`
	App              string `json:"app,omitempty"`
	Addr             string `json:"addr"`
	GuestIP          string `json:"guest_ip"`
	State            string `json:"state"`
	LastUsed         string `json:"last_used,omitempty"`
	SnapKey          string `json:"snap_key,omitempty"`
	SSHHostPublicKey string `json:"ssh_host_public_key"`
}

// ErrAgentCapacity is returned when a host is full or cordoned.
type ErrAgentCapacity struct {
	HostStatus int
	Message    string
}

func (e ErrAgentCapacity) Error() string   { return e.Message }
func (e ErrAgentCapacity) Temporary() bool { return true }

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
	var out InstanceView
	err := c.postJSON(ctx, "/v1/instances/ensure", "agent ensure", instanceBody{
		User:   user,
		App:    app,
		Gen:    gen,
		Image:  image,
		Tier:   tier,
		NoIdle: noIdle,
	}, &out)
	if err != nil {
		if statusErr, ok := statusError(err); ok &&
			(statusErr.StatusCode == http.StatusConflict ||
				statusErr.StatusCode == http.StatusServiceUnavailable) {
			return InstanceView{}, ErrAgentCapacity{
				HostStatus: statusErr.StatusCode, Message: statusErr.Body,
			}
		}
		return InstanceView{}, err
	}
	if out.Addr == "" {
		return InstanceView{}, fmt.Errorf("agent returned empty addr")
	}
	if out.SSHHostPublicKey == "" {
		return InstanceView{}, fmt.Errorf("agent returned empty SSH host key")
	}
	return out, nil
}

// Capacity returns one host's allocatable resource view.
func (c *AgentClient) Capacity(ctx context.Context) (agent.Capacity, error) {
	var capacity agent.Capacity
	if err := c.kernel().json(
		ctx, http.MethodGet, "/v1/host/capacity", "agent capacity", nil, &capacity, nil,
	); err != nil {
		return agent.Capacity{}, err
	}
	return capacity, nil
}

// Instances returns host inventory for drain/reconciliation.
func (c *AgentClient) Instances(ctx context.Context) ([]agent.InstanceInfo, error) {
	var out struct {
		Instances []agent.InstanceInfo `json:"instances"`
	}
	if err := c.kernel().json(
		ctx, http.MethodGet, "/v1/host/instances", "agent instances", nil, &out, nil,
	); err != nil {
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
	return c.postJSON(
		ctx, "/v1/host/uncordon", "agent uncordon",
		map[string]string{"cordon_epoch": epoch}, nil,
	)
}

// Cordon rejects new lifecycle operations, waits for in-flight reservations,
// and returns the epoch required for rollback onto this host.
func (c *AgentClient) Cordon(ctx context.Context) (string, error) {
	var out struct {
		Epoch string `json:"cordon_epoch"`
	}
	if err := c.postJSON(
		ctx, "/v1/host/cordon", "agent cordon", struct{}{}, &out,
	); err != nil {
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
	return c.postJSON(ctx, "/v1/instances/sleep", "agent sleep", instanceBody{
		User: user, App: app, Gen: gen, CordonEpoch: cordonEpoch,
	}, nil)
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
	return c.postJSON(ctx, "/v1/instances/evict", "agent evict", instanceBody{
		User: user, App: app, Gen: gen, CordonEpoch: cordonEpoch,
	}, nil)
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
	var info agent.InstanceInfo
	if err := c.postInstance(
		ctx, "/v1/instances/preflight", "agent preflight", user, app, gen, &info,
	); err != nil {
		return agent.InstanceInfo{}, err
	}
	return info, nil
}

// RegisterSleeping creates a durable host inventory claim without waking.
func (c *AgentClient) RegisterSleeping(ctx context.Context, user, app, gen string) (agent.InstanceInfo, error) {
	return c.RegisterSleepingWithEpoch(ctx, user, app, gen, "")
}

// RegisterSleepingWithEpoch permits recovery of sleeping inventory on the
// exact cordoned source incarnation that owns the operation epoch.
func (c *AgentClient) RegisterSleepingWithEpoch(
	ctx context.Context,
	user, app, gen, cordonEpoch string,
) (agent.InstanceInfo, error) {
	var info agent.InstanceInfo
	if err := c.postJSON(
		ctx,
		"/v1/instances/register-sleeping",
		"agent register sleeping",
		instanceBody{User: user, App: app, Gen: gen, CordonEpoch: cordonEpoch},
		&info,
	); err != nil {
		return agent.InstanceInfo{}, err
	}
	return info, nil
}

func (c *AgentClient) adoptContext(ctx context.Context, user, app, gen, cordonEpoch string) (InstanceView, error) {
	var out InstanceView
	err := c.postJSON(ctx, "/v1/instances/adopt", "agent adopt", instanceBody{
		User: user, App: app, Gen: gen, CordonEpoch: cordonEpoch,
	}, &out)
	if err != nil {
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
	q := make(url.Values)
	q.Set("user", user)
	q.Set("app", app)
	if gen != "" {
		q.Set("gen", gen)
	}
	var out InstanceView
	err := c.kernel().json(
		ctx, http.MethodGet, "/v1/instances/status?"+q.Encode(),
		"agent status", nil, &out, nil,
	)
	if statusErr, ok := statusError(err); ok && statusErr.StatusCode == http.StatusNotFound {
		return InstanceView{}, false, nil
	}
	if err != nil {
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
	return c.postInstance(ctx, "/v1/instances/stop", "agent stop", user, app, gen, nil)
}

// SetNoIdleContext changes the active-operation hold without booting or waking.
func (c *AgentClient) SetNoIdleContext(ctx context.Context, user, app, gen string, noIdle bool) error {
	return c.SetNoIdleWithEpoch(ctx, user, app, gen, noIdle, "")
}

func (c *AgentClient) SetNoIdleWithEpoch(ctx context.Context, user, app, gen string, noIdle bool, cordonEpoch string) error {
	return c.postJSON(ctx, "/v1/instances/no-idle", "agent no-idle", instanceBody{
		User: user, App: app, Gen: gen, NoIdle: noIdle, CordonEpoch: cordonEpoch,
	}, nil)
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
