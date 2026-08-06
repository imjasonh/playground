package backend

import (
	"context"
	"net/http"
	"time"

	"github.com/imjasonh/playground/sshcloud/internal/controlauth"
)

// GatewayClient controls outer sessions during host migration.
type GatewayClient struct {
	BaseURL          string
	ControlClient    *controlauth.Client
	HTTPClient       *http.Client
	InsecureLoopback bool
}

func (c *GatewayClient) kernel() controlHTTPKernel {
	return controlHTTPKernel{
		baseURL: c.BaseURL, controlClient: c.ControlClient, httpClient: c.HTTPClient,
		insecureLoopback: c.InsecureLoopback, timeout: 45 * time.Second,
	}
}

// Freeze disconnects backend hops while preserving matching outer sessions.
func (c *GatewayClient) Freeze(ctx context.Context, user, app, gen string, timeout time.Duration) (string, int, error) {
	var out struct {
		Token    string    `json:"token"`
		Sessions int       `json:"sessions"`
		Deadline time.Time `json:"deadline"`
	}
	err := c.post(ctx, "/v1/sessions/freeze", map[string]any{
		"user": user, "app": app, "gen": gen, "timeout_ms": timeout.Milliseconds(),
	}, &out)
	return out.Token, out.Sessions, err
}

// Thaw reconnects sessions associated with a freeze token.
func (c *GatewayClient) Thaw(ctx context.Context, token string) error {
	return c.post(ctx, "/v1/sessions/thaw", map[string]string{"token": token}, nil)
}

func (c *GatewayClient) post(ctx context.Context, path string, body, out any) error {
	return c.kernel().json(
		ctx, http.MethodPost, path, "gateway control "+path, body, out, nil,
	)
}
