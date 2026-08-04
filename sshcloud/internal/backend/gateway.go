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

// GatewayClient controls outer sessions during host migration.
type GatewayClient struct {
	BaseURL    string
	Token      string
	HTTPClient *http.Client
}

func (c *GatewayClient) client() *http.Client {
	if c.HTTPClient != nil {
		return c.HTTPClient
	}
	return &http.Client{Timeout: 45 * time.Second}
}

// Freeze disconnects backend hops while preserving matching outer sessions.
func (c *GatewayClient) Freeze(ctx context.Context, user, app, gen string, timeout time.Duration) (string, int, error) {
	var out struct {
		Token    string `json:"token"`
		Sessions int    `json:"sessions"`
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

// Abort kicks sessions associated with a freeze token.
func (c *GatewayClient) Abort(ctx context.Context, token string) error {
	return c.post(ctx, "/v1/sessions/abort", map[string]string{"token": token}, nil)
}

func (c *GatewayClient) post(ctx context.Context, path string, body, out any) error {
	payload, err := json.Marshal(body)
	if err != nil {
		return err
	}
	req, err := http.NewRequestWithContext(ctx, http.MethodPost, strings.TrimRight(c.BaseURL, "/")+path, bytes.NewReader(payload))
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
		return fmt.Errorf("gateway control %s: %s: %s", path, res.Status, readErr(res.Body))
	}
	if out != nil {
		return json.NewDecoder(res.Body).Decode(out)
	}
	return nil
}
