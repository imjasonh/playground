// Package genid names deploy generations (microVM instances for one app).
package genid

import (
	"fmt"
	"regexp"
	"strings"
	"time"
)

var generationRE = regexp.MustCompile(`^g[0-9a-f]{1,32}$`)

// New returns a fresh generation id (g + hex timestamp).
func New() string {
	return fmt.Sprintf("g%x", time.Now().UnixNano())
}

// Validate checks a non-empty deploy generation ID.
func Validate(gen string) error {
	if !generationRE.MatchString(gen) {
		return fmt.Errorf("invalid generation %q", gen)
	}
	return nil
}

// AgentApp is the host-agent instance name: plain app, or app.gen.
// gen is not a valid user-chosen ident character set collision (idents are
// [a-z0-9-]; we insert a dot + g-prefix).
func AgentApp(app, gen string) string {
	if gen == "" {
		return app
	}
	return app + "." + gen
}

// SplitAgentApp reverses AgentApp. If no gen suffix, gen is empty.
func SplitAgentApp(agentApp string) (app, gen string) {
	i := strings.LastIndex(agentApp, ".g")
	if i <= 0 {
		return agentApp, ""
	}
	return agentApp[:i], agentApp[i+1:]
}
