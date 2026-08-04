package backend

import (
	"fmt"
	"os"
	"strings"
	"sync"
)

// HostSet is a mutable hostID → AgentClient map. Orchestrator can Replace it
// when a GCE MIG membership file is refreshed.
type HostSet struct {
	mu          sync.RWMutex
	agents      map[string]*AgentClient
	defaultHost string
}

// NewHostSet copies agents into a HostSet. defaultHost may be empty (first key).
func NewHostSet(agents map[string]*AgentClient, defaultHost string) *HostSet {
	cp := make(map[string]*AgentClient, len(agents))
	for k, v := range agents {
		cp[k] = v
	}
	hs := &HostSet{agents: cp, defaultHost: defaultHost}
	if hs.defaultHost == "" {
		for id := range cp {
			hs.defaultHost = id
			break
		}
	}
	return hs
}

// Get returns the agent client for hostID.
func (h *HostSet) Get(id string) (*AgentClient, bool) {
	if h == nil {
		return nil, false
	}
	h.mu.RLock()
	defer h.mu.RUnlock()
	c, ok := h.agents[id]
	return c, ok
}

// DefaultHost is used when placement has no entry yet.
func (h *HostSet) DefaultHost() string {
	if h == nil {
		return ""
	}
	h.mu.RLock()
	defer h.mu.RUnlock()
	if h.defaultHost != "" {
		if _, ok := h.agents[h.defaultHost]; ok {
			return h.defaultHost
		}
	}
	for id := range h.agents {
		return id
	}
	return ""
}

// Replace swaps the live agent map (MIG refresh).
func (h *HostSet) Replace(agents map[string]*AgentClient) {
	cp := make(map[string]*AgentClient, len(agents))
	for k, v := range agents {
		cp[k] = v
	}
	h.mu.Lock()
	defer h.mu.Unlock()
	h.agents = cp
}

// Len returns the number of known hosts.
func (h *HostSet) Len() int {
	if h == nil {
		return 0
	}
	h.mu.RLock()
	defer h.mu.RUnlock()
	return len(h.agents)
}

// IDs returns known host IDs (order undefined).
func (h *HostSet) IDs() []string {
	if h == nil {
		return nil
	}
	h.mu.RLock()
	defer h.mu.RUnlock()
	ids := make([]string, 0, len(h.agents))
	for id := range h.agents {
		ids = append(ids, id)
	}
	return ids
}

// ParseHostsSpec parses "id=url" pairs separated by commas and/or newlines.
func ParseHostsSpec(s string) (map[string]*AgentClient, error) {
	out := make(map[string]*AgentClient)
	s = strings.TrimSpace(s)
	if s == "" {
		return out, nil
	}
	fields := strings.FieldsFunc(s, func(r rune) bool {
		return r == ',' || r == '\n' || r == '\r'
	})
	for _, part := range fields {
		part = strings.TrimSpace(part)
		if part == "" {
			continue
		}
		id, url, ok := strings.Cut(part, "=")
		id = strings.TrimSpace(id)
		url = strings.TrimSpace(url)
		if !ok || id == "" || url == "" {
			return nil, fmt.Errorf("invalid hosts entry %q (want id=url)", part)
		}
		out[id] = &AgentClient{BaseURL: strings.TrimRight(url, "/")}
	}
	return out, nil
}

// LoadHostsFile reads a hosts spec from path.
func LoadHostsFile(path string) (map[string]*AgentClient, error) {
	b, err := os.ReadFile(path)
	if err != nil {
		return nil, err
	}
	return ParseHostsSpec(string(b))
}
