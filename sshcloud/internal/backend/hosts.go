package backend

import (
	"context"
	"fmt"
	"os"
	"sort"
	"strings"
	"sync"
	"time"

	"github.com/imjasonh/playground/sshcloud/internal/agent"
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
	sort.Strings(ids)
	return ids
}

// HostCandidate is a host that can fit one more instance of a tier.
type HostCandidate struct {
	ID        string
	Client    *AgentClient
	Capacity  agent.Capacity
	Remaining agent.Resources
}

// Candidates returns non-cordoned hosts ordered by best-fit bin packing.
func (h *HostSet) Candidates(ctx context.Context, tier string, exclude map[string]bool) ([]HostCandidate, error) {
	need, err := agent.ResourcesForTier(tier)
	if err != nil {
		return nil, err
	}
	return h.CandidatesFor(ctx, need, exclude)
}

// CandidatesFor returns best-fit hosts for an aggregate resource request.
func (h *HostSet) CandidatesFor(ctx context.Context, need agent.Resources, exclude map[string]bool) ([]HostCandidate, error) {
	if h == nil {
		return nil, fmt.Errorf("host set required")
	}
	h.mu.RLock()
	clients := make(map[string]*AgentClient, len(h.agents))
	for id, client := range h.agents {
		if !exclude[id] {
			clients[id] = client
		}
	}
	h.mu.RUnlock()

	type result struct {
		id       string
		client   *AgentClient
		capacity agent.Capacity
		err      error
	}
	results := make(chan result, len(clients))
	for id, client := range clients {
		go func(id string, client *AgentClient) {
			probeCtx, cancel := context.WithTimeout(ctx, 2*time.Second)
			defer cancel()
			capacity, err := client.Capacity(probeCtx)
			results <- result{id: id, client: client, capacity: capacity, err: err}
		}(id, client)
	}
	var candidates []HostCandidate
	var firstErr error
	for range clients {
		result := <-results
		if result.err != nil {
			if firstErr == nil {
				firstErr = result.err
			}
			continue
		}
		if result.capacity.Cordoned {
			continue
		}
		consumed := agent.Resources{
			VCPUs:  result.capacity.Used.VCPUs + result.capacity.Reserved.VCPUs,
			MemMiB: result.capacity.Used.MemMiB + result.capacity.Reserved.MemMiB,
		}
		remaining := agent.Resources{
			VCPUs:  result.capacity.Total.VCPUs - consumed.VCPUs,
			MemMiB: result.capacity.Total.MemMiB - consumed.MemMiB,
		}
		if remaining.VCPUs < need.VCPUs || remaining.MemMiB < need.MemMiB {
			continue
		}
		candidates = append(candidates, HostCandidate{
			ID: result.id, Client: result.client, Capacity: result.capacity, Remaining: remaining,
		})
	}
	sort.Slice(candidates, func(i, j int) bool {
		// Leave the least capacity after placement: pack active VMs together so
		// other hosts can become completely empty and drainable.
		iMem := candidates[i].Remaining.MemMiB - need.MemMiB
		jMem := candidates[j].Remaining.MemMiB - need.MemMiB
		if iMem != jMem {
			return iMem < jMem
		}
		iCPU := candidates[i].Remaining.VCPUs - need.VCPUs
		jCPU := candidates[j].Remaining.VCPUs - need.VCPUs
		if iCPU != jCPU {
			return iCPU < jCPU
		}
		return candidates[i].ID < candidates[j].ID
	})
	if len(candidates) == 0 && firstErr != nil {
		return nil, firstErr
	}
	return candidates, nil
}

// Inventories returns every live host inventory or fails closed.
func (h *HostSet) Inventories(ctx context.Context) (map[string][]agent.InstanceInfo, error) {
	if h == nil {
		return nil, fmt.Errorf("host set required")
	}
	h.mu.RLock()
	clients := make(map[string]*AgentClient, len(h.agents))
	for id, client := range h.agents {
		clients[id] = client
	}
	h.mu.RUnlock()
	type result struct {
		id        string
		instances []agent.InstanceInfo
		err       error
	}
	results := make(chan result, len(clients))
	for id, client := range clients {
		go func(id string, client *AgentClient) {
			probeCtx, cancel := context.WithTimeout(ctx, 2*time.Second)
			defer cancel()
			instances, err := client.Instances(probeCtx)
			results <- result{id: id, instances: instances, err: err}
		}(id, client)
	}
	out := make(map[string][]agent.InstanceInfo, len(clients))
	for range clients {
		result := <-results
		if result.err != nil {
			return nil, fmt.Errorf("host %s inventory: %w", result.id, result.err)
		}
		out[result.id] = result.instances
	}
	return out, nil
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
