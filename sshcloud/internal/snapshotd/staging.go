package snapshotd

import (
	"fmt"
	"sync"
)

type StagingLimits struct {
	MaxBytes        int64 `json:"max_bytes"`
	MaxConcurrent   int   `json:"max_concurrent"`
	MaxPerAgent     int   `json:"max_per_agent"`
	MaxRequestBytes int64 `json:"max_request_bytes"`
}

type StagingUsage struct {
	StagingLimits
	UsedBytes     int64 `json:"used_bytes"`
	RetainedBytes int64 `json:"retained_bytes"`
	Active        int   `json:"active"`
}

// StagingGuard is a nonblocking weighted semaphore with an additional exact
// agent-incarnation cap. Rejection happens before an HTTP package body is read.
type StagingGuard struct {
	mu       sync.Mutex
	limits   StagingLimits
	used     int64
	retained int64
	active   int
	perAgent map[string]int
}

func NewStagingGuard(limits StagingLimits) (*StagingGuard, error) {
	if limits.MaxBytes <= 0 || limits.MaxConcurrent <= 0 ||
		limits.MaxPerAgent <= 0 || limits.MaxPerAgent > limits.MaxConcurrent ||
		limits.MaxRequestBytes <= 0 {
		return nil, fmt.Errorf("snapshot staging limits must be positive and per-agent must not exceed global concurrency")
	}
	return &StagingGuard{limits: limits, perAgent: make(map[string]int)}, nil
}

type StagingLease struct {
	guard  *StagingGuard
	agent  string
	weight int64
	once   sync.Once
}

func (g *StagingGuard) TryAcquire(agent string, weight int64) (*StagingLease, string) {
	if g == nil || agent == "" || weight <= 0 {
		return nil, "invalid"
	}
	g.mu.Lock()
	defer g.mu.Unlock()
	switch {
	case weight > g.limits.MaxBytes || g.used > g.limits.MaxBytes-weight:
		return nil, "bytes"
	case g.active >= g.limits.MaxConcurrent:
		return nil, "concurrency"
	case g.perAgent[agent] >= g.limits.MaxPerAgent:
		return nil, "per_agent"
	}
	g.used += weight
	g.active++
	g.perAgent[agent]++
	return &StagingLease{guard: g, agent: agent, weight: weight}, ""
}

func (l *StagingLease) Release() {
	l.release(false)
}

// Abandon releases concurrency but keeps the byte reservation charged when
// plaintext cleanup failed. Startup cleanup is the recovery boundary; keeping
// the reservation prevents residual bytes from defeating the disk bound.
func (l *StagingLease) Abandon() {
	l.release(true)
}

func (l *StagingLease) release(retainBytes bool) {
	if l == nil || l.guard == nil {
		return
	}
	l.once.Do(func() {
		g := l.guard
		g.mu.Lock()
		defer g.mu.Unlock()
		if retainBytes {
			g.retained += l.weight
		} else {
			g.used -= l.weight
		}
		g.active--
		g.perAgent[l.agent]--
		if g.perAgent[l.agent] == 0 {
			delete(g.perAgent, l.agent)
		}
	})
}

func (g *StagingGuard) Usage() StagingUsage {
	if g == nil {
		return StagingUsage{}
	}
	g.mu.Lock()
	defer g.mu.Unlock()
	return StagingUsage{
		StagingLimits: g.limits,
		UsedBytes:     g.used,
		RetainedBytes: g.retained,
		Active:        g.active,
	}
}
