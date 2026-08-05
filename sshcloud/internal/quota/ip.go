package quota

import (
	"net"
	"net/netip"
	"sync"
	"time"
)

type IPRateLimiter struct {
	mu     sync.Mutex
	max    int
	window time.Duration
	state  map[netip.Addr]ipWindow
}

type ipWindow struct {
	start time.Time
	count int
}

func NewIPRateLimiter(max int, window time.Duration) *IPRateLimiter {
	return &IPRateLimiter{max: max, window: window, state: make(map[netip.Addr]ipWindow)}
}

func (l *IPRateLimiter) Allow(remote net.Addr, now time.Time) bool {
	if l == nil || l.max <= 0 || l.window <= 0 {
		return true
	}
	addr, ok := remoteIP(remote)
	if !ok {
		return false
	}
	l.mu.Lock()
	defer l.mu.Unlock()
	current := l.state[addr]
	if current.start.IsZero() || !now.Before(current.start.Add(l.window)) {
		current = ipWindow{start: now}
	}
	if current.count >= l.max {
		return false
	}
	current.count++
	l.state[addr] = current
	if len(l.state) > 4096 {
		for ip, window := range l.state {
			if !now.Before(window.start.Add(l.window)) {
				delete(l.state, ip)
			}
		}
	}
	return true
}

func remoteIP(remote net.Addr) (netip.Addr, bool) {
	switch value := remote.(type) {
	case *net.TCPAddr:
		addr, ok := netip.AddrFromSlice(value.IP)
		return addr.Unmap(), ok
	default:
		host, _, err := net.SplitHostPort(remote.String())
		if err != nil {
			return netip.Addr{}, false
		}
		addr, err := netip.ParseAddr(host)
		return addr.Unmap(), err == nil
	}
}
