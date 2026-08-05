package quota

import (
	"net"
	"testing"
	"time"
)

func TestIPRateLimiterCanonicalizesAndResets(t *testing.T) {
	t.Parallel()
	limiter := NewIPRateLimiter(2, time.Minute)
	now := time.Unix(100, 0)
	ip4 := &net.TCPAddr{IP: net.ParseIP("192.0.2.1"), Port: 22}
	mapped := &net.TCPAddr{IP: net.ParseIP("::ffff:192.0.2.1"), Port: 23}
	if !limiter.Allow(ip4, now) || !limiter.Allow(mapped, now) {
		t.Fatal("initial canonical requests rejected")
	}
	if limiter.Allow(ip4, now) {
		t.Fatal("rate limit not enforced")
	}
	if !limiter.Allow(ip4, now.Add(time.Minute)) {
		t.Fatal("window did not reset")
	}
	if !limiter.Allow(&net.TCPAddr{IP: net.ParseIP("192.0.2.2"), Port: 22}, now) {
		t.Fatal("independent IP was coupled")
	}
}
