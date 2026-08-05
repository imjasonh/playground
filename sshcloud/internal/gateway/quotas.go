package gateway

import (
	"context"
	"fmt"
	"net/netip"
	"sync"
	"time"

	"github.com/imjasonh/playground/sshcloud/internal/quota"
)

type Limits struct {
	AppsPerUser    int
	DeploysPerHour int
	JoinsPerIPDay  int
	JoinsPerNetDay int
}

func DefaultLimits() Limits {
	return Limits{AppsPerUser: 5, DeploysPerHour: 10, JoinsPerIPDay: 3, JoinsPerNetDay: 20}
}

func (h *Hub) limits() Limits {
	limits := h.Limits
	defaults := DefaultLimits()
	if limits.AppsPerUser <= 0 {
		limits.AppsPerUser = defaults.AppsPerUser
	}
	if limits.DeploysPerHour <= 0 {
		limits.DeploysPerHour = defaults.DeploysPerHour
	}
	if limits.JoinsPerIPDay <= 0 {
		limits.JoinsPerIPDay = defaults.JoinsPerIPDay
	}
	if limits.JoinsPerNetDay <= 0 {
		limits.JoinsPerNetDay = defaults.JoinsPerNetDay
	}
	return limits
}

func (h *Hub) allowJoin(ctx context.Context, sourceIP, username, keyFingerprint string) error {
	if h.Quotas == nil {
		return nil
	}
	addr, err := netip.ParseAddr(sourceIP)
	if err != nil {
		return fmt.Errorf("invalid client IP")
	}
	addr = addr.Unmap()
	bits := 64
	if addr.Is4() {
		bits = 24
	}
	prefix := netip.PrefixFrom(addr, bits).Masked().String()
	now := time.Now()
	eventID := keyFingerprint + "\x00" + username
	limits := h.limits()
	if err := h.Quotas.Take(ctx, quota.Request{
		Kind: "join_ip", Subject: addr.String(), EventID: eventID, At: now,
		Limit: quota.Limit{Max: limits.JoinsPerIPDay, Window: 24 * time.Hour},
	}); err != nil {
		return err
	}
	return h.Quotas.Take(ctx, quota.Request{
		Kind: "join_prefix", Subject: prefix, EventID: eventID, At: now,
		Limit: quota.Limit{Max: limits.JoinsPerNetDay, Window: 24 * time.Hour},
	})
}

func (h *Hub) allowDeploy(ctx context.Context, user, app, image string) error {
	if h.Quotas == nil {
		return nil
	}
	return h.Quotas.Take(ctx, quota.Request{
		Kind: "deploy", Subject: user, EventID: app + "\x00" + image, At: time.Now(),
		Limit: quota.Limit{Max: h.limits().DeploysPerHour, Window: time.Hour},
	})
}

func (h *Hub) lockUser(user string) func() {
	h.quotaMu.Lock()
	if h.quotaUsers == nil {
		h.quotaUsers = make(map[string]*sync.Mutex)
	}
	lock := h.quotaUsers[user]
	if lock == nil {
		lock = &sync.Mutex{}
		h.quotaUsers[user] = lock
	}
	h.quotaMu.Unlock()
	lock.Lock()
	return lock.Unlock
}
