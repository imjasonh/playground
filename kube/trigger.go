package kube

import (
	"context"

	"github.com/imjasonh/playground/kube/internal/queue"
)

// Trigger asks for a reconcile of the object of type T with the given
// namespace and name, from code that runs outside that reconcile, such as a
// Serve handler that learns that something outside Kubernetes changed. Leave
// namespace empty for cluster-scoped types. The reconcile runs soon, ahead of
// keys at low priority, even if the object is waiting to retry an error. If
// the object is being reconciled, it's reconciled again afterward. Every
// controller in the program that reconciles T's kind reconciles the object.
//
// Trigger returns true if a reconcile will start after the call. It returns
// false, and does nothing, if this replica doesn't reconcile the object:
//
//   - No controller in the program reconciles T.
//   - The controllers haven't started, or the program is stopping.
//   - The object isn't in the controller's cache, because it doesn't exist,
//     the controller doesn't watch it, or the cache hasn't loaded yet.
//   - Leader election or sharding is on, and another replica holds the
//     object's shard, or this replica is releasing it or has never held a
//     shard.
//
// Trigger doesn't pass the request to the replica that reconciles the
// object. When Trigger returns false, an HTTP handler can answer 503 Service
// Unavailable with a "Connection: close" header, so that the client tries
// again and may reach another replica.
//
// A true result holds even if this replica loses the shard before the
// reconcile starts. The replica that takes the shard queues every object in
// it at low priority, so the triggered object then waits its turn with the
// rest of the shard.
//
// To hand data from a request to the reconcile, keep the data until Get
// shows that the reconcile wrote it, and only then answer the request, or
// answer 503 if that takes too long. Have the reconcile read the data
// without removing it. The framework carries out a reconcile's writes after
// Reconcile returns, and a write can fail. If the shard moves before the
// retry, the retry runs on the next holder of the shard, which doesn't have
// the data.
func Trigger[T any, P Resource[T]](ctx context.Context, namespace, name string) bool {
	s := scopeFrom(ctx, "Trigger")
	ti := typeFor[T, P](s)
	if ti == nil {
		return false
	}
	return s.w.trigger(ti, Key{Namespace: namespace, Name: name})
}

func (m *Manager) trigger(ti *typeInfo, k Key) bool {
	if !m.started.Load() || m.runCtx.Err() != nil {
		return false
	}
	queued := false
	for _, c := range m.controllers {
		if t, ok := c.(interface{ trigger(*typeInfo, Key) bool }); ok && t.trigger(ti, k) {
			queued = true
		}
	}
	return queued
}

func (c *controller[T, P]) trigger(ti *typeInfo, k Key) bool {
	if ti.group != c.ti.group || ti.kind != c.ti.kind {
		return false
	}
	if !c.res.namespaced {
		k.Namespace = ""
	}
	if c.primary.store.get(k) == nil || !c.sh.owns(k) {
		return false
	}
	c.q.Add(k, queue.High)
	return true
}
