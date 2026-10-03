package kube

import (
	"bytes"
	"context"
	"encoding/json"
	"errors"
	"reflect"
	"strings"

	"github.com/imjasonh/playground/kube/internal/subset"
)

// writeStatus fills in the status fields the framework manages, then writes
// the status with server-side apply if it differs from the cached copy.
func (c *controller[T, P]) writeStatus(ctx context.Context, cached, obj *T, reconcileErr error) error {
	if c.ti.status == nil {
		return nil
	}
	m := metaOf[T, P](obj)
	st := reflect.ValueOf(obj).Elem().FieldByIndex(c.ti.status)
	if c.ti.observedGeneration != nil {
		st.FieldByIndex(c.ti.observedGeneration).SetInt(m.Generation)
	}
	if c.ti.conditions != nil {
		conds := st.FieldByIndex(c.ti.conditions).Addr().Interface().(*[]Condition)
		SetCondition(conds, syncedCondition(reconcileErr, m.Generation))
	}
	before, err := json.Marshal(reflect.ValueOf(cached).Elem().FieldByIndex(c.ti.status).Interface())
	if err != nil {
		return err
	}
	after, err := json.Marshal(st.Interface())
	if err != nil {
		return err
	}
	// Record the status before writing it, because the watch event for the
	// write can arrive before the response and mustn't look like someone
	// else's change.
	key := m.Key()
	h := hashJSON(after)
	c.setStatus(key, h, true)
	if bytes.Equal(before, after) {
		return nil
	}
	// A reconcile can clear a status field that another manager writes, so
	// that this write doesn't take it over. Then the status never equals the
	// cached one. It needs no write when the cached status has every field of
	// it, and this controller's last write applied the same status, which
	// leaves no field that the reconcile stopped setting to remove.
	if last, ok := c.lastStatusApply(key); ok && last == h && containsJSON(before, after) {
		return nil
	}
	// The UID keeps status computed for a deleted object from landing on a
	// new object with the same name.
	meta := map[string]any{"name": m.Name, "uid": m.UID}
	if m.Namespace != "" {
		meta["namespace"] = m.Namespace
	}
	body := map[string]any{
		"apiVersion": c.ti.apiVersion,
		"kind":       c.ti.kind,
		"metadata":   meta,
		"status":     json.RawMessage(after),
	}
	var resp json.RawMessage
	err = c.m.client.Apply(ctx, c.res.path(m.Namespace, m.Name, "status"), c.name, true, body, &resp)
	if err != nil {
		if replaced(err) {
			return nil
		}
		return err
	}
	c.m.metrics.inc("kube_status_writes_total", "controller", c.name)
	c.setStatusApply(key, h)
	// The API server can store a different status than was sent, for example
	// with defaults or another manager's fields, so record what it stored.
	// Like the cache, tolerate fields whose JSON type doesn't match.
	var written T
	var te *json.UnmarshalTypeError
	if err := json.Unmarshal(resp, &written); err == nil || errors.As(err, &te) {
		if b, err := json.Marshal(reflect.ValueOf(&written).Elem().FieldByIndex(c.ti.status).Interface()); err == nil {
			c.setStatus(key, hashJSON(b), true)
		}
	}
	return nil
}

// containsJSON reports whether the JSON document have has every field of the
// JSON document want.
func containsJSON(have, want []byte) bool {
	var h, w any
	for _, d := range []struct {
		b []byte
		v *any
	}{{have, &h}, {want, &w}} {
		dec := json.NewDecoder(bytes.NewReader(d.b))
		dec.UseNumber()
		if err := dec.Decode(d.v); err != nil {
			return false
		}
	}
	return subset.Contains(h, w)
}

// syncedCondition reports the result of the last reconcile.
func syncedCondition(err error, generation int64) Condition {
	c := Condition{Type: "Synced", Status: True, Reason: "Reconciled", ObservedGeneration: generation}
	if err != nil {
		c.Status, c.Reason = False, "ReconcileError"
		if IsPermanent(err) {
			c.Reason = "PermanentError"
		}
		c.Message = err.Error()
		if i := strings.IndexByte(c.Message, '\n'); i >= 0 {
			c.Message = c.Message[:i]
		}
		if len(c.Message) > 1024 {
			c.Message = c.Message[:1024]
		}
	}
	return c
}
