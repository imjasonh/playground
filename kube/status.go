package kube

import (
	"bytes"
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"reflect"
	"strings"

	"github.com/imjasonh/playground/kube/internal/client"
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

// applyStatus applies the status of an Apply intent's object to its status
// subresource, with the field manager that applied the rest of the object.
// owns reports whether the response to the apply of the rest of the object
// showed that the manager owns status fields, and is nil when that apply was
// skipped. applyStatus records a non-empty status in applied, so a record
// shows that the manager owns status fields.
func (c *controller[T, P]) applyStatus(ctx context.Context, key Key, in intent, manager string, owns *bool, applied map[appliedKey]uint64) error {
	if !in.status {
		return nil
	}
	body, empty, err := statusBody(in)
	if err != nil {
		return err
	}
	m := metaOfAny(in.obj)
	ak := appliedKey{ti: in.ti, key: m.Key(), status: true}
	h := hashOf(body, manager)
	last, ok := c.lastApplied(key, ak)
	skip := ok && last == h && in.observed != nil && matches(in.observed, body)
	if empty {
		// An empty status only gives up status fields that the manager owns.
		// If the rest of the object needed no apply, the last successful
		// reconcile applied it too, and recorded a status only if the
		// manager then owned status fields.
		skip = !ok
		if owns != nil {
			skip = !*owns
		}
	}
	if !skip {
		served, err := c.m.client.Serves(ctx, in.res.apiVersion, in.res.plural+"/status")
		if err != nil {
			return fmt.Errorf("applying status of %v %s: %w", in.ti, m.Key(), err)
		}
		if !served && !empty {
			return fmt.Errorf("applying status of %v %s: the server doesn't serve %s/status in %s", in.ti, m.Key(), in.res.plural, in.res.apiVersion)
		}
		skip = !served
	}
	record := func(result string) {
		if !empty {
			applied[ak] = h
		}
		c.m.metrics.inc("kube_apply_total", "controller", c.name, "result", result)
	}
	if skip {
		record("skipped")
		return nil
	}
	if err := c.m.client.Apply(ctx, in.res.path(m.Namespace, m.Name, "status"), manager, true, body, nil); err != nil {
		// The kind may have stopped serving a status subresource since its
		// discovery results were cached.
		if client.IsNotFound(err) {
			c.m.client.Forget(in.res.apiVersion)
		}
		return fmt.Errorf("applying status of %v %s: %w", in.ti, m.Key(), err)
	}
	record("applied")
	c.log.Debug("applied status", "key", key.String(), "object", in.ti.String()+" "+m.Key().String())
	return nil
}

// fieldManagers is the part of an object that lists the managers of its
// fields.
type fieldManagers struct {
	Metadata struct {
		ManagedFields []struct {
			Manager     string `json:"manager"`
			Operation   string `json:"operation"`
			Subresource string `json:"subresource"`
		} `json:"managedFields"`
	} `json:"metadata"`
}

// ownsStatus reports whether manager owns fields that it applied to the
// status subresource. The API server removes a manager's entry once the
// manager owns no fields.
func (f *fieldManagers) ownsStatus(manager string) bool {
	for _, e := range f.Metadata.ManagedFields {
		if e.Manager == manager && e.Operation == "Apply" && e.Subresource == "status" {
			return true
		}
	}
	return false
}

// statusBody builds the server-side apply document for the status of an
// Apply intent's object, and reports whether the status is empty.
func statusBody(in intent) (map[string]any, bool, error) {
	st, err := statusOf(in.obj)
	if err != nil {
		return nil, false, err
	}
	m := metaOfAny(in.obj)
	meta := map[string]any{"name": m.Name}
	if m.Namespace != "" {
		meta["namespace"] = m.Namespace
	}
	uid := m.UID
	if uid == "" && in.observed != nil {
		uid = metaOfAny(in.observed).UID
	}
	if uid != "" {
		meta["uid"] = uid
	}
	body := map[string]any{"apiVersion": in.ti.apiVersion, "kind": in.ti.kind, "metadata": meta}
	if st != nil {
		body["status"] = st
	}
	return body, st == nil, nil
}

// statusOf returns obj's status as Apply sends it, or nil if the status is
// null or has no fields.
func statusOf(obj any) (any, error) {
	doc, err := toMap(obj)
	if err != nil {
		return nil, err
	}
	st := doc["status"]
	if m, ok := st.(map[string]any); ok && len(m) == 0 {
		return nil, nil
	}
	return st, nil
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
