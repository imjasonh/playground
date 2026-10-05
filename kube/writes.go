package kube

import (
	"context"
	"encoding/json"
	"errors"
	"maps"
	"slices"
	"time"

	"github.com/imjasonh/playground/kube/internal/client"
)

// written is what the API server said that a write stored: the object, or,
// when gone is set, only that the object with uid no longer exists.
type written struct {
	obj  json.RawMessage
	uid  string
	gone bool
}

// stored reads a write's response. deleted is set for a delete. It returns
// nil if the response doesn't say what the API server stored.
func stored(resp json.RawMessage, deleted bool) *written {
	var r struct {
		Metadata struct {
			UID                        string     `json:"uid"`
			ResourceVersion            string     `json:"resourceVersion"`
			DeletionTimestamp          *time.Time `json:"deletionTimestamp"`
			DeletionGracePeriodSeconds *int64     `json:"deletionGracePeriodSeconds"`
			Finalizers                 []string   `json:"finalizers"`
		} `json:"metadata"`
		Spec struct {
			Finalizers []string `json:"finalizers"`
		} `json:"spec"`
		// Details is set in the Status that some deletes return.
		Details struct {
			UID string `json:"uid"`
		} `json:"details"`
	}
	var te *json.UnmarshalTypeError
	if err := json.Unmarshal(resp, &r); err != nil && !errors.As(err, &te) {
		return nil
	}
	m := r.Metadata
	switch {
	case deleted && m.UID == "" && r.Details.UID != "":
		return &written{uid: r.Details.UID, gone: true}
	case m.UID == "" || m.ResourceVersion == "":
		return nil
	case deleted && m.DeletionTimestamp == nil,
		// The API server deletes an object that's being deleted once no
		// finalizer or grace period holds it, even when the write that
		// releases it is an update. Namespaces hold theirs in the spec.
		m.DeletionTimestamp != nil && len(m.Finalizers) == 0 && len(r.Spec.Finalizers) == 0 &&
			(m.DeletionGracePeriodSeconds == nil || *m.DeletionGracePeriodSeconds == 0):
		return &written{uid: m.UID, gone: true}
	}
	return &written{obj: resp, uid: m.UID}
}

// track runs write, a write of the object of type ti at k. When write
// returns, every cache of that kind shows what it stored, until the cache's
// watch catches up.
func (m *Manager) track(ti *typeInfo, k Key, write func() (*written, error)) error {
	m.mu.Lock()
	caches := slices.AppendSeq(slices.Clone(m.unshared), maps.Values(m.caches))
	m.mu.Unlock()
	var w *written
	for _, c := range caches {
		if cti := c.typeInfo(); cti.apiVersion != ti.apiVersion || cti.kind != ti.kind {
			continue
		}
		if end := c.begin(k); end != nil {
			defer func() { end(w) }()
		}
	}
	var err error
	w, err = write()
	return err
}

// apply writes body to path with a forced server-side apply as manager, and
// decodes the response into out unless out is nil.
func (m *Manager) apply(ctx context.Context, ti *typeInfo, k Key, path, manager string, body, out any) error {
	return m.track(ti, k, func() (*written, error) {
		var resp json.RawMessage
		if err := m.client.Apply(ctx, path, manager, true, body, &resp); err != nil {
			return nil, err
		}
		w := stored(resp, false)
		if out != nil {
			return w, json.Unmarshal(resp, out)
		}
		return w, nil
	})
}

// patch sends a patch of patchType to path, and decodes the response into
// out unless out is nil.
func (m *Manager) patch(ctx context.Context, ti *typeInfo, k Key, path, patchType string, body []byte, out any) error {
	return m.track(ti, k, func() (*written, error) {
		var resp json.RawMessage
		if err := m.client.Patch(ctx, path, patchType, nil, body, &resp); err != nil {
			return nil, err
		}
		w := stored(resp, false)
		if out != nil {
			return w, json.Unmarshal(resp, out)
		}
		return w, nil
	})
}

// delete deletes the object at path. If the delete has a UID precondition
// and finds no object, caches show the object with that UID as gone. A
// conflict doesn't show that the object is gone, because an admission
// webhook can deny a delete with one.
func (m *Manager) delete(ctx context.Context, ti *typeInfo, k Key, path string, opts client.DeleteOptions) error {
	return m.track(ti, k, func() (*written, error) {
		var resp json.RawMessage
		err := m.client.DeleteInto(ctx, path, opts, &resp)
		switch {
		case err == nil:
			return stored(resp, true), nil
		case opts.UID != "" && client.IsNotFound(err):
			return &written{uid: opts.UID, gone: true}, err
		}
		return nil, err
	})
}
