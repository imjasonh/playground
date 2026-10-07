package kube

import (
	"bytes"
	"context"
	"encoding/json"
	"fmt"
	"net/http"
	"runtime/debug"
	"time"

	"github.com/imjasonh/playground/kube/internal/jsonpatch"
)

// Validator is implemented by reconcilers, and by handlers passed to
// Webhooks, that check objects before the API server stores them, for rules
// that a field tag can't express, such as one field's limit depending on
// another. The framework registers a validating admission webhook for the
// type and calls Validate for every create and update, on every replica.
type Validator[T any] interface {
	// Validate returns an error to reject obj. The person or program that
	// made the request sees the error's message. On a create, and on an
	// update of an object that doesn't decode as T, old is nil. Validate can
	// read with Get, List, and Fetch, but can't change anything.
	Validate(ctx context.Context, obj, old *T) error
}

// Defaulter is implemented by reconcilers, and by handlers passed to
// Webhooks, that change objects before the API server stores them, for
// example to fill in defaults that depend on other fields. The framework
// registers a mutating admission webhook for the type and calls Default for
// every create and update, on every replica.
type Defaulter[T any] interface {
	// Default changes obj in place. The framework sends the API server a
	// patch of only the fields that changed, so fields that T doesn't
	// declare keep their values. On a create, and on an update of an object
	// that doesn't decode as T, old is nil. On an update, change only fields
	// that an update may change: a Pod's containers, for example, are fixed
	// once it exists. Returning an error rejects obj.
	Default(ctx context.Context, obj, old *T) error
}

// Webhooks returns a Controller that serves admission webhooks for T without
// reconciling it, for a type that another program reconciles, such as Pods.
// h implements Validator[T], Defaulter[T], or both. To validate or default a
// type that a controller reconciles, add the methods to its reconciler
// instead.
func Webhooks[T any, P Resource[T]](h any) Controller {
	return &webhookController[T, P]{h: h}
}

type webhookController[T any, P Resource[T]] struct {
	h  any
	ti *typeInfo
}

func (w *webhookController[T, P]) prepare(ctx context.Context, m *Manager) error {
	ti, err := typeInfoFor[T, P]()
	if err != nil {
		return err
	}
	w.ti = ti
	v, _ := w.h.(Validator[T])
	d, _ := w.h.(Defaulter[T])
	if v == nil && d == nil {
		return fmt.Errorf("kube.Webhooks[%s]: %T has neither a Validate(context.Context, *%s, *%s) error method nor a Default(context.Context, *%s) error method",
			ti.kind, w.h, ti.goType.Name(), ti.goType.Name(), ti.goType.Name())
	}
	return registerAdmission[T, P](ctx, m, ti, v, d)
}

func (w *webhookController[T, P]) describe() (declared, error) {
	ti, err := typeInfoFor[T, P]()
	return declared{ti: ti, webhooks: true}, err
}

func (w *webhookController[T, P]) setup(context.Context, *Manager) error { return nil }
func (w *webhookController[T, P]) run(context.Context) error             { return nil }
func (w *webhookController[T, P]) reconciles() bool                      { return false }
func (w *webhookController[T, P]) synced() bool                          { return true }
func (w *webhookController[T, P]) controllerName() string {
	if w.ti == nil {
		return "webhooks"
	}
	return "webhooks-" + w.ti.singular
}

// registerAdmission registers the validating and mutating webhooks for T
// that v and d implement. Either may be nil.
func registerAdmission[T any, P Resource[T]](ctx context.Context, m *Manager, ti *typeInfo, v Validator[T], d Defaulter[T]) error {
	if v == nil && d == nil {
		return nil
	}
	res, err := m.resolve(ctx, ti)
	if err != nil {
		return fmt.Errorf("webhooks for %v: %w", ti, err)
	}
	ws := m.webhooks()
	register := func(mutating bool, kind string, h func(context.Context, *admissionRequest) *admissionResponse) error {
		path := admissionPath(kind, ti, res.plural)
		hook := ws.admissionRule(ti, res, !ti.custom)
		if err := ws.addAdmission(mutating, hook["name"].(string), path, hook); err != nil {
			return err
		}
		ws.handle(path, func(w http.ResponseWriter, r *http.Request) { serveAdmission(w, r, m, ti, h) })
		return nil
	}
	if v != nil {
		if err := register(false, "validate", func(ctx context.Context, req *admissionRequest) *admissionResponse {
			return validate[T, P](ctx, m, ti, v, req)
		}); err != nil {
			return err
		}
	}
	if d != nil {
		if err := register(true, "mutate", func(ctx context.Context, req *admissionRequest) *admissionResponse {
			return mutate[T, P](ctx, m, ti, d, req)
		}); err != nil {
			return err
		}
	}
	return nil
}

type admissionReview struct {
	APIVersion string             `json:"apiVersion"`
	Kind       string             `json:"kind"`
	Request    *admissionRequest  `json:"request,omitempty"`
	Response   *admissionResponse `json:"response,omitempty"`
}

type admissionRequest struct {
	UID       string          `json:"uid"`
	Operation string          `json:"operation"`
	Namespace string          `json:"namespace,omitempty"`
	Name      string          `json:"name,omitempty"`
	Object    json.RawMessage `json:"object,omitempty"`
	OldObject json.RawMessage `json:"oldObject,omitempty"`
}

type admissionResponse struct {
	UID       string        `json:"uid"`
	Allowed   bool          `json:"allowed"`
	Result    *statusResult `json:"status,omitempty"`
	PatchType string        `json:"patchType,omitempty"`
	Patch     []byte        `json:"patch,omitempty"`
}

type statusResult struct {
	Code    int32  `json:"code"`
	Reason  string `json:"reason,omitempty"`
	Message string `json:"message"`
}

func deny(err error) *admissionResponse {
	return &admissionResponse{Result: &statusResult{Code: http.StatusForbidden, Reason: "Forbidden", Message: err.Error()}}
}

func serveAdmission(w http.ResponseWriter, r *http.Request, m *Manager, ti *typeInfo, h func(context.Context, *admissionRequest) *admissionResponse) {
	var review admissionReview
	if err := json.NewDecoder(http.MaxBytesReader(w, r.Body, 16<<20)).Decode(&review); err != nil || review.Request == nil {
		http.Error(w, "the request body must be an AdmissionReview", http.StatusBadRequest)
		return
	}
	ctx, cancel := context.WithTimeout(r.Context(), 10*time.Second)
	defer cancel()
	start := time.Now()
	resp := func() (resp *admissionResponse) {
		defer func() {
			if p := recover(); p != nil {
				m.log.Error("webhook panicked", "type", ti.String(), "panic", p, "stack", string(debug.Stack()))
				resp = deny(fmt.Errorf("panic: %v", p))
			}
		}()
		return h(ctx, review.Request)
	}()
	resp.UID = review.Request.UID
	result := "allowed"
	if !resp.Allowed {
		result = "denied"
	}
	m.metrics.inc("kube_webhook_requests_total", "path", r.URL.Path, "result", result)
	m.metrics.observe("kube_webhook_duration_seconds", time.Since(start).Seconds(), "path", r.URL.Path)
	w.Header().Set("Content-Type", "application/json")
	_ = json.NewEncoder(w).Encode(admissionReview{APIVersion: review.APIVersion, Kind: review.Kind, Response: resp})
}

// decodeAs decodes an object from a webhook request into a new T. As caches
// do, it treats an object with any error as undecodable, because the error
// may have stopped decoding partway.
func decodeAs[T any, P Resource[T]](ti *typeInfo, raw json.RawMessage) (*T, error) {
	if len(raw) == 0 || string(raw) == "null" {
		return nil, nil
	}
	obj := new(T)
	if err := json.Unmarshal(raw, obj); err != nil {
		return nil, err
	}
	o := P(obj).object()
	o.APIVersion, o.Kind = ti.apiVersion, ti.kind
	return obj, nil
}

func validate[T any, P Resource[T]](ctx context.Context, m *Manager, ti *typeInfo, v Validator[T], req *admissionRequest) *admissionResponse {
	obj, err := decodeAs[T, P](ti, req.Object)
	if err != nil || obj == nil {
		return deny(fmt.Errorf("decoding the object: %v", err))
	}
	// Denying updates of an object that doesn't decode would keep anyone
	// from fixing it.
	old, _ := decodeAs[T, P](ti, req.OldObject)
	ctx, s := newWebhookScope(ctx, m)
	defer s.cancel(nil)
	err = v.Validate(ctx, obj, old)
	if s.err != nil {
		err = s.err
	}
	if err != nil {
		return deny(err)
	}
	return &admissionResponse{Allowed: true}
}

func mutate[T any, P Resource[T]](ctx context.Context, m *Manager, ti *typeInfo, d Defaulter[T], req *admissionRequest) *admissionResponse {
	obj, err := decodeAs[T, P](ti, req.Object)
	if err != nil || obj == nil {
		return deny(fmt.Errorf("decoding the object: %v", err))
	}
	// As in validate.
	old, _ := decodeAs[T, P](ti, req.OldObject)
	before, err := generic(obj)
	if err != nil {
		return deny(err)
	}
	ctx, s := newWebhookScope(ctx, m)
	defer s.cancel(nil)
	err = d.Default(ctx, obj, old)
	if s.err != nil {
		err = s.err
	}
	if err != nil {
		return deny(err)
	}
	after, err := generic(obj)
	if err != nil {
		return deny(err)
	}
	var doc any
	dec := json.NewDecoder(bytes.NewReader(req.Object))
	dec.UseNumber()
	if err := dec.Decode(&doc); err != nil {
		return deny(fmt.Errorf("decoding the object: %w", err))
	}
	ops := jsonpatch.Diff(doc, jsonpatch.Overlay(doc, before, after))
	if len(ops) == 0 {
		return &admissionResponse{Allowed: true}
	}
	patch, err := json.Marshal(ops)
	if err != nil {
		return deny(err)
	}
	return &admissionResponse{Allowed: true, PatchType: "JSONPatch", Patch: patch}
}

// generic encodes v and decodes it into map[string]any and friends, keeping
// numbers exact.
func generic(v any) (any, error) {
	b, err := json.Marshal(v)
	if err != nil {
		return nil, err
	}
	dec := json.NewDecoder(bytes.NewReader(b))
	dec.UseNumber()
	var out any
	return out, dec.Decode(&out)
}
