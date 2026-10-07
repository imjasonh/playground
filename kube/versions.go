package kube

import (
	"context"
	"encoding/json"
	"fmt"
	"net/http"
	"runtime/debug"
	"time"
)

// Version declares another version of the custom type that a controller
// reconciles, for example an older version that clients still use. V is a
// struct for that version: it embeds kube.Object with a tag that names the
// same group and kind and a different version, and declares that version's
// fields:
//
//	type WidgetV1beta1 struct {
//		kube.Object `kube:"group=example.dev,kind=Widget,version=v1beta1,deprecated"`
//		Spec        struct{ Size int `json:"size"` } `json:"spec"`
//	}
//
// The deprecated option makes the API server warn clients that use the
// version. The controller reconciles its own type, which is the version the
// API server stores, and the API server converts objects between versions.
// If *V has these methods, where T is the type the controller reconciles,
// the API server sends conversions to the manager's webhook, which calls
// them:
//
//	func (v *V) ConvertTo(t *T) error   // sets t from v
//	func (v *V) ConvertFrom(t *T) error // sets v from t
//
// Without the methods, the API server converts by changing only the
// apiVersion, which works when the versions have the same fields. Conversion
// can't change metadata.
//
// When the stored version changes, the framework rewrites objects stored in
// older versions and records that in the CustomResourceDefinition. To retire
// a version, first add unserved to its tag: the API server stops serving it,
// and the framework removes field ownership records that name it from every
// object, because they break server-side apply once the version is gone.
// After that release has run, delete the version's kube.Version; the
// framework refuses to remove a version that objects might still depend on.
func Version[V any, PV Resource[V]]() Option {
	return func(o *options) {
		o.versions = append(o.versions, versionOption{
			info:   typeInfoFor[V, PV],
			newObj: func() any { return PV(new(V)) },
		})
	}
}

type versionOption struct {
	info   func() (*typeInfo, error)
	newObj func() any
}

// servedVersion is another version of a controller's type.
type servedVersion struct {
	ti     *typeInfo
	newObj func() any
}

// converter is implemented by other versions of T that convert themselves.
type converter[T any] interface {
	ConvertTo(*T) error
	ConvertFrom(*T) error
}

// prepareVersions checks the controller's other versions and, when any of
// them converts itself, registers the conversion webhook.
func (c *controller[T, P]) prepareVersions(m *Manager) error {
	if c.ti.unserved {
		return fmt.Errorf("kube: %v is the version the API server stores, so it must be served; remove unserved from its tag", c.ti.goType)
	}
	if len(c.opts.versions) == 0 {
		return nil
	}
	if !c.ti.custom {
		return fmt.Errorf("kube.Version: %v is a type that already exists; only types that the program defines can have versions", c.ti)
	}
	seen := map[string]bool{c.ti.version: true}
	for _, vo := range c.opts.versions {
		vti, err := vo.info()
		if err != nil {
			return err
		}
		switch {
		case !vti.custom || vti.group != c.ti.group || vti.kind != c.ti.kind:
			return fmt.Errorf("kube.Version: %v must name the same group and kind as %v", vti.goType, c.ti)
		case vti.scope != c.ti.scope:
			return fmt.Errorf("kube.Version: %v and %v must have the same scope", vti.goType, c.ti.goType)
		case seen[vti.version]:
			return fmt.Errorf("kube.Version: %v declares version %s twice", c.ti, vti.version)
		}
		seen[vti.version] = true
		if _, ok := vo.newObj().(converter[T]); ok {
			c.conversion = true
		}
		c.versions = append(c.versions, servedVersion{ti: vti, newObj: vo.newObj})
	}
	if !c.conversion {
		return nil
	}
	ws := m.webhooks()
	ws.handle(c.conversionPath(), c.serveConversion)
	ws.whenBundleChanges(func(ctx context.Context) error {
		return m.updateConversionBundle(ctx, c.ti, ws.clientConfig(c.conversionPath()))
	})
	return nil
}

func (c *controller[T, P]) conversionPath() string {
	return "/convert/" + c.ti.group + "/" + c.ti.plural
}

// crd describes the CustomResourceDefinition for the controller's type.
func (c *controller[T, P]) crd() crdSpec {
	s := crdSpec{ti: c.ti}
	for _, v := range c.versions {
		s.versions = append(s.versions, v.ti)
	}
	switch {
	case c.conversion:
		s.conversion = map[string]any{
			"strategy": "Webhook",
			"webhook": map[string]any{
				"conversionReviewVersions": []string{"v1"},
				"clientConfig":             c.m.webhooks().clientConfig(c.conversionPath()),
			},
		}
	case len(c.versions) > 0:
		s.conversion = map[string]any{"strategy": "None"}
	}
	return s
}

type conversionReview struct {
	APIVersion string              `json:"apiVersion"`
	Kind       string              `json:"kind"`
	Request    *conversionRequest  `json:"request,omitempty"`
	Response   *conversionResponse `json:"response,omitempty"`
}

type conversionRequest struct {
	UID               string            `json:"uid"`
	DesiredAPIVersion string            `json:"desiredAPIVersion"`
	Objects           []json.RawMessage `json:"objects"`
}

type conversionResponse struct {
	UID              string            `json:"uid"`
	ConvertedObjects []json.RawMessage `json:"convertedObjects"`
	Result           struct {
		Status  string `json:"status"`
		Message string `json:"message,omitempty"`
	} `json:"result"`
}

func (c *controller[T, P]) serveConversion(w http.ResponseWriter, r *http.Request) {
	var review conversionReview
	if err := json.NewDecoder(http.MaxBytesReader(w, r.Body, 64<<20)).Decode(&review); err != nil || review.Request == nil {
		http.Error(w, "the request body must be a ConversionReview", http.StatusBadRequest)
		return
	}
	start := time.Now()
	resp := &conversionResponse{UID: review.Request.UID, ConvertedObjects: []json.RawMessage{}}
	err := func() (err error) {
		defer func() {
			if p := recover(); p != nil {
				c.log.Error("conversion panicked", "panic", p, "stack", string(debug.Stack()))
				err = fmt.Errorf("panic: %v", p)
			}
		}()
		for _, raw := range review.Request.Objects {
			out, err := c.convert(raw, review.Request.DesiredAPIVersion)
			if err != nil {
				return err
			}
			resp.ConvertedObjects = append(resp.ConvertedObjects, out)
		}
		return nil
	}()
	result := "converted"
	if err != nil {
		resp.ConvertedObjects = nil
		resp.Result.Status, resp.Result.Message = "Failure", err.Error()
		result = "failed"
	} else {
		resp.Result.Status = "Success"
	}
	c.m.metrics.inc("kube_webhook_requests_total", "path", r.URL.Path, "result", result)
	c.m.metrics.observe("kube_webhook_duration_seconds", time.Since(start).Seconds(), "path", r.URL.Path)
	w.Header().Set("Content-Type", "application/json")
	_ = json.NewEncoder(w).Encode(conversionReview{APIVersion: review.APIVersion, Kind: review.Kind, Response: resp})
}

// convert converts one object to the desired version, through the version
// the controller reconciles.
func (c *controller[T, P]) convert(raw json.RawMessage, desired string) (json.RawMessage, error) {
	var head struct {
		APIVersion string          `json:"apiVersion"`
		Metadata   json.RawMessage `json:"metadata"`
	}
	if err := json.Unmarshal(raw, &head); err != nil {
		return nil, err
	}
	if head.APIVersion == desired {
		return raw, nil
	}
	from, err := c.versionObject(head.APIVersion)
	if err != nil {
		return nil, err
	}
	if err := json.Unmarshal(raw, from); err != nil {
		return nil, fmt.Errorf("decoding %s: %w", head.APIVersion, err)
	}
	hub, ok := from.(*T)
	if !ok {
		hub = new(T)
		if conv, ok := from.(converter[T]); ok {
			if err := conv.ConvertTo(hub); err != nil {
				return nil, fmt.Errorf("converting %s to %s: %w", head.APIVersion, c.ti.apiVersion, err)
			}
		} else if err := roundTrip(from, hub); err != nil {
			return nil, fmt.Errorf("converting %s to %s: %w", head.APIVersion, c.ti.apiVersion, err)
		}
	}
	var to any = hub
	if desired != c.ti.apiVersion {
		if to, err = c.versionObject(desired); err != nil {
			return nil, err
		}
		if conv, ok := to.(converter[T]); ok {
			if err := conv.ConvertFrom(hub); err != nil {
				return nil, fmt.Errorf("converting %s to %s: %w", c.ti.apiVersion, desired, err)
			}
		} else if err := roundTrip(hub, to); err != nil {
			return nil, fmt.Errorf("converting %s to %s: %w", c.ti.apiVersion, desired, err)
		}
	}
	out, err := generic(to)
	if err != nil {
		return nil, err
	}
	doc, ok := out.(map[string]any)
	if !ok {
		return nil, fmt.Errorf("%s didn't encode to a JSON object", desired)
	}
	doc["apiVersion"], doc["kind"] = desired, c.ti.kind
	doc["metadata"] = head.Metadata
	return json.Marshal(doc)
}

// versionObject returns a new object of the Go type for apiVersion.
func (c *controller[T, P]) versionObject(apiVersion string) (any, error) {
	if apiVersion == c.ti.apiVersion {
		return new(T), nil
	}
	for _, v := range c.versions {
		if v.ti.apiVersion == apiVersion {
			return v.newObj(), nil
		}
	}
	return nil, fmt.Errorf("%s isn't a version of %s", apiVersion, c.ti.kind)
}

// roundTrip copies the fields of from into to by name, for versions that
// don't convert themselves. A field whose value doesn't fit to's field is an
// error, so the API server rejects the request instead of storing an object
// without the field.
func roundTrip(from, to any) error {
	b, err := json.Marshal(from)
	if err != nil {
		return err
	}
	return json.Unmarshal(b, to)
}
