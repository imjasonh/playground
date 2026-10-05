package client

import (
	"context"
	"fmt"
	"slices"
	"strings"
	"sync"
)

// APIResource describes one resource that the API server serves.
type APIResource struct {
	// Name is the plural resource name, for example "deployments".
	Name         string   `json:"name"`
	SingularName string   `json:"singularName"`
	Namespaced   bool     `json:"namespaced"`
	Kind         string   `json:"kind"`
	Verbs        []string `json:"verbs"`
	ShortNames   []string `json:"shortNames"`
}

// NoKindError says the server doesn't serve a kind in an API version.
type NoKindError struct {
	APIVersion, Kind string
}

func (e *NoKindError) Error() string {
	return fmt.Sprintf("the server doesn't serve kind %q in %q", e.Kind, e.APIVersion)
}

type discovery struct {
	mu    sync.Mutex
	lists map[string][]APIResource
}

// Resource finds the resource that serves kind in apiVersion. It caches
// discovery results and refetches once when a kind is missing, so a newly
// installed CustomResourceDefinition is found.
func (c *Client) Resource(ctx context.Context, apiVersion, kind string) (APIResource, error) {
	r, ok, err := c.lookup(ctx, apiVersion, func(r APIResource) bool {
		return r.Kind == kind && !strings.Contains(r.Name, "/")
	})
	if err != nil {
		return APIResource{}, err
	}
	if !ok {
		return APIResource{}, &NoKindError{APIVersion: apiVersion, Kind: kind}
	}
	return r, nil
}

// Serves reports whether the server serves the resource or subresource
// name, such as "deployments/status", in apiVersion. Like Resource, it
// refetches discovery results once when they don't list name.
func (c *Client) Serves(ctx context.Context, apiVersion, name string) (bool, error) {
	_, ok, err := c.lookup(ctx, apiVersion, func(r APIResource) bool { return r.Name == name })
	return ok, err
}

// Forget drops the cached discovery results for apiVersion, so the next
// lookup in it fetches them.
func (c *Client) Forget(apiVersion string) {
	c.disco.mu.Lock()
	defer c.disco.mu.Unlock()
	delete(c.disco.lists, apiVersion)
}

// lookup returns the first resource in apiVersion that match accepts. It
// fetches discovery results, at most once, when none are cached or the cached
// ones have no match.
func (c *Client) lookup(ctx context.Context, apiVersion string, match func(APIResource) bool) (APIResource, bool, error) {
	c.disco.mu.Lock()
	list := c.disco.lists[apiVersion]
	c.disco.mu.Unlock()
	if i := slices.IndexFunc(list, match); i >= 0 {
		return list[i], true, nil
	}
	list, err := c.fetchResources(ctx, apiVersion)
	if err != nil {
		return APIResource{}, false, err
	}
	if i := slices.IndexFunc(list, match); i >= 0 {
		return list[i], true, nil
	}
	return APIResource{}, false, nil
}

func (c *Client) fetchResources(ctx context.Context, apiVersion string) ([]APIResource, error) {
	path := "/apis/" + apiVersion
	if !strings.Contains(apiVersion, "/") {
		path = "/api/" + apiVersion
	}
	var out struct {
		Resources []APIResource `json:"resources"`
	}
	if err := c.Get(ctx, path, &out); err != nil {
		if IsNotFound(err) {
			out.Resources = nil
		} else {
			return nil, fmt.Errorf("discovering %s: %w", apiVersion, err)
		}
	}
	c.disco.mu.Lock()
	defer c.disco.mu.Unlock()
	if c.disco.lists == nil {
		c.disco.lists = map[string][]APIResource{}
	}
	c.disco.lists[apiVersion] = out.Resources
	return out.Resources, nil
}
