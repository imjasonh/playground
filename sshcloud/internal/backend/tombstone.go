package backend

import (
	"context"
	"errors"
	"fmt"
	"strconv"
	"strings"

	"google.golang.org/api/compute/v1"
	"google.golang.org/api/googleapi"
)

// InstanceTombstones proves that one immutable GCE instance incarnation no
// longer exists. A missing name or the same name with a different numeric ID
// is proof for the old incarnation; lookup failures are never treated as
// absence.
type InstanceTombstones interface {
	Gone(context.Context, string, string) (bool, error)
}

type GCEInstanceTombstones struct {
	service *compute.Service
	project string
	zone    string
}

func NewGCEInstanceTombstones(ctx context.Context, project, zone string) (*GCEInstanceTombstones, error) {
	if strings.TrimSpace(project) == "" || strings.TrimSpace(zone) == "" {
		return nil, fmt.Errorf("GCE tombstone project and zone are required")
	}
	service, err := compute.NewService(ctx)
	if err != nil {
		return nil, fmt.Errorf("create Compute Engine client: %w", err)
	}
	return &GCEInstanceTombstones{service: service, project: project, zone: zone}, nil
}

func (g *GCEInstanceTombstones) Gone(ctx context.Context, name, instanceID string) (bool, error) {
	if g == nil || g.service == nil {
		return false, fmt.Errorf("GCE tombstone verifier is unavailable")
	}
	if strings.TrimSpace(name) == "" {
		return false, fmt.Errorf("GCE instance name is required")
	}
	expected, err := strconv.ParseUint(instanceID, 10, 64)
	if err != nil || expected == 0 || strconv.FormatUint(expected, 10) != instanceID {
		return false, fmt.Errorf("canonical immutable GCE instance ID is required")
	}
	instance, err := g.service.Instances.Get(g.project, g.zone, name).Context(ctx).Do()
	if err != nil {
		var apiErr *googleapi.Error
		if errors.As(err, &apiErr) && apiErr.Code == 404 {
			return true, nil
		}
		return false, fmt.Errorf("look up GCE instance %s@%s: %w", name, instanceID, err)
	}
	if instance == nil || instance.Id == 0 {
		return false, fmt.Errorf("Compute Engine returned an incomplete instance record for %s", name)
	}
	return instance.Id != expected, nil
}

var _ InstanceTombstones = (*GCEInstanceTombstones)(nil)
