// Package csidriver is the CSI driver that gives a Substrate actor its
// inputs from its own node. It runs on every worker node. When ateapi
// creates an actor from a template with an external volume of this driver's
// StorageClass, CreateVolume names a volume for that actor; when atelet
// starts the actor on a node, NodePublishVolume on that node mounts a casfs
// inputs volume at the path atelet hands it, and atelet binds that path into
// the sandbox. The runner in the sandbox then makes each action's exec root
// with a mkdir, and this process, on the host, loads the tree and fetches
// each file from the node's cascache as the action reads it.
//
// The driver holds the tenant table, as cascache does, and fetches as the
// tenant whose instance the volume's StorageClass names. The sandbox never
// holds the token, and no input byte crosses the sandbox's network path or
// Substrate's egress gateway.
//
// A StorageClass is per tenant, and Substrate lets a template in any atespace
// name any StorageClass, so the driver enforces who may use one. The class
// names its atespace, and CreateVolume denies a volume for an actor that is
// not in that atespace. That check runs where the driver can still refuse:
// the volume is never created, so the actor never resumes with it.
//
// Volumes have no state to provision: a volume is the name of the actor it
// belongs to, and its contents are whatever exec roots the runner has made.
// So CreateVolume and DeleteVolume only validate, and there is no staging.
package csidriver

import (
	"context"
	"errors"
	"fmt"
	"log/slog"
	"os"
	"path/filepath"
	"regexp"
	"sync"
	"syscall"

	"github.com/container-storage-interface/spec/lib/go/csi"
	"google.golang.org/grpc"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"
	"google.golang.org/protobuf/types/known/wrapperspb"

	"github.com/imjasonh/playground/ci-substrate/internal/casfs"
	"github.com/imjasonh/playground/ci-substrate/internal/tenant"
	"github.com/imjasonh/playground/ci-substrate/internal/tree"
)

const (
	// DriverName is the CSI driver name: the StorageClass provisioner and
	// the CSIDriverConfig name.
	DriverName = "casfs.ci-substrate.dev"
	// InstanceParameter is the StorageClass parameter that names the Remote
	// Execution instance a volume serves. Its StorageClass is per tenant.
	InstanceParameter = "instance"
	// AtespaceParameter is the StorageClass parameter that names the one
	// atespace whose actors may have a volume of the class.
	AtespaceParameter = "atespace"
	version           = "v1"
)

// volumeName is how ateapi names the volume of an actor: substrate-<actor
// uid>-<volume name>.
var volumeName = regexp.MustCompile(`^substrate-([0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12})-[a-z0-9]([-a-z0-9]*[a-z0-9])?$`)

// ActorDirectory says where an actor is.
type ActorDirectory interface {
	// InAtespace reports whether the actor with that uid is in the atespace.
	// An error means it could not tell, and is not an answer.
	InAtespace(ctx context.Context, atespace, actorUID string) (bool, error)
}

// Unmounter is a served mount. *fuse.Server is one.
type Unmounter interface {
	Unmount() error
}

// Config wires a Driver.
type Config struct {
	// NodeID is what NodeGetInfo reports: the Kubernetes node name.
	NodeID string
	// Fetcher reads blobs for every volume on this node, usually from the
	// node-local cascache. The driver adds the tenant token per volume.
	Fetcher tree.Fetcher
	// Tenants gives the token for each volume's instance.
	Tenants *tenant.Registry
	// Actors checks that a volume's actor is in its StorageClass's atespace.
	Actors ActorDirectory
	// Mount serves an inputs volume at dir. It defaults to
	// casfs.MountVolume; tests replace it.
	Mount func(dir string, f tree.Fetcher, instance string) (Unmounter, error)
}

// Driver serves the CSI Identity, Controller, and Node services.
type Driver struct {
	csi.UnimplementedIdentityServer
	csi.UnimplementedControllerServer
	csi.UnimplementedNodeServer

	cfg Config

	mu     sync.Mutex
	mounts map[string]mounted // by target path
}

type mounted struct {
	volumeID string
	server   Unmounter
}

// New returns a Driver.
func New(cfg Config) (*Driver, error) {
	if cfg.NodeID == "" || cfg.Fetcher == nil || cfg.Tenants == nil || cfg.Actors == nil {
		return nil, errors.New("csidriver: NodeID, Fetcher, Tenants, and Actors are required")
	}
	if cfg.Mount == nil {
		cfg.Mount = func(dir string, f tree.Fetcher, instance string) (Unmounter, error) {
			return casfs.MountVolume(dir, f, instance)
		}
	}
	return &Driver{cfg: cfg, mounts: map[string]mounted{}}, nil
}

// Register adds the three CSI services to srv.
func (d *Driver) Register(srv *grpc.Server) {
	csi.RegisterIdentityServer(srv, d)
	csi.RegisterControllerServer(srv, d)
	csi.RegisterNodeServer(srv, d)
}

// Close unmounts every volume this process still serves, for a shutdown
// that leaves no mount whose server is gone.
func (d *Driver) Close() error {
	d.mu.Lock()
	defer d.mu.Unlock()
	var errs []error
	for target, m := range d.mounts {
		if err := m.server.Unmount(); err != nil {
			errs = append(errs, fmt.Errorf("unmounting %s: %w", target, err))
		}
		delete(d.mounts, target)
	}
	return errors.Join(errs...)
}

// Identity service.

func (d *Driver) GetPluginInfo(context.Context, *csi.GetPluginInfoRequest) (*csi.GetPluginInfoResponse, error) {
	return &csi.GetPluginInfoResponse{Name: DriverName, VendorVersion: version}, nil
}

func (d *Driver) GetPluginCapabilities(context.Context, *csi.GetPluginCapabilitiesRequest) (*csi.GetPluginCapabilitiesResponse, error) {
	return &csi.GetPluginCapabilitiesResponse{Capabilities: []*csi.PluginCapability{{
		Type: &csi.PluginCapability_Service_{Service: &csi.PluginCapability_Service{Type: csi.PluginCapability_Service_CONTROLLER_SERVICE}},
	}}}, nil
}

func (d *Driver) Probe(context.Context, *csi.ProbeRequest) (*csi.ProbeResponse, error) {
	return &csi.ProbeResponse{Ready: wrapperspb.Bool(true)}, nil
}

// Controller service.

func (d *Driver) ControllerGetCapabilities(context.Context, *csi.ControllerGetCapabilitiesRequest) (*csi.ControllerGetCapabilitiesResponse, error) {
	return &csi.ControllerGetCapabilitiesResponse{Capabilities: []*csi.ControllerServiceCapability{{
		Type: &csi.ControllerServiceCapability_Rpc{Rpc: &csi.ControllerServiceCapability_RPC{Type: csi.ControllerServiceCapability_RPC_CREATE_DELETE_VOLUME}},
	}}}, nil
}

// CreateVolume checks that the request names an instance some tenant may use
// and that the actor it is for is in the StorageClass's atespace, and returns
// a volume named after the request. The volume context carries the instance
// to NodePublishVolume. A denied volume is PermissionDenied; one the driver
// could not check is Unavailable, which ateapi retries.
func (d *Driver) CreateVolume(ctx context.Context, req *csi.CreateVolumeRequest) (*csi.CreateVolumeResponse, error) {
	if req.GetName() == "" {
		return nil, status.Error(codes.InvalidArgument, "volume name is required")
	}
	if err := mountCapabilities(req.GetVolumeCapabilities()); err != nil {
		return nil, err
	}
	instance, err := d.instanceOf(req.GetParameters())
	if err != nil {
		return nil, err
	}
	if err := d.checkAtespace(ctx, req.GetName(), req.GetParameters()); err != nil {
		return nil, err
	}
	return &csi.CreateVolumeResponse{Volume: &csi.Volume{
		VolumeId:      req.GetName(),
		CapacityBytes: req.GetCapacityRange().GetRequiredBytes(),
		VolumeContext: map[string]string{InstanceParameter: instance},
	}}, nil
}

func (d *Driver) DeleteVolume(_ context.Context, req *csi.DeleteVolumeRequest) (*csi.DeleteVolumeResponse, error) {
	if req.GetVolumeId() == "" {
		return nil, status.Error(codes.InvalidArgument, "volume id is required")
	}
	return &csi.DeleteVolumeResponse{}, nil
}

func (d *Driver) ValidateVolumeCapabilities(_ context.Context, req *csi.ValidateVolumeCapabilitiesRequest) (*csi.ValidateVolumeCapabilitiesResponse, error) {
	if req.GetVolumeId() == "" {
		return nil, status.Error(codes.InvalidArgument, "volume id is required")
	}
	if err := mountCapabilities(req.GetVolumeCapabilities()); err != nil {
		return &csi.ValidateVolumeCapabilitiesResponse{Message: err.Error()}, nil
	}
	return &csi.ValidateVolumeCapabilitiesResponse{Confirmed: &csi.ValidateVolumeCapabilitiesResponse_Confirmed{
		VolumeCapabilities: req.GetVolumeCapabilities(),
		VolumeContext:      req.GetVolumeContext(),
	}}, nil
}

// checkAtespace refuses a volume for an actor outside the atespace the
// StorageClass names. It fails closed: a class with no atespace, a name that
// isn't an actor's volume, and a directory that can't answer all refuse.
func (d *Driver) checkAtespace(ctx context.Context, name string, params map[string]string) error {
	atespace := params[AtespaceParameter]
	if atespace == "" {
		return status.Errorf(codes.InvalidArgument, "StorageClass parameter %q is required", AtespaceParameter)
	}
	m := volumeName.FindStringSubmatch(name)
	if m == nil {
		return status.Errorf(codes.InvalidArgument, "volume name %q is not an actor's volume", name)
	}
	in, err := d.cfg.Actors.InAtespace(ctx, atespace, m[1])
	if err != nil {
		return status.Errorf(codes.Unavailable, "checking the atespace of actor %s: %v", m[1], err)
	}
	if !in {
		slog.Warn("refusing a volume for an actor outside the StorageClass's atespace", "volume", name, "atespace", atespace)
		return status.Errorf(codes.PermissionDenied, "actor %s is not in atespace %q, the only one that may use this StorageClass", m[1], atespace)
	}
	return nil
}

// instanceOf reads the instance a volume serves and checks that a tenant
// may use it, since a volume for an instance no token covers could never
// hydrate.
func (d *Driver) instanceOf(params map[string]string) (string, error) {
	instance, ok := params[InstanceParameter]
	if !ok || instance == "" {
		return "", status.Errorf(codes.InvalidArgument, "StorageClass parameter %q is required", InstanceParameter)
	}
	if _, ok := d.cfg.Tenants.TokenFor(instance); !ok {
		return "", status.Errorf(codes.InvalidArgument, "no tenant may use instance %q", instance)
	}
	return instance, nil
}

// mountCapabilities accepts mount volumes of any access mode and refuses
// block volumes, which a filesystem cannot be.
func mountCapabilities(caps []*csi.VolumeCapability) error {
	if len(caps) == 0 {
		return status.Error(codes.InvalidArgument, "volume capabilities are required")
	}
	for _, c := range caps {
		if c.GetBlock() != nil {
			return status.Error(codes.InvalidArgument, "block volumes are not supported")
		}
	}
	return nil
}

// Node service.

func (d *Driver) NodeGetInfo(context.Context, *csi.NodeGetInfoRequest) (*csi.NodeGetInfoResponse, error) {
	return &csi.NodeGetInfoResponse{NodeId: d.cfg.NodeID}, nil
}

// NodeGetCapabilities reports none: the driver stages nothing. A caller that
// tries NodeStageVolume anyway gets Unimplemented.
func (d *Driver) NodeGetCapabilities(context.Context, *csi.NodeGetCapabilitiesRequest) (*csi.NodeGetCapabilitiesResponse, error) {
	return &csi.NodeGetCapabilitiesResponse{}, nil
}

// NodePublishVolume mounts an inputs volume at the target path for the
// volume's instance. A second publish of the same volume at the same path
// succeeds without a second mount. A mount at the path whose server is gone
// (this process restarted) is detached first.
func (d *Driver) NodePublishVolume(_ context.Context, req *csi.NodePublishVolumeRequest) (*csi.NodePublishVolumeResponse, error) {
	volumeID, target := req.GetVolumeId(), req.GetTargetPath()
	if volumeID == "" || target == "" {
		return nil, status.Error(codes.InvalidArgument, "volume id and target path are required")
	}
	if req.GetVolumeCapability() == nil {
		return nil, status.Error(codes.InvalidArgument, "volume capability is required")
	}
	if err := mountCapabilities([]*csi.VolumeCapability{req.GetVolumeCapability()}); err != nil {
		return nil, err
	}
	instance, err := d.instanceOf(req.GetVolumeContext())
	if err != nil {
		return nil, err
	}
	token, _ := d.cfg.Tenants.TokenFor(instance)

	d.mu.Lock()
	defer d.mu.Unlock()
	if m, ok := d.mounts[target]; ok {
		if m.volumeID != volumeID {
			return nil, status.Errorf(codes.AlreadyExists, "%s serves volume %q", target, m.volumeID)
		}
		return &csi.NodePublishVolumeResponse{}, nil
	}
	if err := detachStale(target); err != nil {
		return nil, status.Errorf(codes.Internal, "detaching stale mount at %s: %v", target, err)
	}
	if err := os.MkdirAll(target, 0o755); err != nil {
		return nil, status.Errorf(codes.Internal, "creating %s: %v", target, err)
	}
	server, err := d.cfg.Mount(target, tree.WithToken(d.cfg.Fetcher, token), instance)
	if err != nil {
		return nil, status.Errorf(codes.Internal, "mounting %s: %v", target, err)
	}
	d.mounts[target] = mounted{volumeID: volumeID, server: server}
	slog.Info("published inputs volume", "volume", volumeID, "instance", instance, "target", target)
	return &csi.NodePublishVolumeResponse{}, nil
}

// NodeUnpublishVolume unmounts the volume at the target path and removes
// the path. A path this process does not serve, such as one left by an
// earlier process, is detached if it is a mount point.
func (d *Driver) NodeUnpublishVolume(_ context.Context, req *csi.NodeUnpublishVolumeRequest) (*csi.NodeUnpublishVolumeResponse, error) {
	volumeID, target := req.GetVolumeId(), req.GetTargetPath()
	if volumeID == "" || target == "" {
		return nil, status.Error(codes.InvalidArgument, "volume id and target path are required")
	}
	d.mu.Lock()
	defer d.mu.Unlock()
	if m, ok := d.mounts[target]; ok {
		if err := m.server.Unmount(); err != nil {
			return nil, status.Errorf(codes.Internal, "unmounting %s: %v", target, err)
		}
		delete(d.mounts, target)
	} else if err := detachStale(target); err != nil {
		return nil, status.Errorf(codes.Internal, "detaching %s: %v", target, err)
	}
	if err := os.Remove(target); err != nil && !errors.Is(err, os.ErrNotExist) {
		return nil, status.Errorf(codes.Internal, "removing %s: %v", target, err)
	}
	slog.Info("unpublished inputs volume", "volume", volumeID, "target", target)
	return &csi.NodeUnpublishVolumeResponse{}, nil
}

// detachStale lazily unmounts whatever is mounted at target, if anything.
// A FUSE mount whose server died answers ENOTCONN, and a mount point has a
// different device than its parent; a plain directory is left alone.
func detachStale(target string) error {
	var st, parent syscall.Stat_t
	err := syscall.Lstat(target, &st)
	switch {
	case errors.Is(err, syscall.ENOTCONN):
	case errors.Is(err, os.ErrNotExist):
		return nil
	case err != nil:
		return err
	default:
		if err := syscall.Lstat(filepath.Dir(target), &parent); err != nil {
			return err
		}
		if st.Dev == parent.Dev {
			return nil
		}
	}
	if err := syscall.Unmount(target, syscall.MNT_DETACH); err != nil && !errors.Is(err, syscall.EINVAL) && !errors.Is(err, os.ErrNotExist) {
		return err
	}
	return nil
}
