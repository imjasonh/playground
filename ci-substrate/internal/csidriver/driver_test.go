package csidriver_test

import (
	"context"
	"errors"
	"net"
	"os"
	"os/exec"
	"path/filepath"
	"runtime/debug"
	"sync"
	"testing"

	repb "github.com/bazelbuild/remote-apis/build/bazel/remote/execution/v2"
	"github.com/container-storage-interface/spec/lib/go/csi"
	"google.golang.org/grpc"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/credentials/insecure"
	"google.golang.org/grpc/metadata"
	"google.golang.org/grpc/status"
	"google.golang.org/grpc/test/bufconn"

	"github.com/imjasonh/playground/ci-substrate/internal/casfs"
	"github.com/imjasonh/playground/ci-substrate/internal/csidriver"
	"github.com/imjasonh/playground/ci-substrate/internal/digest"
	"github.com/imjasonh/playground/ci-substrate/internal/tenant"
	"github.com/imjasonh/playground/ci-substrate/internal/tree"
)

// memFetcher serves blobs from memory and records the token each read
// carried, since the driver must fetch as the volume's tenant.
type memFetcher struct {
	mu     sync.Mutex
	blobs  map[string][]byte
	tokens map[string]bool
}

func newMemFetcher() *memFetcher {
	return &memFetcher{blobs: map[string][]byte{}, tokens: map[string]bool{}}
}

func (m *memFetcher) put(b []byte) *repb.Digest {
	d := digest.FromBytes(b)
	m.blobs[digest.Key(d)] = b
	return d
}

// saw reports whether a read carried token.
func (m *memFetcher) saw(token string) bool {
	m.mu.Lock()
	defer m.mu.Unlock()
	return m.tokens[token]
}

func (m *memFetcher) Fetch(ctx context.Context, _ string, d *repb.Digest) ([]byte, error) {
	m.mu.Lock()
	defer m.mu.Unlock()
	// The driver's fetcher is called from the FUSE server with the token on
	// the outgoing metadata, which a server would see as incoming.
	m.tokens[outgoingToken(ctx)] = true
	b, ok := m.blobs[digest.Key(d)]
	if !ok {
		return nil, os.ErrNotExist
	}
	return b, nil
}

// outgoingToken is the tenant token a client call would send.
func outgoingToken(ctx context.Context) string {
	md, _ := metadata.FromOutgoingContext(ctx)
	if vals := md.Get(tenant.MetadataKey); len(vals) > 0 {
		return vals[0]
	}
	return ""
}

// fakeMount records mounts instead of mounting.
type fakeMount struct {
	mu        sync.Mutex
	mounted   map[string]string // dir -> instance
	unmounted []string
	fetchers  map[string]tree.Fetcher
}

func newFakeMount() *fakeMount {
	return &fakeMount{mounted: map[string]string{}, fetchers: map[string]tree.Fetcher{}}
}

func (f *fakeMount) mount(dir string, fetcher tree.Fetcher, instance string) (csidriver.Unmounter, error) {
	f.mu.Lock()
	defer f.mu.Unlock()
	f.mounted[dir] = instance
	f.fetchers[dir] = fetcher
	return unmountFunc(func() error {
		f.mu.Lock()
		defer f.mu.Unlock()
		delete(f.mounted, dir)
		f.unmounted = append(f.unmounted, dir)
		return nil
	}), nil
}

type unmountFunc func() error

// actorUID and otherUID are actors' uids; the volume of an actor is named
// substrate-<uid>-inputs, as ateapi names it.
const (
	actorUID = "11111111-2222-3333-4444-555555555555"
	otherUID = "99999999-8888-7777-6666-555555555555"
)

func volumeFor(uid string) string { return "substrate-" + uid + "-inputs" }

// directory is a fake ActorDirectory: the atespaces and uids it holds, or an
// error for every question.
type directory struct {
	actors map[string]string // uid -> atespace
	err    error
}

func (d directory) InAtespace(_ context.Context, atespace, uid string) (bool, error) {
	return d.err == nil && d.actors[uid] == atespace, d.err
}

func actors() directory {
	return directory{actors: map[string]string{actorUID: "tenant-a", otherUID: "tenant-b"}}
}

func (u unmountFunc) Unmount() error { return u() }

type clients struct {
	identity   csi.IdentityClient
	controller csi.ControllerClient
	node       csi.NodeClient
}

func serve(t *testing.T, cfg csidriver.Config) (*csidriver.Driver, clients) {
	t.Helper()
	d, err := csidriver.New(cfg)
	if err != nil {
		t.Fatal(err)
	}
	lis := bufconn.Listen(1 << 20)
	srv := grpc.NewServer()
	d.Register(srv)
	go srv.Serve(lis)
	t.Cleanup(srv.Stop)
	conn, err := grpc.NewClient("passthrough:///bufconn",
		grpc.WithContextDialer(func(context.Context, string) (net.Conn, error) { return lis.Dial() }),
		grpc.WithTransportCredentials(insecure.NewCredentials()))
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { conn.Close() })
	return d, clients{identity: csi.NewIdentityClient(conn), controller: csi.NewControllerClient(conn), node: csi.NewNodeClient(conn)}
}

func mountCap() *csi.VolumeCapability {
	return &csi.VolumeCapability{
		AccessMode: &csi.VolumeCapability_AccessMode{Mode: csi.VolumeCapability_AccessMode_SINGLE_NODE_WRITER},
		AccessType: &csi.VolumeCapability_Mount{Mount: &csi.VolumeCapability_MountVolume{}},
	}
}

func tenants() *tenant.Registry {
	r := tenant.NewRegistry()
	r.Allow("tok-a", "tenant-a", "shared")
	r.Allow("tok-b", "tenant-b", "shared")
	return r
}

func TestIdentity(t *testing.T) {
	_, c := serve(t, csidriver.Config{NodeID: "node-1", Fetcher: newMemFetcher(), Tenants: tenants(), Actors: actors(), Mount: newFakeMount().mount})
	info, err := c.identity.GetPluginInfo(t.Context(), &csi.GetPluginInfoRequest{})
	if err != nil || info.GetName() != csidriver.DriverName {
		t.Fatalf("GetPluginInfo: %v, %v", info, err)
	}
	caps, err := c.identity.GetPluginCapabilities(t.Context(), &csi.GetPluginCapabilitiesRequest{})
	if err != nil || len(caps.GetCapabilities()) != 1 || caps.GetCapabilities()[0].GetService().GetType() != csi.PluginCapability_Service_CONTROLLER_SERVICE {
		t.Fatalf("GetPluginCapabilities: %v, %v", caps, err)
	}
	ready, err := c.identity.Probe(t.Context(), &csi.ProbeRequest{})
	if err != nil || !ready.GetReady().GetValue() {
		t.Fatalf("Probe: %v, %v", ready, err)
	}
	node, err := c.node.NodeGetInfo(t.Context(), &csi.NodeGetInfoRequest{})
	if err != nil || node.GetNodeId() != "node-1" {
		t.Fatalf("NodeGetInfo: %v, %v", node, err)
	}
	ccaps, err := c.controller.ControllerGetCapabilities(t.Context(), &csi.ControllerGetCapabilitiesRequest{})
	if err != nil || len(ccaps.GetCapabilities()) != 1 || ccaps.GetCapabilities()[0].GetRpc().GetType() != csi.ControllerServiceCapability_RPC_CREATE_DELETE_VOLUME {
		t.Fatalf("ControllerGetCapabilities: %v, %v", ccaps, err)
	}
	ncaps, err := c.node.NodeGetCapabilities(t.Context(), &csi.NodeGetCapabilitiesRequest{})
	if err != nil || len(ncaps.GetCapabilities()) != 0 {
		t.Fatalf("NodeGetCapabilities: %v, %v", ncaps, err)
	}
	if _, err := c.node.NodeStageVolume(t.Context(), &csi.NodeStageVolumeRequest{}); status.Code(err) != codes.Unimplemented {
		t.Fatalf("NodeStageVolume: %v, want Unimplemented", err)
	}
}

func classFor(instance, atespace string) map[string]string {
	return map[string]string{csidriver.InstanceParameter: instance, csidriver.AtespaceParameter: atespace}
}

func TestCreateVolumeNamesTheInstance(t *testing.T) {
	_, c := serve(t, csidriver.Config{NodeID: "node-1", Fetcher: newMemFetcher(), Tenants: tenants(), Actors: actors(), Mount: newFakeMount().mount})
	ctx := t.Context()
	name := volumeFor(actorUID)

	resp, err := c.controller.CreateVolume(ctx, &csi.CreateVolumeRequest{
		Name:               name,
		CapacityRange:      &csi.CapacityRange{RequiredBytes: 1 << 30},
		VolumeCapabilities: []*csi.VolumeCapability{mountCap()},
		Parameters:         classFor("tenant-a", "tenant-a"),
	})
	if err != nil {
		t.Fatal(err)
	}
	if resp.GetVolume().GetVolumeId() != name || resp.GetVolume().GetVolumeContext()[csidriver.InstanceParameter] != "tenant-a" {
		t.Fatalf("volume %v", resp.GetVolume())
	}
	// Creating it again is the same answer.
	again, err := c.controller.CreateVolume(ctx, &csi.CreateVolumeRequest{
		Name:               name,
		VolumeCapabilities: []*csi.VolumeCapability{mountCap()},
		Parameters:         classFor("tenant-a", "tenant-a"),
	})
	if err != nil || again.GetVolume().GetVolumeId() != name {
		t.Fatalf("second CreateVolume: %v, %v", again, err)
	}

	caps := []*csi.VolumeCapability{mountCap()}
	for name, req := range map[string]*csi.CreateVolumeRequest{
		"no name":         {VolumeCapabilities: caps, Parameters: classFor("tenant-a", "tenant-a")},
		"no instance":     {Name: volumeFor(actorUID), VolumeCapabilities: caps, Parameters: map[string]string{csidriver.AtespaceParameter: "tenant-a"}},
		"unknown tenant":  {Name: volumeFor(actorUID), VolumeCapabilities: caps, Parameters: classFor("tenant-z", "tenant-a")},
		"no atespace":     {Name: volumeFor(actorUID), VolumeCapabilities: caps, Parameters: map[string]string{csidriver.InstanceParameter: "tenant-a"}},
		"not an actor's":  {Name: "actor-1-inputs", VolumeCapabilities: caps, Parameters: classFor("tenant-a", "tenant-a")},
		"no capabilities": {Name: volumeFor(actorUID), Parameters: classFor("tenant-a", "tenant-a")},
		"block volume": {Name: volumeFor(actorUID), Parameters: classFor("tenant-a", "tenant-a"), VolumeCapabilities: []*csi.VolumeCapability{{
			AccessType: &csi.VolumeCapability_Block{Block: &csi.VolumeCapability_BlockVolume{}},
		}}},
	} {
		if _, err := c.controller.CreateVolume(ctx, req); status.Code(err) != codes.InvalidArgument {
			t.Errorf("%s: %v, want InvalidArgument", name, err)
		}
	}

	if _, err := c.controller.DeleteVolume(ctx, &csi.DeleteVolumeRequest{VolumeId: name}); err != nil {
		t.Fatal(err)
	}
	valid, err := c.controller.ValidateVolumeCapabilities(ctx, &csi.ValidateVolumeCapabilitiesRequest{VolumeId: "v", VolumeCapabilities: []*csi.VolumeCapability{mountCap()}})
	if err != nil || valid.GetConfirmed() == nil {
		t.Fatalf("ValidateVolumeCapabilities: %v, %v", valid, err)
	}
}

// A StorageClass belongs to one atespace. Substrate lets any template name
// any StorageClass, so a tenant in another atespace that names this one gets
// no volume, and so no view of the tenant's cache.
func TestCreateVolumeRefusesAnotherAtespace(t *testing.T) {
	create := func(dir csidriver.ActorDirectory, uid, class string) error {
		_, c := serve(t, csidriver.Config{NodeID: "node-1", Fetcher: newMemFetcher(), Tenants: tenants(), Actors: dir, Mount: newFakeMount().mount})
		_, err := c.controller.CreateVolume(t.Context(), &csi.CreateVolumeRequest{
			Name:               volumeFor(uid),
			VolumeCapabilities: []*csi.VolumeCapability{mountCap()},
			Parameters:         classFor("tenant-a", class),
		})
		return err
	}
	for name, tc := range map[string]struct {
		dir   csidriver.ActorDirectory
		uid   string
		class string
		want  codes.Code
	}{
		"actor in the class's atespace": {actors(), actorUID, "tenant-a", codes.OK},
		"actor in another atespace":     {actors(), otherUID, "tenant-a", codes.PermissionDenied},
		"actor nobody has heard of":     {actors(), "00000000-0000-0000-0000-000000000000", "tenant-a", codes.PermissionDenied},
		"class names an empty atespace": {actors(), actorUID, "tenant-z", codes.PermissionDenied},
		"directory cannot answer":       {directory{err: errors.New("down")}, actorUID, "tenant-a", codes.Unavailable},
		"directory denies the driver":   {directory{err: status.Error(codes.PermissionDenied, "no role")}, actorUID, "tenant-a", codes.Unavailable},
	} {
		if err := create(tc.dir, tc.uid, tc.class); status.Code(err) != tc.want {
			t.Errorf("%s: %v, want %v", name, err, tc.want)
		}
	}
}

func TestPublishMountsForTheTenant(t *testing.T) {
	fm := newFakeMount()
	f := newMemFetcher()
	d, c := serve(t, csidriver.Config{NodeID: "node-1", Fetcher: f, Tenants: tenants(), Actors: actors(), Mount: fm.mount})
	ctx := t.Context()
	target := filepath.Join(t.TempDir(), "actors", "uid-1", "volumes", "inputs")

	publish := func(volume, instance string) error {
		_, err := c.node.NodePublishVolume(ctx, &csi.NodePublishVolumeRequest{
			VolumeId:         volume,
			TargetPath:       target,
			VolumeCapability: mountCap(),
			VolumeContext:    map[string]string{csidriver.InstanceParameter: instance},
		})
		return err
	}
	if err := publish("actor-1-inputs", "tenant-b"); err != nil {
		t.Fatal(err)
	}
	if fm.mounted[target] != "tenant-b" {
		t.Fatalf("mounted %v", fm.mounted)
	}
	if _, err := os.Stat(target); err != nil {
		t.Fatalf("target path was not created: %v", err)
	}
	// The fetcher the mount got carries tenant-b's token.
	blob := f.put([]byte("x"))
	if _, err := fm.fetchers[target].Fetch(ctx, "tenant-b", blob); err != nil {
		t.Fatal(err)
	}
	if !f.saw("tok-b") || f.saw("tok-a") {
		t.Fatal("fetch did not carry tok-b alone")
	}

	// Publishing the same volume at the same path again is idempotent;
	// another volume at that path is refused.
	if err := publish("actor-1-inputs", "tenant-b"); err != nil {
		t.Fatalf("second publish: %v", err)
	}
	if len(fm.mounted) != 1 {
		t.Fatalf("second publish mounted again: %v", fm.mounted)
	}
	if err := publish("actor-2-inputs", "tenant-b"); status.Code(err) != codes.AlreadyExists {
		t.Fatalf("publish of another volume at the path: %v, want AlreadyExists", err)
	}
	other := filepath.Join(t.TempDir(), "inputs")
	if _, err := c.node.NodePublishVolume(ctx, &csi.NodePublishVolumeRequest{
		VolumeId: "v", TargetPath: other, VolumeCapability: mountCap(),
		VolumeContext: map[string]string{csidriver.InstanceParameter: "tenant-z"},
	}); status.Code(err) != codes.InvalidArgument {
		t.Fatalf("publish for an instance no tenant may use: %v", err)
	}

	if _, err := c.node.NodeUnpublishVolume(ctx, &csi.NodeUnpublishVolumeRequest{VolumeId: "actor-1-inputs", TargetPath: target}); err != nil {
		t.Fatal(err)
	}
	if len(fm.unmounted) != 1 || fm.unmounted[0] != target {
		t.Fatalf("unmounted %v", fm.unmounted)
	}
	if _, err := os.Stat(target); !os.IsNotExist(err) {
		t.Fatalf("target path after unpublish: %v", err)
	}
	// Unpublishing a path nothing serves, such as after a restart, is fine.
	if _, err := c.node.NodeUnpublishVolume(ctx, &csi.NodeUnpublishVolumeRequest{VolumeId: "actor-1-inputs", TargetPath: target}); err != nil {
		t.Fatalf("unpublish of an unserved path: %v", err)
	}

	if err := publish("actor-1-inputs", "tenant-a"); err != nil {
		t.Fatal(err)
	}
	if err := d.Close(); err != nil {
		t.Fatal(err)
	}
	if len(fm.mounted) != 0 {
		t.Fatalf("Close left %v mounted", fm.mounted)
	}
}

// TestPublishServesExecRoots mounts for real: a publish, then the mkdir a
// runner in the sandbox would do, then a read that fetches through the
// driver's fetcher.
func TestPublishServesExecRoots(t *testing.T) {
	if _, err := os.Stat("/dev/fuse"); err != nil {
		t.Skip("/dev/fuse not available")
	}
	if _, err := exec.LookPath("fusermount3"); err != nil {
		if _, err := exec.LookPath("fusermount"); err != nil {
			t.Skip("fusermount not available")
		}
	}
	// The test reads a mount this process serves, which deadlocks if a
	// garbage collection stops the world mid-read.
	debug.SetGCPercent(-1)
	f := newMemFetcher()
	hello := f.put([]byte("from the node's cache"))
	root := f.put(tree.Marshal(&repb.Directory{Files: []*repb.FileNode{{Name: "hello.txt", Digest: hello}}}))
	d, c := serve(t, csidriver.Config{NodeID: "node-1", Fetcher: f, Tenants: tenants(), Actors: actors()})
	t.Cleanup(func() { d.Close() })
	ctx := t.Context()
	target := filepath.Join(t.TempDir(), "inputs")

	if _, err := c.node.NodePublishVolume(ctx, &csi.NodePublishVolumeRequest{
		VolumeId: "actor-1-inputs", TargetPath: target, VolumeCapability: mountCap(),
		VolumeContext: map[string]string{csidriver.InstanceParameter: "tenant-a"},
	}); err != nil {
		t.Fatal(err)
	}
	execRoot := filepath.Join(target, casfs.ExecRootName(root, "job"))
	if err := os.Mkdir(execRoot, 0o755); err != nil {
		t.Fatalf("mkdir exec root on the published volume: %v", err)
	}
	got, err := os.ReadFile(filepath.Join(execRoot, "hello.txt"))
	if err != nil || string(got) != "from the node's cache" {
		t.Fatalf("hello.txt: %q, %v", got, err)
	}
	if !f.saw("tok-a") {
		t.Fatal("reads did not carry tok-a")
	}
	if err := os.Remove(execRoot); err != nil {
		t.Fatal(err)
	}
	if _, err := c.node.NodeUnpublishVolume(ctx, &csi.NodeUnpublishVolumeRequest{VolumeId: "actor-1-inputs", TargetPath: target}); err != nil {
		t.Fatal(err)
	}
	if _, err := os.Stat(target); !os.IsNotExist(err) {
		t.Fatalf("target after unpublish: %v", err)
	}
}
