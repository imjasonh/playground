package e2e_test

import (
	"bytes"
	"context"
	"crypto/ecdsa"
	"crypto/elliptic"
	"crypto/rand"
	"crypto/sha256"
	"encoding/base64"
	"encoding/json"
	"fmt"
	"io"
	"net/http"
	"strings"
	"testing"
	"time"

	longrunning "cloud.google.com/go/longrunning/autogen/longrunningpb"
	assetpb "github.com/bazelbuild/remote-apis/build/bazel/remote/asset/v1"
	repb "github.com/bazelbuild/remote-apis/build/bazel/remote/execution/v2"
	logstreampb "github.com/bazelbuild/remote-apis/build/bazel/remote/logstream/v1"
	"github.com/google/uuid"
	"github.com/klauspost/compress/zstd"
	"github.com/sethvargo/go-envconfig"
	"google.golang.org/genproto/googleapis/bytestream"
	"google.golang.org/grpc"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/credentials/insecure"
	"google.golang.org/grpc/status"
	"google.golang.org/protobuf/proto"
	"google.golang.org/protobuf/types/known/durationpb"

	workerv1 "github.com/imjasonh/playground/ci-substrate/api/worker/v1"
	"github.com/imjasonh/playground/ci-substrate/internal/cache"
	"github.com/imjasonh/playground/ci-substrate/internal/digest"
	"github.com/imjasonh/playground/ci-substrate/internal/platform"
	"github.com/imjasonh/playground/ci-substrate/internal/remote"
	"github.com/imjasonh/playground/ci-substrate/internal/tenant"
	"github.com/imjasonh/playground/ci-substrate/internal/tree"
)

type e2eConfig struct {
	OriginAddr      string        `env:"CI_SUBSTRATE_E2E_ORIGIN_ADDR"`
	CacheAddr       string        `env:"CI_SUBSTRATE_E2E_CACHE_ADDR"`
	MetricsURL      string        `env:"CI_SUBSTRATE_E2E_CACHE_METRICS_URL"`
	InstanceA       string        `env:"CI_SUBSTRATE_E2E_INSTANCE_A, default=tenant-a"`
	Shared          string        `env:"CI_SUBSTRATE_E2E_SHARED, default=shared"`
	TokenA          string        `env:"CI_SUBSTRATE_E2E_TOKEN_A, default=tok-a"`
	TokenARO        string        `env:"CI_SUBSTRATE_E2E_TOKEN_A_RO, default=tok-a-ro"`
	TokenB          string        `env:"CI_SUBSTRATE_E2E_TOKEN_B, default=tok-b"`
	ActorJWT        bool          `env:"CI_SUBSTRATE_E2E_ACTOR_JWT"`
	EnvTag          string        `env:"CI_SUBSTRATE_E2E_ENV_TAG"`
	EnvMarker       string        `env:"CI_SUBSTRATE_E2E_ENV_MARKER"`
	ExecTimeout     time.Duration `env:"CI_SUBSTRATE_E2E_EXEC_TIMEOUT, default=3m"`
	WorkerPrefix    string        `env:"CI_SUBSTRATE_E2E_WORKER_PREFIX"`
	ExpectInputMode string        `env:"CI_SUBSTRATE_E2E_EXPECT_INPUT_MODE"`
}

type e2eEnv struct {
	e2eConfig
	originConn  *grpc.ClientConn
	cacheConn   *grpc.ClientConn
	origin      *remote.Client
	cacheClient *remote.Client
}

func dialE2E(t *testing.T) *e2eEnv {
	t.Helper()
	var cfg e2eConfig
	if err := envconfig.Process(t.Context(), &cfg); err != nil {
		t.Fatalf("parsing E2E env config: %v", err)
	}
	if cfg.OriginAddr == "" {
		t.Skip("set CI_SUBSTRATE_E2E_ORIGIN_ADDR to run against a live cluster (e2e/run-kind.sh sets this)")
	}
	if cfg.CacheAddr == "" {
		cfg.CacheAddr = cfg.OriginAddr
	}
	originConn, err := grpc.NewClient(cfg.OriginAddr, grpc.WithTransportCredentials(insecure.NewCredentials()))
	if err != nil {
		t.Fatalf("dial origin %s: %v", cfg.OriginAddr, err)
	}
	t.Cleanup(func() { _ = originConn.Close() })

	cacheConn, err := grpc.NewClient(cfg.CacheAddr, grpc.WithTransportCredentials(insecure.NewCredentials()))
	if err != nil {
		t.Fatalf("dial cache %s: %v", cfg.CacheAddr, err)
	}
	t.Cleanup(func() { _ = cacheConn.Close() })

	return &e2eEnv{
		e2eConfig:   cfg,
		originConn:  originConn,
		cacheConn:   cacheConn,
		origin:      remote.NewClient(originConn),
		cacheClient: remote.NewClient(cacheConn),
	}
}

func (e *e2eEnv) ctxA(t *testing.T) context.Context {
	return tenant.Outgoing(t.Context(), e.TokenA)
}

func (e *e2eEnv) ctxARO(t *testing.T) context.Context {
	return tenant.Outgoing(t.Context(), e.TokenARO)
}

func (e *e2eEnv) ctxB(t *testing.T) context.Context {
	return tenant.Outgoing(t.Context(), e.TokenB)
}

// TestE2ECacheReuseAndIsolation verifies node-local cache reuse across tenants
// and isolation of private instances and action caches.
func TestE2ECacheReuseAndIsolation(t *testing.T) {
	e := dialE2E(t)
	ctxA, ctxB := e.ctxA(t), e.ctxB(t)

	content := []byte(fmt.Sprintf("shared build artifact %d", time.Now().UnixNano()))
	d, err := retryCall(func() (*repb.Digest, error) {
		return e.origin.Upload(ctxA, e.Shared, content)
	})
	if err != nil {
		t.Fatalf("tenant A upload: %v", err)
	}

	stats := func() cache.Stats {
		t.Helper()
		if e.MetricsURL == "" {
			return cache.Stats{}
		}
		s, err := fetchCacheStats(e.MetricsURL)
		if err != nil {
			t.Fatalf("fetch cache stats: %v", err)
		}
		return s
	}
	before := stats()

	// Cold read through node-local cascache (one origin fetch).
	if _, err := retryCall(func() ([]byte, error) {
		return e.cacheClient.Fetch(ctxA, e.Shared, d)
	}); err != nil {
		t.Fatalf("tenant A cold read: %v", err)
	}
	afterCold := stats()

	// Warm read as tenant B (node-local hit, zero origin fetches).
	got, err := retryCall(func() ([]byte, error) {
		return e.cacheClient.Fetch(ctxB, e.Shared, d)
	})
	if err != nil {
		t.Fatalf("tenant B warm read: %v", err)
	}
	if !bytes.Equal(got, content) {
		t.Fatalf("tenant B read wrong bytes from cache")
	}
	afterWarm := stats()
	if e.MetricsURL != "" {
		if n := afterCold.OriginFetches - before.OriginFetches; n != 1 {
			t.Errorf("cold read origin fetches = %d, want 1", n)
		}
		if n := afterWarm.OriginFetches - afterCold.OriginFetches; n != 0 {
			t.Errorf("warm read origin fetches = %d, want 0", n)
		}
		if n := afterWarm.Hits - afterCold.Hits; n != 1 {
			t.Errorf("warm read cache hits = %d, want 1", n)
		}
	}

	// Tenant B cannot read through tenant A's private instance or action cache.
	if _, err := e.cacheClient.Fetch(ctxB, e.InstanceA, d); status.Code(err) != codes.PermissionDenied {
		t.Errorf("tenant B reading tenant A's instance: got %v, want PermissionDenied", err)
	}
	action := digest.FromBytes([]byte(fmt.Sprintf("tenant A action %d", time.Now().UnixNano())))
	if err := e.origin.UpdateActionResult(ctxA, e.InstanceA, action, &repb.ActionResult{StdoutDigest: d}); err != nil {
		t.Fatalf("tenant A UpdateActionResult: %v", err)
	}
	if _, _, err := e.origin.GetActionResult(ctxB, e.InstanceA, action); status.Code(err) != codes.PermissionDenied {
		t.Errorf("tenant B GetActionResult in tenant A: got %v, want PermissionDenied", err)
	}
	if _, ok, err := e.origin.GetActionResult(ctxA, e.InstanceA, action); err != nil || !ok {
		t.Errorf("tenant A GetActionResult: ok=%v err=%v", ok, err)
	}
}

// TestE2EZstdCompression verifies Zstd-compressed ByteStream uploads to cas and
// Zstd-compressed BatchReadBlobs through node-local cascache.
func TestE2EZstdCompression(t *testing.T) {
	e := dialE2E(t)
	ctxA := e.ctxA(t)

	raw := bytes.Repeat([]byte("ci-substrate-zstd-e2e-payload-"), 256)
	rawDigest := digest.FromBytes(raw)
	enc, err := zstd.NewWriter(nil, zstd.WithEncoderConcurrency(1))
	if err != nil {
		t.Fatal(err)
	}
	compressed := enc.EncodeAll(raw, nil)
	enc.Close()

	bs := bytestream.NewByteStreamClient(e.originConn)
	ws, err := bs.Write(ctxA)
	if err != nil {
		t.Fatalf("compressed Write: %v", err)
	}
	if err := ws.Send(&bytestream.WriteRequest{
		ResourceName: remote.CompressedWriteResourceName(e.InstanceA, uuid.NewString(), repb.Compressor_ZSTD, rawDigest),
		Data:         compressed,
		FinishWrite:  true,
	}); err != nil {
		t.Fatalf("sending compressed chunk: %v", err)
	}
	wresp, err := ws.CloseAndRecv()
	if err != nil {
		t.Fatalf("closing compressed write: %v", err)
	}
	if wresp.GetCommittedSize() != -1 {
		t.Errorf("compressed write committed_size = %d, want -1", wresp.GetCommittedSize())
	}

	cacheCAS := repb.NewContentAddressableStorageClient(e.cacheConn)
	bresp, err := cacheCAS.BatchReadBlobs(ctxA, &repb.BatchReadBlobsRequest{
		InstanceName:          e.InstanceA,
		Digests:               []*repb.Digest{rawDigest},
		AcceptableCompressors: []repb.Compressor_Value{repb.Compressor_ZSTD},
	})
	if err != nil || len(bresp.GetResponses()) != 1 || bresp.GetResponses()[0].GetStatus().GetCode() != 0 {
		t.Fatalf("compressed BatchReadBlobs via cascache: resp=%v err=%v", bresp, err)
	}
	if got := bresp.GetResponses()[0].GetCompressor(); got != repb.Compressor_ZSTD {
		t.Errorf("cascache BatchReadBlobs compressor = %v, want ZSTD", got)
	}
	dec, err := zstd.NewReader(nil, zstd.WithDecoderConcurrency(1))
	if err != nil {
		t.Fatal(err)
	}
	defer dec.Close()
	gotRaw, err := dec.DecodeAll(bresp.GetResponses()[0].GetData(), nil)
	if err != nil || !bytes.Equal(gotRaw, raw) {
		t.Fatalf("decompressed payload mismatch: err=%v len=%d", err, len(gotRaw))
	}
}

// TestE2EReadOnlyActionCacheAndInlining verifies that a read-only AC token sees
// update_enabled=false in GetCapabilities, is denied UpdateActionResult, and
// receives inlined outputs from GetActionResult.
func TestE2EReadOnlyActionCacheAndInlining(t *testing.T) {
	e := dialE2E(t)
	ctxA, ctxARO := e.ctxA(t), e.ctxARO(t)

	caps := repb.NewCapabilitiesClient(e.originConn)
	roCaps, err := caps.GetCapabilities(ctxARO, &repb.GetCapabilitiesRequest{InstanceName: e.InstanceA})
	if err != nil {
		t.Fatalf("read-only GetCapabilities: %v", err)
	}
	if roCaps.GetCacheCapabilities().GetActionCacheUpdateCapabilities().GetUpdateEnabled() {
		t.Error("read-only token saw update_enabled=true in GetCapabilities")
	}

	payload := []byte(fmt.Sprintf("inline-stdout-%d", time.Now().UnixNano()))
	stdoutD, err := e.origin.Upload(ctxA, e.InstanceA, payload)
	if err != nil {
		t.Fatalf("uploading stdout: %v", err)
	}
	actD := digest.FromBytes([]byte(fmt.Sprintf("ro-ac-action-%d", time.Now().UnixNano())))
	ac := repb.NewActionCacheClient(e.originConn)
	if _, err := ac.UpdateActionResult(ctxARO, &repb.UpdateActionResultRequest{
		InstanceName: e.InstanceA,
		ActionDigest: actD,
		ActionResult: &repb.ActionResult{StdoutDigest: stdoutD},
	}); status.Code(err) != codes.PermissionDenied {
		t.Errorf("read-only UpdateActionResult: got %v, want PermissionDenied", err)
	}
	if _, err := ac.UpdateActionResult(ctxA, &repb.UpdateActionResultRequest{
		InstanceName: e.InstanceA,
		ActionDigest: actD,
		ActionResult: &repb.ActionResult{StdoutDigest: stdoutD},
	}); err != nil {
		t.Fatalf("writable UpdateActionResult: %v", err)
	}
	gotAR, err := ac.GetActionResult(ctxARO, &repb.GetActionResultRequest{
		InstanceName: e.InstanceA,
		ActionDigest: actD,
		InlineStdout: true,
	})
	if err != nil {
		t.Fatalf("read-only GetActionResult: %v", err)
	}
	if !bytes.Equal(gotAR.GetStdoutRaw(), payload) {
		t.Errorf("inlined stdout = %q, want %q", gotAR.GetStdoutRaw(), payload)
	}
}

// TestE2ERemoteAsset verifies PushBlob, FetchBlob, tenant isolation, and
// read-only token denial on the Remote Asset API.
func TestE2ERemoteAsset(t *testing.T) {
	e := dialE2E(t)
	ctxA, ctxARO, ctxB := e.ctxA(t), e.ctxARO(t), e.ctxB(t)

	blobD, err := e.origin.Upload(ctxA, e.InstanceA, []byte("remote-asset-e2e"))
	if err != nil {
		t.Fatal(err)
	}
	pushClient := assetpb.NewPushClient(e.originConn)
	fetchClient := assetpb.NewFetchClient(e.originConn)
	uri := fmt.Sprintf("https://example.invalid/ci-substrate/%d.tar.zst", time.Now().UnixNano())

	if _, err := pushClient.PushBlob(ctxARO, &assetpb.PushBlobRequest{
		InstanceName: e.InstanceA,
		Uris:         []string{uri},
		BlobDigest:   blobD,
	}); status.Code(err) != codes.PermissionDenied {
		t.Errorf("read-only PushBlob: got %v, want PermissionDenied", err)
	}
	if _, err := pushClient.PushBlob(ctxA, &assetpb.PushBlobRequest{
		InstanceName: e.InstanceA,
		Uris:         []string{uri},
		Qualifiers:   []*assetpb.Qualifier{{Name: "checksum.sri", Value: "sha256-e2e"}},
		BlobDigest:   blobD,
	}); err != nil {
		t.Fatalf("PushBlob: %v", err)
	}
	fresp, err := fetchClient.FetchBlob(ctxA, &assetpb.FetchBlobRequest{
		InstanceName: e.InstanceA,
		Uris:         []string{uri},
		Qualifiers:   []*assetpb.Qualifier{{Name: "checksum.sri", Value: "sha256-e2e"}},
	})
	if err != nil || fresp.GetBlobDigest().GetHash() != blobD.GetHash() {
		t.Fatalf("FetchBlob: resp=%v err=%v", fresp, err)
	}
	if _, err := fetchClient.FetchBlob(ctxB, &assetpb.FetchBlobRequest{
		InstanceName: e.InstanceA,
		Uris:         []string{uri},
	}); status.Code(err) != codes.PermissionDenied {
		t.Errorf("tenant B FetchBlob in tenant A: got %v, want PermissionDenied", err)
	}
}

// TestE2ERemoteLogstream verifies CreateLogStream, live ByteStream write/read,
// and tenant isolation.
func TestE2ERemoteLogstream(t *testing.T) {
	e := dialE2E(t)
	ctxA, ctxB := e.ctxA(t), e.ctxB(t)

	lsClient := logstreampb.NewLogStreamServiceClient(e.originConn)
	bs := bytestream.NewByteStreamClient(e.originConn)
	ls, err := lsClient.CreateLogStream(ctxA, &logstreampb.CreateLogStreamRequest{Parent: e.InstanceA})
	if err != nil {
		t.Fatalf("CreateLogStream: %v", err)
	}
	readStream, err := bs.Read(ctxA, &bytestream.ReadRequest{ResourceName: ls.GetName()})
	if err != nil {
		t.Fatalf("logstream Read: %v", err)
	}
	writeStream, err := bs.Write(ctxA)
	if err != nil {
		t.Fatalf("logstream Write: %v", err)
	}
	const wantLog = "line-1\nline-2\n"
	if err := writeStream.Send(&bytestream.WriteRequest{
		ResourceName: ls.GetWriteResourceName(),
		Data:         []byte("line-1\n"),
	}); err != nil {
		t.Fatal(err)
	}
	if err := writeStream.Send(&bytestream.WriteRequest{
		ResourceName: ls.GetWriteResourceName(),
		WriteOffset:  int64(len("line-1\n")),
		Data:         []byte("line-2\n"),
		FinishWrite:  true,
	}); err != nil {
		t.Fatal(err)
	}
	if _, err := writeStream.CloseAndRecv(); err != nil {
		t.Fatalf("closing logstream write: %v", err)
	}
	var got bytes.Buffer
	for {
		msg, rerr := readStream.Recv()
		if rerr == io.EOF {
			break
		}
		if rerr != nil {
			t.Fatalf("reading logstream: %v", rerr)
		}
		got.Write(msg.GetData())
	}
	if got.String() != wantLog {
		t.Errorf("logstream = %q, want %q", got.String(), wantLog)
	}
	denied, err := bs.Read(ctxB, &bytestream.ReadRequest{ResourceName: ls.GetName()})
	if err == nil {
		_, err = denied.Recv()
	}
	if status.Code(err) != codes.PermissionDenied {
		t.Errorf("tenant B logstream Read: got %v, want PermissionDenied", err)
	}
}

// TestE2EExecuteGetTreeTimeoutAndCancel exercises remote execution on the live
// runner: output files/directories, CAS.GetTree, VirtualExecutionDuration,
// Operations.GetOperation, AC cache hit, Action.timeout with partial stdout,
// and Operations.CancelOperation.
func TestE2EExecuteGetTreeTimeoutAndCancel(t *testing.T) {
	e := dialE2E(t)
	ctxA, ctxB := e.ctxA(t), e.ctxB(t)
	execer := repb.NewExecutionClient(e.originConn)
	ops := longrunning.NewOperationsClient(e.originConn)
	casClient := repb.NewContentAddressableStorageClient(e.originConn)

	content := fmt.Sprintf("hello from tenant A at %d\n", time.Now().UnixNano())
	input, err := e.origin.Upload(ctxA, e.InstanceA, []byte(content))
	if err != nil {
		t.Fatalf("uploading input: %v", err)
	}
	root := mustUploadProto(ctxA, t, e.origin, e.InstanceA, &repb.Directory{
		Files: []*repb.FileNode{{Name: "input.txt", Digest: input}},
	})
	cmd := mustUploadProto(ctxA, t, e.origin, e.InstanceA, &repb.Command{
		Arguments:   []string{"sh", "-c", "tr a-z A-Z < input.txt > out/upper.txt && mkdir -p out/tree && cp input.txt out/tree/copy.txt && echo done"},
		OutputPaths: []string{"out/upper.txt", "out/tree"},
	})
	action := mustUploadProto(ctxA, t, e.origin, e.InstanceA, &repb.Action{
		CommandDigest:   cmd,
		InputRootDigest: root,
	})

	// Tenant B cannot execute in tenant A's instance.
	if _, _, err := runAction(ctxB, execer, e.InstanceA, action, e.ExecTimeout); status.Code(err) != codes.PermissionDenied {
		t.Errorf("tenant B Execute in tenant A: got %v, want PermissionDenied", err)
	}

	opName, resp, err := runAction(ctxA, execer, e.InstanceA, action, e.ExecTimeout)
	if err != nil {
		t.Fatalf("Execute: %v", err)
	}
	if resp.GetStatus().GetCode() != 0 {
		t.Fatalf("action status = %v", resp.GetStatus())
	}
	ar := resp.GetResult()
	if ar.GetExitCode() != 0 {
		t.Fatalf("action exit code = %d", ar.GetExitCode())
	}
	if ar.GetExecutionMetadata().GetVirtualExecutionDuration().AsDuration() <= 0 {
		t.Error("ExecutionMetadata.VirtualExecutionDuration was not populated")
	}
	if worker := ar.GetExecutionMetadata().GetWorker(); !strings.HasPrefix(worker, e.WorkerPrefix) {
		t.Errorf("worker = %q, want prefix %q", worker, e.WorkerPrefix)
	}
	if mode := runnerInputMode(ar); e.ExpectInputMode != "" && mode != e.ExpectInputMode {
		t.Errorf("runner input mode = %q, want %q", mode, e.ExpectInputMode)
	}
	if got := mustFetchString(ctxA, t, e.cacheClient, e.InstanceA, ar.GetStdoutDigest()); got != "done\n" {
		t.Errorf("stdout = %q, want %q", got, "done\n")
	}
	if len(ar.GetOutputFiles()) != 1 || ar.GetOutputFiles()[0].GetPath() != "out/upper.txt" {
		t.Fatalf("output files = %v, want out/upper.txt", ar.GetOutputFiles())
	}
	if got := mustFetchString(ctxA, t, e.cacheClient, e.InstanceA, ar.GetOutputFiles()[0].GetDigest()); got != strings.ToUpper(content) {
		t.Errorf("out/upper.txt = %q, want %q", got, strings.ToUpper(content))
	}
	if len(ar.GetOutputDirectories()) != 1 || ar.GetOutputDirectories()[0].GetPath() != "out/tree" {
		t.Fatalf("output directories = %v, want out/tree", ar.GetOutputDirectories())
	}
	outDir := ar.GetOutputDirectories()[0]
	if outDir.GetRootDirectoryDigest() == nil {
		t.Fatal("OutputDirectory.RootDirectoryDigest was not populated")
	}
	treeStream, err := casClient.GetTree(ctxA, &repb.GetTreeRequest{
		InstanceName: e.InstanceA,
		RootDigest:   outDir.GetRootDirectoryDigest(),
	})
	if err != nil {
		t.Fatalf("GetTree: %v", err)
	}
	treeResp, err := treeStream.Recv()
	if err != nil || len(treeResp.GetDirectories()) != 1 {
		t.Fatalf("GetTree recv: resp=%v err=%v", treeResp, err)
	}

	// Operations.GetOperation works for tenant A and is denied for tenant B.
	op, err := ops.GetOperation(ctxA, &longrunning.GetOperationRequest{Name: opName})
	if err != nil || !op.GetDone() {
		t.Fatalf("GetOperation(%s): op=%v err=%v", opName, op, err)
	}
	if _, err := ops.GetOperation(ctxB, &longrunning.GetOperationRequest{Name: opName}); status.Code(err) != codes.PermissionDenied {
		t.Errorf("tenant B GetOperation: got %v, want PermissionDenied", err)
	}

	// Second Execute hits the ActionCache.
	_, again, err := runAction(ctxA, execer, e.InstanceA, action, e.ExecTimeout)
	if err != nil {
		t.Fatalf("re-Execute: %v", err)
	}
	if !again.GetCachedResult() {
		t.Error("second Execute was not a cache hit")
	}

	// Action.timeout kills the process group, preserves partial stdout, and returns DeadlineExceeded.
	timeoutCmd := mustUploadProto(ctxA, t, e.origin, e.InstanceA, &repb.Command{
		Arguments: []string{"sh", "-c", "echo before-timeout; sleep 30"},
	})
	timeoutAction := mustUploadProto(ctxA, t, e.origin, e.InstanceA, &repb.Action{
		CommandDigest:   timeoutCmd,
		InputRootDigest: root,
		Timeout:         durationpb.New(time.Second),
		DoNotCache:      true,
	})
	_, toResp, err := runAction(ctxA, execer, e.InstanceA, timeoutAction, e.ExecTimeout)
	if err != nil {
		t.Fatalf("timeout Execute: %v", err)
	}
	if codes.Code(toResp.GetStatus().GetCode()) != codes.DeadlineExceeded {
		t.Errorf("timeout status = %v, want DeadlineExceeded", toResp.GetStatus())
	}
	if got := mustFetchString(ctxA, t, e.cacheClient, e.InstanceA, toResp.GetResult().GetStdoutDigest()); !strings.Contains(got, "before-timeout") {
		t.Errorf("timeout partial stdout = %q, want before-timeout", got)
	}

	// Operations.CancelOperation cancels an in-flight action.
	slowCmd := mustUploadProto(ctxA, t, e.origin, e.InstanceA, &repb.Command{
		Arguments: []string{"sh", "-c", "sleep 60"},
	})
	slowAction := mustUploadProto(ctxA, t, e.origin, e.InstanceA, &repb.Action{
		CommandDigest:   slowCmd,
		InputRootDigest: root,
		DoNotCache:      true,
	})
	cctx, ccancel := context.WithTimeout(ctxA, e.ExecTimeout)
	defer ccancel()
	cstream, err := execer.Execute(cctx, &repb.ExecuteRequest{InstanceName: e.InstanceA, ActionDigest: slowAction})
	if err != nil {
		t.Fatalf("starting cancellable Execute: %v", err)
	}
	firstOp, err := cstream.Recv()
	if err != nil {
		t.Fatalf("receiving initial operation: %v", err)
	}
	if _, err := ops.CancelOperation(ctxA, &longrunning.CancelOperationRequest{Name: firstOp.GetName()}); err != nil {
		t.Fatalf("CancelOperation: %v", err)
	}
	for {
		cur, rerr := cstream.Recv()
		if rerr != nil {
			t.Fatalf("waiting for cancelled operation: %v", rerr)
		}
		if !cur.GetDone() {
			continue
		}
		cr := &repb.ExecuteResponse{}
		if err := cur.GetResponse().UnmarshalTo(cr); err != nil {
			t.Fatal(err)
		}
		if codes.Code(cr.GetStatus().GetCode()) != codes.Canceled {
			t.Errorf("cancelled status = %v, want Canceled", cr.GetStatus())
		}
		break
	}
}

// TestE2EActorJWTSecurityRejection verifies that cas rejects forged and
// unsigned Actor JWTs on both WorkerService and CAS RPCs.
func TestE2EActorJWTSecurityRejection(t *testing.T) {
	env := dialE2E(t)
	if !env.ActorJWT {
		t.Skip("set CI_SUBSTRATE_E2E_ACTOR_JWT=1 to test Actor JWT rejection")
	}
	worker := workerv1.NewWorkerServiceClient(env.originConn)
	casClient := repb.NewContentAddressableStorageClient(env.originConn)

	// Generate a self-signed ES256 key not in ate-idp-server's JWKS.
	fakeKey, err := ecdsa.GenerateKey(elliptic.P256(), rand.Reader)
	if err != nil {
		t.Fatal(err)
	}
	now := time.Now()
	claims, _ := json.Marshal(map[string]any{
		"iss": "https://idp.ate-system.svc",
		"sub": "actor/" + env.InstanceA + "/forged-bot",
		"aud": []string{"cas.ci-substrate.svc.cluster.local"},
		"iat": now.Unix(),
		"nbf": now.Add(-time.Minute).Unix(),
		"exp": now.Add(10 * time.Minute).Unix(),
		"actor.ate.dev": map[string]string{
			"atespace":  env.InstanceA,
			"actorName": "forged-bot",
			"actorUID":  uuid.NewString(),
		},
	})
	esHdr, _ := json.Marshal(map[string]string{"typ": "JWT", "alg": "ES256", "kid": "forged-kid"})
	input := base64.RawURLEncoding.EncodeToString(esHdr) + "." + base64.RawURLEncoding.EncodeToString(claims)
	sum := sha256.Sum256([]byte(input))
	r, s, err := ecdsa.Sign(rand.Reader, fakeKey, sum[:])
	if err != nil {
		t.Fatal(err)
	}
	sig := make([]byte, 64)
	r.FillBytes(sig[:32])
	s.FillBytes(sig[32:])
	forgedJWT := input + "." + base64.RawURLEncoding.EncodeToString(sig)

	noneHdr, _ := json.Marshal(map[string]string{"typ": "JWT", "alg": "none"})
	unsignedJWT := base64.RawURLEncoding.EncodeToString(noneHdr) + "." + base64.RawURLEncoding.EncodeToString(claims) + "."

	for name, tok := range map[string]string{
		"forged_es256": forgedJWT,
		"alg_none":     unsignedJWT,
	} {
		t.Run(name, func(t *testing.T) {
			ctx, cancel := context.WithTimeout(tenant.Outgoing(t.Context(), tok), 10*time.Second)
			defer cancel()
			if _, err := worker.Lease(ctx, &workerv1.LeaseRequest{BotId: "forged-bot", InstanceNames: []string{env.InstanceA}}); status.Code(err) != codes.Unauthenticated {
				t.Fatalf("Lease with %s = %v (%v), want Unauthenticated", name, status.Code(err), err)
			}
			if _, err := casClient.FindMissingBlobs(ctx, &repb.FindMissingBlobsRequest{InstanceName: env.InstanceA}); status.Code(err) != codes.Unauthenticated {
				t.Fatalf("FindMissingBlobs with %s = %v (%v), want Unauthenticated", name, status.Code(err), err)
			}
		})
	}
}

// TestE2ESourceTagForkedEnv verifies that an RBE Action carrying
// Platform.Properties{"ci-substrate/env": "<tag>"} is routed to an actor
// forked from that Substrate Tag (copy-on-write snapshot) and sees the
// pre-warmed filesystem state captured in the tag.
func TestE2ESourceTagForkedEnv(t *testing.T) {
	env := dialE2E(t)
	if env.EnvTag == "" {
		t.Skip("set CI_SUBSTRATE_E2E_ENV_TAG to test sourceTag forked environments")
	}
	ctx := env.ctxA(t)
	execer := repb.NewExecutionClient(env.originConn)
	cmdDigest := mustUploadProto(ctx, t, env.origin, env.InstanceA, &repb.Command{
		Arguments: []string{"cat", "/var/tmp/ci-substrate-warm-env"},
	})
	actDigest := mustUploadProto(ctx, t, env.origin, env.InstanceA, &repb.Action{
		CommandDigest: cmdDigest,
		DoNotCache:    true,
		Platform: &repb.Platform{
			Properties: []*repb.Platform_Property{
				{Name: platform.PropEnv, Value: env.EnvTag},
			},
		},
	})
	start := time.Now()
	_, resp, err := runAction(ctx, execer, env.InstanceA, actDigest, env.ExecTimeout)
	if err != nil {
		t.Fatalf("Execute on env=%s: %v", env.EnvTag, err)
	}
	took := time.Since(start)
	if resp.GetResult().GetExitCode() != 0 {
		t.Fatalf("exit code %d, stderr=%q", resp.GetResult().GetExitCode(), mustFetchString(ctx, t, env.origin, env.InstanceA, resp.GetResult().GetStderrDigest()))
	}
	got := strings.TrimSpace(mustFetchString(ctx, t, env.origin, env.InstanceA, resp.GetResult().GetStdoutDigest()))
	if env.EnvMarker != "" && got != env.EnvMarker {
		t.Fatalf("warm-env marker = %q, want %q", got, env.EnvMarker)
	}
	worker := resp.GetResult().GetExecutionMetadata().GetWorker()
	wantPrefix := "ci-runner-env-" + env.EnvTag + "--"
	if !strings.HasPrefix(worker, wantPrefix) {
		t.Fatalf("worker = %q, want prefix %q", worker, wantPrefix)
	}
	t.Logf("BENCH source_tag_fork_execute tag=%s worker=%s duration=%s", env.EnvTag, worker, took.Round(time.Millisecond))
}

func runAction(ctx context.Context, execer repb.ExecutionClient, instance string, action *repb.Digest, timeout time.Duration) (string, *repb.ExecuteResponse, error) {
	ctx, cancel := context.WithTimeout(ctx, timeout)
	defer cancel()
	stream, err := execer.Execute(ctx, &repb.ExecuteRequest{InstanceName: instance, ActionDigest: action})
	if err != nil {
		return "", nil, err
	}
	var opName string
	for {
		op, err := stream.Recv()
		if err != nil {
			return opName, nil, err
		}
		opName = op.GetName()
		if !op.GetDone() {
			continue
		}
		resp := &repb.ExecuteResponse{}
		if err := op.GetResponse().UnmarshalTo(resp); err != nil {
			return opName, nil, err
		}
		return opName, resp, nil
	}
}

func mustUploadProto(ctx context.Context, t *testing.T, c *remote.Client, instance string, m proto.Message) *repb.Digest {
	t.Helper()
	d, err := c.Upload(ctx, instance, tree.Marshal(m))
	if err != nil {
		t.Fatalf("uploading %T: %v", m, err)
	}
	return d
}

func mustFetchString(ctx context.Context, t *testing.T, c *remote.Client, instance string, d *repb.Digest) string {
	t.Helper()
	if d == nil {
		t.Fatal("nil digest")
	}
	b, err := c.Fetch(ctx, instance, d)
	if err != nil {
		t.Fatalf("fetching %s: %v", digest.Key(d), err)
	}
	if err := digest.Verify(d, b); err != nil {
		t.Fatalf("verifying %s: %v", digest.Key(d), err)
	}
	return string(b)
}

func retryCall[T any](fn func() (T, error)) (T, error) {
	var zero T
	var last error
	for range 10 {
		v, err := fn()
		if err == nil {
			return v, nil
		}
		last = err
		if c := status.Code(err); c != codes.Unavailable && c != codes.DeadlineExceeded {
			return zero, err
		}
		time.Sleep(time.Second)
	}
	return zero, last
}

func fetchCacheStats(metricsURL string) (cache.Stats, error) {
	var s cache.Stats
	resp, err := http.Get(metricsURL + "/stats")
	if err != nil {
		return s, err
	}
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusOK {
		return s, fmt.Errorf("GET %s/stats: %s", metricsURL, resp.Status)
	}
	err = json.NewDecoder(resp.Body).Decode(&s)
	return s, err
}

func runnerInputMode(ar *repb.ActionResult) string {
	for _, a := range ar.GetExecutionMetadata().GetAuxiliaryMetadata() {
		md := &workerv1.RunnerMetadata{}
		if a.MessageIs(md) && a.UnmarshalTo(md) == nil {
			return md.GetInputMode()
		}
	}
	return ""
}
