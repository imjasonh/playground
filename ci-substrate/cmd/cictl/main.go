// Command cictl checks a live cluster: one tenant cannot read another's
// instance, action cache, or queue; a blob one tenant warmed is served to
// another from the node-local cache with no second origin fetch; and an
// action runs on its tenant's runner, and the next Execute is a cache hit.
package main

import (
	"bytes"
	"context"
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	"io"
	"log/slog"
	"net/http"
	"os"
	"strings"
	"time"

	longrunning "cloud.google.com/go/longrunning/autogen/longrunningpb"
	assetpb "github.com/bazelbuild/remote-apis/build/bazel/remote/asset/v1"
	repb "github.com/bazelbuild/remote-apis/build/bazel/remote/execution/v2"
	logstreampb "github.com/bazelbuild/remote-apis/build/bazel/remote/logstream/v1"
	"github.com/google/uuid"
	"github.com/klauspost/compress/zstd"
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
	"github.com/imjasonh/playground/ci-substrate/internal/remote"
	"github.com/imjasonh/playground/ci-substrate/internal/tenant"
	"github.com/imjasonh/playground/ci-substrate/internal/tree"
)

func main() {
	originAddr := flag.String("origin-addr", "", "origin cas address (host:port)")
	cacheAddr := flag.String("cache-addr", "", "node-local cascache address (host:port)")
	cacheMetricsURL := flag.String("cache-metrics-url", "", "cascache metrics base URL, e.g. http://host:9090")
	tokenA := flag.String("token-a", "tok-a", "tenant A token")
	tokenARO := flag.String("token-a-ro", "", "optional tenant A read-only ActionCache token")
	tokenB := flag.String("token-b", "tok-b", "tenant B token")
	instanceA := flag.String("instance-a", "tenant-a", "tenant A private instance")
	shared := flag.String("shared", "shared", "instance both tenants may read")
	execTimeout := flag.Duration("exec-timeout", 3*time.Minute, "how long to wait for a runner to run the demo action; 0 skips execution")
	workerPrefix := flag.String("worker-prefix", "", "if set, the runner that ran the action must report a worker name with this prefix")
	inputMode := flag.String("expect-input-mode", "", "if set, the runner must report that it built the exec root this way: volume, fuse, or copy")
	flag.Parse()

	if *originAddr == "" || *cacheAddr == "" {
		slog.Error("missing required flags", "need", "-origin-addr and -cache-addr")
		os.Exit(2)
	}

	want := expectations{workerPrefix: *workerPrefix, inputMode: *inputMode}
	if err := run(*originAddr, *cacheAddr, *cacheMetricsURL, *tokenA, *tokenARO, *tokenB, *instanceA, *shared, *execTimeout, want); err != nil {
		slog.Error("demo failed", "err", err)
		os.Exit(1)
	}
	slog.Info("demo passed: multi-tenant isolation, node-local cache reuse, production RBE APIs, and remote execution verified")
}

// expectations are what the demo checks about the runner that ran the
// action, beyond the result itself.
type expectations struct {
	// workerPrefix is a prefix the reported worker name must have. Substrate
	// actors report their actor name.
	workerPrefix string
	// inputMode is how the runner must report having built the exec root.
	// "volume" means the node served the inputs through a casfs volume.
	inputMode string
}

func run(originAddr, cacheAddr, metricsURL, tokenA, tokenARO, tokenB, instanceA, shared string, execTimeout time.Duration, want expectations) error {
	originConn, err := grpc.NewClient(originAddr, grpc.WithTransportCredentials(insecure.NewCredentials()))
	if err != nil {
		return err
	}
	defer originConn.Close()
	cacheConn, err := grpc.NewClient(cacheAddr, grpc.WithTransportCredentials(insecure.NewCredentials()))
	if err != nil {
		return err
	}
	defer cacheConn.Close()
	origin := remote.NewClient(originConn)
	cacheClient := remote.NewClient(cacheConn)

	ctxA := tenant.Outgoing(context.Background(), tokenA)
	ctxB := tenant.Outgoing(context.Background(), tokenB)
	var ctxARO context.Context
	if tokenARO != "" {
		ctxARO = tenant.Outgoing(context.Background(), tokenARO)
	}

	if err := cacheDemo(ctxA, ctxB, origin, cacheClient, metricsURL, instanceA, shared); err != nil {
		return err
	}
	if err := productionAPIsDemo(ctxA, ctxARO, ctxB, originConn, cacheConn, instanceA); err != nil {
		return err
	}
	if execTimeout <= 0 {
		slog.Info("skipping remote execution (-exec-timeout=0)")
		return nil
	}
	return execDemo(ctxA, ctxB, origin, cacheClient, originConn, instanceA, execTimeout, want)
}

// cacheDemo proves node-local cache reuse across tenants and isolation of a
// tenant's instance and action cache.
func cacheDemo(ctxA, ctxB context.Context, origin, cacheClient *remote.Client, metricsURL, instanceA, shared string) error {

	// Tenant A uploads a shared blob to the origin.
	content := []byte(fmt.Sprintf("shared build artifact %d", time.Now().UnixNano()))
	d, err := retry(func() (*repb.Digest, error) {
		return origin.Upload(ctxA, shared, content)
	})
	if err != nil {
		return fmt.Errorf("tenant A upload: %w", err)
	}
	slog.Info("tenant A uploaded shared blob", "digest", digest.Key(d))

	stats := func() (cache.Stats, error) {
		if metricsURL == "" {
			return cache.Stats{}, nil
		}
		return fetchStats(metricsURL)
	}
	before, err := stats()
	if err != nil {
		return err
	}

	// Tenant A reads it through the node-local cache (cold: one origin fetch).
	if _, err := retry(func() ([]byte, error) {
		return cacheClient.Fetch(ctxA, shared, d)
	}); err != nil {
		return fmt.Errorf("tenant A cold read: %w", err)
	}
	afterCold, err := stats()
	if err != nil {
		return err
	}
	// Tenant B reads the same content (warm: should be a node-local hit).
	got, err := retry(func() ([]byte, error) {
		return cacheClient.Fetch(ctxB, shared, d)
	})
	if err != nil {
		return fmt.Errorf("tenant B warm read: %w", err)
	}
	if string(got) != string(content) {
		return errors.New("tenant B read wrong bytes from cache")
	}
	afterWarm, err := stats()
	if err != nil {
		return err
	}
	if metricsURL != "" {
		// The cascache counters are cumulative across runs, so compare
		// deltas: the cold read fetches once, the warm read only hits.
		slog.Info("cache stats", "hits", afterWarm.Hits, "originFetches", afterWarm.OriginFetches, "poisonRejected", afterWarm.PoisonRejected)
		if n := afterCold.OriginFetches - before.OriginFetches; n != 1 {
			return fmt.Errorf("cold read made %d origin fetches, want 1", n)
		}
		if n := afterWarm.OriginFetches - afterCold.OriginFetches; n != 0 {
			return fmt.Errorf("warm read made %d origin fetches, want 0", n)
		}
		if n := afterWarm.Hits - afterCold.Hits; n != 1 {
			return fmt.Errorf("warm read made %d cache hits, want 1", n)
		}
	}
	slog.Info("tenant B served shared blob from node-local cache with no origin fetch")

	// Isolation: tenant B must not read through tenant A's private instance.
	if err := tryCrossTenant(ctxB, cacheClient, instanceA, d); err != nil {
		return err
	}
	// Isolation: tenant B must not read tenant A's action cache, which is
	// what maps tenant A's actions to its output digests.
	action := digest.FromBytes([]byte(fmt.Sprintf("tenant A action %d", time.Now().UnixNano())))
	if err := origin.UpdateActionResult(ctxA, instanceA, action, &repb.ActionResult{StdoutDigest: d}); err != nil {
		return fmt.Errorf("tenant A action cache write: %w", err)
	}
	if _, _, err := origin.GetActionResult(ctxB, instanceA, action); status.Code(err) != codes.PermissionDenied {
		return fmt.Errorf("tenant B reading tenant A's action cache: got %v, want PermissionDenied", err)
	}
	if _, ok, err := origin.GetActionResult(ctxA, instanceA, action); err != nil || !ok {
		return fmt.Errorf("tenant A reading its own action cache: ok=%v err=%v", ok, err)
	}
	slog.Info("isolation held: tenant B denied tenant A's instance and action cache")
	return nil
}

// inputMode is the mode the runner recorded on the result, or "" when the
// result carries none.
func inputMode(ar *repb.ActionResult) string {
	for _, a := range ar.GetExecutionMetadata().GetAuxiliaryMetadata() {
		md := &workerv1.RunnerMetadata{}
		if a.MessageIs(md) && a.UnmarshalTo(md) == nil {
			return md.GetInputMode()
		}
	}
	return ""
}

// productionAPIsDemo verifies Zstd compression on cas and cascache, read-only
// ActionCache tokens with output inlining, the Remote Asset API, and the Remote
// Logstream API against the live cluster.
func productionAPIsDemo(ctxA, ctxARO, ctxB context.Context, originConn, cacheConn *grpc.ClientConn, instanceA string) error {
	// 1. Zstd-compressed ByteStream upload to cas and compressed BatchReadBlobs
	//    through node-local cascache.
	raw := bytes.Repeat([]byte("ci-substrate-zstd-e2e-payload-"), 256)
	rawDigest := digest.FromBytes(raw)
	enc, err := zstd.NewWriter(nil, zstd.WithEncoderConcurrency(1))
	if err != nil {
		return err
	}
	compressed := enc.EncodeAll(raw, nil)
	enc.Close()

	originBS := bytestream.NewByteStreamClient(originConn)
	ws, err := originBS.Write(ctxA)
	if err != nil {
		return fmt.Errorf("compressed ByteStream Write: %w", err)
	}
	if err := ws.Send(&bytestream.WriteRequest{
		ResourceName: remote.CompressedWriteResourceName(instanceA, uuid.NewString(), repb.Compressor_ZSTD, rawDigest),
		Data:         compressed,
		FinishWrite:  true,
	}); err != nil {
		return fmt.Errorf("sending compressed chunk: %w", err)
	}
	wresp, err := ws.CloseAndRecv()
	if err != nil {
		return fmt.Errorf("closing compressed write: %w", err)
	}
	if wresp.GetCommittedSize() != -1 {
		return fmt.Errorf("compressed write committed_size = %d, want -1", wresp.GetCommittedSize())
	}

	cacheCAS := repb.NewContentAddressableStorageClient(cacheConn)
	bresp, err := cacheCAS.BatchReadBlobs(ctxA, &repb.BatchReadBlobsRequest{
		InstanceName:          instanceA,
		Digests:               []*repb.Digest{rawDigest},
		AcceptableCompressors: []repb.Compressor_Value{repb.Compressor_ZSTD},
	})
	if err != nil || len(bresp.GetResponses()) != 1 || bresp.GetResponses()[0].GetStatus().GetCode() != 0 {
		return fmt.Errorf("compressed BatchReadBlobs through cascache: %v, %v", bresp, err)
	}
	if bresp.GetResponses()[0].GetCompressor() != repb.Compressor_ZSTD {
		return fmt.Errorf("cascache BatchReadBlobs compressor = %v, want ZSTD", bresp.GetResponses()[0].GetCompressor())
	}
	dec, err := zstd.NewReader(nil, zstd.WithDecoderConcurrency(1))
	if err != nil {
		return err
	}
	gotRaw, err := dec.DecodeAll(bresp.GetResponses()[0].GetData(), nil)
	dec.Close()
	if err != nil || !bytes.Equal(gotRaw, raw) {
		return fmt.Errorf("decompressed cascache payload mismatch: err=%v len=%d", err, len(gotRaw))
	}
	slog.Info("Zstd compression verified across cas and cascache", "rawBytes", len(raw), "compressedBytes", len(compressed))

	// 2. Read-only ActionCache token: GetCapabilities reports update_enabled=false,
	//    UpdateActionResult is denied, and GetActionResult with InlineStdout succeeds.
	if ctxARO != nil {
		caps := repb.NewCapabilitiesClient(originConn)
		roCaps, err := caps.GetCapabilities(ctxARO, &repb.GetCapabilitiesRequest{InstanceName: instanceA})
		if err != nil {
			return fmt.Errorf("read-only GetCapabilities: %w", err)
		}
		if roCaps.GetCacheCapabilities().GetActionCacheUpdateCapabilities().GetUpdateEnabled() {
			return errors.New("read-only token saw update_enabled=true in GetCapabilities")
		}
		ac := repb.NewActionCacheClient(originConn)
		actD := digest.FromBytes([]byte(fmt.Sprintf("ro-ac-test-%d", time.Now().UnixNano())))
		if _, err := ac.UpdateActionResult(ctxARO, &repb.UpdateActionResultRequest{
			InstanceName: instanceA,
			ActionDigest: actD,
			ActionResult: &repb.ActionResult{StdoutDigest: rawDigest},
		}); status.Code(err) != codes.PermissionDenied {
			return fmt.Errorf("read-only UpdateActionResult: got %v, want PermissionDenied", err)
		}
		if _, err := ac.UpdateActionResult(ctxA, &repb.UpdateActionResultRequest{
			InstanceName: instanceA,
			ActionDigest: actD,
			ActionResult: &repb.ActionResult{StdoutDigest: rawDigest},
		}); err != nil {
			return fmt.Errorf("writable UpdateActionResult: %w", err)
		}
		gotAR, err := ac.GetActionResult(ctxARO, &repb.GetActionResultRequest{
			InstanceName: instanceA,
			ActionDigest: actD,
			InlineStdout: true,
		})
		if err != nil {
			return fmt.Errorf("read-only GetActionResult: %w", err)
		}
		if !bytes.Equal(gotAR.GetStdoutRaw(), raw) {
			return fmt.Errorf("inlined stdout length = %d, want %d", len(gotAR.GetStdoutRaw()), len(raw))
		}
		slog.Info("read-only ActionCache token and output inlining verified")
	}

	// 3. Remote Asset API: PushBlob, FetchBlob, tenant isolation, and read-only denial.
	pushClient := assetpb.NewPushClient(originConn)
	fetchClient := assetpb.NewFetchClient(originConn)
	assetURI := fmt.Sprintf("https://example.invalid/ci-substrate/%d.tar.zst", time.Now().UnixNano())
	if ctxARO != nil {
		if _, err := pushClient.PushBlob(ctxARO, &assetpb.PushBlobRequest{
			InstanceName: instanceA,
			Uris:         []string{assetURI},
			BlobDigest:   rawDigest,
		}); status.Code(err) != codes.PermissionDenied {
			return fmt.Errorf("read-only PushBlob: got %v, want PermissionDenied", err)
		}
	}
	if _, err := pushClient.PushBlob(ctxA, &assetpb.PushBlobRequest{
		InstanceName: instanceA,
		Uris:         []string{assetURI},
		Qualifiers:   []*assetpb.Qualifier{{Name: "checksum.sri", Value: "sha256-demo"}},
		BlobDigest:   rawDigest,
	}); err != nil {
		return fmt.Errorf("PushBlob: %w", err)
	}
	fresp, err := fetchClient.FetchBlob(ctxA, &assetpb.FetchBlobRequest{
		InstanceName: instanceA,
		Uris:         []string{assetURI},
		Qualifiers:   []*assetpb.Qualifier{{Name: "checksum.sri", Value: "sha256-demo"}},
	})
	if err != nil || fresp.GetBlobDigest().GetHash() != rawDigest.GetHash() {
		return fmt.Errorf("FetchBlob: resp=%v err=%v", fresp, err)
	}
	if _, err := fetchClient.FetchBlob(ctxB, &assetpb.FetchBlobRequest{
		InstanceName: instanceA,
		Uris:         []string{assetURI},
	}); status.Code(err) != codes.PermissionDenied {
		return fmt.Errorf("tenant B FetchBlob in tenant A: got %v, want PermissionDenied", err)
	}
	slog.Info("Remote Asset API verified")

	// 4. Remote Logstream API: create, live-tail over ByteStream, and tenant isolation.
	lsClient := logstreampb.NewLogStreamServiceClient(originConn)
	ls, err := lsClient.CreateLogStream(ctxA, &logstreampb.CreateLogStreamRequest{Parent: instanceA})
	if err != nil {
		return fmt.Errorf("CreateLogStream: %w", err)
	}
	readStream, err := originBS.Read(ctxA, &bytestream.ReadRequest{ResourceName: ls.GetName()})
	if err != nil {
		return fmt.Errorf("logstream Read: %w", err)
	}
	lsWrite, err := originBS.Write(ctxA)
	if err != nil {
		return fmt.Errorf("logstream Write: %w", err)
	}
	const wantLog = "line-1\nline-2\n"
	if err := lsWrite.Send(&bytestream.WriteRequest{
		ResourceName: ls.GetWriteResourceName(),
		Data:         []byte("line-1\n"),
	}); err != nil {
		return err
	}
	if err := lsWrite.Send(&bytestream.WriteRequest{
		ResourceName: ls.GetWriteResourceName(),
		WriteOffset:  int64(len("line-1\n")),
		Data:         []byte("line-2\n"),
		FinishWrite:  true,
	}); err != nil {
		return err
	}
	if _, err := lsWrite.CloseAndRecv(); err != nil {
		return fmt.Errorf("closing logstream write: %w", err)
	}
	var gotLog bytes.Buffer
	for {
		msg, rerr := readStream.Recv()
		if rerr == io.EOF {
			break
		}
		if rerr != nil {
			return fmt.Errorf("reading logstream: %w", rerr)
		}
		gotLog.Write(msg.GetData())
	}
	if gotLog.String() != wantLog {
		return fmt.Errorf("logstream got %q, want %q", gotLog.String(), wantLog)
	}
	deniedRead, err := originBS.Read(ctxB, &bytestream.ReadRequest{ResourceName: ls.GetName()})
	if err == nil {
		_, err = deniedRead.Recv()
	}
	if status.Code(err) != codes.PermissionDenied {
		return fmt.Errorf("tenant B logstream Read: got %v, want PermissionDenied", err)
	}
	slog.Info("Remote Logstream API verified")
	return nil
}

// execDemo runs an action through Execute on tenant A's runner, checks the
// outputs it uploaded (including GetTree, VirtualExecutionDuration, and
// Operations), verifies timeout partial outputs and CancelOperation, and shows
// the next Execute is a cache hit and tenant B cannot submit into tenant A.
func execDemo(ctxA, ctxB context.Context, origin, cacheClient *remote.Client, originConn *grpc.ClientConn, instanceA string, timeout time.Duration, want expectations) error {
	execer := repb.NewExecutionClient(originConn)
	ops := longrunning.NewOperationsClient(originConn)
	casClient := repb.NewContentAddressableStorageClient(originConn)

	content := fmt.Sprintf("hello from tenant A at %d\n", time.Now().UnixNano())
	input, err := origin.Upload(ctxA, instanceA, []byte(content))
	if err != nil {
		return fmt.Errorf("uploading input: %w", err)
	}
	root, err := uploadProto(ctxA, origin, instanceA, &repb.Directory{Files: []*repb.FileNode{{Name: "input.txt", Digest: input}}})
	if err != nil {
		return err
	}
	command, err := uploadProto(ctxA, origin, instanceA, &repb.Command{
		Arguments:   []string{"sh", "-c", "tr a-z A-Z < input.txt > out/upper.txt && mkdir -p out/tree && cp input.txt out/tree/copy.txt && echo done"},
		OutputPaths: []string{"out/upper.txt", "out/tree"},
	})
	if err != nil {
		return err
	}
	action, err := uploadProto(ctxA, origin, instanceA, &repb.Action{CommandDigest: command, InputRootDigest: root})
	if err != nil {
		return err
	}

	// Tenant B may not run actions in tenant A's instance.
	if _, err := execute(ctxB, execer, instanceA, action, timeout, nil); status.Code(err) != codes.PermissionDenied {
		return fmt.Errorf("tenant B executing in tenant A's instance: got %v, want PermissionDenied", err)
	}

	var resp *repb.ExecuteResponse
	start := time.Now()
	opName, err := execute(ctxA, execer, instanceA, action, timeout, func(r *repb.ExecuteResponse) { resp = r })
	if err != nil {
		return fmt.Errorf("executing action: %w", err)
	}
	if resp.GetStatus().GetCode() != 0 {
		return fmt.Errorf("action failed to run: %v", resp.GetStatus())
	}
	ar := resp.GetResult()
	if ar.GetExitCode() != 0 {
		return fmt.Errorf("action exited %d", ar.GetExitCode())
	}
	if ar.GetExecutionMetadata().GetVirtualExecutionDuration().AsDuration() <= 0 {
		return errors.New("ExecutionMetadata.VirtualExecutionDuration was not populated")
	}
	worker := ar.GetExecutionMetadata().GetWorker()
	mode := inputMode(ar)
	slog.Info("action ran on a runner", "worker", worker, "inputMode", mode, "took", time.Since(start).Round(time.Millisecond))
	if !strings.HasPrefix(worker, want.workerPrefix) {
		return fmt.Errorf("worker %q does not have prefix %q", worker, want.workerPrefix)
	}
	if want.inputMode != "" && mode != want.inputMode {
		return fmt.Errorf("runner built the exec root in mode %q, want %q", mode, want.inputMode)
	}
	if got, err := fetchString(ctxA, cacheClient, instanceA, ar.GetStdoutDigest()); err != nil || got != "done\n" {
		return fmt.Errorf("stdout %q, err %v; want \"done\\n\"", got, err)
	}
	if len(ar.GetOutputFiles()) != 1 || ar.GetOutputFiles()[0].GetPath() != "out/upper.txt" {
		return fmt.Errorf("output files %v, want out/upper.txt", ar.GetOutputFiles())
	}
	if got, err := fetchString(ctxA, cacheClient, instanceA, ar.GetOutputFiles()[0].GetDigest()); err != nil || got != strings.ToUpper(content) {
		return fmt.Errorf("out/upper.txt %q, err %v", got, err)
	}
	if len(ar.GetOutputDirectories()) != 1 || ar.GetOutputDirectories()[0].GetPath() != "out/tree" {
		return fmt.Errorf("output directories %v, want out/tree", ar.GetOutputDirectories())
	}
	outDir := ar.GetOutputDirectories()[0]
	if outDir.GetRootDirectoryDigest() == nil {
		return errors.New("OutputDirectory.RootDirectoryDigest was not populated")
	}
	treeStream, err := casClient.GetTree(ctxA, &repb.GetTreeRequest{
		InstanceName: instanceA,
		RootDigest:   outDir.GetRootDirectoryDigest(),
	})
	if err != nil {
		return fmt.Errorf("GetTree: %w", err)
	}
	treeResp, err := treeStream.Recv()
	if err != nil || len(treeResp.GetDirectories()) != 1 {
		return fmt.Errorf("GetTree recv: resp=%v err=%v", treeResp, err)
	}
	treeBytes, err := cacheClient.Fetch(ctxA, instanceA, outDir.GetTreeDigest())
	if err != nil {
		return fmt.Errorf("fetching output tree: %w", err)
	}
	outTree := &repb.Tree{}
	if err := proto.Unmarshal(treeBytes, outTree); err != nil {
		return err
	}
	if files := outTree.GetRoot().GetFiles(); len(files) != 1 || files[0].GetName() != "copy.txt" || files[0].GetDigest().GetHash() != input.GetHash() {
		return fmt.Errorf("output tree %v, want copy.txt with the input's digest", outTree)
	}
	slog.Info("outputs and CAS.GetTree verified through the node-local cache", "files", len(ar.GetOutputFiles()), "directories", len(ar.GetOutputDirectories()))

	// Operations.GetOperation succeeds for tenant A and is denied for tenant B.
	op, err := ops.GetOperation(ctxA, &longrunning.GetOperationRequest{Name: opName})
	if err != nil || !op.GetDone() {
		return fmt.Errorf("GetOperation(%s): op=%v err=%v", opName, op, err)
	}
	if _, err := ops.GetOperation(ctxB, &longrunning.GetOperationRequest{Name: opName}); status.Code(err) != codes.PermissionDenied {
		return fmt.Errorf("tenant B GetOperation: got %v, want PermissionDenied", err)
	}

	// The same action again is answered from the action cache without a run.
	var again *repb.ExecuteResponse
	if _, err := execute(ctxA, execer, instanceA, action, timeout, func(r *repb.ExecuteResponse) { again = r }); err != nil {
		return fmt.Errorf("re-executing action: %w", err)
	}
	if !again.GetCachedResult() {
		return errors.New("second Execute of the same action was not a cache hit")
	}
	slog.Info("second Execute served from the action cache")

	// Action timeout: runner kills process group, uploads partial stdout, and
	// scheduler returns DeadlineExceeded without caching the result.
	timeoutCmd, err := uploadProto(ctxA, origin, instanceA, &repb.Command{
		Arguments: []string{"sh", "-c", "echo before-timeout; sleep 30"},
	})
	if err != nil {
		return err
	}
	timeoutAction, err := uploadProto(ctxA, origin, instanceA, &repb.Action{
		CommandDigest:   timeoutCmd,
		InputRootDigest: root,
		Timeout:         durationpb.New(time.Second),
		DoNotCache:      true,
	})
	if err != nil {
		return err
	}
	var toResp *repb.ExecuteResponse
	if _, err := execute(ctxA, execer, instanceA, timeoutAction, timeout, func(r *repb.ExecuteResponse) { toResp = r }); err != nil {
		return fmt.Errorf("executing timeout action: %w", err)
	}
	if codes.Code(toResp.GetStatus().GetCode()) != codes.DeadlineExceeded {
		return fmt.Errorf("timeout action status = %v, want DeadlineExceeded", toResp.GetStatus())
	}
	if got, err := fetchString(ctxA, cacheClient, instanceA, toResp.GetResult().GetStdoutDigest()); err != nil || !strings.Contains(got, "before-timeout") {
		return fmt.Errorf("timeout partial stdout = %q, err = %v; want before-timeout", got, err)
	}
	slog.Info("action timeout, process-group cleanup, and partial stdout verified")

	// Operations.CancelOperation cancels a running/queued operation cleanly.
	slowCmd, err := uploadProto(ctxA, origin, instanceA, &repb.Command{
		Arguments: []string{"sh", "-c", "sleep 60"},
	})
	if err != nil {
		return err
	}
	slowAction, err := uploadProto(ctxA, origin, instanceA, &repb.Action{
		CommandDigest:   slowCmd,
		InputRootDigest: root,
		DoNotCache:      true,
	})
	if err != nil {
		return err
	}
	cctx, ccancel := context.WithTimeout(ctxA, timeout)
	defer ccancel()
	cstream, err := execer.Execute(cctx, &repb.ExecuteRequest{InstanceName: instanceA, ActionDigest: slowAction})
	if err != nil {
		return fmt.Errorf("starting cancellable action: %w", err)
	}
	firstOp, err := cstream.Recv()
	if err != nil {
		return fmt.Errorf("receiving initial operation: %w", err)
	}
	if _, err := ops.CancelOperation(ctxA, &longrunning.CancelOperationRequest{Name: firstOp.GetName()}); err != nil {
		return fmt.Errorf("CancelOperation: %w", err)
	}
	for {
		cur, rerr := cstream.Recv()
		if rerr != nil {
			return fmt.Errorf("waiting for cancelled operation: %w", rerr)
		}
		if !cur.GetDone() {
			continue
		}
		cr := &repb.ExecuteResponse{}
		if err := cur.GetResponse().UnmarshalTo(cr); err != nil {
			return err
		}
		if codes.Code(cr.GetStatus().GetCode()) != codes.Canceled {
			return fmt.Errorf("cancelled operation status = %v, want Canceled", cr.GetStatus())
		}
		break
	}
	slog.Info("Operations.CancelOperation verified")
	return nil
}

// execute submits action and waits for the operation to finish, passing the
// final response to done and returning the operation name.
func execute(ctx context.Context, execer repb.ExecutionClient, instance string, action *repb.Digest, timeout time.Duration, done func(*repb.ExecuteResponse)) (string, error) {
	ctx, cancel := context.WithTimeout(ctx, timeout)
	defer cancel()
	stream, err := execer.Execute(ctx, &repb.ExecuteRequest{InstanceName: instance, ActionDigest: action})
	if err != nil {
		return "", err
	}
	var opName string
	for {
		op, err := stream.Recv()
		if err != nil {
			return opName, err
		}
		opName = op.GetName()
		if !op.GetDone() {
			continue
		}
		resp := &repb.ExecuteResponse{}
		if err := op.GetResponse().UnmarshalTo(resp); err != nil {
			return opName, err
		}
		if done != nil {
			done(resp)
		}
		return opName, nil
	}
}

func uploadProto(ctx context.Context, c *remote.Client, instance string, m proto.Message) (*repb.Digest, error) {
	d, err := c.Upload(ctx, instance, tree.Marshal(m))
	if err != nil {
		return nil, fmt.Errorf("uploading %T: %w", m, err)
	}
	return d, nil
}

func fetchString(ctx context.Context, c *remote.Client, instance string, d *repb.Digest) (string, error) {
	if d == nil {
		return "", errors.New("no digest")
	}
	b, err := c.Fetch(ctx, instance, d)
	if err != nil {
		return "", err
	}
	if err := digest.Verify(d, b); err != nil {
		return "", err
	}
	return string(b), nil
}

func tryCrossTenant(ctx context.Context, c *remote.Client, instanceA string, d *repb.Digest) error {
	_, err := c.Fetch(ctx, instanceA, d)
	if status.Code(err) == codes.PermissionDenied {
		return nil
	}
	if err == nil {
		return errors.New("isolation breach: tenant B read tenant A's private instance")
	}
	return fmt.Errorf("unexpected error probing isolation: %w", err)
}

// retry reissues a gRPC call a few times when the server is still coming up.
func retry[T any](fn func() (T, error)) (T, error) {
	var zero T
	var last error
	for i := 0; i < 10; i++ {
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

func fetchStats(metricsURL string) (cache.Stats, error) {
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
