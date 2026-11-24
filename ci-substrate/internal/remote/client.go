package remote

import (
	"context"
	"fmt"
	"io"

	repb "github.com/bazelbuild/remote-apis/build/bazel/remote/execution/v2"
	"github.com/google/uuid"
	"google.golang.org/genproto/googleapis/bytestream"
	"google.golang.org/grpc"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"

	"github.com/imjasonh/playground/ci-substrate/internal/digest"
)

// Client is a CAS and action-cache client over a single gRPC connection. The
// cache uses it as its Origin; the runner uses it to read inputs, upload
// outputs, and read and write the action cache.
type Client struct {
	cas repb.ContentAddressableStorageClient
	ac  repb.ActionCacheClient
	bs  bytestream.ByteStreamClient
}

// NewClient wraps an existing gRPC connection.
func NewClient(conn grpc.ClientConnInterface) *Client {
	return &Client{
		cas: repb.NewContentAddressableStorageClient(conn),
		ac:  repb.NewActionCacheClient(conn),
		bs:  bytestream.NewByteStreamClient(conn),
	}
}

// Fetch reads one blob.
func (c *Client) Fetch(ctx context.Context, instanceName string, d *repb.Digest) ([]byte, error) {
	bs, err := c.FetchBatch(ctx, instanceName, []*repb.Digest{d})
	if err != nil {
		return nil, err
	}
	return bs[0], nil
}

// FetchBatch reads ds and returns their contents in the order of ds. It
// reads each distinct blob once: small blobs share BatchReadBlobs calls, and
// anything over the batch limit goes by ByteStream.
func (c *Client) FetchBatch(ctx context.Context, instanceName string, ds []*repb.Digest) ([][]byte, error) {
	data := map[string][]byte{}
	seen := map[string]bool{}
	var small []*repb.Digest
	for _, d := range ds {
		k := digest.Key(d)
		if seen[k] {
			continue
		}
		seen[k] = true
		if d.GetSizeBytes() <= MaxBatchBytes {
			small = append(small, d)
			continue
		}
		b, err := c.readStream(ctx, instanceName, d)
		if err != nil {
			return nil, err
		}
		data[k] = b
	}
	for _, batch := range digest.Batches(small, batchSendCount, batchSendBytes) {
		resp, err := c.cas.BatchReadBlobs(ctx, &repb.BatchReadBlobsRequest{InstanceName: instanceName, Digests: batch})
		if err != nil {
			return nil, err
		}
		for _, r := range resp.GetResponses() {
			if cd := codes.Code(r.GetStatus().GetCode()); cd != codes.OK {
				return nil, status.Error(cd, r.GetStatus().GetMessage())
			}
			data[digest.Key(r.GetDigest())] = r.GetData()
		}
	}
	out := make([][]byte, len(ds))
	for i, d := range ds {
		b, ok := data[digest.Key(d)]
		if !ok {
			return nil, fmt.Errorf("batch read returned no response for %s", digest.Key(d))
		}
		out[i] = b
	}
	return out, nil
}

func (c *Client) readStream(ctx context.Context, instanceName string, d *repb.Digest) ([]byte, error) {
	stream, err := c.bs.Read(ctx, &bytestream.ReadRequest{ResourceName: ReadResourceName(instanceName, d)})
	if err != nil {
		return nil, err
	}
	var buf []byte
	for {
		resp, err := stream.Recv()
		if err == io.EOF {
			break
		}
		if err != nil {
			return nil, err
		}
		buf = append(buf, resp.GetData()...)
	}
	return buf, nil
}

// FindMissing returns which of digests the CAS lacks.
func (c *Client) FindMissing(ctx context.Context, instanceName string, digests []*repb.Digest) ([]*repb.Digest, error) {
	resp, err := c.cas.FindMissingBlobs(ctx, &repb.FindMissingBlobsRequest{
		InstanceName: instanceName,
		BlobDigests:  digests,
	})
	if err != nil {
		return nil, err
	}
	return resp.GetMissingBlobDigests(), nil
}

// Upload stores one blob if the CAS lacks it.
func (c *Client) Upload(ctx context.Context, instanceName string, b []byte) (*repb.Digest, error) {
	d := digest.FromBytes(b)
	if _, _, err := c.PutBatch(ctx, instanceName, map[string][]byte{digest.Key(d): b}); err != nil {
		return nil, err
	}
	return d, nil
}

// PutBatch stores the blobs the CAS is missing. One FindMissingBlobs covers
// the whole set; the missing small blobs share BatchUpdateBlobs calls, and
// anything over the batch limit goes by ByteStream. It returns how many
// blobs were missing and how many bytes were sent.
func (c *Client) PutBatch(ctx context.Context, instanceName string, blobs map[string][]byte) (int, int64, error) {
	if len(blobs) == 0 {
		return 0, 0, nil
	}
	byKey := map[string]*repb.Digest{}
	var digests []*repb.Digest
	for _, data := range blobs {
		d := digest.FromBytes(data)
		byKey[digest.Key(d)] = d
		digests = append(digests, d)
	}
	missing, err := c.FindMissing(ctx, instanceName, digests)
	if err != nil {
		return 0, 0, err
	}
	var small []*repb.Digest
	var sent int64
	for _, d := range missing {
		data := blobs[digest.Key(d)]
		sent += int64(len(data))
		if int64(len(data)) <= MaxBatchBytes {
			small = append(small, byKey[digest.Key(d)])
			continue
		}
		if _, err := c.writeStream(ctx, instanceName, d, data); err != nil {
			return 0, 0, err
		}
	}
	for _, batch := range digest.Batches(small, batchSendCount, batchSendBytes) {
		req := &repb.BatchUpdateBlobsRequest{InstanceName: instanceName}
		for _, d := range batch {
			req.Requests = append(req.Requests, &repb.BatchUpdateBlobsRequest_Request{Digest: d, Data: blobs[digest.Key(d)]})
		}
		resp, err := c.cas.BatchUpdateBlobs(ctx, req)
		if err != nil {
			return 0, 0, err
		}
		for _, r := range resp.GetResponses() {
			if cd := codes.Code(r.GetStatus().GetCode()); cd != codes.OK {
				return 0, 0, status.Error(cd, r.GetStatus().GetMessage())
			}
		}
	}
	return len(missing), sent, nil
}

func (c *Client) writeStream(ctx context.Context, instanceName string, d *repb.Digest, b []byte) (*repb.Digest, error) {
	stream, err := c.bs.Write(ctx)
	if err != nil {
		return nil, err
	}
	name := WriteResourceName(instanceName, uuid.NewString(), d)
	const chunk = 1 << 20
	for off := 0; off < len(b); off += chunk {
		end := min(off+chunk, len(b))
		if err := stream.Send(&bytestream.WriteRequest{
			ResourceName: name,
			WriteOffset:  int64(off),
			Data:         b[off:end],
			FinishWrite:  end == len(b),
		}); err != nil {
			return nil, err
		}
	}
	if _, err := stream.CloseAndRecv(); err != nil {
		return nil, err
	}
	return d, nil
}

// GetActionResult returns a cached action result, or (nil, false) when absent.
func (c *Client) GetActionResult(ctx context.Context, instanceName string, action *repb.Digest) (*repb.ActionResult, bool, error) {
	ar, err := c.ac.GetActionResult(ctx, &repb.GetActionResultRequest{
		InstanceName: instanceName,
		ActionDigest: action,
	})
	if status.Code(err) == codes.NotFound {
		return nil, false, nil
	}
	if err != nil {
		return nil, false, err
	}
	return ar, true, nil
}

// UpdateActionResult records an action result.
func (c *Client) UpdateActionResult(ctx context.Context, instanceName string, action *repb.Digest, ar *repb.ActionResult) error {
	_, err := c.ac.UpdateActionResult(ctx, &repb.UpdateActionResultRequest{
		InstanceName: instanceName,
		ActionDigest: action,
		ActionResult: ar,
	})
	return err
}
