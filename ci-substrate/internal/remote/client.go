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

// Fetch implements cache.Origin by reading one blob, preferring the batch API
// and falling back to ByteStream for blobs over the batch limit.
func (c *Client) Fetch(ctx context.Context, instanceName string, d *repb.Digest) ([]byte, error) {
	if d.GetSizeBytes() <= MaxBatchBytes {
		resp, err := c.cas.BatchReadBlobs(ctx, &repb.BatchReadBlobsRequest{
			InstanceName: instanceName,
			Digests:      []*repb.Digest{d},
		})
		if err != nil {
			return nil, err
		}
		if len(resp.GetResponses()) != 1 {
			return nil, fmt.Errorf("batch read returned %d responses", len(resp.GetResponses()))
		}
		r := resp.GetResponses()[0]
		if c := codes.Code(r.GetStatus().GetCode()); c != codes.OK {
			return nil, status.Error(c, r.GetStatus().GetMessage())
		}
		return r.GetData(), nil
	}
	return c.readStream(ctx, instanceName, d)
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

// Upload stores one blob, routing small blobs through BatchUpdateBlobs and
// large ones through ByteStream.Write, as the plan's output handling requires.
func (c *Client) Upload(ctx context.Context, instanceName string, b []byte) (*repb.Digest, error) {
	d := digest.FromBytes(b)
	if _, _, err := c.PutBatch(ctx, instanceName, map[string][]byte{digest.Key(d): b}); err != nil {
		return nil, err
	}
	return d, nil
}

// FetchBatch reads many blobs, grouping the ones that fit into as few
// BatchReadBlobs calls as the size limit allows and streaming the rest.
// The result is keyed by digest.Key.
func (c *Client) FetchBatch(ctx context.Context, instanceName string, digests []*repb.Digest) (map[string][]byte, error) {
	out := map[string][]byte{}
	var batch []*repb.Digest
	var batchSize int64
	flush := func() error {
		if len(batch) == 0 {
			return nil
		}
		resp, err := c.cas.BatchReadBlobs(ctx, &repb.BatchReadBlobsRequest{
			InstanceName: instanceName,
			Digests:      batch,
		})
		if err != nil {
			return err
		}
		if len(resp.GetResponses()) != len(batch) {
			return fmt.Errorf("batch read returned %d responses for %d digests", len(resp.GetResponses()), len(batch))
		}
		for _, r := range resp.GetResponses() {
			if cd := codes.Code(r.GetStatus().GetCode()); cd != codes.OK {
				return status.Error(cd, r.GetStatus().GetMessage())
			}
			out[digest.Key(r.GetDigest())] = r.GetData()
		}
		batch, batchSize = nil, 0
		return nil
	}
	for _, d := range digests {
		if d.GetSizeBytes() > MaxBatchBytes {
			if err := flush(); err != nil {
				return nil, err
			}
			b, err := c.readStream(ctx, instanceName, d)
			if err != nil {
				return nil, err
			}
			out[digest.Key(d)] = b
			continue
		}
		if len(batch) > 0 && (len(batch) >= batchSendCount || batchSize+d.GetSizeBytes() > batchSendBytes) {
			if err := flush(); err != nil {
				return nil, err
			}
		}
		batch = append(batch, d)
		batchSize += d.GetSizeBytes()
	}
	if err := flush(); err != nil {
		return nil, err
	}
	return out, nil
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
	var reqs []*repb.BatchUpdateBlobsRequest_Request
	var reqSize int64
	var sent int64
	flush := func() error {
		if len(reqs) == 0 {
			return nil
		}
		resp, err := c.cas.BatchUpdateBlobs(ctx, &repb.BatchUpdateBlobsRequest{
			InstanceName: instanceName,
			Requests:     reqs,
		})
		if err != nil {
			return err
		}
		for _, r := range resp.GetResponses() {
			if cd := codes.Code(r.GetStatus().GetCode()); cd != codes.OK {
				return status.Error(cd, r.GetStatus().GetMessage())
			}
		}
		reqs, reqSize = nil, 0
		return nil
	}
	for _, d := range missing {
		data := blobs[digest.Key(d)]
		if int64(len(data)) > MaxBatchBytes {
			if err := flush(); err != nil {
				return 0, 0, err
			}
			if _, err := c.writeStream(ctx, instanceName, d, data); err != nil {
				return 0, 0, err
			}
			sent += int64(len(data))
			continue
		}
		if len(reqs) > 0 && (len(reqs) >= batchSendCount || reqSize+int64(len(data)) > batchSendBytes) {
			if err := flush(); err != nil {
				return 0, 0, err
			}
		}
		reqs = append(reqs, &repb.BatchUpdateBlobsRequest_Request{Digest: byKey[digest.Key(d)], Data: data})
		reqSize += int64(len(data))
		sent += int64(len(data))
	}
	if err := flush(); err != nil {
		return 0, 0, err
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
