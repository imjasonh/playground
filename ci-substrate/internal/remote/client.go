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
	if d.SizeBytes <= MaxBatchBytes {
		resp, err := c.cas.BatchUpdateBlobs(ctx, &repb.BatchUpdateBlobsRequest{
			InstanceName: instanceName,
			Requests: []*repb.BatchUpdateBlobsRequest_Request{
				{Digest: d, Data: b},
			},
		})
		if err != nil {
			return nil, err
		}
		if len(resp.GetResponses()) != 1 {
			return nil, fmt.Errorf("batch update returned %d responses", len(resp.GetResponses()))
		}
		if cd := codes.Code(resp.GetResponses()[0].GetStatus().GetCode()); cd != codes.OK {
			return nil, status.Error(cd, resp.GetResponses()[0].GetStatus().GetMessage())
		}
		return d, nil
	}
	return c.writeStream(ctx, instanceName, d, b)
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
