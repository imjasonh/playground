package store

import (
	"bytes"
	"context"
	"crypto/tls"
	"errors"
	"fmt"
	"io"
	"io/fs"
	"net/http"
	"os"
	"path/filepath"
	"sync"
	"sync/atomic"
	"time"

	"cloud.google.com/go/storage"
	"github.com/aws/aws-sdk-go-v2/aws"
	"github.com/aws/aws-sdk-go-v2/config"
	"github.com/aws/aws-sdk-go-v2/credentials"
	"github.com/aws/aws-sdk-go-v2/feature/s3/manager"
	"github.com/aws/aws-sdk-go-v2/service/s3"
	"github.com/aws/smithy-go"
	"github.com/benbjohnson/litestream"
	"github.com/benbjohnson/litestream/file"
	"github.com/benbjohnson/litestream/gs"
	lss3 "github.com/benbjohnson/litestream/s3"
	"github.com/superfly/ltx"
	"google.golang.org/api/googleapi"

	"github.com/imjasonh/playground/cloudrun-sqlite/internal/observe"
)

// l0ChunkSize is the upload buffer for an L0 object. The Cloud Storage
// client's default is 16 MiB, and it allocates that buffer on every upload
// while readers wait for the batch. An L0 file is a handful of pages, so
// 1 MiB still sends it in one request and still lets the client retry.
const l0ChunkSize = 1 << 20

// errExists reports that a conditional create found an object already there.
var errExists = errors.New("object already exists")

// l0Creator creates an L0 LTX object only if no object exists at its key.
// Implementations must use the same key layout and metadata as the
// Litestream client for the backend, so the rest of Litestream can list and
// read the files they write.
type l0Creator interface {
	create(ctx context.Context, minTXID, maxTXID ltx.TXID, data []byte, ts time.Time) error
}

// fencedClient makes L0 uploads conditional. Two instances that both think
// they are the writer (Cloud Run overlaps instances during a deploy) then
// cannot both publish the same TXID: the loser gets litestream.ErrConflict
// instead of silently overwriting the winner's transaction.
type fencedClient struct {
	litestream.ReplicaClient
	creator   l0Creator
	conflicts atomic.Int64
	warm      atomic.Pointer[warmCache]
	gets      latencies
	lists     latencies
	puts      latencies
}

func newFencedClient(ctx context.Context, c litestream.ReplicaClient) (*fencedClient, error) {
	var creator l0Creator
	switch c := c.(type) {
	case *file.ReplicaClient:
		creator = &fileCreator{client: c}
	case *gs.ReplicaClient:
		client, err := storage.NewClient(ctx)
		if err != nil {
			return nil, fmt.Errorf("gcs client: %w", err)
		}
		creator = &gcsCreator{bucket: client.Bucket(c.Bucket), path: c.Path}
	case *lss3.ReplicaClient:
		client, err := newS3Client(ctx, c)
		if err != nil {
			return nil, err
		}
		creator = &s3Creator{client: client, bucket: c.Bucket, path: c.Path}
	default:
		return nil, fmt.Errorf("replica type %q does not support conditional writes", c.Type())
	}
	return &fencedClient{ReplicaClient: c, creator: creator}, nil
}

func (c *fencedClient) WriteLTXFile(ctx context.Context, level int, minTXID, maxTXID ltx.TXID, r io.Reader) (*ltx.FileInfo, error) {
	ctx, end := observe.Span(ctx, "replica.put")
	start := time.Now()
	info, err := c.writeLTXFile(ctx, level, minTXID, maxTXID, r)
	d := time.Since(start)
	c.puts.add(d)
	observe.Measure(ctx, "replica.operation", "op", "put", d)
	end(err)
	return info, err
}

func (c *fencedClient) writeLTXFile(ctx context.Context, level int, minTXID, maxTXID ltx.TXID, r io.Reader) (*ltx.FileInfo, error) {
	if level != 0 {
		return c.ReplicaClient.WriteLTXFile(ctx, level, minTXID, maxTXID, r)
	}
	data, err := io.ReadAll(r)
	if err != nil {
		return nil, err
	}
	hdr, _, err := ltx.PeekHeader(bytes.NewReader(data))
	if err != nil {
		return nil, fmt.Errorf("read LTX header: %w", err)
	}
	ts := time.UnixMilli(hdr.Timestamp).UTC()

	if err := c.creator.create(ctx, minTXID, maxTXID, data, ts); errors.Is(err, errExists) {
		// A retry of our own upload, whose first response was lost, finds
		// our own bytes. Anything else is another writer's transaction.
		if !c.sameObject(ctx, minTXID, maxTXID, data) {
			c.conflicts.Add(1)
			return nil, fmt.Errorf("%w: another writer already published L0 %s", litestream.ErrConflict, ltx.FormatFilename(minTXID, maxTXID))
		}
	} else if err != nil {
		return nil, err
	}
	return &ltx.FileInfo{Level: 0, MinTXID: minTXID, MaxTXID: maxTXID, Size: int64(len(data)), CreatedAt: ts}, nil
}

func (c *fencedClient) remoteOpen(ctx context.Context, level int, minTXID, maxTXID ltx.TXID, offset, size int64) (io.ReadCloser, error) {
	ctx, end := observe.Span(ctx, "replica.get")
	start := time.Now()
	rc, err := c.ReplicaClient.OpenLTXFile(ctx, level, minTXID, maxTXID, offset, size)
	d := time.Since(start)
	c.gets.add(d)
	observe.Measure(ctx, "replica.operation", "op", "get", d)
	end(err)
	return rc, err
}

func (c *fencedClient) remoteList(ctx context.Context, level int, seek ltx.TXID, useMetadata bool) (ltx.FileIterator, error) {
	ctx, end := observe.Span(ctx, "replica.list")
	start := time.Now()
	itr, err := c.ReplicaClient.LTXFiles(ctx, level, seek, useMetadata)
	if err != nil {
		d := time.Since(start)
		c.lists.add(d)
		observe.Measure(ctx, "replica.operation", "op", "list", d)
		end(err)
		return nil, err
	}
	return &recordingIter{FileIterator: itr, start: start, done: func(d time.Duration, err error) {
		c.lists.add(d)
		observe.Measure(ctx, "replica.operation", "op", "list", d)
		end(err)
	}}, nil
}

// recordingIter times a listing through Close, which is when the pages of
// results have been read.
type recordingIter struct {
	ltx.FileIterator
	start time.Time
	once  sync.Once
	done  func(time.Duration, error)
}

func (r *recordingIter) Close() error {
	err := r.FileIterator.Close()
	r.once.Do(func() {
		spanErr := err
		if spanErr == nil {
			spanErr = r.FileIterator.Err()
		}
		r.done(time.Since(r.start), spanErr)
	})
	return err
}

func (c *fencedClient) sameObject(ctx context.Context, minTXID, maxTXID ltx.TXID, data []byte) bool {
	rc, err := c.OpenLTXFile(ctx, 0, minTXID, maxTXID, 0, 0)
	if err != nil {
		return false
	}
	defer rc.Close()
	existing, err := io.ReadAll(rc)
	return err == nil && bytes.Equal(existing, data)
}

type fileCreator struct{ client *file.ReplicaClient }

func (f *fileCreator) create(_ context.Context, minTXID, maxTXID ltx.TXID, data []byte, ts time.Time) error {
	path := f.client.LTXFilePath(0, minTXID, maxTXID)
	dir := filepath.Dir(path)
	if err := os.MkdirAll(dir, 0o755); err != nil {
		return err
	}
	// The .tmp suffix matches the files Litestream's file client sweeps up.
	tmp, err := os.CreateTemp(dir, ".fence-*.tmp")
	if err != nil {
		return err
	}
	defer os.Remove(tmp.Name())
	if _, err := tmp.Write(data); err != nil {
		tmp.Close()
		return err
	}
	if err := tmp.Sync(); err != nil {
		tmp.Close()
		return err
	}
	if err := tmp.Close(); err != nil {
		return err
	}
	// link(2) fails if the destination exists, unlike rename(2).
	if err := os.Link(tmp.Name(), path); err != nil {
		if errors.Is(err, fs.ErrExist) {
			return errExists
		}
		return err
	}
	return os.Chtimes(path, ts, ts)
}

type gcsCreator struct {
	bucket *storage.BucketHandle
	path   string
}

func (g *gcsCreator) create(ctx context.Context, minTXID, maxTXID ltx.TXID, data []byte, ts time.Time) error {
	key := litestream.LTXFilePath(g.path, 0, minTXID, maxTXID)
	w := g.bucket.Object(key).If(storage.Conditions{DoesNotExist: true}).NewWriter(ctx)
	w.ChunkSize = l0ChunkSize
	w.Metadata = map[string]string{gs.MetadataKeyTimestamp: ts.Format(time.RFC3339Nano)}
	if _, err := w.Write(data); err != nil {
		w.Close()
		return err
	}
	if err := w.Close(); err != nil {
		var gerr *googleapi.Error
		if errors.As(err, &gerr) && gerr.Code == http.StatusPreconditionFailed {
			return errExists
		}
		return err
	}
	return nil
}

type s3Creator struct {
	client *s3.Client
	bucket string
	path   string
}

func (s *s3Creator) create(ctx context.Context, minTXID, maxTXID ltx.TXID, data []byte, ts time.Time) error {
	key := s.path + "/" + fmt.Sprintf("%04x/%s", 0, ltx.FormatFilename(minTXID, maxTXID))
	_, err := s.client.PutObject(ctx, &s3.PutObjectInput{
		Bucket:        aws.String(s.bucket),
		Key:           aws.String(key),
		Body:          bytes.NewReader(data),
		ContentLength: aws.Int64(int64(len(data))),
		IfNoneMatch:   aws.String("*"),
		Metadata:      map[string]string{lss3.MetadataKeyTimestamp: ts.Format(time.RFC3339Nano)},
	})
	var apiErr smithy.APIError
	if errors.As(err, &apiErr) {
		switch apiErr.ErrorCode() {
		case "PreconditionFailed", "ConditionalRequestConflict":
			return errExists
		}
	}
	return err
}

// newS3Client builds an S3 client from the same settings Litestream's S3
// replica client parsed out of the replica URL.
func newS3Client(ctx context.Context, c *lss3.ReplicaClient) (*s3.Client, error) {
	region := c.Region
	if region == "" {
		region = lss3.DefaultRegion
	}
	transport := http.DefaultTransport.(*http.Transport).Clone()
	if c.SkipVerify {
		transport.TLSClientConfig = &tls.Config{InsecureSkipVerify: true}
	}
	opts := []func(*config.LoadOptions) error{
		config.WithRegion(region),
		config.WithHTTPClient(&http.Client{Transport: transport}),
	}
	if c.AccessKeyID != "" && c.SecretAccessKey != "" {
		opts = append(opts, config.WithCredentialsProvider(
			credentials.NewStaticCredentialsProvider(c.AccessKeyID, c.SecretAccessKey, "")))
	}
	cfg, err := config.LoadDefaultConfig(ctx, opts...)
	if err != nil {
		return nil, fmt.Errorf("s3 config: %w", err)
	}
	if c.Region == "" && c.Endpoint == "" {
		region, err := manager.GetBucketRegion(ctx, s3.NewFromConfig(cfg), c.Bucket)
		if err != nil {
			return nil, fmt.Errorf("s3 bucket region: %w", err)
		}
		cfg.Region = region
	}
	return s3.NewFromConfig(cfg, func(o *s3.Options) {
		if c.Endpoint != "" {
			o.BaseEndpoint = aws.String(c.Endpoint)
		}
		o.UsePathStyle = c.ForcePathStyle
	}), nil
}
