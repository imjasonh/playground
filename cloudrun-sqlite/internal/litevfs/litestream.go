package litevfs

import "github.com/benbjohnson/litestream"

// vfs.go and vfs_config.go are copied from package litestream, so these
// aliases resolve the names they used unqualified to the upstream module.

type (
	ReplicaClient    = litestream.ReplicaClient
	Compactor        = litestream.Compactor
	CompactionLevel  = litestream.CompactionLevel
	CompactionLevels = litestream.CompactionLevels
	DBNotReadyError  = litestream.DBNotReadyError
)

const (
	SnapshotLevel       = litestream.SnapshotLevel
	DefaultSyncInterval = litestream.DefaultSyncInterval
)

var (
	CalcRestorePlan         = litestream.CalcRestorePlan
	DefaultCompactionLevels = litestream.DefaultCompactionLevels
	ErrDBNotReady           = litestream.ErrDBNotReady
	ErrNoCompaction         = litestream.ErrNoCompaction
	ErrTxNotAvailable       = litestream.ErrTxNotAvailable
	FetchLTXHeader          = litestream.FetchLTXHeader
	FetchPage               = litestream.FetchPage
	FetchPageIndex          = litestream.FetchPageIndex
	NewCompactor            = litestream.NewCompactor
	NewReplicaClientFromURL = litestream.NewReplicaClientFromURL
)
