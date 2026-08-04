// Package store defines persistence for users, keys, and apps.
// Memory is used in tests and local gateway; Firestore for production.
package store

import "context"

// User is a registered platform identity (from join).
type User struct {
	ID string // e.g. "alice"
}

// Session cutover strategies for deploy (see design §8).
const (
	StrategyDrain = "drain" // default: route new→new, drain old, kick after timeout
	StrategyKick  = "kick"  // kick now, cut over immediately
)

// App is an app in a user's namespace.
type App struct {
	Owner           string
	Name            string
	Image           string // digest-pinned reference (required for a bootable app)
	PreviousImage   string // image before last deploy (rollback later)
	Tier            string // "tiny" | "small"
	SessionStrategy string // StrategyDrain | StrategyKick; empty means drain
	ActiveGen       string // generation receiving new sessions
	DrainingGen     string // cordoned generation (drain cutover); "" is legacy singleton
	DrainUntilUnix  int64  // unix seconds; 0 if not draining
}

// Store is the control-plane persistence surface used by the gateway.
type Store interface {
	LookupUserByKey(ctx context.Context, keyFingerprint string) (*User, error)
	CreateUser(ctx context.Context, id, keyFingerprint string) error
	AddKey(ctx context.Context, userID, keyFingerprint string) error
	HasApp(ctx context.Context, userID, app string) (bool, error)
	GetApp(ctx context.Context, userID, app string) (*App, error)
	UpsertApp(ctx context.Context, app App) error
	ListApps(ctx context.Context, userID string) ([]App, error)
}
