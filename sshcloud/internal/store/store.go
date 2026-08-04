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
	Image           string // digest-pinned reference; empty for lazy platform demos until first wake
	Tier            string // "tiny" | "small"
	Demo            bool   // platform demo (e.g. fortune) — may lazy-create
	SessionStrategy string // StrategyDrain | StrategyKick; empty means drain
}

// Store is the control-plane persistence surface used by the gateway.
type Store interface {
	LookupUserByKey(ctx context.Context, keyFingerprint string) (*User, error)
	CreateUser(ctx context.Context, id, keyFingerprint string) error
	AddKey(ctx context.Context, userID, keyFingerprint string) error
	HasApp(ctx context.Context, userID, app string) (bool, error)
	GetApp(ctx context.Context, userID, app string) (*App, error)
	UpsertApp(ctx context.Context, app App) error
	EnsureDemoApp(ctx context.Context, userID, app string) error
	ListApps(ctx context.Context, userID string) ([]App, error)
}

// PlatformDemos are app names the menu always offers (lazy-created on connect).
var PlatformDemos = map[string]struct{}{
	"fortune": {},
}

// IsPlatformDemo reports whether name is a lazy platform demo.
func IsPlatformDemo(name string) bool {
	_, ok := PlatformDemos[name]
	return ok
}
