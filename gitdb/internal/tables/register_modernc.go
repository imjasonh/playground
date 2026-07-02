//go:build !js

package tables

import (
	"database/sql"
	"fmt"
	"sync"

	"github.com/values-conflict/go-sqlite-fdw/modernc"
)

var (
	moderncOnce sync.Once
	moderncErr  error
)

// Register registers every git virtual-table module on the modernc driver.
// modernc module registration is process-global, so repeated calls are no-ops.
func Register(db *sql.DB) error {
	moderncOnce.Do(func() {
		for _, d := range registry {
			if err := modernc.Register(db, d.module, d.factory, d.factory); err != nil {
				moderncErr = fmt.Errorf("register %s: %w", d.module, err)
				return
			}
		}
	})
	return moderncErr
}
