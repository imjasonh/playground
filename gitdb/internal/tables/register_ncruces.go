package tables

import (
	"fmt"

	sqlite3 "github.com/ncruces/go-sqlite3"
	ncrucesfdw "github.com/values-conflict/go-sqlite-fdw/ncruces"
)

// RegisterNcruces registers every git virtual-table module on one ncruces
// connection. Unlike modernc registration, this must run for each physical
// SQLite connection.
func RegisterNcruces(conn *sqlite3.Conn) error {
	for _, d := range registry {
		if err := ncrucesfdw.Register(conn, d.module, d.factory, d.factory); err != nil {
			return fmt.Errorf("register %s: %w", d.module, err)
		}
	}
	return nil
}
