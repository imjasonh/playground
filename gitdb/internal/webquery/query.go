// Package webquery converts database/sql result sets into JSON-safe values for
// the browser demo.
package webquery

import (
	"context"
	"database/sql"
	"encoding/base64"
	"fmt"
	"strings"
	"time"
)

// Result is the bounded result of one SQL statement.
type Result struct {
	Columns   []string `json:"columns"`
	Rows      [][]any  `json:"rows"`
	Truncated bool     `json:"truncated,omitempty"`
	ElapsedMS int64    `json:"elapsedMs"`
}

// Run executes one SQL statement and returns at most maxRows rows.
func Run(ctx context.Context, db *sql.DB, statement string, maxRows int) (result Result, err error) {
	started := time.Now()
	defer func() {
		result.ElapsedMS = time.Since(started).Milliseconds()
	}()

	if strings.TrimSpace(statement) == "" {
		return result, fmt.Errorf("query is empty")
	}
	if maxRows <= 0 {
		return result, fmt.Errorf("row limit must be positive")
	}

	rows, err := db.QueryContext(ctx, statement)
	if err != nil {
		return result, err
	}
	defer rows.Close()

	result.Columns, err = rows.Columns()
	if err != nil {
		return result, err
	}

	for len(result.Rows) < maxRows && rows.Next() {
		values := make([]any, len(result.Columns))
		dest := make([]any, len(values))
		for i := range values {
			dest[i] = &values[i]
		}
		if err := rows.Scan(dest...); err != nil {
			return result, err
		}
		for i, value := range values {
			values[i] = jsonValue(value)
		}
		result.Rows = append(result.Rows, values)
	}
	if err := rows.Err(); err != nil {
		return result, err
	}
	if len(result.Rows) == maxRows && rows.Next() {
		result.Truncated = true
	}
	return result, rows.Err()
}

func jsonValue(value any) any {
	switch value := value.(type) {
	case nil, int64, float64, bool, string:
		return value
	case []byte:
		return "base64:" + base64.StdEncoding.EncodeToString(value)
	case time.Time:
		return value.Format(time.RFC3339Nano)
	default:
		return fmt.Sprint(value)
	}
}
