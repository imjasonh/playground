package tenant

import (
	"encoding/json"
	"fmt"
)

// LoadJSON builds a Registry from a JSON object mapping each tenant token to
// the list of instance names it may use, for example:
//
//	{"tok-a":["tenant-a","shared"],"tok-b":["tenant-b","shared"]}
//
// It is how the cas and cascache binaries read their tenant table from the
// environment or a mounted config.
func LoadJSON(data []byte) (*Registry, error) {
	var m map[string][]string
	if err := json.Unmarshal(data, &m); err != nil {
		return nil, fmt.Errorf("parsing tenant config: %w", err)
	}
	r := NewRegistry()
	for tok, instances := range m {
		r.Allow(tok, instances...)
	}
	return r, nil
}
