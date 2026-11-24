package tenant

import (
	"encoding/json"
	"fmt"
)

type tokenGrant struct {
	Instances           []string `json:"instances"`
	ActionCacheReadOnly bool     `json:"action_cache_read_only"`
}

// LoadJSON builds a Registry from a JSON object mapping each tenant token to
// either a list of allowed instance names or a grant object:
//
//	{
//	  "tok-a": ["tenant-a", "shared"],
//	  "tok-dev": {"instances": ["tenant-a"], "action_cache_read_only": true}
//	}
//
// It is how the cas and cascache binaries read their tenant table from the
// environment or a mounted config.
func LoadJSON(data []byte) (*Registry, error) {
	var raw map[string]json.RawMessage
	if err := json.Unmarshal(data, &raw); err != nil {
		return nil, fmt.Errorf("parsing tenant config: %w", err)
	}
	r := NewRegistry()
	for tok, v := range raw {
		var instances []string
		if err := json.Unmarshal(v, &instances); err == nil {
			r.Allow(tok, instances...)
			continue
		}
		var grant tokenGrant
		if err := json.Unmarshal(v, &grant); err != nil {
			return nil, fmt.Errorf("parsing tenant config for token: %w", err)
		}
		if grant.ActionCacheReadOnly {
			r.AllowReadOnlyAC(tok, grant.Instances...)
		} else {
			r.Allow(tok, grant.Instances...)
		}
	}
	return r, nil
}
