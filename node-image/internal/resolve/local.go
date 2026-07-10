package resolve

import (
	"encoding/json"
	"os"
)

func readFile(path string) ([]byte, error) {
	return os.ReadFile(path)
}

func parseNameVersionJSON(b []byte) (nameVer, error) {
	var m struct {
		Name    string `json:"name"`
		Version string `json:"version"`
	}
	if err := json.Unmarshal(b, &m); err != nil {
		return nameVer{}, err
	}
	return nameVer{name: m.Name, version: m.Version}, nil
}
