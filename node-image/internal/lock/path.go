package lock

import (
	"path/filepath"
)

func absClean(dir string) (string, error) {
	return filepath.Abs(dir)
}

func parentDir(dir string) string {
	return filepath.Dir(dir)
}

// ImporterKey returns the lock importers map key for packageDir relative to lockRoot.
// Root importer is ".".
func ImporterKey(lockRoot, packageDir string) (string, error) {
	absRoot, err := filepath.Abs(lockRoot)
	if err != nil {
		return "", err
	}
	absPkg, err := filepath.Abs(packageDir)
	if err != nil {
		return "", err
	}
	rel, err := filepath.Rel(absRoot, absPkg)
	if err != nil {
		return "", err
	}
	rel = filepath.ToSlash(rel)
	if rel == "." || rel == "" {
		return ".", nil
	}
	return rel, nil
}
