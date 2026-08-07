package ocirootfs

import (
	"fmt"
	"os"
	"path/filepath"
	"regexp"
	"sort"
	"strings"
	"sync"
	"time"
)

const (
	// DefaultCacheBytes bounds digest materializations to a fraction of the
	// production agent boot disk.
	DefaultCacheBytes int64 = 8 << 30
	maxBootSpecBytes        = 64 << 10
)

var (
	cacheEvictionMu    sync.Mutex
	activeCacheEntries = make(map[string]int)
	cacheReservations  = make(map[string]int64)
	cacheBasePattern   = regexp.MustCompile(`^[0-9a-f]{64}-v[0-9]+-[0-9]+m$`)
)

type cacheEntry struct {
	base    string
	paths   []string
	bytes   int64
	lastUse time.Time
}

func markCacheEntryActive(base string) {
	cacheEvictionMu.Lock()
	defer cacheEvictionMu.Unlock()
	activeCacheEntries[base]++
}

func unmarkCacheEntryActive(base string) {
	cacheEvictionMu.Lock()
	defer cacheEvictionMu.Unlock()
	if activeCacheEntries[base] <= 1 {
		delete(activeCacheEntries, base)
		return
	}
	activeCacheEntries[base]--
}

func protectedCacheEntries(protectedBase string) map[string]bool {
	protected := map[string]bool{protectedBase: true}
	for base, count := range activeCacheEntries {
		if count > 0 {
			protected[base] = true
		}
	}
	return protected
}

func reservedCacheBytes(excludeBase string) int64 {
	var total int64
	for base, bytes := range cacheReservations {
		if base != excludeBase {
			total += bytes
		}
	}
	return total
}

func enforceRootfsCacheLimit(cacheDir string, maxBytes int64, protectedBase string) error {
	cacheEvictionMu.Lock()
	defer cacheEvictionMu.Unlock()
	return evictRootfsCache(
		cacheDir, maxBytes, reservedCacheBytes(""),
		protectedCacheEntries(protectedBase),
	)
}

func reserveRootfsCacheSpace(cacheDir string, maxBytes, incomingBytes int64, protectedBase string) error {
	cacheEvictionMu.Lock()
	defer cacheEvictionMu.Unlock()
	if _, exists := cacheReservations[protectedBase]; exists {
		return fmt.Errorf("rootfs cache entry %s already has a build reservation", protectedBase)
	}
	if err := evictRootfsCache(
		cacheDir, maxBytes, incomingBytes+reservedCacheBytes(""),
		protectedCacheEntries(protectedBase),
	); err != nil {
		return err
	}
	cacheReservations[protectedBase] = incomingBytes
	return nil
}

func releaseRootfsCacheSpace(base string) {
	cacheEvictionMu.Lock()
	delete(cacheReservations, base)
	cacheEvictionMu.Unlock()
}

func evictRootfsCache(cacheDir string, maxBytes, incomingBytes int64, protected map[string]bool) error {
	if maxBytes <= 0 {
		return fmt.Errorf("rootfs cache byte limit must be positive")
	}
	if incomingBytes < 0 || incomingBytes > maxBytes {
		return fmt.Errorf("rootfs cache item size %d exceeds byte limit %d", incomingBytes, maxBytes)
	}
	entries, err := os.ReadDir(cacheDir)
	if err != nil {
		return err
	}
	byBase := make(map[string]*cacheEntry)
	for _, entry := range entries {
		if entry.IsDir() {
			continue
		}
		suffix := ""
		switch {
		case strings.HasSuffix(entry.Name(), ".ext4"):
			suffix = ".ext4"
		case strings.HasSuffix(entry.Name(), ".boot.json"):
			suffix = ".boot.json"
		default:
			continue
		}
		base := strings.TrimSuffix(entry.Name(), suffix)
		if !cacheBasePattern.MatchString(base) {
			continue
		}
		info, err := entry.Info()
		if err != nil {
			return err
		}
		if !info.Mode().IsRegular() {
			continue
		}
		item := byBase[base]
		if item == nil {
			item = &cacheEntry{base: base}
			byBase[base] = item
		}
		item.paths = append(item.paths, filepath.Join(cacheDir, entry.Name()))
		item.bytes += info.Size()
		if info.ModTime().After(item.lastUse) {
			item.lastUse = info.ModTime()
		}
	}
	cached := make([]cacheEntry, 0, len(byBase))
	var total int64
	for _, item := range byBase {
		cached = append(cached, *item)
		total += item.bytes
	}
	if total+incomingBytes <= maxBytes {
		return nil
	}
	sort.Slice(cached, func(i, j int) bool {
		if !cached[i].lastUse.Equal(cached[j].lastUse) {
			return cached[i].lastUse.Before(cached[j].lastUse)
		}
		return cached[i].base < cached[j].base
	})
	for _, entry := range cached {
		if protected[entry.base] {
			continue
		}
		for _, path := range entry.paths {
			if err := os.Remove(path); err != nil && !os.IsNotExist(err) {
				return err
			}
		}
		total -= entry.bytes
		if total+incomingBytes <= maxBytes {
			return nil
		}
	}
	return fmt.Errorf("rootfs cache cannot fit %d bytes within %d-byte limit while active entries are protected", incomingBytes, maxBytes)
}

func touchCacheEntry(paths ...string) {
	now := time.Now()
	for _, path := range paths {
		_ = os.Chtimes(path, now, now)
	}
}
