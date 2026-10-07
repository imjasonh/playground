package main

import (
	"flag"
	"fmt"
	"math"
	"strconv"

	"github.com/imjasonh/playground/kube/k8s"
)

// The most disk space that each of a test Pod's volumes can use. The src
// volume holds the repository. The tmp volume is the home directory, which
// holds Go's module and build caches and the tests' temporary files. With
// -go-cache, the go-cache volume can use goCacheSize too.
var (
	sourceSize  = size(2 << 30)
	goCacheSize = size(4 << 30)
)

// cpuLimit is the most CPUs that each container in a test Pod can use. Go
// 1.25 and later set GOMAXPROCS from a container's CPU limit, and go test
// runs that many builds and test binaries at once, so the limit also bounds
// how many of them share the test container's memory.
var cpuLimit = flag.Int("cpu-limit", 2, "most CPUs that each container in a test Pod can use; 0 means no limit")

func init() {
	flag.Var(&sourceSize, "source-size", "most disk space that a test Pod's copy of the repository can use")
	flag.Var(&goCacheSize, "go-cache-size", "most disk space that a test Pod's Go module and build caches and temporary files can use; with -go-cache, its shared build outputs can use the same")
}

const (
	// storageRequest is the ephemeral storage that each container in a test
	// Pod requests, which the scheduler reserves on the Pod's node.
	storageRequest = 1 << 30
	// logSize is the room that a test Pod leaves for its containers' logs.
	logSize = 256 << 20
)

// size is a flag that holds a number of bytes, written as a size such as
// 2Gi.
type size int64

func (s *size) String() string { return formatSize(int64(*s)) }

func (s *size) Set(v string) error {
	n := parseSize(v)
	if n == 0 {
		return fmt.Errorf("%q isn't a size such as 2Gi", v)
	}
	*s = size(n)
	return nil
}

// podDisk is each test Pod's ephemeral-storage limit in bytes. The kubelet
// evicts a Pod whose volumes and logs use more than the Pod's limit, which
// is its containers' largest limit, so that limit covers every volume.
func podDisk() int64 {
	n := int64(sourceSize) + int64(goCacheSize) + logSize
	if goCache.url != "" {
		n += int64(goCacheSize)
	}
	return n
}

// resources returns the resources of a container in a test Pod that
// requests cpu and memory and can use up to memoryLimit.
func resources(cpu, memory, memoryLimit k8s.Quantity) *Resources {
	disk := podDisk()
	r := &Resources{
		Requests: map[string]k8s.Quantity{"cpu": cpu, "memory": memory, "ephemeral-storage": k8s.Quantity(formatSize(min(storageRequest, disk)))},
		Limits:   map[string]k8s.Quantity{"memory": memoryLimit, "ephemeral-storage": k8s.Quantity(formatSize(disk))},
	}
	if *cpuLimit > 0 {
		r.Limits["cpu"] = k8s.Quantity(strconv.Itoa(*cpuLimit))
	}
	return r
}

// parseSize returns the bytes in a size such as 2Gi or 500M. It returns 0
// for a size that isn't a positive whole number with a suffix of at most T
// or Ti, and for one so big that adding up the Pod's volumes could
// overflow.
func parseSize(s string) int64 {
	i := 0
	for i < len(s) && '0' <= s[i] && s[i] <= '9' {
		i++
	}
	unit := map[string]int64{"": 1, "k": 1e3, "M": 1e6, "G": 1e9, "T": 1e12, "Ki": 1 << 10, "Mi": 1 << 20, "Gi": 1 << 30, "Ti": 1 << 40}[s[i:]]
	n, err := strconv.ParseInt(s[:i], 10, 64)
	if unit == 0 || err != nil || n <= 0 || n > math.MaxInt64/4/unit {
		return 0
	}
	return n * unit
}

// formatSize writes n bytes as a size in the largest binary unit that
// divides it.
func formatSize(n int64) string {
	units := []string{"", "Ki", "Mi", "Gi", "Ti"}
	i := 0
	for i < len(units)-1 && n%1024 == 0 {
		n /= 1024
		i++
	}
	return strconv.FormatInt(n, 10) + units[i]
}
