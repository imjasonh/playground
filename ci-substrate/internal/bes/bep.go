package bes

import (
	"strings"

	"google.golang.org/protobuf/encoding/protowire"
)

// FileRef records an artifact referenced in a BEP event, such as a JSON trace
// profile (command.profile.gz), a test log, or a coverage report.
type FileRef struct {
	Name   string `json:"name,omitempty"`
	URI    string `json:"uri,omitempty"`
	Digest string `json:"digest,omitempty"`
	Length int64  `json:"length,omitempty"`
}

// BuildMetrics holds the client-side build performance metrics Bazel reports
// in build_event_stream.BuildMetrics.
type BuildMetrics struct {
	ActionsCreated                    int64  `json:"actions_created,omitempty"`
	ActionsExecuted                   int64  `json:"actions_executed,omitempty"`
	RemoteCacheHits                   int64  `json:"remote_cache_hits,omitempty"`
	UsedHeapSizePostBuild             int64  `json:"used_heap_size_post_build,omitempty"`
	PeakPostGCHeapSize                int64  `json:"peak_post_gc_heap_size,omitempty"`
	PeakPostGCHeapSizeDuringExecution int64  `json:"peak_post_gc_heap_size_during_execution,omitempty"`
	TargetsLoaded                     int64  `json:"targets_loaded,omitempty"`
	TargetsConfigured                 int64  `json:"targets_configured,omitempty"`
	PackagesLoaded                    int64  `json:"packages_loaded,omitempty"`
	CPUTimeMs                         int64  `json:"cpu_time_ms,omitempty"`
	WallTimeMs                        int64  `json:"wall_time_ms,omitempty"`
	AnalysisPhaseTimeMs               int64  `json:"analysis_phase_time_ms,omitempty"`
	ExecutionPhaseTimeMs              int64  `json:"execution_phase_time_ms,omitempty"`
	ActionsExecutionStartMs           int64  `json:"actions_execution_start_ms,omitempty"`
	NumAnalyses                       int32  `json:"num_analyses,omitempty"`
	NumBuilds                         int32  `json:"num_builds,omitempty"`
	ServerInstanceID                  string `json:"server_instance_id,omitempty"`
	NetworkBytesSent                  uint64 `json:"network_bytes_sent,omitempty"`
	NetworkBytesRecv                  uint64 `json:"network_bytes_recv,omitempty"`
}

// TestResultSummary captures one Bazel test attempt reported over BEP.
type TestResultSummary struct {
	Label         string    `json:"label,omitempty"`
	Status        string    `json:"status"`
	CachedLocally bool      `json:"cached_locally,omitempty"`
	Outputs       []FileRef `json:"outputs,omitempty"`
}

type parsedEvent struct {
	testLabel   string
	started     *startedEvent
	finished    *finishedEvent
	metrics     *BuildMetrics
	toolLogs    []FileRef
	testResult  *TestResultSummary
	namedFiles  []FileRef
	lastMessage bool
}

type startedEvent struct {
	UUID             string
	BuildToolVersion string
	Command          string
	WorkingDirectory string
	Workspace        string
	Host             string
	User             string
}

type finishedEvent struct {
	OverallSuccess bool
	ExitCodeName   string
	ExitCode       int32
	HasExitCode    bool
}

// decodeBazelEvent decodes the subset of build_event_stream.BuildEvent fields
// ci-substrate indexes from raw protobuf wire bytes. Unknown fields are
// skipped cleanly so newer Bazel releases remain compatible.
func decodeBazelEvent(b []byte) parsedEvent {
	var ev parsedEvent
	for len(b) > 0 {
		num, typ, n := protowire.ConsumeTag(b)
		if n < 0 {
			return ev
		}
		b = b[n:]
		switch {
		case num == 1 && typ == protowire.BytesType:
			v, m := protowire.ConsumeBytes(b)
			if m < 0 {
				return ev
			}
			ev.testLabel = decodeBuildEventIDTestLabel(v)
			b = b[m:]
		case num == 5 && typ == protowire.BytesType:
			v, m := protowire.ConsumeBytes(b)
			if m < 0 {
				return ev
			}
			s := decodeBuildStarted(v)
			ev.started = &s
			b = b[m:]
		case num == 10 && typ == protowire.BytesType:
			v, m := protowire.ConsumeBytes(b)
			if m < 0 {
				return ev
			}
			tr := decodeTestResult(v)
			ev.testResult = &tr
			b = b[m:]
		case num == 14 && typ == protowire.BytesType:
			v, m := protowire.ConsumeBytes(b)
			if m < 0 {
				return ev
			}
			f := decodeBuildFinished(v)
			ev.finished = &f
			b = b[m:]
		case num == 15 && typ == protowire.BytesType:
			v, m := protowire.ConsumeBytes(b)
			if m < 0 {
				return ev
			}
			ev.namedFiles = append(ev.namedFiles, decodeNamedSetOfFiles(v)...)
			b = b[m:]
		case num == 20 && typ == protowire.VarintType:
			v, m := protowire.ConsumeVarint(b)
			if m < 0 {
				return ev
			}
			ev.lastMessage = v != 0
			b = b[m:]
		case num == 23 && typ == protowire.BytesType:
			v, m := protowire.ConsumeBytes(b)
			if m < 0 {
				return ev
			}
			ev.toolLogs = append(ev.toolLogs, decodeBuildToolLogs(v)...)
			b = b[m:]
		case num == 24 && typ == protowire.BytesType:
			v, m := protowire.ConsumeBytes(b)
			if m < 0 {
				return ev
			}
			bm := decodeBuildMetrics(v)
			ev.metrics = &bm
			b = b[m:]
		default:
			m := protowire.ConsumeFieldValue(num, typ, b)
			if m < 0 {
				return ev
			}
			b = b[m:]
		}
	}
	if ev.testResult != nil && ev.testResult.Label == "" {
		ev.testResult.Label = ev.testLabel
	}
	return ev
}

func decodeBuildEventIDTestLabel(b []byte) string {
	for len(b) > 0 {
		num, typ, n := protowire.ConsumeTag(b)
		if n < 0 {
			return ""
		}
		b = b[n:]
		// BuildEventId.test_result is field 8; TestResultId.label is field 1.
		if num == 8 && typ == protowire.BytesType {
			v, m := protowire.ConsumeBytes(b)
			if m < 0 {
				return ""
			}
			return decodeFirstString(v, 1)
		}
		m := protowire.ConsumeFieldValue(num, typ, b)
		if m < 0 {
			return ""
		}
		b = b[m:]
	}
	return ""
}

func decodeFirstString(b []byte, want protowire.Number) string {
	for len(b) > 0 {
		num, typ, n := protowire.ConsumeTag(b)
		if n < 0 {
			return ""
		}
		b = b[n:]
		if num == want && typ == protowire.BytesType {
			s, m := protowire.ConsumeString(b)
			if m < 0 {
				return ""
			}
			return s
		}
		m := protowire.ConsumeFieldValue(num, typ, b)
		if m < 0 {
			return ""
		}
		b = b[m:]
	}
	return ""
}

func decodeBuildStarted(b []byte) startedEvent {
	var s startedEvent
	for len(b) > 0 {
		num, typ, n := protowire.ConsumeTag(b)
		if n < 0 {
			return s
		}
		b = b[n:]
		if typ == protowire.BytesType {
			v, m := protowire.ConsumeString(b)
			if m < 0 {
				return s
			}
			switch num {
			case 1:
				s.UUID = v
			case 3:
				s.BuildToolVersion = v
			case 5:
				s.Command = v
			case 6:
				s.WorkingDirectory = v
			case 7:
				s.Workspace = v
			case 10:
				s.Host = v
			case 11:
				s.User = v
			}
			b = b[m:]
			continue
		}
		m := protowire.ConsumeFieldValue(num, typ, b)
		if m < 0 {
			return s
		}
		b = b[m:]
	}
	return s
}

func decodeBuildFinished(b []byte) finishedEvent {
	var f finishedEvent
	for len(b) > 0 {
		num, typ, n := protowire.ConsumeTag(b)
		if n < 0 {
			return f
		}
		b = b[n:]
		switch {
		case num == 1 && typ == protowire.VarintType:
			v, m := protowire.ConsumeVarint(b)
			if m < 0 {
				return f
			}
			f.OverallSuccess = v != 0
			b = b[m:]
		case num == 3 && typ == protowire.BytesType:
			v, m := protowire.ConsumeBytes(b)
			if m < 0 {
				return f
			}
			f.HasExitCode = true
		exitCode:
			for len(v) > 0 {
				en, et, k := protowire.ConsumeTag(v)
				if k < 0 {
					break
				}
				v = v[k:]
				// A bare break inside this switch would only leave the switch
				// and spin forever on truncated input, so break the loop by label.
				switch {
				case en == 1 && et == protowire.BytesType:
					name, l := protowire.ConsumeString(v)
					if l < 0 {
						break exitCode
					}
					f.ExitCodeName = name
					v = v[l:]
				case en == 2 && et == protowire.VarintType:
					code, l := protowire.ConsumeVarint(v)
					if l < 0 {
						break exitCode
					}
					f.ExitCode = int32(code)
					v = v[l:]
				default:
					l := protowire.ConsumeFieldValue(en, et, v)
					if l < 0 {
						break exitCode
					}
					v = v[l:]
				}
			}
			b = b[m:]
		default:
			m := protowire.ConsumeFieldValue(num, typ, b)
			if m < 0 {
				return f
			}
			b = b[m:]
		}
	}
	if f.HasExitCode {
		f.OverallSuccess = f.ExitCode == 0
	}
	return f
}

func decodeFile(b []byte) FileRef {
	var f FileRef
	for len(b) > 0 {
		num, typ, n := protowire.ConsumeTag(b)
		if n < 0 {
			return f
		}
		b = b[n:]
		switch {
		case num == 1 && typ == protowire.BytesType:
			v, m := protowire.ConsumeString(b)
			if m < 0 {
				return f
			}
			f.Name = v
			b = b[m:]
		case num == 2 && typ == protowire.BytesType:
			v, m := protowire.ConsumeString(b)
			if m < 0 {
				return f
			}
			f.URI = v
			b = b[m:]
		case num == 5 && typ == protowire.BytesType:
			v, m := protowire.ConsumeString(b)
			if m < 0 {
				return f
			}
			f.Digest = v
			b = b[m:]
		case num == 6 && typ == protowire.VarintType:
			v, m := protowire.ConsumeVarint(b)
			if m < 0 {
				return f
			}
			f.Length = int64(v)
			b = b[m:]
		default:
			m := protowire.ConsumeFieldValue(num, typ, b)
			if m < 0 {
				return f
			}
			b = b[m:]
		}
	}
	return f
}

func decodeBuildToolLogs(b []byte) []FileRef {
	var out []FileRef
	for len(b) > 0 {
		num, typ, n := protowire.ConsumeTag(b)
		if n < 0 {
			return out
		}
		b = b[n:]
		if num == 1 && typ == protowire.BytesType {
			v, m := protowire.ConsumeBytes(b)
			if m < 0 {
				return out
			}
			out = append(out, decodeFile(v))
			b = b[m:]
			continue
		}
		m := protowire.ConsumeFieldValue(num, typ, b)
		if m < 0 {
			return out
		}
		b = b[m:]
	}
	return out
}

func decodeNamedSetOfFiles(b []byte) []FileRef {
	var out []FileRef
	for len(b) > 0 {
		num, typ, n := protowire.ConsumeTag(b)
		if n < 0 {
			return out
		}
		b = b[n:]
		if num == 1 && typ == protowire.BytesType {
			v, m := protowire.ConsumeBytes(b)
			if m < 0 {
				return out
			}
			out = append(out, decodeFile(v))
			b = b[m:]
			continue
		}
		m := protowire.ConsumeFieldValue(num, typ, b)
		if m < 0 {
			return out
		}
		b = b[m:]
	}
	return out
}

var testStatusNames = map[uint64]string{
	0: "NO_STATUS",
	1: "PASSED",
	2: "FLAKY",
	3: "TIMEOUT",
	4: "FAILED",
	5: "INCOMPLETE",
	6: "REMOTE_FAILURE",
	7: "FAILED_TO_BUILD",
	8: "TOOL_HALTED_BEFORE_TESTING",
}

func decodeTestResult(b []byte) TestResultSummary {
	tr := TestResultSummary{Status: "NO_STATUS"}
	for len(b) > 0 {
		num, typ, n := protowire.ConsumeTag(b)
		if n < 0 {
			return tr
		}
		b = b[n:]
		switch {
		case num == 2 && typ == protowire.BytesType:
			v, m := protowire.ConsumeBytes(b)
			if m < 0 {
				return tr
			}
			tr.Outputs = append(tr.Outputs, decodeFile(v))
			b = b[m:]
		case num == 4 && typ == protowire.VarintType:
			v, m := protowire.ConsumeVarint(b)
			if m < 0 {
				return tr
			}
			tr.CachedLocally = v != 0
			b = b[m:]
		case num == 5 && typ == protowire.VarintType:
			v, m := protowire.ConsumeVarint(b)
			if m < 0 {
				return tr
			}
			if name, ok := testStatusNames[v]; ok {
				tr.Status = name
			}
			b = b[m:]
		default:
			m := protowire.ConsumeFieldValue(num, typ, b)
			if m < 0 {
				return tr
			}
			b = b[m:]
		}
	}
	return tr
}

func decodeBuildMetrics(b []byte) BuildMetrics {
	var bm BuildMetrics
	for len(b) > 0 {
		num, typ, n := protowire.ConsumeTag(b)
		if n < 0 {
			return bm
		}
		b = b[n:]
		if typ != protowire.BytesType {
			m := protowire.ConsumeFieldValue(num, typ, b)
			if m < 0 {
				return bm
			}
			b = b[m:]
			continue
		}
		v, m := protowire.ConsumeBytes(b)
		if m < 0 {
			return bm
		}
		b = b[m:]
		switch num {
		case 1:
			decodeActionSummary(v, &bm)
		case 2:
			decodeMemoryMetrics(v, &bm)
		case 3:
			decodeTargetMetrics(v, &bm)
		case 4:
			decodePackageMetrics(v, &bm)
		case 5:
			decodeTimingMetrics(v, &bm)
		case 6:
			decodeCumulativeMetrics(v, &bm)
		case 10:
			decodeNetworkMetrics(v, &bm)
		}
	}
	return bm
}

func decodeActionSummary(b []byte, bm *BuildMetrics) {
	for len(b) > 0 {
		num, typ, n := protowire.ConsumeTag(b)
		if n < 0 {
			return
		}
		b = b[n:]
		if typ == protowire.VarintType {
			v, m := protowire.ConsumeVarint(b)
			if m < 0 {
				return
			}
			switch num {
			case 1:
				bm.ActionsCreated = int64(v)
			case 2:
				bm.ActionsExecuted = int64(v)
			case 5:
				bm.RemoteCacheHits = int64(v)
			}
			b = b[m:]
			continue
		}
		m := protowire.ConsumeFieldValue(num, typ, b)
		if m < 0 {
			return
		}
		b = b[m:]
	}
}

func decodeMemoryMetrics(b []byte, bm *BuildMetrics) {
	for len(b) > 0 {
		num, typ, n := protowire.ConsumeTag(b)
		if n < 0 {
			return
		}
		b = b[n:]
		if typ == protowire.VarintType {
			v, m := protowire.ConsumeVarint(b)
			if m < 0 {
				return
			}
			switch num {
			case 1:
				bm.UsedHeapSizePostBuild = int64(v)
			case 2:
				bm.PeakPostGCHeapSize = int64(v)
			case 5:
				bm.PeakPostGCHeapSizeDuringExecution = int64(v)
			}
			b = b[m:]
			continue
		}
		m := protowire.ConsumeFieldValue(num, typ, b)
		if m < 0 {
			return
		}
		b = b[m:]
	}
}

func decodeTargetMetrics(b []byte, bm *BuildMetrics) {
	for len(b) > 0 {
		num, typ, n := protowire.ConsumeTag(b)
		if n < 0 {
			return
		}
		b = b[n:]
		if typ == protowire.VarintType {
			v, m := protowire.ConsumeVarint(b)
			if m < 0 {
				return
			}
			switch num {
			case 1:
				bm.TargetsLoaded = int64(v)
			case 2:
				bm.TargetsConfigured = int64(v)
			}
			b = b[m:]
			continue
		}
		m := protowire.ConsumeFieldValue(num, typ, b)
		if m < 0 {
			return
		}
		b = b[m:]
	}
}

func decodePackageMetrics(b []byte, bm *BuildMetrics) {
	for len(b) > 0 {
		num, typ, n := protowire.ConsumeTag(b)
		if n < 0 {
			return
		}
		b = b[n:]
		if num == 1 && typ == protowire.VarintType {
			v, m := protowire.ConsumeVarint(b)
			if m < 0 {
				return
			}
			bm.PackagesLoaded = int64(v)
			b = b[m:]
			continue
		}
		m := protowire.ConsumeFieldValue(num, typ, b)
		if m < 0 {
			return
		}
		b = b[m:]
	}
}

func decodeTimingMetrics(b []byte, bm *BuildMetrics) {
	for len(b) > 0 {
		num, typ, n := protowire.ConsumeTag(b)
		if n < 0 {
			return
		}
		b = b[n:]
		if typ == protowire.VarintType {
			v, m := protowire.ConsumeVarint(b)
			if m < 0 {
				return
			}
			switch num {
			case 1:
				bm.CPUTimeMs = int64(v)
			case 2:
				bm.WallTimeMs = int64(v)
			case 3:
				bm.AnalysisPhaseTimeMs = int64(v)
			case 4:
				bm.ExecutionPhaseTimeMs = int64(v)
			case 5:
				bm.ActionsExecutionStartMs = int64(v)
			}
			b = b[m:]
			continue
		}
		m := protowire.ConsumeFieldValue(num, typ, b)
		if m < 0 {
			return
		}
		b = b[m:]
	}
}

func decodeCumulativeMetrics(b []byte, bm *BuildMetrics) {
	for len(b) > 0 {
		num, typ, n := protowire.ConsumeTag(b)
		if n < 0 {
			return
		}
		b = b[n:]
		switch {
		case num == 11 && typ == protowire.VarintType:
			v, m := protowire.ConsumeVarint(b)
			if m < 0 {
				return
			}
			bm.NumAnalyses = int32(v)
			b = b[m:]
		case num == 12 && typ == protowire.VarintType:
			v, m := protowire.ConsumeVarint(b)
			if m < 0 {
				return
			}
			bm.NumBuilds = int32(v)
			b = b[m:]
		case num == 13 && typ == protowire.BytesType:
			v, m := protowire.ConsumeString(b)
			if m < 0 {
				return
			}
			bm.ServerInstanceID = v
			b = b[m:]
		default:
			m := protowire.ConsumeFieldValue(num, typ, b)
			if m < 0 {
				return
			}
			b = b[m:]
		}
	}
}

func decodeNetworkMetrics(b []byte, bm *BuildMetrics) {
	for len(b) > 0 {
		num, typ, n := protowire.ConsumeTag(b)
		if n < 0 {
			return
		}
		b = b[n:]
		if num == 1 && typ == protowire.BytesType {
			v, m := protowire.ConsumeBytes(b)
			if m < 0 {
				return
			}
			for len(v) > 0 {
				fn, ft, k := protowire.ConsumeTag(v)
				if k < 0 {
					break
				}
				v = v[k:]
				if ft == protowire.VarintType {
					val, l := protowire.ConsumeVarint(v)
					if l < 0 {
						break
					}
					switch fn {
					case 1:
						bm.NetworkBytesSent = val
					case 2:
						bm.NetworkBytesRecv = val
					}
					v = v[l:]
					continue
				}
				l := protowire.ConsumeFieldValue(fn, ft, v)
				if l < 0 {
					break
				}
				v = v[l:]
			}
			b = b[m:]
			continue
		}
		m := protowire.ConsumeFieldValue(num, typ, b)
		if m < 0 {
			return
		}
		b = b[m:]
	}
}

func isCoverageFile(f FileRef) bool {
	lower := strings.ToLower(f.Name)
	return strings.Contains(lower, "coverage") || strings.HasSuffix(lower, ".lcov")
}

func isProfileFile(f FileRef) bool {
	lower := strings.ToLower(f.Name)
	return strings.Contains(lower, "command.profile") || strings.HasSuffix(lower, ".profile.gz") || strings.HasSuffix(lower, ".profile")
}
