// Package otlp parses OTLP/HTTP v1 JSON metrics payloads and forwards them to
// Google Cloud Monitoring (monitoring.googleapis.com/v3/projects/{project}/timeSeries).
package otlp

import (
	"bytes"
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"net/http"
	"strconv"
	"strings"
	"time"

	"golang.org/x/oauth2"
)

// Payload is the subset of OTLP/HTTP v1 ExportMetricsServiceRequest JSON used
// by the XIAO ESP32C3 iOS forwarder.
type Payload struct {
	ResourceMetrics []ResourceMetrics `json:"resourceMetrics"`
}

// ResourceMetrics groups metrics for one OTLP resource.
type ResourceMetrics struct {
	Resource     Resource       `json:"resource"`
	ScopeMetrics []ScopeMetrics `json:"scopeMetrics"`
}

// Resource holds OTLP resource attributes (such as service.name and device.id).
type Resource struct {
	Attributes []KeyValue `json:"attributes"`
}

// ScopeMetrics holds metrics for one instrumentation scope.
type ScopeMetrics struct {
	Metrics []Metric `json:"metrics"`
}

// Metric is a single named OTLP gauge or sum.
type Metric struct {
	Name  string      `json:"name"`
	Gauge *GaugeOrSum `json:"gauge,omitempty"`
	Sum   *GaugeOrSum `json:"sum,omitempty"`
}

// GaugeOrSum holds OTLP number data points.
type GaugeOrSum struct {
	DataPoints []NumberDataPoint `json:"dataPoints"`
}

// NumberDataPoint is a single integer or floating-point observation.
type NumberDataPoint struct {
	Attributes   []KeyValue `json:"attributes,omitempty"`
	TimeUnixNano string     `json:"timeUnixNano,omitempty"`
	AsInt        any        `json:"asInt,omitempty"`
	AsDouble     *float64   `json:"asDouble,omitempty"`
}

// KeyValue is an OTLP attribute key-value pair.
type KeyValue struct {
	Key   string   `json:"key"`
	Value AnyValue `json:"value"`
}

// AnyValue holds an OTLP string or integer attribute value.
type AnyValue struct {
	StringValue string `json:"stringValue,omitempty"`
	IntValue    string `json:"intValue,omitempty"`
}

// Point is a normalized metric observation ready for Cloud Monitoring.
type Point struct {
	MetricType string
	Labels     map[string]string
	DeviceID   string
	Service    string
	EndTime    time.Time
	Int64Value int64
}

const (
	maxPointsPerPayload = 64
	maxLabelsPerPoint   = 8
	maxLabelValueChars  = 128
	appMetricPrefix     = "mcu.app."
	maxAppMetricSuffix  = 64
	maxAppMetricSegs    = 4
)

var allowedMetrics = map[string]string{
	"mcu.wake.count":             "custom.googleapis.com/mcu_lab/mcu/wake/count",
	"mcu.phase.duration_us":      "custom.googleapis.com/mcu_lab/mcu/phase/duration_us",
	"mcu.battery_mv":             "custom.googleapis.com/mcu_lab/mcu/battery_mv",
	"mcu.ble.rssi":               "custom.googleapis.com/mcu_lab/mcu/ble/rssi",
	"mcu.heap.free_bytes":        "custom.googleapis.com/mcu_lab/mcu/heap/free_bytes",
	"mcu.heap.min_free_bytes":    "custom.googleapis.com/mcu_lab/mcu/heap/min_free_bytes",
	"mcu.stack.high_water_bytes": "custom.googleapis.com/mcu_lab/mcu/stack/high_water_bytes",
	"mcu.cpu.cycles":             "custom.googleapis.com/mcu_lab/mcu/cpu/cycles",
	"mcu.ota.duration_ms":        "custom.googleapis.com/mcu_lab/mcu/ota/duration_ms",
	"mcu.ota.throughput_bps":     "custom.googleapis.com/mcu_lab/mcu/ota/throughput_bps",
	"mcu.ota.bytes":              "custom.googleapis.com/mcu_lab/mcu/ota/bytes",
	"mcu.ota.rtt_ms":             "custom.googleapis.com/mcu_lab/mcu/ota/rtt_ms",
	"mcu.ota.energy_mj":          "custom.googleapis.com/mcu_lab/mcu/ota/energy_mj",
	"mcu.ota.battery_delta_mv":   "custom.googleapis.com/mcu_lab/mcu/ota/battery_delta_mv",
	"mcu.ota.phone_battery_pct":  "custom.googleapis.com/mcu_lab/mcu/ota/phone_battery_pct",
}

// Parse extracts normalized Cloud Monitoring points from an OTLP/HTTP v1 JSON body.
func Parse(raw []byte, defaultNow time.Time) ([]Point, error) {
	var p Payload
	if err := json.Unmarshal(raw, &p); err != nil {
		return nil, fmt.Errorf("parse OTLP JSON: %w", err)
	}
	var out []Point
	for _, rm := range p.ResourceMetrics {
		service := "xiao-esp32c3"
		deviceID := "unknown"
		for _, attr := range rm.Resource.Attributes {
			switch attr.Key {
			case "service.name":
				if v := sanitizeLabelValue(attr.Value.StringValue); v != "" {
					service = v
				}
			case "device.id":
				if v := sanitizeLabelValue(attr.Value.StringValue); v != "" {
					deviceID = v
				}
			}
		}
		for _, sm := range rm.ScopeMetrics {
			for _, m := range sm.Metrics {
				if m.Name == "" {
					continue
				}
				metricType, err := toCloudMonitoringType(m.Name)
				if err != nil {
					return nil, err
				}
				var dps []NumberDataPoint
				if m.Gauge != nil {
					dps = append(dps, m.Gauge.DataPoints...)
				}
				if m.Sum != nil {
					dps = append(dps, m.Sum.DataPoints...)
				}
				for _, dp := range dps {
					if len(out) >= maxPointsPerPayload {
						return nil, fmt.Errorf("OTLP payload exceeds %d data points", maxPointsPerPayload)
					}
					val, err := parsePointInt(dp)
					if err != nil {
						return nil, fmt.Errorf("metric %s: %w", m.Name, err)
					}
					ts := parseUnixNano(dp.TimeUnixNano, defaultNow)
					labels := make(map[string]string, min(len(dp.Attributes), maxLabelsPerPoint))
					for _, a := range dp.Attributes {
						if len(labels) >= maxLabelsPerPoint {
							break
						}
						k := sanitizeLabelKey(a.Key)
						v := sanitizeLabelValue(a.Value.StringValue)
						if k != "" && v != "" {
							labels[k] = v
						}
					}
					out = append(out, Point{
						MetricType: metricType,
						Labels:     labels,
						DeviceID:   deviceID,
						Service:    service,
						EndTime:    ts,
						Int64Value: val,
					})
				}
			}
		}
	}
	if len(out) == 0 {
		return nil, errors.New("OTLP payload contains no metric data points")
	}
	return out, nil
}

func toCloudMonitoringType(otlpName string) (string, error) {
	clean := strings.TrimSpace(otlpName)
	if mapped, ok := allowedMetrics[clean]; ok {
		return mapped, nil
	}
	if suffix, ok := strings.CutPrefix(clean, appMetricPrefix); ok {
		if path, valid := validateAppMetricSuffix(suffix); valid {
			return "custom.googleapis.com/mcu_lab/mcu/app/" + path, nil
		}
	}
	return "", fmt.Errorf("unsupported metric name %q", otlpName)
}

func validateAppMetricSuffix(suffix string) (string, bool) {
	if suffix == "" || len(suffix) > maxAppMetricSuffix {
		return "", false
	}
	segs := strings.Split(suffix, ".")
	if len(segs) == 0 || len(segs) > maxAppMetricSegs {
		return "", false
	}
	for _, seg := range segs {
		if seg == "" {
			return "", false
		}
		for i := 0; i < len(seg); i++ {
			c := seg[i]
			if !((c >= 'a' && c <= 'z') || (c >= '0' && c <= '9') || c == '_') {
				return "", false
			}
		}
	}
	return strings.Join(segs, "/"), true
}

func sanitizeLabelKey(k string) string {
	var b strings.Builder
	for _, r := range k {
		if b.Len() >= 64 {
			break
		}
		if (r >= 'a' && r <= 'z') || (r >= 'A' && r <= 'Z') || (r >= '0' && r <= '9') || r == '_' {
			b.WriteRune(r)
		} else {
			b.WriteByte('_')
		}
	}
	return b.String()
}

func sanitizeLabelValue(v string) string {
	trimmed := strings.TrimSpace(v)
	if len(trimmed) > maxLabelValueChars {
		return trimmed[:maxLabelValueChars]
	}
	return trimmed
}

func parsePointInt(dp NumberDataPoint) (int64, error) {
	switch v := dp.AsInt.(type) {
	case string:
		return strconv.ParseInt(v, 10, 64)
	case float64:
		return int64(v), nil
	case nil:
		if dp.AsDouble != nil {
			return int64(*dp.AsDouble), nil
		}
		return 0, errors.New("missing asInt or asDouble")
	default:
		return 0, fmt.Errorf("unsupported asInt type %T", v)
	}
}

func parseUnixNano(s string, fallback time.Time) time.Time {
	if s == "" {
		return fallback.UTC()
	}
	ns, err := strconv.ParseUint(s, 10, 64)
	if err != nil || ns == 0 {
		return fallback.UTC()
	}
	t := time.Unix(0, int64(ns)).UTC()
	// Cloud Monitoring rejects points older than 24h or more than 5m in the future.
	if t.Before(fallback.Add(-23*time.Hour)) || t.After(fallback.Add(4*time.Minute)) {
		return fallback.UTC()
	}
	return t
}

// Exporter writes normalized metric points to a destination (such as Google Cloud Monitoring).
type Exporter interface {
	Export(ctx context.Context, attestedUserID, attestedDeviceID string, points []Point) error
}

// CloudMonitoringExporter POSTs time series to Google Cloud Monitoring REST v3.
type CloudMonitoringExporter struct {
	ProjectID   string
	BaseURL     string
	HTTPClient  *http.Client
	TokenSource oauth2.TokenSource
}

type cmTimeSeriesRequest struct {
	TimeSeries []cmTimeSeries `json:"timeSeries"`
}

type cmTimeSeries struct {
	Metric     cmMetric   `json:"metric"`
	Resource   cmResource `json:"resource"`
	MetricKind string     `json:"metricKind"`
	ValueType  string     `json:"valueType"`
	Points     []cmDataPt `json:"points"`
}

type cmMetric struct {
	Type   string            `json:"type"`
	Labels map[string]string `json:"labels,omitempty"`
}

type cmResource struct {
	Type   string            `json:"type"`
	Labels map[string]string `json:"labels"`
}

type cmDataPt struct {
	Interval cmInterval `json:"interval"`
	Value    cmValue    `json:"value"`
}

type cmInterval struct {
	EndTime string `json:"endTime"`
}

type cmValue struct {
	Int64Value string `json:"int64Value"`
}

// Export formats points as custom.googleapis.com/mcu_lab/* time series and
// POSTs them to Cloud Monitoring.
func (e *CloudMonitoringExporter) Export(ctx context.Context, attestedUserID, attestedDeviceID string, points []Point) error {
	if e.ProjectID == "" {
		return nil
	}
	series := make([]cmTimeSeries, 0, len(points))
	for _, pt := range points {
		labels := make(map[string]string, len(pt.Labels)+2)
		for k, v := range pt.Labels {
			labels[k] = v
		}
		if attestedUserID != "" {
			labels["attested_user"] = attestedUserID
		}
		if attestedDeviceID != "" {
			labels["attested_ios_device"] = attestedDeviceID
		}
		series = append(series, cmTimeSeries{
			Metric: cmMetric{
				Type:   pt.MetricType,
				Labels: labels,
			},
			Resource: cmResource{
				Type: "generic_node",
				Labels: map[string]string{
					"project_id": e.ProjectID,
					"location":   "global",
					"namespace":  pt.Service,
					"node_id":    pt.DeviceID,
				},
			},
			MetricKind: "GAUGE",
			ValueType:  "INT64",
			Points: []cmDataPt{{
				Interval: cmInterval{
					EndTime: pt.EndTime.UTC().Format(time.RFC3339Nano),
				},
				Value: cmValue{
					Int64Value: strconv.FormatInt(pt.Int64Value, 10),
				},
			}},
		})
	}
	bodyBytes, err := json.Marshal(cmTimeSeriesRequest{TimeSeries: series})
	if err != nil {
		return err
	}
	base := e.BaseURL
	if base == "" {
		base = "https://monitoring.googleapis.com"
	}
	url := fmt.Sprintf("%s/v3/projects/%s/timeSeries", strings.TrimRight(base, "/"), e.ProjectID)
	req, err := http.NewRequestWithContext(ctx, http.MethodPost, url, bytes.NewReader(bodyBytes))
	if err != nil {
		return err
	}
	req.Header.Set("Content-Type", "application/json")
	if e.TokenSource != nil {
		tok, err := e.TokenSource.Token()
		if err != nil {
			return fmt.Errorf("fetch GCP token: %w", err)
		}
		req.Header.Set("Authorization", "Bearer "+tok.AccessToken)
	}
	client := e.HTTPClient
	if client == nil {
		client = &http.Client{Timeout: 10 * time.Second}
	}
	resp, err := client.Do(req)
	if err != nil {
		return err
	}
	defer resp.Body.Close()
	if resp.StatusCode < 200 || resp.StatusCode >= 300 {
		msg, _ := io.ReadAll(io.LimitReader(resp.Body, 2048))
		return fmt.Errorf("Cloud Monitoring returned HTTP %d: %s", resp.StatusCode, strings.TrimSpace(string(msg)))
	}
	return nil
}
