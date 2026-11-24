package otlp

import (
	"testing"
	"time"
)

func TestParseOTAMetrics(t *testing.T) {
	raw := []byte(`{
		"resourceMetrics": [{
			"resource": {
				"attributes": [
					{"key": "service.name", "value": {"stringValue": "waveshare-epd75"}},
					{"key": "device.id", "value": {"stringValue": "epd75-01"}}
				]
			},
			"scopeMetrics": [{
				"metrics": [
					{"name": "mcu.ota.duration_ms", "gauge": {"dataPoints": [
						{"asInt": "35000", "timeUnixNano": "1700000035000000000", "attributes": [{"key": "phase", "value": {"stringValue": "total"}}]},
						{"asInt": "28100", "timeUnixNano": "1700000035000000000", "attributes": [{"key": "phase", "value": {"stringValue": "stream"}}]}
					]}},
					{"name": "mcu.ota.throughput_bps", "gauge": {"dataPoints": [
						{"asInt": "27591", "timeUnixNano": "1700000035000000000", "attributes": [{"key": "kind", "value": {"stringValue": "effective"}}]}
					]}},
					{"name": "mcu.ota.bytes", "gauge": {"dataPoints": [
						{"asInt": "775328", "timeUnixNano": "1700000035000000000", "attributes": [{"key": "kind", "value": {"stringValue": "raw"}}]},
						{"asInt": "440000", "timeUnixNano": "1700000035000000000", "attributes": [{"key": "kind", "value": {"stringValue": "wire"}}]}
					]}},
					{"name": "mcu.ota.rtt_ms", "gauge": {"dataPoints": [{"asInt": "30", "timeUnixNano": "1700000035000000000"}]}},
					{"name": "mcu.ota.energy_mj", "gauge": {"dataPoints": [{"asInt": "12768", "timeUnixNano": "1700000035000000000"}]}},
					{"name": "mcu.ota.battery_delta_mv", "gauge": {"dataPoints": [{"asInt": "-25", "timeUnixNano": "1700000035000000000"}]}},
					{"name": "mcu.ota.phone_battery_pct", "gauge": {"dataPoints": [{"asInt": "-1", "timeUnixNano": "1700000035000000000"}]}}
				]
			}]
		}]
	}`)

	points, err := Parse(raw, time.Unix(1700000035, 0))
	if err != nil {
		t.Fatalf("Parse failed: %v", err)
	}
	if len(points) != 9 {
		t.Fatalf("got %d points, want 9", len(points))
	}
}

func TestParseAppMetrics(t *testing.T) {
	raw := []byte(`{
		"resourceMetrics": [{
			"resource": {
				"attributes": [
					{"key": "service.name", "value": {"stringValue": "xiao-esp32c3-gzip-bench"}},
					{"key": "device.id", "value": {"stringValue": "xiao-01"}}
				]
			},
			"scopeMetrics": [{
				"metrics": [
					{"name": "mcu.app.gzip.inflate_bps", "gauge": {"dataPoints": [
						{"asInt": "1850000", "timeUnixNano": "1700000035000000000", "attributes": [
							{"key": "corpus", "value": {"stringValue": "json_otel"}},
							{"key": "impl", "value": {"stringValue": "miniz_oxide"}}
						]}
					]}},
					{"name": "mcu.app.gzip.deflate_oom", "gauge": {"dataPoints": [
						{"asInt": "1", "timeUnixNano": "1700000035000000000", "attributes": [
							{"key": "impl", "value": {"stringValue": "miniz_oxide"}}
						]}
					]}}
				]
			}]
		}]
	}`)

	points, err := Parse(raw, time.Unix(1700000035, 0))
	if err != nil {
		t.Fatalf("Parse failed: %v", err)
	}
	if len(points) != 2 {
		t.Fatalf("got %d points, want 2", len(points))
	}
	if want := "custom.googleapis.com/mcu_lab/mcu/app/gzip/inflate_bps"; points[0].MetricType != want {
		t.Errorf("MetricType = %q, want %q", points[0].MetricType, want)
	}
	if points[0].Labels["corpus"] != "json_otel" || points[0].Labels["impl"] != "miniz_oxide" {
		t.Errorf("unexpected labels: %v", points[0].Labels)
	}

	for _, bad := range []string{
		"mcu.app.",
		"mcu.app..foo",
		"mcu.app.GZIP.bad",
		"mcu.app.a/b",
		"mcu.app.a.b.c.d.e",
		"other.metric",
	} {
		if _, err := toCloudMonitoringType(bad); err == nil {
			t.Errorf("toCloudMonitoringType(%q) succeeded, want error", bad)
		}
	}
}
