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
