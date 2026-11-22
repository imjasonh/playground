package otlp

import (
	"bytes"
	"context"
	"crypto/rand"
	"encoding/hex"
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

// TracePayload is the subset of OTLP/HTTP v1 ExportTraceServiceRequest JSON
// accepted by xiao-otel on POST /v1/traces.
type TracePayload struct {
	ResourceSpans []ResourceSpans `json:"resourceSpans"`
}

// ResourceSpans groups spans for one OTLP resource.
type ResourceSpans struct {
	Resource   Resource     `json:"resource"`
	ScopeSpans []ScopeSpans `json:"scopeSpans"`
}

// ScopeSpans holds spans for one instrumentation scope.
type ScopeSpans struct {
	Spans []OTLPSpan `json:"spans"`
}

// OTLPSpan is a single OTLP/HTTP JSON span.
type OTLPSpan struct {
	TraceID           string          `json:"traceId"`
	SpanID            string          `json:"spanId"`
	ParentSpanID      string          `json:"parentSpanId,omitempty"`
	Name              string          `json:"name"`
	Kind              int             `json:"kind,omitempty"`
	StartTimeUnixNano string          `json:"startTimeUnixNano"`
	EndTimeUnixNano   string          `json:"endTimeUnixNano"`
	Attributes        []SpanKeyValue  `json:"attributes,omitempty"`
	Events            []OTLPSpanEvent `json:"events,omitempty"`
}

// SpanKeyValue is an OTLP span attribute key-value pair.
type SpanKeyValue struct {
	Key   string       `json:"key"`
	Value SpanAnyValue `json:"value"`
}

// SpanAnyValue holds string, int, double, or bool OTLP attribute values.
type SpanAnyValue struct {
	StringValue *string  `json:"stringValue,omitempty"`
	IntValue    any      `json:"intValue,omitempty"`
	DoubleValue *float64 `json:"doubleValue,omitempty"`
	BoolValue   *bool    `json:"boolValue,omitempty"`
}

// OTLPSpanEvent is an OTLP span event (mapped to Cloud Trace TimeEvent Annotation).
type OTLPSpanEvent struct {
	TimeUnixNano string         `json:"timeUnixNano"`
	Name         string         `json:"name"`
	Attributes   []SpanKeyValue `json:"attributes,omitempty"`
}

// Span is a normalized trace span ready for Google Cloud Trace v2 batchWrite.
type Span struct {
	TraceID      string
	SpanID       string
	ParentSpanID string
	Name         string
	Service      string
	DeviceID     string
	StartTime    time.Time
	EndTime      time.Time
	Attributes   map[string]any
	Events       []SpanEvent
}

// SpanEvent is a normalized timestamped annotation on a Span.
type SpanEvent struct {
	Time       time.Time
	Name       string
	Attributes map[string]any
}

const (
	maxSpansPerPayload  = 128
	maxAttrsPerSpan     = 32
	maxEventsPerSpan    = 16
	maxSpanNameChars    = 128
	maxAttrValueChars   = 256
	defaultTraceBaseURL = "https://cloudtrace.googleapis.com"
)

// ParseTraces extracts normalized spans from an OTLP/HTTP v1 JSON trace request.
func ParseTraces(raw []byte, defaultNow time.Time) ([]Span, error) {
	var p TracePayload
	if err := json.Unmarshal(raw, &p); err != nil {
		return nil, fmt.Errorf("parse OTLP trace JSON: %w", err)
	}
	var out []Span
	for _, rs := range p.ResourceSpans {
		service := "xiao-esp32c3"
		deviceID := "unknown"
		for _, attr := range rs.Resource.Attributes {
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
		for _, ss := range rs.ScopeSpans {
			for _, sp := range ss.Spans {
				if len(out) >= maxSpansPerPayload {
					return nil, fmt.Errorf("too many spans in payload (max %d)", maxSpansPerPayload)
				}
				traceID := strings.ToLower(strings.TrimSpace(sp.TraceID))
				if !isValidHex(traceID, 32) {
					return nil, errors.New("span traceId must be 32 hex characters")
				}
				spanID := strings.ToLower(strings.TrimSpace(sp.SpanID))
				if !isValidHex(spanID, 16) {
					return nil, errors.New("span spanId must be 16 hex characters")
				}
				parentID := strings.ToLower(strings.TrimSpace(sp.ParentSpanID))
				if parentID != "" && !isValidHex(parentID, 16) {
					return nil, errors.New("span parentSpanId must be 16 hex characters")
				}
				name := strings.TrimSpace(sp.Name)
				if name == "" {
					return nil, errors.New("span name is required")
				}
				if len(name) > maxSpanNameChars {
					name = name[:maxSpanNameChars]
				}
				start := parseUnixNano(sp.StartTimeUnixNano, defaultNow)
				end := parseUnixNano(sp.EndTimeUnixNano, start)
				if end.Before(start) {
					end = start
				}
				attrs := parseSpanAttrs(sp.Attributes)
				events := make([]SpanEvent, 0, min(len(sp.Events), maxEventsPerSpan))
				for _, ev := range sp.Events {
					if len(events) >= maxEventsPerSpan {
						break
					}
					evName := strings.TrimSpace(ev.Name)
					if evName == "" {
						continue
					}
					if len(evName) > maxSpanNameChars {
						evName = evName[:maxSpanNameChars]
					}
					events = append(events, SpanEvent{
						Time:       parseUnixNano(ev.TimeUnixNano, start),
						Name:       evName,
						Attributes: parseSpanAttrs(ev.Attributes),
					})
				}
				out = append(out, Span{
					TraceID:      traceID,
					SpanID:       spanID,
					ParentSpanID: parentID,
					Name:         name,
					Service:      service,
					DeviceID:     deviceID,
					StartTime:    start,
					EndTime:      end,
					Attributes:   attrs,
					Events:       events,
				})
			}
		}
	}
	if len(out) == 0 {
		return nil, errors.New("OTLP trace payload contained no spans")
	}
	return out, nil
}

func parseSpanAttrs(kvs []SpanKeyValue) map[string]any {
	attrs := make(map[string]any, min(len(kvs), maxAttrsPerSpan))
	for _, kv := range kvs {
		if len(attrs) >= maxAttrsPerSpan {
			break
		}
		k := strings.TrimSpace(kv.Key)
		if k == "" || len(k) > 128 {
			continue
		}
		switch {
		case kv.Value.StringValue != nil:
			s := *kv.Value.StringValue
			if len(s) > maxAttrValueChars {
				s = s[:maxAttrValueChars]
			}
			attrs[k] = s
		case kv.Value.BoolValue != nil:
			attrs[k] = *kv.Value.BoolValue
		case kv.Value.IntValue != nil:
			if v, ok := coerceInt64(kv.Value.IntValue); ok {
				attrs[k] = v
			}
		case kv.Value.DoubleValue != nil:
			attrs[k] = strconv.FormatFloat(*kv.Value.DoubleValue, 'f', -1, 64)
		}
	}
	return attrs
}

func coerceInt64(raw any) (int64, bool) {
	switch v := raw.(type) {
	case string:
		n, err := strconv.ParseInt(v, 10, 64)
		return n, err == nil
	case float64:
		return int64(v), true
	case int64:
		return v, true
	default:
		return 0, false
	}
}

func isValidHex(s string, wantLen int) bool {
	if len(s) != wantLen {
		return false
	}
	allZero := true
	for i := 0; i < len(s); i++ {
		c := s[i]
		isHex := (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f')
		if !isHex {
			return false
		}
		if c != '0' {
			allZero = false
		}
	}
	return !allZero
}

// ParseTraceparent parses a W3C traceparent header (`00-<traceId>-<spanId>-<flags>`).
func ParseTraceparent(hdr string) (traceID, parentSpanID string, ok bool) {
	parts := strings.Split(strings.TrimSpace(hdr), "-")
	if len(parts) != 4 || parts[0] != "00" {
		return "", "", false
	}
	tid := strings.ToLower(parts[1])
	sid := strings.ToLower(parts[2])
	if !isValidHex(tid, 32) || !isValidHex(sid, 16) {
		return "", "", false
	}
	return tid, sid, true
}

// NewSpanID returns a random 16-char lowercase hex OpenTelemetry span ID.
func NewSpanID() string {
	var b [8]byte
	if _, err := rand.Read(b[:]); err != nil {
		b[7] = 1
	}
	return hex.EncodeToString(b[:])
}

// TraceExporter writes normalized spans to a trace backend.
type TraceExporter interface {
	ExportSpans(ctx context.Context, userID, deviceID string, spans []Span) error
}

// CloudTraceExporter writes spans to Google Cloud Trace v2 traces:batchWrite.
type CloudTraceExporter struct {
	ProjectID   string
	BaseURL     string
	HTTPClient  *http.Client
	TokenSource oauth2.TokenSource
}

type ctBatchWriteRequest struct {
	Spans []ctSpan `json:"spans"`
}

type ctSpan struct {
	Name         string           `json:"name"`
	SpanID       string           `json:"spanId"`
	ParentSpanID string           `json:"parentSpanId,omitempty"`
	DisplayName  ctTruncatableStr `json:"displayName"`
	StartTime    string           `json:"startTime"`
	EndTime      string           `json:"endTime"`
	Attributes   *ctAttributes    `json:"attributes,omitempty"`
	TimeEvents   *ctTimeEvents    `json:"timeEvents,omitempty"`
	SameProcess  *bool            `json:"sameProcessAsParentSpan,omitempty"`
}

type ctTruncatableStr struct {
	Value string `json:"value"`
}

type ctAttributes struct {
	AttributeMap map[string]ctAttributeValue `json:"attributeMap"`
}

type ctAttributeValue struct {
	StringValue *ctTruncatableStr `json:"stringValue,omitempty"`
	IntValue    string            `json:"intValue,omitempty"`
	BoolValue   *bool             `json:"boolValue,omitempty"`
}

type ctTimeEvents struct {
	TimeEvent []ctTimeEvent `json:"timeEvent"`
}

type ctTimeEvent struct {
	Time       string        `json:"time"`
	Annotation *ctAnnotation `json:"annotation,omitempty"`
}

type ctAnnotation struct {
	Description ctTruncatableStr `json:"description"`
	Attributes  *ctAttributes    `json:"attributes,omitempty"`
}

// ExportSpans writes spans to Google Cloud Trace v2 traces:batchWrite.
func (e *CloudTraceExporter) ExportSpans(ctx context.Context, userID, iosDeviceID string, spans []Span) error {
	if len(spans) == 0 {
		return nil
	}
	base := e.BaseURL
	if base == "" {
		base = defaultTraceBaseURL
	}
	client := e.HTTPClient
	if client == nil {
		client = &http.Client{Timeout: 10 * time.Second}
	}

	reqBody := ctBatchWriteRequest{
		Spans: make([]ctSpan, 0, len(spans)),
	}
	for _, sp := range spans {
		attrMap := toCloudTraceAttrs(sp.Attributes)
		if sp.Service != "" {
			attrMap["service.name"] = ctStringAttr(sp.Service)
		}
		if sp.DeviceID != "" {
			attrMap["device.id"] = ctStringAttr(sp.DeviceID)
		}
		if iosDeviceID != "" {
			attrMap["ios.device_id"] = ctStringAttr(iosDeviceID)
		}
		if userID != "" {
			attrMap["user.id"] = ctStringAttr(userID)
		}
		cs := ctSpan{
			Name:         fmt.Sprintf("projects/%s/traces/%s/spans/%s", e.ProjectID, sp.TraceID, sp.SpanID),
			SpanID:       sp.SpanID,
			ParentSpanID: sp.ParentSpanID,
			DisplayName:  ctTruncatableStr{Value: sp.Name},
			StartTime:    sp.StartTime.UTC().Format(time.RFC3339Nano),
			EndTime:      sp.EndTime.UTC().Format(time.RFC3339Nano),
			Attributes:   &ctAttributes{AttributeMap: attrMap},
		}
		if len(sp.Events) > 0 {
			te := make([]ctTimeEvent, 0, len(sp.Events))
			for _, ev := range sp.Events {
				ann := &ctAnnotation{
					Description: ctTruncatableStr{Value: ev.Name},
				}
				if len(ev.Attributes) > 0 {
					ann.Attributes = &ctAttributes{AttributeMap: toCloudTraceAttrs(ev.Attributes)}
				}
				te = append(te, ctTimeEvent{
					Time:       ev.Time.UTC().Format(time.RFC3339Nano),
					Annotation: ann,
				})
			}
			cs.TimeEvents = &ctTimeEvents{TimeEvent: te}
		}
		reqBody.Spans = append(reqBody.Spans, cs)
	}

	payload, err := json.Marshal(reqBody)
	if err != nil {
		return err
	}
	endpoint := fmt.Sprintf("%s/v2/projects/%s/traces:batchWrite", strings.TrimRight(base, "/"), e.ProjectID)
	req, err := http.NewRequestWithContext(ctx, http.MethodPost, endpoint, bytes.NewReader(payload))
	if err != nil {
		return err
	}
	req.Header.Set("Content-Type", "application/json")
	if e.TokenSource != nil {
		tok, err := e.TokenSource.Token()
		if err != nil {
			return fmt.Errorf("fetch GCP access token for Cloud Trace: %w", err)
		}
		req.Header.Set("Authorization", "Bearer "+tok.AccessToken)
	}
	resp, err := client.Do(req)
	if err != nil {
		return err
	}
	defer resp.Body.Close()
	if resp.StatusCode >= 200 && resp.StatusCode < 300 {
		return nil
	}
	errBody, _ := io.ReadAll(io.LimitReader(resp.Body, 4096))
	return fmt.Errorf("Cloud Trace API HTTP %d: %s", resp.StatusCode, strings.TrimSpace(string(errBody)))
}

func ctStringAttr(s string) ctAttributeValue {
	return ctAttributeValue{StringValue: &ctTruncatableStr{Value: s}}
}

func toCloudTraceAttrs(in map[string]any) map[string]ctAttributeValue {
	out := make(map[string]ctAttributeValue, len(in)+4)
	for k, v := range in {
		switch tv := v.(type) {
		case string:
			out[k] = ctStringAttr(tv)
		case int64:
			out[k] = ctAttributeValue{IntValue: strconv.FormatInt(tv, 10)}
		case bool:
			b := tv
			out[k] = ctAttributeValue{BoolValue: &b}
		}
	}
	return out
}
