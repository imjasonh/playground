// Command xiao-otel verifies Apple App Attest assertions from the Playground
// iOS app and forwards XIAO ESP32C3 OTLP/HTTP metrics to Google Cloud Monitoring.
package main

import (
	"encoding/base64"
	"encoding/json"
	"errors"
	"io"
	"net/http"
	"strings"

	"github.com/chainguard-dev/clog"
	"github.com/imjasonh/playground/xiao-otel/internal/attest"
	"github.com/imjasonh/playground/xiao-otel/internal/otlp"
)

const maxRequestBodyBytes = 64 * 1024

// Server handles App Attest registration and OTLP metric/trace ingestion.
type Server struct {
	Verifier      *attest.Verifier
	Exporter      otlp.Exporter
	TraceExporter otlp.TraceExporter
}

// Routes returns the HTTP handler for the service.
func (s *Server) Routes() http.Handler {
	mux := http.NewServeMux()
	mux.HandleFunc("GET /", s.handleHealth)
	mux.HandleFunc("GET /health", s.handleHealth)
	mux.HandleFunc("POST /v1/challenge", s.handleChallenge)
	mux.HandleFunc("POST /v1/token", s.handleToken)
	mux.HandleFunc("POST /v1/unattested-token", s.handleUnattestedToken)
	mux.HandleFunc("POST /v1/whoami", s.handleWhoami)
	mux.HandleFunc("POST /v1/metrics", s.handleMetrics)
	mux.HandleFunc("POST /v1/traces", s.handleTraces)
	return mux
}

func (s *Server) handleHealth(w http.ResponseWriter, r *http.Request) {
	writeJSON(w, http.StatusOK, map[string]any{
		"service":         "xiao-otel",
		"appId":           s.Verifier.AppID,
		"allowUnattested": s.Verifier.AllowUnattested,
	})
}

func (s *Server) handleChallenge(w http.ResponseWriter, r *http.Request) {
	chal, exp, err := s.Verifier.IssueChallenge()
	if err != nil {
		writeError(w, http.StatusInternalServerError, err)
		return
	}
	writeJSON(w, http.StatusOK, map[string]any{
		"challenge": chal,
		"expiresAt": exp,
	})
}

type registerRequest struct {
	KeyID             string          `json:"keyId"`
	AttestationObject string          `json:"attestationObject"`
	ClientData        json.RawMessage `json:"clientData"`
}

type unattestedRequest struct {
	ClientData json.RawMessage `json:"clientData"`
}

type assertionEnvelope struct {
	KeyID           string          `json:"keyId"`
	AssertionObject string          `json:"assertionObject,omitempty"`
	ClientData      json.RawMessage `json:"clientData"`
	Metrics         json.RawMessage `json:"metrics,omitempty"`
}

func unpackClientDataBytes(raw json.RawMessage) ([]byte, error) {
	if len(raw) == 0 {
		return nil, errors.New("clientData is missing")
	}
	var asStr string
	if err := json.Unmarshal(raw, &asStr); err == nil {
		return []byte(asStr), nil
	}
	return raw, nil
}

func (s *Server) handleToken(w http.ResponseWriter, r *http.Request) {
	body, err := readBody(w, r)
	if err != nil {
		writeError(w, http.StatusBadRequest, err)
		return
	}
	var req registerRequest
	if err := json.Unmarshal(body, &req); err != nil {
		writeError(w, http.StatusBadRequest, errors.New("invalid token request"))
		return
	}
	cdBytes, err := unpackClientDataBytes(req.ClientData)
	if err != nil {
		writeError(w, http.StatusBadRequest, err)
		return
	}
	rec, err := s.Verifier.Register(req.KeyID, req.AttestationObject, cdBytes)
	if err != nil {
		writeError(w, http.StatusUnauthorized, err)
		return
	}
	clog.FromContext(r.Context()).Info("attested device registered", "device_id", rec.DeviceID, "user_id", rec.UserID)
	writeDeviceRecord(w, rec)
}

func (s *Server) handleUnattestedToken(w http.ResponseWriter, r *http.Request) {
	body, err := readBody(w, r)
	if err != nil {
		writeError(w, http.StatusBadRequest, err)
		return
	}
	var req unattestedRequest
	if err := json.Unmarshal(body, &req); err != nil {
		writeError(w, http.StatusBadRequest, errors.New("invalid unattested request"))
		return
	}
	cdBytes, err := unpackClientDataBytes(req.ClientData)
	if err != nil {
		writeError(w, http.StatusBadRequest, err)
		return
	}
	rec, err := s.Verifier.RegisterUnattested(cdBytes)
	if err != nil {
		writeError(w, http.StatusBadRequest, err)
		return
	}
	clog.FromContext(r.Context()).Info("unattested device registered", "device_id", rec.DeviceID, "user_id", rec.UserID)
	writeDeviceRecord(w, rec)
}

func (s *Server) handleWhoami(w http.ResponseWriter, r *http.Request) {
	body, err := readBody(w, r)
	if err != nil {
		writeError(w, http.StatusBadRequest, err)
		return
	}
	var req assertionEnvelope
	if err := json.Unmarshal(body, &req); err != nil {
		writeError(w, http.StatusBadRequest, errors.New("invalid whoami request"))
		return
	}
	cdBytes, err := unpackClientDataBytes(req.ClientData)
	if err != nil {
		writeError(w, http.StatusBadRequest, err)
		return
	}
	rec, err := s.Verifier.VerifyAssertion(req.KeyID, req.AssertionObject, cdBytes, nil, attest.ActionWhoami)
	if err != nil {
		writeError(w, http.StatusUnauthorized, err)
		return
	}
	writeDeviceRecord(w, rec)
}

// handleMetrics accepts an App Attest-authorized OTLP metrics request.
//
// Two wire modes are supported:
//  1. Header mode (standard OTLP/HTTP body + headers):
//     - X-Apple-App-Attest-Key-Id: <keyId>
//     - X-Apple-App-Attest-Assertion: <base64 CBOR assertionObject> (omitted on Simulator unattested)
//     - X-Apple-App-Attest-Client-Data: <base64 or raw JSON string of {"action":"metrics","challenge":"..."}>
//     - Body: raw OTLP/HTTP v1 JSON
//  2. JSON envelope mode:
//     - Body: {"keyId":"...","assertionObject":"...","clientData":"...","metrics":{...OTLP JSON...}}
func (s *Server) handleMetrics(w http.ResponseWriter, r *http.Request) {
	ctx := r.Context()
	log := clog.FromContext(ctx)
	reqStart := s.Verifier.Now()
	body, err := readBody(w, r)
	if err != nil {
		writeError(w, http.StatusBadRequest, err)
		return
	}

	var keyID, assertionB64 string
	var cdBytes, otlpBytes []byte

	if hdrKey := strings.TrimSpace(r.Header.Get("X-Apple-App-Attest-Key-Id")); hdrKey != "" {
		keyID = hdrKey
		assertionB64 = strings.TrimSpace(r.Header.Get("X-Apple-App-Attest-Assertion"))
		hdrCD := strings.TrimSpace(r.Header.Get("X-Apple-App-Attest-Client-Data"))
		if hdrCD == "" {
			writeError(w, http.StatusUnauthorized, errors.New("missing X-Apple-App-Attest-Client-Data header"))
			return
		}
		if strings.HasPrefix(hdrCD, "{") {
			cdBytes = []byte(hdrCD)
		} else {
			var err error
			cdBytes, err = decodeHeaderBase64(hdrCD)
			if err != nil {
				writeError(w, http.StatusBadRequest, errors.New("invalid X-Apple-App-Attest-Client-Data encoding"))
				return
			}
		}
		otlpBytes = body
	} else {
		var env assertionEnvelope
		if err := json.Unmarshal(body, &env); err != nil || env.KeyID == "" {
			writeError(w, http.StatusUnauthorized, errors.New("App Attest authorization required (headers or JSON envelope)"))
			return
		}
		keyID = env.KeyID
		assertionB64 = env.AssertionObject
		cdBytes, err = unpackClientDataBytes(env.ClientData)
		if err != nil {
			writeError(w, http.StatusBadRequest, err)
			return
		}
		if len(env.Metrics) == 0 {
			writeError(w, http.StatusBadRequest, errors.New("metrics field is missing"))
			return
		}
		var metricsAsString string
		if err := json.Unmarshal(env.Metrics, &metricsAsString); err == nil {
			otlpBytes = []byte(metricsAsString)
		} else {
			otlpBytes = env.Metrics
		}
	}

	verifyStart := s.Verifier.Now()
	rec, err := s.Verifier.VerifyAssertion(keyID, assertionB64, cdBytes, otlpBytes, attest.ActionMetrics)
	verifyEnd := s.Verifier.Now()
	if err != nil {
		log.Warn("app attest verification failed", "err", err)
		writeError(w, http.StatusUnauthorized, err)
		return
	}

	points, err := otlp.Parse(otlpBytes, s.Verifier.Now())
	if err != nil {
		writeError(w, http.StatusBadRequest, err)
		return
	}

	exportStart := s.Verifier.Now()
	if s.Exporter != nil {
		if err := s.Exporter.Export(ctx, rec.UserID, rec.DeviceID, points); err != nil {
			log.Error("cloud monitoring export failed", "err", err, "points", len(points))
			writeError(w, http.StatusBadGateway, err)
			return
		}
	}
	exportEnd := s.Verifier.Now()

	if s.TraceExporter != nil {
		if traceID, parentSpanID, ok := otlp.ParseTraceparent(r.Header.Get("traceparent")); ok {
			reqSpanID := otlp.NewSpanID()
			serverSpans := []otlp.Span{
				{
					TraceID:      traceID,
					SpanID:       reqSpanID,
					ParentSpanID: parentSpanID,
					Name:         "xiao-otel.metrics",
					Service:      "xiao-otel",
					DeviceID:     rec.DeviceID,
					StartTime:    reqStart,
					EndTime:      exportEnd,
					Attributes: map[string]any{
						"otlp.points": int64(len(points)),
						"unattested":  rec.Unattested,
					},
				},
				{
					TraceID:      traceID,
					SpanID:       otlp.NewSpanID(),
					ParentSpanID: reqSpanID,
					Name:         "xiao-otel.app_attest.verify",
					Service:      "xiao-otel",
					DeviceID:     rec.DeviceID,
					StartTime:    verifyStart,
					EndTime:      verifyEnd,
					Attributes: map[string]any{
						"attest.counter": int64(rec.Counter),
					},
				},
				{
					TraceID:      traceID,
					SpanID:       otlp.NewSpanID(),
					ParentSpanID: reqSpanID,
					Name:         "xiao-otel.cloud_monitoring.export",
					Service:      "xiao-otel",
					DeviceID:     rec.DeviceID,
					StartTime:    exportStart,
					EndTime:      exportEnd,
					Attributes: map[string]any{
						"otlp.points": int64(len(points)),
					},
				},
			}
			if err := s.TraceExporter.ExportSpans(ctx, rec.UserID, rec.DeviceID, serverSpans); err != nil {
				log.Warn("failed to export server-side metrics spans", "err", err)
			}
		}
	}

	log.Info("exported xiao-esp32c3 metrics",
		"points", len(points),
		"user_id", rec.UserID,
		"ios_device_id", rec.DeviceID,
		"counter", rec.Counter,
		"unattested", rec.Unattested,
	)
	writeJSON(w, http.StatusOK, map[string]any{
		"acceptedPoints": len(points),
		"userId":         rec.UserID,
		"deviceId":       rec.DeviceID,
		"counter":        rec.Counter,
		"unattested":     rec.Unattested,
	})
}

// handleTraces accepts an App Attest-authorized OTLP/HTTP v1 JSON traces request
// and exports the spans to Google Cloud Trace.
func (s *Server) handleTraces(w http.ResponseWriter, r *http.Request) {
	ctx := r.Context()
	log := clog.FromContext(ctx)
	body, err := readBody(w, r)
	if err != nil {
		writeError(w, http.StatusBadRequest, err)
		return
	}

	keyID := strings.TrimSpace(r.Header.Get("X-Apple-App-Attest-Key-Id"))
	if keyID == "" {
		writeError(w, http.StatusUnauthorized, errors.New("App Attest authorization required"))
		return
	}
	assertionB64 := strings.TrimSpace(r.Header.Get("X-Apple-App-Attest-Assertion"))
	hdrCD := strings.TrimSpace(r.Header.Get("X-Apple-App-Attest-Client-Data"))
	if hdrCD == "" {
		writeError(w, http.StatusUnauthorized, errors.New("missing X-Apple-App-Attest-Client-Data header"))
		return
	}
	var cdBytes []byte
	if strings.HasPrefix(hdrCD, "{") {
		cdBytes = []byte(hdrCD)
	} else {
		cdBytes, err = decodeHeaderBase64(hdrCD)
		if err != nil {
			writeError(w, http.StatusBadRequest, errors.New("invalid X-Apple-App-Attest-Client-Data encoding"))
			return
		}
	}

	rec, err := s.Verifier.VerifyAssertion(keyID, assertionB64, cdBytes, body, attest.ActionTraces)
	if err != nil {
		log.Warn("app attest trace verification failed", "err", err)
		writeError(w, http.StatusUnauthorized, err)
		return
	}

	spans, err := otlp.ParseTraces(body, s.Verifier.Now())
	if err != nil {
		writeError(w, http.StatusBadRequest, err)
		return
	}

	if s.TraceExporter != nil {
		if err := s.TraceExporter.ExportSpans(ctx, rec.UserID, rec.DeviceID, spans); err != nil {
			log.Error("cloud trace export failed", "err", err, "spans", len(spans))
			writeError(w, http.StatusBadGateway, err)
			return
		}
	}

	log.Info("exported xiao-esp32c3 spans",
		"spans", len(spans),
		"trace_id", spans[0].TraceID,
		"user_id", rec.UserID,
		"ios_device_id", rec.DeviceID,
		"counter", rec.Counter,
		"unattested", rec.Unattested,
	)
	writeJSON(w, http.StatusOK, map[string]any{
		"acceptedSpans": len(spans),
		"traceId":       spans[0].TraceID,
		"userId":        rec.UserID,
		"deviceId":      rec.DeviceID,
		"counter":       rec.Counter,
		"unattested":    rec.Unattested,
	})
}

func decodeHeaderBase64(s string) ([]byte, error) {
	for _, enc := range []*base64.Encoding{
		base64.StdEncoding,
		base64.RawStdEncoding,
		base64.URLEncoding,
		base64.RawURLEncoding,
	} {
		if b, err := enc.DecodeString(s); err == nil {
			return b, nil
		}
	}
	return nil, errors.New("invalid base64")
}

func readBody(w http.ResponseWriter, r *http.Request) ([]byte, error) {
	r.Body = http.MaxBytesReader(w, r.Body, maxRequestBodyBytes)
	defer r.Body.Close()
	body, err := io.ReadAll(r.Body)
	if err != nil {
		return nil, errors.New("request body is invalid or exceeds 64 KiB")
	}
	return body, nil
}

func writeDeviceRecord(w http.ResponseWriter, rec *attest.DeviceRecord) {
	writeJSON(w, http.StatusOK, map[string]any{
		"userId":     rec.UserID,
		"deviceId":   rec.DeviceID,
		"keyId":      rec.KeyID,
		"unattested": rec.Unattested,
		"counter":    rec.Counter,
	})
}

func writeError(w http.ResponseWriter, status int, err error) {
	writeJSON(w, status, map[string]string{
		"error": err.Error(),
	})
}

func writeJSON(w http.ResponseWriter, status int, v any) {
	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(status)
	_ = json.NewEncoder(w).Encode(v)
}
