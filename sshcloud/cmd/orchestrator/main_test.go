package main

import (
	"net/http"
	"net/http/httptest"
	"testing"
)

func TestGatewayAndAdminRouteSeparation(t *testing.T) {
	ok := http.HandlerFunc(func(w http.ResponseWriter, _ *http.Request) {
		w.WriteHeader(http.StatusNoContent)
	})
	gateway := gatewayServiceRoutes(ok)
	admin := adminRoutes(ok)

	for _, tc := range []struct {
		name    string
		handler http.Handler
		method  string
		path    string
		want    int
	}{
		{name: "gateway readiness", handler: gateway, method: http.MethodGet, path: "/v1/readyz", want: http.StatusNoContent},
		{name: "gateway ensure", handler: gateway, method: http.MethodPost, path: "/v1/ensure", want: http.StatusNoContent},
		{name: "gateway cannot drain", handler: gateway, method: http.MethodPost, path: "/v1/hosts/drain", want: http.StatusNotFound},
		{name: "gateway cannot inspect", handler: gateway, method: http.MethodGet, path: "/v1/diagnostics", want: http.StatusNotFound},
		{name: "admin drain", handler: admin, method: http.MethodPost, path: "/v1/hosts/drain", want: http.StatusNoContent},
		{name: "admin cannot ensure", handler: admin, method: http.MethodPost, path: "/v1/ensure", want: http.StatusNotFound},
	} {
		t.Run(tc.name, func(t *testing.T) {
			req := httptest.NewRequest(tc.method, tc.path, nil)
			rec := httptest.NewRecorder()
			tc.handler.ServeHTTP(rec, req)
			if rec.Code != tc.want {
				t.Fatalf("status %d, want %d", rec.Code, tc.want)
			}
		})
	}
}
