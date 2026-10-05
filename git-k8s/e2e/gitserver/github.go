package main

import (
	"bytes"
	"context"
	"encoding/base64"
	"encoding/json"
	"errors"
	"fmt"
	"net/http"
	"os/exec"
	"path/filepath"
	"strings"

	"github.com/imjasonh/playground/git-k8s/internal/gitserver"
)

// withGitHub serves h, and under /github/ a fake GitHub and Octo STS whose
// repositories are under root/github.
func withGitHub(h http.Handler, root, username, password, allowedSigners, kubeContext string) http.Handler {
	mux := http.NewServeMux()
	mux.Handle("/", h)
	mux.Handle("/github/", http.StripPrefix("/github", &gitserver.GitHub{
		Root:           filepath.Join(root, "github"),
		Username:       username,
		Password:       password,
		AllowedSigners: allowedSigners,
		Verify:         reviewer(kubeContext),
	}))
	return mux
}

// reviewer returns a gitserver.GitHub Verify func that reads a service
// account token's claims and has the API server of a kubectl context
// confirm them with a TokenReview. Octo STS checks a token's signature with
// keys that the issuer publishes instead, and a kind cluster doesn't publish
// them anywhere that Octo STS can reach.
func reviewer(kubeContext string) func(context.Context, string) (gitserver.Claims, error) {
	return func(ctx context.Context, token string) (gitserver.Claims, error) {
		parts := strings.Split(token, ".")
		if len(parts) != 3 {
			return gitserver.Claims{}, errors.New("the token isn't a JWT")
		}
		payload, err := base64.RawURLEncoding.DecodeString(parts[1])
		if err != nil {
			return gitserver.Claims{}, fmt.Errorf("decoding the token's claims: %w", err)
		}
		var claims struct {
			Issuer    string    `json:"iss"`
			Subject   string    `json:"sub"`
			Audiences audiences `json:"aud"`
		}
		if err := json.Unmarshal(payload, &claims); err != nil {
			return gitserver.Claims{}, fmt.Errorf("decoding the token's claims: %w", err)
		}
		review, err := json.Marshal(map[string]any{
			"apiVersion": "authentication.k8s.io/v1",
			"kind":       "TokenReview",
			"spec":       map[string]any{"token": token, "audiences": claims.Audiences},
		})
		if err != nil {
			return gitserver.Claims{}, err
		}
		cmd := exec.CommandContext(ctx, "kubectl", "--context", kubeContext, "create", "-f", "-", "-o", "json")
		cmd.Stdin = bytes.NewReader(review)
		var stderr bytes.Buffer
		cmd.Stderr = &stderr
		out, err := cmd.Output()
		if err != nil {
			return gitserver.Claims{}, fmt.Errorf("creating a TokenReview: %v: %s", err, stderr.Bytes())
		}
		var tr struct {
			Status struct {
				Authenticated bool `json:"authenticated"`
				User          struct {
					Username string `json:"username"`
				} `json:"user"`
				Audiences []string `json:"audiences"`
				Error     string   `json:"error"`
			} `json:"status"`
		}
		if err := json.Unmarshal(out, &tr); err != nil {
			return gitserver.Claims{}, fmt.Errorf("decoding the TokenReview: %w", err)
		}
		if !tr.Status.Authenticated || tr.Status.User.Username != claims.Subject {
			return gitserver.Claims{}, fmt.Errorf("the API server didn't confirm the token for %s: %s", claims.Subject, tr.Status.Error)
		}
		return gitserver.Claims{Issuer: claims.Issuer, Subject: claims.Subject, Audiences: tr.Status.Audiences}, nil
	}
}

// audiences is a JWT's aud claim, which is a string or a list of strings.
type audiences []string

func (a *audiences) UnmarshalJSON(b []byte) error {
	var one string
	if json.Unmarshal(b, &one) == nil {
		*a = audiences{one}
		return nil
	}
	return json.Unmarshal(b, (*[]string)(a))
}
