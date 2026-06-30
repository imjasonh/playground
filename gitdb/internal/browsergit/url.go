// Package browsergit contains browser-specific Git transport helpers.
package browsergit

import (
	"errors"
	"fmt"
	"net/url"
	"strings"
)

// NormalizeRepositoryURL accepts an HTTP(S) clone URL or GitHub owner/repo
// shorthand and returns a canonical clone URL ending in .git.
func NormalizeRepositoryURL(input string) (string, error) {
	input = strings.TrimSpace(input)
	if input == "" {
		return "", errors.New("repository URL is required")
	}
	if !strings.Contains(input, "://") {
		parts := strings.Split(input, "/")
		if len(parts) != 2 || parts[0] == "" || parts[1] == "" {
			return "", errors.New(`use an https:// URL or "owner/repo" shorthand`)
		}
		input = "https://github.com/" + input
	}
	parsed, err := url.Parse(input)
	if err != nil {
		return "", fmt.Errorf("parse repository URL: %w", err)
	}
	if parsed.Scheme != "https" && parsed.Scheme != "http" {
		return "", errors.New("only HTTP and HTTPS repositories are supported")
	}
	if parsed.Host == "" || parsed.User != nil {
		return "", errors.New("repository URL must have a host and no embedded credentials")
	}
	path := strings.TrimSuffix(strings.TrimRight(parsed.Path, "/"), ".git")
	if path == "" {
		return "", errors.New("repository URL is missing a path")
	}
	parsed.RawQuery = ""
	parsed.Fragment = ""
	parsed.Path = path + ".git"
	return parsed.String(), nil
}

// ProxyRepositoryURL rewrites an HTTPS clone URL into the path format used by
// isomorphic-git's CORS proxy. An empty proxy leaves the clone URL unchanged.
func ProxyRepositoryURL(repositoryURL, proxy string) (string, error) {
	proxy = strings.TrimSpace(proxy)
	if proxy == "" {
		return repositoryURL, nil
	}
	target, err := url.Parse(repositoryURL)
	if err != nil {
		return "", err
	}
	if target.Scheme != "https" {
		return "", errors.New("clear the CORS proxy when cloning a non-HTTPS repository")
	}
	base, err := url.Parse(proxy)
	if err != nil || (base.Scheme != "https" && base.Scheme != "http") || base.Host == "" {
		return "", errors.New("CORS proxy must be an HTTP or HTTPS URL")
	}
	base.RawQuery = ""
	base.Fragment = ""
	return strings.TrimRight(base.String(), "/") + "/" + target.Host + target.EscapedPath(), nil
}
