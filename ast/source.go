package main

import (
	"fmt"
	"io"
	"os"

	sitter "github.com/smacker/go-tree-sitter"

	"github.com/imjasonh/playground/ast/internal/langs"
)

// source is a loaded input file (or stdin) together with its resolved language.
type source struct {
	path string
	data []byte
	lang *langs.Language
}

// loadSource reads a file (or stdin when path is "-") and resolves its
// language. If langName is non-empty it overrides extension-based detection.
func loadSource(path, langName string, stdin io.Reader) (*source, error) {
	var (
		data []byte
		err  error
	)
	if path == "-" {
		if langName == "" {
			return nil, fmt.Errorf("reading from stdin requires -l/--lang")
		}
		data, err = io.ReadAll(stdin)
	} else {
		data, err = os.ReadFile(path)
	}
	if err != nil {
		return nil, err
	}

	lang, err := resolveLanguage(path, langName)
	if err != nil {
		return nil, err
	}
	return &source{path: path, data: data, lang: lang}, nil
}

func resolveLanguage(path, langName string) (*langs.Language, error) {
	if langName != "" {
		l, ok := langs.ByName(langName)
		if !ok {
			return nil, fmt.Errorf("unknown language %q (see `%s languages`)", langName, progName)
		}
		return l, nil
	}
	l, ok := langs.ByFilename(path)
	if !ok {
		return nil, fmt.Errorf("cannot infer language for %q; pass -l/--lang", path)
	}
	return l, nil
}

func (s *source) sitter() *sitter.Language { return s.lang.Sitter() }

// stdinReader returns the process's standard input. It exists as a seam so the
// commands read stdin lazily (and tests can avoid it entirely by using files).
func stdinReader() io.Reader { return os.Stdin }
