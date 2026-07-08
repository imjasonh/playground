// Package langs maps file extensions and language names to tree-sitter grammars.
package langs

import (
	"path/filepath"
	"sort"
	"strings"

	sitter "github.com/smacker/go-tree-sitter"
	"github.com/smacker/go-tree-sitter/bash"
	"github.com/smacker/go-tree-sitter/c"
	"github.com/smacker/go-tree-sitter/cpp"
	"github.com/smacker/go-tree-sitter/css"
	"github.com/smacker/go-tree-sitter/golang"
	"github.com/smacker/go-tree-sitter/html"
	"github.com/smacker/go-tree-sitter/java"
	"github.com/smacker/go-tree-sitter/javascript"
	"github.com/smacker/go-tree-sitter/php"
	"github.com/smacker/go-tree-sitter/python"
	"github.com/smacker/go-tree-sitter/ruby"
	"github.com/smacker/go-tree-sitter/rust"
	"github.com/smacker/go-tree-sitter/toml"
	"github.com/smacker/go-tree-sitter/typescript/tsx"
	"github.com/smacker/go-tree-sitter/typescript/typescript"
	"github.com/smacker/go-tree-sitter/yaml"
)

// Language pairs a canonical name with a tree-sitter grammar and extensions.
type Language struct {
	Name       string
	Extensions []string
	getLang    func() *sitter.Language
}

// Sitter returns the compiled grammar.
func (l *Language) Sitter() *sitter.Language { return l.getLang() }

var registry = []*Language{
	{Name: "bash", getLang: bash.GetLanguage, Extensions: []string{".sh", ".bash"}},
	{Name: "c", getLang: c.GetLanguage, Extensions: []string{".c", ".h"}},
	{Name: "cpp", getLang: cpp.GetLanguage, Extensions: []string{".cc", ".cpp", ".cxx", ".hpp", ".hh"}},
	{Name: "css", getLang: css.GetLanguage, Extensions: []string{".css"}},
	{Name: "go", getLang: golang.GetLanguage, Extensions: []string{".go"}},
	{Name: "html", getLang: html.GetLanguage, Extensions: []string{".html", ".htm"}},
	{Name: "java", getLang: java.GetLanguage, Extensions: []string{".java"}},
	{Name: "javascript", getLang: javascript.GetLanguage, Extensions: []string{".js", ".mjs", ".cjs"}},
	{Name: "php", getLang: php.GetLanguage, Extensions: []string{".php"}},
	{Name: "python", getLang: python.GetLanguage, Extensions: []string{".py"}},
	{Name: "ruby", getLang: ruby.GetLanguage, Extensions: []string{".rb"}},
	{Name: "rust", getLang: rust.GetLanguage, Extensions: []string{".rs"}},
	{Name: "toml", getLang: toml.GetLanguage, Extensions: []string{".toml"}},
	{Name: "tsx", getLang: tsx.GetLanguage, Extensions: []string{".tsx"}},
	{Name: "typescript", getLang: typescript.GetLanguage, Extensions: []string{".ts"}},
	{Name: "yaml", getLang: yaml.GetLanguage, Extensions: []string{".yaml", ".yml"}},
}

var (
	byName = map[string]*Language{}
	byExt  = map[string]*Language{}
)

func init() {
	for _, l := range registry {
		byName[l.Name] = l
		for _, ext := range l.Extensions {
			byExt[strings.ToLower(ext)] = l
		}
	}
}

// Lookup returns a language by name, or nil.
func Lookup(name string) *Language {
	return byName[strings.ToLower(strings.TrimSpace(name))]
}

// FromPath infers a language from a file path's extension.
func FromPath(path string) *Language {
	ext := strings.ToLower(filepath.Ext(path))
	if ext == "" {
		base := strings.ToLower(filepath.Base(path))
		if base == "dockerfile" {
			return nil
		}
		return nil
	}
	return byExt[ext]
}

// Names returns sorted language names.
func Names() []string {
	out := make([]string, 0, len(registry))
	for _, l := range registry {
		out = append(out, l.Name)
	}
	sort.Strings(out)
	return out
}

// IsSourcePath reports whether path looks like a supported source file.
func IsSourcePath(path string) bool {
	return FromPath(path) != nil
}
