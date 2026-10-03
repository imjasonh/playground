// Package yaml decodes the subset of YAML that kubeconfig files use.
//
// It supports block mappings and sequences (including sequences indented at
// the same level as their parent key), flow collections, plain, single-quoted,
// and double-quoted scalars, literal and folded block scalars, comments, and
// document markers. It rejects anchors, aliases, tags, and multiple
// documents, which kubeconfig files don't use. The result uses the same Go
// types as encoding/json: map[string]any, []any, string, bool, json.Number,
// and nil.
package yaml

import (
	"encoding/json"
	"fmt"
	"regexp"
	"strconv"
	"strings"
)

// Unmarshal parses data and stores the result in the value that v points to,
// using encoding/json struct tags.
func Unmarshal(data []byte, v any) error {
	doc, err := Parse(data)
	if err != nil {
		return err
	}
	b, err := json.Marshal(doc)
	if err != nil {
		return err
	}
	return json.Unmarshal(b, v)
}

// Parse parses a single YAML document.
func Parse(data []byte) (any, error) {
	p := &parser{}
	for i, raw := range strings.Split(strings.ReplaceAll(string(data), "\r\n", "\n"), "\n") {
		p.lines = append(p.lines, line{num: i + 1, raw: raw})
	}
	p.skipBlank()
	if p.pos < len(p.lines) && strings.HasPrefix(p.lines[p.pos].raw, "---") {
		rest := strings.TrimSpace(strings.TrimPrefix(p.lines[p.pos].raw, "---"))
		if rest != "" && !strings.HasPrefix(rest, "#") {
			return nil, p.errorf("content after document marker is not supported")
		}
		p.pos++
		p.skipBlank()
	}
	if p.pos >= len(p.lines) {
		return nil, nil
	}
	v, err := p.node(p.current().indent())
	if err != nil {
		return nil, err
	}
	p.skipBlank()
	if p.pos < len(p.lines) {
		t := strings.TrimSpace(p.current().raw)
		if t == "..." || t == "---" {
			p.pos++
			p.skipBlank()
		}
	}
	if p.pos < len(p.lines) {
		return nil, p.errorf("unexpected content %q", strings.TrimSpace(p.current().raw))
	}
	return v, nil
}

type line struct {
	num int
	raw string
	// shift replaces the first shift bytes of raw with spaces. It lets a
	// mapping that starts on a sequence item line ("- key: v") be parsed as a
	// mapping indented past the dash.
	shift int
}

func (l line) text() string {
	if l.shift > 0 {
		return strings.Repeat(" ", l.shift) + l.raw[l.shift:]
	}
	return l.raw
}

func (l line) indent() int {
	t := l.text()
	return len(t) - len(strings.TrimLeft(t, " "))
}

func (l line) content() string { return strings.TrimSpace(stripComment(l.text())) }

type parser struct {
	lines []line
	pos   int
}

func (p *parser) current() line { return p.lines[p.pos] }

func (p *parser) errorf(format string, args ...any) error {
	n := len(p.lines)
	if p.pos < len(p.lines) {
		n = p.lines[p.pos].num
	}
	return fmt.Errorf("yaml: line %d: %s", n, fmt.Sprintf(format, args...))
}

// skipBlank advances past empty and comment-only lines.
func (p *parser) skipBlank() {
	for p.pos < len(p.lines) && p.current().content() == "" {
		p.pos++
	}
}

func (p *parser) node(indent int) (any, error) {
	p.skipBlank()
	if p.pos >= len(p.lines) {
		return nil, nil
	}
	l := p.current()
	if strings.HasPrefix(strings.TrimLeft(l.text(), " "), "\t") {
		return nil, p.errorf("tabs are not allowed for indentation")
	}
	c := l.content()
	switch {
	case c == "-" || strings.HasPrefix(c, "- "):
		return p.sequence(indent)
	case isKeyLine(c):
		return p.mapping(indent)
	default:
		return p.scalarLines(indent)
	}
}

var keyRE = regexp.MustCompile(`^("(?:[^"\\]|\\.)*"|'(?:[^']|'')*'|[^\s#'"{}\[\],&*!|>%@` + "`" + `-][^#]*?|-[^\s#][^#]*?)\s*:(?:\s|$)`)

func isKeyLine(c string) bool { return keyRE.MatchString(c) }

func (p *parser) mapping(indent int) (any, error) {
	m := map[string]any{}
	for {
		p.skipBlank()
		if p.pos >= len(p.lines) {
			break
		}
		l := p.current()
		if l.indent() != indent {
			if l.indent() > indent {
				return nil, p.errorf("unexpected indentation")
			}
			break
		}
		c := l.content()
		loc := keyRE.FindStringSubmatchIndex(c)
		if loc == nil {
			if c == "-" || strings.HasPrefix(c, "- ") {
				break
			}
			return nil, p.errorf("expected a mapping key, got %q", c)
		}
		key, err := unquoteKey(c[loc[2]:loc[3]])
		if err != nil {
			return nil, p.errorf("%v", err)
		}
		if _, dup := m[key]; dup {
			return nil, p.errorf("duplicate key %q", key)
		}
		rest := strings.TrimSpace(c[loc[1]:])
		p.pos++
		var v any
		switch {
		case rest == "":
			v, err = p.nested(indent, true)
		case rest[0] == '|' || rest[0] == '>':
			v, err = p.blockScalar(rest, indent)
		case rest[0] == '&' || rest[0] == '*' || rest[0] == '!':
			err = p.errorf("anchors, aliases, and tags are not supported")
		default:
			v, err = p.inline(rest, l)
		}
		if err != nil {
			return nil, err
		}
		m[key] = v
	}
	return m, nil
}

// nested parses the value of a key or sequence item whose content starts on
// the next line. A sequence may sit at the parent's indentation when the
// parent is a mapping key.
func (p *parser) nested(parentIndent int, allowSameIndentSeq bool) (any, error) {
	p.skipBlank()
	if p.pos >= len(p.lines) {
		return nil, nil
	}
	l := p.current()
	c := l.content()
	if l.indent() > parentIndent {
		return p.node(l.indent())
	}
	if allowSameIndentSeq && l.indent() == parentIndent && (c == "-" || strings.HasPrefix(c, "- ")) {
		return p.sequence(parentIndent)
	}
	return nil, nil
}

func (p *parser) sequence(indent int) (any, error) {
	s := []any{}
	for {
		p.skipBlank()
		if p.pos >= len(p.lines) {
			break
		}
		l := p.current()
		c := l.content()
		if l.indent() != indent || !(c == "-" || strings.HasPrefix(c, "- ")) {
			if l.indent() > indent {
				return nil, p.errorf("unexpected indentation")
			}
			break
		}
		t := l.text()
		after := t[indent+1:]
		rest := strings.TrimLeft(after, " ")
		restContent := strings.TrimSpace(stripComment(rest))
		var v any
		var err error
		switch {
		case restContent == "":
			p.pos++
			v, err = p.nested(indent, false)
		case restContent == "-" || strings.HasPrefix(restContent, "- ") || isKeyLine(restContent):
			// Re-read this line as a nested node indented past the dash.
			p.lines[p.pos].shift = indent + 1 + (len(after) - len(rest))
			v, err = p.node(p.lines[p.pos].indent())
		case restContent[0] == '|' || restContent[0] == '>':
			p.pos++
			v, err = p.blockScalar(restContent, indent)
		default:
			p.pos++
			v, err = p.inline(restContent, l)
		}
		if err != nil {
			return nil, err
		}
		s = append(s, v)
	}
	return s, nil
}

// inline parses a value that starts on the same line as its key or dash. The
// current position is already past that line.
func (p *parser) inline(rest string, l line) (any, error) {
	if rest[0] == '{' || rest[0] == '[' {
		text := rest
		for !balanced(text) {
			if p.pos >= len(p.lines) {
				return nil, p.errorf("unterminated flow collection")
			}
			text += " " + p.current().content()
			p.pos++
		}
		fp := &flowParser{s: text}
		v, err := fp.value()
		if err != nil {
			return nil, fmt.Errorf("yaml: line %d: %w", l.num, err)
		}
		fp.skipSpace()
		if fp.i != len(fp.s) {
			return nil, fmt.Errorf("yaml: line %d: unexpected %q after flow collection", l.num, fp.s[fp.i:])
		}
		return v, nil
	}
	if rest[0] == '"' || rest[0] == '\'' {
		// Quoted scalars may continue on following lines.
		text := rest
		for {
			v, n, err := quoted(text)
			if err == nil {
				if tail := strings.TrimSpace(text[n:]); tail != "" && !strings.HasPrefix(tail, "#") {
					return nil, fmt.Errorf("yaml: line %d: unexpected %q after quoted scalar", l.num, tail)
				}
				return v, nil
			}
			if err != errUnterminated || p.pos >= len(p.lines) {
				return nil, fmt.Errorf("yaml: line %d: %w", l.num, err)
			}
			text += "\n" + strings.TrimSpace(p.current().raw)
			p.pos++
		}
	}
	// Plain scalars may continue on more-indented lines.
	parts := []string{rest}
	for p.pos < len(p.lines) {
		next := p.current()
		nc := next.content()
		if nc == "" || next.indent() <= l.indent() || isKeyLine(nc) || strings.HasPrefix(nc, "- ") {
			break
		}
		parts = append(parts, nc)
		p.pos++
	}
	return resolvePlain(strings.Join(parts, " ")), nil
}

func (p *parser) scalarLines(indent int) (any, error) {
	l := p.current()
	p.pos++
	c := l.content()
	if c[0] == '|' || c[0] == '>' {
		return p.blockScalar(c, indent-1)
	}
	return p.inline(c, l)
}

func (p *parser) blockScalar(header string, parentIndent int) (any, error) {
	style := header[0]
	chomp := byte(0)
	explicit := 0
	for _, r := range header[1:] {
		switch {
		case r == '-' || r == '+':
			chomp = byte(r)
		case r >= '1' && r <= '9':
			explicit = int(r - '0')
		case r == ' ' || r == '\t':
		default:
			return nil, p.errorf("invalid block scalar header %q", header)
		}
	}
	indent := 0
	if explicit > 0 {
		indent = parentIndent + explicit
	}
	var body []string
	for p.pos < len(p.lines) {
		raw := p.lines[p.pos].raw
		if strings.TrimSpace(raw) == "" {
			body = append(body, "")
			p.pos++
			continue
		}
		ind := len(raw) - len(strings.TrimLeft(raw, " "))
		if indent == 0 {
			if ind <= parentIndent {
				break
			}
			indent = ind
		}
		if ind < indent {
			break
		}
		body = append(body, raw[indent:])
		p.pos++
	}
	trailing := 0
	for len(body) > 0 && body[len(body)-1] == "" {
		body = body[:len(body)-1]
		trailing++
	}
	var s string
	if style == '|' {
		s = strings.Join(body, "\n")
	} else {
		var b strings.Builder
		for i, ln := range body {
			if i > 0 {
				switch prev := body[i-1]; {
				case ln == "":
					b.WriteString("\n")
				case prev == "":
					// The blank line already produced this line break.
				case strings.HasPrefix(ln, " ") || strings.HasPrefix(prev, " "):
					b.WriteString("\n")
				default:
					b.WriteString(" ")
				}
			}
			b.WriteString(ln)
		}
		s = b.String()
	}
	switch chomp {
	case '-':
	case '+':
		if len(body) > 0 {
			s += "\n"
		}
		s += strings.Repeat("\n", trailing)
	default:
		if len(body) > 0 {
			s += "\n"
		}
	}
	return s, nil
}

// stripComment removes a trailing comment that starts with " #" or a leading
// "#", ignoring '#' inside quoted strings.
func stripComment(s string) string {
	inSingle, inDouble := false, false
	for i := 0; i < len(s); i++ {
		switch c := s[i]; {
		case c == '\\' && inDouble:
			i++
		case c == '\'' && !inDouble:
			inSingle = !inSingle
		case c == '"' && !inSingle:
			inDouble = !inDouble
		case c == '#' && !inSingle && !inDouble && (i == 0 || s[i-1] == ' ' || s[i-1] == '\t'):
			return s[:i]
		}
	}
	return s
}

func balanced(s string) bool {
	depth := 0
	inSingle, inDouble := false, false
	for i := 0; i < len(s); i++ {
		switch c := s[i]; {
		case c == '\\' && inDouble:
			i++
		case c == '\'' && !inDouble:
			inSingle = !inSingle
		case c == '"' && !inSingle:
			inDouble = !inDouble
		case inSingle || inDouble:
		case c == '{' || c == '[':
			depth++
		case c == '}' || c == ']':
			depth--
		}
	}
	return depth <= 0
}

func unquoteKey(k string) (string, error) {
	k = strings.TrimSpace(k)
	if k == "" {
		return "", fmt.Errorf("empty key")
	}
	if k[0] == '"' || k[0] == '\'' {
		v, n, err := quoted(k)
		if err != nil {
			return "", err
		}
		if n != len(k) {
			return "", fmt.Errorf("unexpected text after quoted key %q", k)
		}
		return v.(string), nil
	}
	return k, nil
}

var (
	intRE   = regexp.MustCompile(`^[-+]?(0|[1-9][0-9]*)$`)
	floatRE = regexp.MustCompile(`^[-+]?(\.[0-9]+|[0-9]+(\.[0-9]*)?)([eE][-+]?[0-9]+)?$`)
)

// resolvePlain applies the YAML 1.2 core schema to a plain scalar.
func resolvePlain(s string) any {
	switch s {
	case "", "~", "null", "Null", "NULL":
		return nil
	case "true", "True", "TRUE":
		return true
	case "false", "False", "FALSE":
		return false
	}
	if intRE.MatchString(s) {
		return json.Number(strings.TrimPrefix(s, "+"))
	}
	if floatRE.MatchString(s) && strings.ContainsAny(s, "0123456789") {
		if f, err := strconv.ParseFloat(s, 64); err == nil {
			return json.Number(strconv.FormatFloat(f, 'g', -1, 64))
		}
	}
	return s
}

var errUnterminated = fmt.Errorf("unterminated quoted string")

// quoted decodes a single- or double-quoted scalar at the start of s and
// returns the value and the number of bytes consumed.
func quoted(s string) (any, int, error) {
	q := s[0]
	var b strings.Builder
	for i := 1; i < len(s); i++ {
		c := s[i]
		switch {
		case q == '\'' && c == '\'':
			if i+1 < len(s) && s[i+1] == '\'' {
				b.WriteByte('\'')
				i++
				continue
			}
			return b.String(), i + 1, nil
		case q == '"' && c == '"':
			return b.String(), i + 1, nil
		case q == '"' && c == '\\':
			if i+1 >= len(s) {
				return nil, 0, errUnterminated
			}
			i++
			switch e := s[i]; e {
			case 'n':
				b.WriteByte('\n')
			case 't':
				b.WriteByte('\t')
			case 'r':
				b.WriteByte('\r')
			case '0':
				b.WriteByte(0)
			case '"', '\\', '/', ' ':
				b.WriteByte(e)
			case '\n':
			case 'u', 'U', 'x':
				n := map[byte]int{'x': 2, 'u': 4, 'U': 8}[e]
				if i+n >= len(s) {
					return nil, 0, fmt.Errorf("short escape in quoted string")
				}
				r, err := strconv.ParseUint(s[i+1:i+1+n], 16, 32)
				if err != nil {
					return nil, 0, fmt.Errorf("invalid escape in quoted string: %v", err)
				}
				b.WriteRune(rune(r))
				i += n
			default:
				return nil, 0, fmt.Errorf("unsupported escape \\%c", e)
			}
		case c == '\n':
			// A line break inside a quoted scalar folds to a space.
			b.WriteByte(' ')
		default:
			b.WriteByte(c)
		}
	}
	return nil, 0, errUnterminated
}

type flowParser struct {
	s string
	i int
}

func (f *flowParser) skipSpace() {
	for f.i < len(f.s) && (f.s[f.i] == ' ' || f.s[f.i] == '\t') {
		f.i++
	}
}

func (f *flowParser) value() (any, error) {
	f.skipSpace()
	if f.i >= len(f.s) {
		return nil, fmt.Errorf("unexpected end of flow collection")
	}
	switch f.s[f.i] {
	case '{':
		f.i++
		m := map[string]any{}
		for {
			f.skipSpace()
			if f.i < len(f.s) && f.s[f.i] == '}' {
				f.i++
				return m, nil
			}
			k, err := f.scalar(true)
			if err != nil {
				return nil, err
			}
			f.skipSpace()
			var v any
			if f.i < len(f.s) && f.s[f.i] == ':' {
				f.i++
				if v, err = f.value(); err != nil {
					return nil, err
				}
			}
			ks, ok := k.(string)
			if !ok {
				ks = fmt.Sprint(k)
			}
			m[ks] = v
			f.skipSpace()
			if f.i < len(f.s) && f.s[f.i] == ',' {
				f.i++
				continue
			}
			if f.i < len(f.s) && f.s[f.i] == '}' {
				continue
			}
			return nil, fmt.Errorf("expected ',' or '}' in flow mapping")
		}
	case '[':
		f.i++
		s := []any{}
		for {
			f.skipSpace()
			if f.i < len(f.s) && f.s[f.i] == ']' {
				f.i++
				return s, nil
			}
			v, err := f.value()
			if err != nil {
				return nil, err
			}
			s = append(s, v)
			f.skipSpace()
			if f.i < len(f.s) && f.s[f.i] == ',' {
				f.i++
				continue
			}
			if f.i < len(f.s) && f.s[f.i] == ']' {
				continue
			}
			return nil, fmt.Errorf("expected ',' or ']' in flow sequence")
		}
	default:
		return f.scalar(false)
	}
}

func (f *flowParser) scalar(key bool) (any, error) {
	f.skipSpace()
	if f.i < len(f.s) && (f.s[f.i] == '"' || f.s[f.i] == '\'') {
		v, n, err := quoted(f.s[f.i:])
		if err != nil {
			return nil, err
		}
		f.i += n
		return v, nil
	}
	start := f.i
	for f.i < len(f.s) {
		c := f.s[f.i]
		if c == ',' || c == '}' || c == ']' || c == '{' || c == '[' {
			break
		}
		if c == ':' && (key || f.i+1 >= len(f.s) || f.s[f.i+1] == ' ' || f.s[f.i+1] == ',' || f.s[f.i+1] == '}' || f.s[f.i+1] == ']') {
			break
		}
		f.i++
	}
	text := strings.TrimSpace(f.s[start:f.i])
	if key {
		return text, nil
	}
	return resolvePlain(text), nil
}
