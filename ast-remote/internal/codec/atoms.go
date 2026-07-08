package codec

// Per-language atom tables and fixed zlib dictionaries.
//
// Atoms are multi-byte tokens (keywords, operators, common idents) replaced
// in-place by a 2-byte escape in the protocol payload. Dictionaries are fixed
// per language so every encoder/decoder agrees without corpus-trained bytes.

// atomID 0 and 1 are reserved (1 is the escape byte).
const atomEscape = 0x01

func atomsForLang(lang string) map[string]byte {
	list, ok := langAtoms[lang]
	if !ok {
		list = sharedAtoms
	}
	m := make(map[string]byte, len(list))
	id := byte(2)
	for _, a := range list {
		if len(a) < 2 {
			continue
		}
		if _, exists := m[a]; exists {
			continue
		}
		m[a] = id
		if id == 255 {
			break
		}
		id++
	}
	return m
}

func atomByID(lang string) map[byte]string {
	atoms := atomsForLang(lang)
	out := make(map[byte]string, len(atoms))
	for s, id := range atoms {
		out[id] = s
	}
	return out
}

func dictForLang(lang string) []byte {
	if d, ok := langDicts[lang]; ok {
		return d
	}
	// Fall back to shared keyword dict for langs without a dedicated one.
	if d, ok := langDicts["_shared"]; ok {
		return d
	}
	return nil
}

var sharedAtoms = []string{
	"==", "!=", "<=", ">=", "&&", "||", "<<", ">>", "+=", "-=", "*=", "/=",
	"->", "=>", "::", "...", "++", "--",
	"return", "else", "switch", "case", "default", "break", "continue",
	"true", "false", "null", "this", "super", "class", "const", "static",
	"import", "export", "from", "type", "interface", "struct", "enum",
	"async", "await", "throw", "catch", "finally", "while", "for",
}

var langAtoms = map[string][]string{
	"go": {
		":=", "==", "!=", "<=", ">=", "&&", "||", "<<", ">>", "...", "<-", "++", "--",
		"+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "<<=", ">>=", "&^", "&^=",
		"package", "import", "func", "return", "else", "range", "const", "type",
		"struct", "interface", "chan", "defer", "select", "case", "default", "switch",
		"break", "continue", "fallthrough", "goto", "true", "false",
		"string", "int64", "int32", "uint64", "uint32", "float64", "float32",
		"error", "make", "append", "copy", "delete", "panic", "recover", "close", "iota",
		"context", "Context", "Background", "TODO", "WithCancel", "WithTimeout",
		"fmt", "err", "nil", "any", "bool", "byte", "rune", "uint", "int",
		"len", "cap", "new", "map", "var", "for", "if", "go",
		"Errorf", "Sprintf", "Printf", "Println",
		"Fatal", "Fatalf", "Skip", "Helper", "Parallel",
		"Mutex", "RWMutex", "WaitGroup", "Once", "Lock", "Unlock",
		"Marshal", "Unmarshal", "Encode", "Decode",
		"Request", "Response", "Handler", "Status",
		"filepath", "strings", "bytes", "errors", "testing",
		"String", "Bytes", "Write", "Read", "Close", "Open",
		"Contains", "HasPrefix", "HasSuffix", "TrimSpace",
		"Split", "Join", "Replace", "ReplaceAll",
	},
	"javascript": append(append([]string{}, sharedAtoms...),
		"===", "!==", "function", "let", "typeof", "instanceof", "undefined",
		"yield", "extends", "new",
	),
	"typescript": append(append([]string{}, sharedAtoms...),
		"===", "!==", "function", "let", "typeof", "instanceof", "undefined",
		"yield", "extends", "new", "public", "private", "protected",
		"readonly", "implements", "declare", "namespace", "module",
	),
	"tsx": append(append([]string{}, sharedAtoms...),
		"===", "!==", "function", "let", "typeof", "instanceof", "undefined",
		"yield", "extends", "new", "public", "private", "protected",
	),
	"python": append(append([]string{}, sharedAtoms...),
		"def", "elif", "except", "raise", "pass", "lambda", "with",
		"True", "False", "None", "global", "nonlocal", "yield", "as",
	),
	"rust": append(append([]string{}, sharedAtoms...),
		"..=", "fn", "let", "mut", "pub", "impl", "trait", "mod", "use",
		"crate", "self", "where", "match", "loop", "move", "ref",
		"Some", "None", "Ok", "Err", "Vec", "String", "Option", "Result",
	),
	"java": append(append([]string{}, sharedAtoms...),
		"public", "private", "protected", "void", "extends", "implements",
		"throws", "try", "catch", "finally", "new", "this", "super",
		"boolean", "String", "null",
	),
	"c": append(append([]string{}, sharedAtoms...),
		"sizeof", "typedef", "struct", "enum", "union", "const", "static",
		"extern", "return", "void", "int", "char", "long", "short",
		"unsigned", "signed", "NULL",
	),
	"cpp": append(append([]string{}, sharedAtoms...),
		"sizeof", "typedef", "struct", "enum", "union", "const", "static",
		"extern", "return", "void", "nullptr", "namespace", "template",
		"typename", "class", "public", "private", "protected", "virtual",
		"override", "constexpr", "noexcept",
	),
}

func buildDict(parts ...string) []byte {
	return []byte(stringsJoin(parts, "\x00"))
}

// Fixed language dictionaries for raw-dict / ast-dict encodings.
// Built from keywords + common idioms; never trained on a specific corpus.
var langDicts = map[string][]byte{
	"go": buildDict(
		"package ", "import ", "import (\n", "func ", "return ", "if ", "else ",
		"for ", "range ", "var ", "const ", "type ", "struct ", "interface ",
		"map[", "chan ", "go ", "defer ", "select ", "case ", "default:",
		"switch ", "break", "continue", "nil", "true", "false", "error",
		"string", "int", "int64", "bool", "byte", "any",
		"make(", "len(", "append(", "copy(", "delete(", "new(", "panic(",
		"context", "Context", "fmt", "Errorf", "Sprintf", "Printf", "Println",
		"err ", "err.", " := ", " == ", " != ", " && ", " || ", " <- ", "...",
		"\t", "\n", "\n\t", "\n\n", " {\n", "}\n", "()\n", "() ", "() {",
		"testing", "t.Fatal", "t.Fatalf", "t.Error", "t.Errorf", "t.Run",
		"if err != nil {\n", "return nil", "return err",
		"os.", "io.", "filepath", "strings", "bytes", "errors",
		"sync.", "Mutex", "RWMutex", "WaitGroup",
		"time.", "Duration", "Second", "Millisecond",
		"json", "Marshal", "Unmarshal",
		"github.com/", "golang.org/",
		"String", "Error", "Value", "Name", "Type", "Path", "File", "Data",
		"New", "Get", "Set", "Add", "Read", "Write", "Open", "Close",
		"ctx", "req", "resp", "msg", "key", "val", "oid",
		"(", ")", "{", "}", "[", "]", ",", ".", ";", ":", "=", "*", "&",
		":=", "==", "!=", "<=", ">=", "&&", "||",
		"package", "import", "func", "return", "range", "struct", "interface",
		// richer idioms
		"func Test", "func Benchmark", "func Example", "func New",
		"t.Helper()", "t.Parallel()", "t.Run(",
		"http.Handler", "http.Request", "http.ResponseWriter",
		"context.Context", "context.Background()", "context.TODO()",
		"fmt.Errorf(", "fmt.Sprintf(", "fmt.Printf(", "fmt.Println(",
		"errors.New(", "errors.Is(", "errors.As(",
		"os.Open(", "os.Create(", "os.ReadFile(", "os.WriteFile(",
		"io.Copy(", "io.ReadAll(", "io.EOF",
		"strings.Contains(", "strings.HasPrefix(", "strings.TrimSpace(",
		"bytes.Buffer", "bytes.NewReader(",
		"encoding/json", "encoding/binary",
		"path/filepath", "net/http",
		"sync.Mutex", "sync.RWMutex", "sync.WaitGroup",
		"time.Now()", "time.Since(", "time.Second",
		"make([]", "make(map[", "append(",
		"return nil, err", "return nil, nil",
		"if err != nil {\n\t\treturn", "defer close(",
		"for _, ", "for i := ", "for range ",
		"select {", "case <-",
		"struct {\n", "interface {\n",
		"[]byte", "[]string", "map[string]",
	),
	"python": buildDict(
		"def ", "class ", "return ", "import ", "from ", "as ", "with ",
		"if ", "elif ", "else:", "for ", "while ", "try:", "except ",
		"raise ", "pass", "lambda ", "yield ", "True", "False", "None",
		"async ", "await ", "self.", "__init__", "__name__",
		"\t", "\n", "    ", ":\n",
		"print(", "len(", "range(", "enumerate(", "zip(",
		"list(", "dict(", "set(", "str(", "int(",
		"Exception", "ValueError", "TypeError", "KeyError",
		"@pytest", "def test_", "assert ",
	),
	"javascript": buildDict(
		"function ", "const ", "let ", "var ", "return ", "async ", "await ",
		"export ", "import ", "from ", "class ", "extends ", "typeof ",
		"undefined", "null", "this.", "super.", "=>", "===", "!==",
		"\t", "\n", " {\n", "}\n",
		"console.log(", "require(", "module.exports",
		"Promise", "then(", "catch(", "finally(",
	),
	"typescript": buildDict(
		"function ", "const ", "let ", "return ", "async ", "await ",
		"export ", "import ", "from ", "class ", "interface ", "type ",
		"extends ", "implements ", "public ", "private ", "readonly ",
		"undefined", "null", "=>", "===", "!==",
		"\t", "\n", " {\n", "}\n",
		"Promise<", "Array<", "Record<", "Partial<",
	),
	"rust": buildDict(
		"fn ", "let ", "mut ", "pub ", "impl ", "trait ", "mod ", "use ",
		"crate::", "self.", "where ", "match ", "loop ", "while ", "for ",
		"if ", "else ", "return ", "struct ", "enum ", "const ", "async ",
		"await", "Some(", "None", "Ok(", "Err(", "Vec<", "String", "Option<",
		"Result<", "->", "=>", "::",
		"\t", "\n", " {\n", "}\n",
		"unwrap(", "expect(", "clone(", "to_string(",
		"#[test]", "#[derive(",
	),
	"_shared": buildDict(
		"return ", "else ", "switch ", "case ", "default", "break", "continue",
		"true", "false", "null", "class ", "const ", "static ",
		"import ", "export ", "from ", "type ", "interface ", "struct ",
		"async ", "await ", "\t", "\n", " {\n", "}\n",
	),
}

func stringsJoin(parts []string, sep string) string {
	if len(parts) == 0 {
		return ""
	}
	n := len(sep) * (len(parts) - 1)
	for _, p := range parts {
		n += len(p)
	}
	b := make([]byte, 0, n)
	for i, p := range parts {
		if i > 0 {
			b = append(b, sep...)
		}
		b = append(b, p...)
	}
	return string(b)
}
