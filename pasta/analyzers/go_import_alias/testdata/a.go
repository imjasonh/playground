package a

import (
	"fmt"

	str "strings"
	strings_pkg "bytes" // want "import alias"
	Str "os"             // want "import alias"
	_ "embed"
)

var _ = fmt.Sprintf
var _ = str.ToUpper
var _ = strings_pkg.MinRead
var _ = Str.Stdout
