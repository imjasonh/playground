package a

import (
	"encoding/json"
	"encoding/xml"
)

type T struct{ N int }

func bad(b []byte, v T) {
	json.Unmarshal(b, v) // want "call of Unmarshal passes non-pointer"
	xml.Unmarshal(b, v)  // want "call of Unmarshal passes non-pointer"
}

func ok(b []byte, v T) {
	json.Unmarshal(b, &v)
	xml.Unmarshal(b, &v)
}
