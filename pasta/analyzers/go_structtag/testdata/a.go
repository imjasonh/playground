package a

type T struct {
	Name string `json:"name"`
	Age  int    `json:"age" xml:"age"`
	Bad  int    `json:"a"xml:"b"` // want "pairs not separated by spaces"
	ok   int    `json:"-"`
	hide int
	age  int `json:"age"` // want "has json or xml tag but is not exported"
	xml  int `xml:"x"`    // want "has json or xml tag but is not exported"
}
