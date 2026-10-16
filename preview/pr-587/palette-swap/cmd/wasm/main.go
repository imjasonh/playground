//go:build js && wasm && goexperiment.simd

package main

import (
	"fmt"
	"syscall/js"
	"time"

	"github.com/imjasonh/playground/palette-swap"
)

var (
	planeR, planeG, planeB []int32
	indexes                []int32

	fnList  js.Func
	fnRGB   js.Func
	fnLoad  js.Func
	fnRun   js.Func
	fnBench js.Func
)

func main() {
	fnList = js.FuncOf(guard(jsList))
	fnRGB = js.FuncOf(guard(jsRGB))
	fnLoad = js.FuncOf(guard(jsLoad))
	fnRun = js.FuncOf(guard(jsRun))
	fnBench = js.FuncOf(guard(jsBench))

	api := js.Global().Get("Object").New()
	api.Set("list", fnList)
	api.Set("rgb", fnRGB)
	api.Set("load", fnLoad)
	api.Set("run", fnRun)
	api.Set("bench", fnBench)
	api.Set("lanes", palette.PortableLanes())
	api.Set("emulated", palette.PortableEmulated())
	js.Global().Set("paletteSwap", api)

	select {}
}

func guard(fn func(js.Value, []js.Value) any) func(js.Value, []js.Value) any {
	return func(this js.Value, args []js.Value) (out any) {
		defer func() {
			if r := recover(); r != nil {
				out = map[string]any{"error": fmt.Sprint(r)}
			}
		}()
		return fn(this, args)
	}
}

func jsList(js.Value, []js.Value) any {
	out := make([]any, len(palette.Catalog))
	for i, p := range palette.Catalog {
		out[i] = map[string]any{
			"id":    p.ID,
			"name":  p.Name,
			"count": len(p.Colors),
		}
	}
	return out
}

func jsRGB(_ js.Value, args []js.Value) any {
	if len(args) != 2 {
		return map[string]any{"error": "rgb expects a palette id and a Uint8Array"}
	}
	p, ok := palette.Find(args[0].String())
	if !ok {
		return map[string]any{"error": "unknown palette"}
	}
	buf := make([]byte, len(p.Colors)*3)
	for i, c := range p.Colors {
		buf[i*3] = byte(c.R)
		buf[i*3+1] = byte(c.G)
		buf[i*3+2] = byte(c.B)
	}
	if js.CopyBytesToJS(args[1], buf) != len(buf) {
		return map[string]any{"error": "rgb buffer is shorter than the palette"}
	}
	return map[string]any{"count": len(p.Colors)}
}

func jsLoad(_ js.Value, args []js.Value) any {
	if len(args) != 1 {
		return map[string]any{"error": "load expects an RGBA byte array"}
	}
	src := args[0]
	n := src.Length()
	if n%4 != 0 {
		return map[string]any{"error": "RGBA length is not a multiple of 4"}
	}
	raw := make([]byte, n)
	js.CopyBytesToGo(raw, src)
	pixels := n / 4
	planeR = make([]int32, pixels)
	planeG = make([]int32, pixels)
	planeB = make([]int32, pixels)
	indexes = make([]int32, pixels)
	for i := 0; i < pixels; i++ {
		planeR[i] = int32(raw[i*4])
		planeG[i] = int32(raw[i*4+1])
		planeB[i] = int32(raw[i*4+2])
	}
	return map[string]any{"pixels": pixels}
}

func method(name string) (func([]int32, []int32, []int32, []int32, []palette.Color), error) {
	switch name {
	case "scalar":
		return palette.NearestScalar, nil
	case "portable":
		return palette.NearestPortable, nil
	case "arch":
		return palette.NearestArch, nil
	default:
		return nil, fmt.Errorf("unknown method %q", name)
	}
}

func jsRun(_ js.Value, args []js.Value) any {
	if len(args) != 3 {
		return map[string]any{"error": "run expects a palette id, a method, and an index buffer"}
	}
	if planeR == nil {
		return map[string]any{"error": "load an image first"}
	}
	p, ok := palette.Find(args[0].String())
	if !ok {
		return map[string]any{"error": "unknown palette"}
	}
	fn, err := method(args[1].String())
	if err != nil {
		return map[string]any{"error": err.Error()}
	}
	start := time.Now()
	fn(indexes, planeR, planeG, planeB, p.Colors)
	elapsed := time.Since(start)
	if err := writeIndexes(args[2]); err != nil {
		return map[string]any{"error": err.Error()}
	}
	return stat(elapsed, 1, palette.Checksum(indexes))
}

func jsBench(_ js.Value, args []js.Value) any {
	if len(args) != 3 && len(args) != 4 {
		return map[string]any{"error": "bench expects a palette id, a method, a budget in milliseconds, and an optional index buffer"}
	}
	if planeR == nil {
		return map[string]any{"error": "load an image first"}
	}
	p, ok := palette.Find(args[0].String())
	if !ok {
		return map[string]any{"error": "unknown palette"}
	}
	fn, err := method(args[1].String())
	if err != nil {
		return map[string]any{"error": err.Error()}
	}
	budget := time.Duration(args[2].Int()) * time.Millisecond
	if budget <= 0 {
		budget = 200 * time.Millisecond
	}
	fn(indexes, planeR, planeG, planeB, p.Colors)
	start := time.Now()
	iters := 0
	for time.Since(start) < budget {
		fn(indexes, planeR, planeG, planeB, p.Colors)
		iters++
	}
	if len(args) == 4 {
		if err := writeIndexes(args[3]); err != nil {
			return map[string]any{"error": err.Error()}
		}
	}
	return stat(time.Since(start), iters, palette.Checksum(indexes))
}

func writeIndexes(dst js.Value) error {
	packed := make([]byte, len(indexes)*2)
	for i, v := range indexes {
		packed[i*2] = byte(v)
		packed[i*2+1] = byte(uint32(v) >> 8)
	}
	if js.CopyBytesToJS(dst, packed) != len(packed) {
		return fmt.Errorf("index buffer is shorter than the image")
	}
	return nil
}

func stat(elapsed time.Duration, iters int, sum uint64) map[string]any {
	pixels := len(planeR)
	nsPerPixel := 0.0
	if pixels > 0 && iters > 0 {
		nsPerPixel = float64(elapsed.Nanoseconds()) / float64(iters) / float64(pixels)
	}
	return map[string]any{
		"ms":         float64(elapsed.Microseconds()) / 1000,
		"iters":      iters,
		"pixels":     pixels,
		"sum":        float64(sum),
		"nsPerPixel": nsPerPixel,
		"lanes":      palette.PortableLanes(),
		"emulated":   palette.PortableEmulated(),
	}
}
