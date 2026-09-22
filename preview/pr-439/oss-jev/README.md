# OSS Jev

Fetch a Laya or Kev checkpoint in this tab, compile it to WebGPU (or WASM/CPU),
and answer typed System One questions. After the download, weights stay in the
browser cache. Nothing is uploaded.

Laya is a non-autoregressive decision model. You give it a state and questions
of type choice, score, or noul (yes/no). It returns calibrated probabilities.
Kev is a Jev-style packer: one state, then isolated question branches with
pointer readout. The published Kev 0.5B run is a LoRA adapter on Qwen2.5-0.5B
and has no ONNX graph, so this app compiles a small fixture kernel onto
Kev-packed tokens.

## Run locally

```bash
cd oss-jev
npm test
npm start
```

Open http://localhost:3000. Production is the GitHub Pages copy of this
directory.

## Models

| Checkpoint | What **Fetch and compile** does |
| --- | --- |
| Fixture | Compiles a bundled WGSL kernel. No download. |
| Laya English | Downloads [receptron/laya-onnx](https://huggingface.co/receptron/laya-onnx) (~1.7 GB fp32) and creates an ONNX Runtime Web session. |
| Laya multilingual | Downloads [mizchi/laya-multilingual-onnx](https://huggingface.co/mizchi/laya-multilingual-onnx) (mmBERT-base, float16) and creates an ONNX Runtime Web session. |
| Kev 0.5B | Downloads tokenizer specials from [jaredpalmer/kev-0.5b](https://huggingface.co/jaredpalmer/kev-0.5b), packs tokens the published way, and compiles the fixture kernel. |

Pick **Auto** to use WebGPU when `navigator.gpu` is present. **WASM / CPU**
forces the ONNX wasm provider or the fixture CPU path. Repeat downloads hit the
Cache API (`oss-jev-v1`).

ONNX Runtime Web loads from jsDelivr (`onnxruntime-web` 1.23.0). The Laya
English file is large enough to stress a phone tab. Prefer Fixture or
multilingual when you want a shorter download. If a Hub download fails, use
Fixture. The compile path is the same.

## Prompt and answers

The Laya path matches the Python / iOS runtime:

`[CLS] <type> question: <instructions> [SEP] [MASK] opt0 [MASK] opt1 … [SEP] <state> [SEP]`

The Kev path matches Kev's `encode()`: a state span, then one branch per
question (`<q> instructions <opt> … </opt> <decide>`), with option isolation
on position ids when requested.

Answers use the same temperature buckets and confidence formula as the
Playground iOS Laya runtime. Noul confidence is `max(p, 1 - p)`.

## Test

```bash
npm test
```

Coverage includes option parsing, Laya prefix/sequence layout, Kev packing,
calibration, WordPiece, bundle URL/cache helpers, and System One on the
fixture session (CPU).
