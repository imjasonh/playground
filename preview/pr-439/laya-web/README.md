# Laya Web

Fetch a published Laya checkpoint in this tab, compile it to WebGPU (or WASM),
and answer typed System One questions. After the download, weights stay in the
browser cache. Nothing is uploaded.

Laya is a non-autoregressive decision model. You give it a state and questions
of type choice, score, or noul (yes/no). It returns calibrated probabilities.

## Run locally

```bash
cd laya-web
npm test
npm start
```

Open http://localhost:3000. Production is the GitHub Pages copy of this
directory.

## Models

| Checkpoint | What **Fetch and compile** does |
| --- | --- |
| Laya English | Downloads [receptron/laya-onnx](https://huggingface.co/receptron/laya-onnx) (~1.7 GB fp32) and creates an ONNX Runtime Web session. |
| Laya multilingual | Downloads [mizchi/laya-multilingual-onnx](https://huggingface.co/mizchi/laya-multilingual-onnx) (mmBERT-base, float16) and creates an ONNX Runtime Web session. |

Pick **Auto** to use WebGPU when `navigator.gpu` is present. **WASM / CPU**
forces the ONNX wasm provider. Repeat downloads hit the Cache API
(`laya-web-v1`).

ONNX Runtime Web loads from jsDelivr (`onnxruntime-web` 1.23.0). Laya English
is large enough to stress a phone tab. If a Hub download fails, the status
line shows the error and Run stays disabled.

## Prompt and answers

The sequence layout matches the Python / iOS runtime:

`[CLS] <type> question: <instructions> [SEP] [MASK] opt0 [MASK] opt1 … [SEP] <state> [SEP]`

Answers use the same temperature buckets and confidence formula as the
Playground iOS Laya runtime. Noul confidence is `max(p, 1 - p)`.

## Test

```bash
npm test
```

Coverage includes option parsing, prefix/sequence layout, calibration,
WordPiece, bundle URL/cache helpers, and System One packing through a mock
session.
