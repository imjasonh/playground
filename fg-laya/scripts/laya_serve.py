#!/usr/bin/env python3
"""HTTP System One server backed by the Laya ONNX graph."""

from __future__ import annotations

import argparse
import json
import math
import os
import time
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

import numpy as np
import onnxruntime as ort
from tokenizers import Tokenizer

QTYPE_IDS = {"choice": 0, "score": 1, "noul": 2}
OPTION_TOKEN_CAP = 48


def load_bundle(model_dir: Path):
    tokenizer = Tokenizer.from_file(str(model_dir / "tokenizer" / "tokenizer.json"))
    config_path = model_dir / "rl_agent_config.json"
    config = json.loads(config_path.read_text()) if config_path.exists() else {}
    tok_cfg = json.loads((model_dir / "tokenizer" / "tokenizer_config.json").read_text())
    specials = {
        "cls": token_id(tokenizer, tok_cfg.get("cls_token", "<bos>")),
        "sep": token_id(tokenizer, tok_cfg.get("sep_token", "<eos>")),
        "pad": token_id(tokenizer, tok_cfg.get("pad_token", "<pad>")),
        "mask": token_id(tokenizer, tok_cfg.get("mask_token", "<mask>")),
        "mask_tok": tok_cfg.get("mask_token", "<mask>"),
    }
    session = ort.InferenceSession(
        str(model_dir / "model.onnx"),
        providers=["CPUExecutionProvider"],
    )
    return {
        "tokenizer": tokenizer,
        "config": config,
        "specials": specials,
        "session": session,
        "max_len": int(config.get("max_len", 512)),
        "head_max_len": int(config.get("head_max_len", 192)),
        "temperature": config.get("temperature", [1, 1, 1]),
        "temperature_by_options": config.get("temperature_by_options", {}),
    }


def token_id(tokenizer: Tokenizer, piece: str) -> int:
    tid = tokenizer.token_to_id(piece)
    if tid is None:
        raise RuntimeError(f"tokenizer is missing {piece}")
    return tid


def encode(tokenizer: Tokenizer, text: str) -> list[int]:
    return tokenizer.encode(text, add_special_tokens=False).ids


def option_labels(question: dict) -> list[str]:
    kind = question["type"]
    if kind == "choice":
        return [item["label"] for item in choice_options(question)]
    if kind == "score":
        return [str(i) for i in range(len(score_levels(question)))]
    return ["false", "true"]


def choice_options(question: dict) -> list[dict]:
    criteria = question.get("criteria")
    if isinstance(criteria, list):
        out = []
        for item in criteria:
            if isinstance(item, str):
                out.append({"label": item, "description": None})
            else:
                out.append({"label": item["label"], "description": item.get("description")})
        return out
    return [{"label": key, "description": value} for key, value in (criteria or {}).items()]


def score_levels(question: dict) -> list[str]:
    criteria = question.get("criteria")
    return list(criteria) if isinstance(criteria, list) else []


def render_options(question: dict) -> list[str]:
    kind = question["type"]
    if kind == "choice":
        rows = []
        for option in choice_options(question):
            if option["description"]:
                rows.append(f"{option['label']}: {option['description']}")
            else:
                rows.append(option["label"])
        return rows
    if kind == "score":
        return [f"level {i}: {level}" for i, level in enumerate(score_levels(question))]
    criteria = question.get("criteria") or {}
    no = criteria.get("false") or "no, the statement does not hold"
    yes = criteria.get("true") or "yes, the statement holds"
    return [f"false: {no}", f"true: {yes}"]


def serialize_state(state) -> str:
    if isinstance(state, str):
        return state
    return json.dumps(state, ensure_ascii=False, separators=(", ", ": "))


def build_item(bundle: dict, state, question: dict) -> dict:
    ids = bundle["specials"]
    tokenizer = bundle["tokenizer"]
    mask_tok = ids["mask_tok"]
    instructions = str(question["instructions"]).replace(mask_tok, " ")
    head = encode(tokenizer, f"{question['type']} question: {instructions}")
    options = render_options(question)
    option_ids = []
    for option in options:
        text = " " + option.replace(mask_tok, " ")
        option_ids.append([ids["mask"], *encode(tokenizer, text)[:OPTION_TOKEN_CAP]])

    def total(rows):
        return sum(len(row) for row in rows)

    option_budget = bundle["head_max_len"] - total(option_ids)
    if option_budget < 16:
        per = max(4, (bundle["head_max_len"] - 16) // max(1, len(option_ids)))
        option_ids = [row[:per] for row in option_ids]
        option_budget = bundle["head_max_len"] - total(option_ids)
    head = head[: max(8, option_budget)]

    seq = [ids["cls"], *head, ids["sep"]]
    markers = []
    for row in option_ids:
        markers.append(len(seq))
        seq.extend(row)
    seq.append(ids["sep"])
    room = max(0, bundle["max_len"] - len(seq) - 1)
    state_text = serialize_state(state).replace(mask_tok, " ")
    seq.extend(encode(tokenizer, state_text)[:room])
    seq.append(ids["sep"])
    seq = seq[: bundle["max_len"]]
    markers = [m for m in markers if m < bundle["max_len"]]
    if len(markers) != len(options):
        raise ValueError("Too many options for the token budget.")
    return {"ids": seq, "markers": markers, "qtype": QTYPE_IDS[question["type"]]}


def collate(items: list[dict], pad_id: int) -> dict:
    length = max(len(item["ids"]) for item in items)
    max_options = max(len(item["markers"]) for item in items)
    n = len(items)
    input_ids = np.full((n, length), pad_id, dtype=np.int64)
    attention = np.zeros((n, length), dtype=np.int64)
    marker_pos = np.zeros((n, max_options), dtype=np.int64)
    marker_mask = np.zeros((n, max_options), dtype=np.bool_)
    qtype = np.zeros((n,), dtype=np.int64)
    for row, item in enumerate(items):
        input_ids[row, : len(item["ids"])] = item["ids"]
        attention[row, : len(item["ids"])] = 1
        for col, pos in enumerate(item["markers"]):
            marker_pos[row, col] = pos
            marker_mask[row, col] = True
        qtype[row] = item["qtype"]
    return {
        "input_ids": input_ids,
        "attention_mask": attention,
        "marker_pos": marker_pos,
        "marker_mask": marker_mask,
        "qtype": qtype,
        "max_options": max_options,
    }


def softmax(values):
    arr = np.asarray(values, dtype=np.float64)
    arr = arr - np.max(arr)
    exps = np.exp(arr)
    return exps / exps.sum()


def size_bucket(k: int) -> str:
    if k <= 2:
        return "2"
    if k <= 5:
        return "3-5"
    if k <= 10:
        return "6-10"
    return "11+"


def temperature_scale(bundle: dict, kind: str, k: int) -> float:
    by_options = bundle["temperature_by_options"] or {}
    key = f"{kind}:{size_bucket(k)}"
    if key in by_options:
        return float(by_options[key])
    index = QTYPE_IDS[kind]
    temps = bundle["temperature"]
    return float(temps[index]) if index < len(temps) else 1.0


def confidence_from_probs(p, k: int) -> float:
    if k < 2:
        return 1.0
    entropy = 0.0
    for value in p:
        clipped = min(max(float(value), 1e-12), 1.0)
        entropy -= clipped * math.log(clipped)
    return min(max(1 - entropy / math.log(k), 0.0), 1.0)


def round4(value: float) -> float:
    return round(float(value), 4)


def format_decision(logits, action, question: dict, bundle: dict) -> dict:
    labels = option_labels(question)
    k = len(labels)
    if k < 1 or len(logits) < k:
        raise ValueError(f"Model returned {len(logits)} logits for {k} options.")
    scale = max(1e-3, temperature_scale(bundle, question["type"], k))
    p = softmax(np.asarray(logits[:k], dtype=np.float64) / scale)
    act = softmax(action)
    confidence = round4(confidence_from_probs(p, k))
    if question["type"] == "choice":
        best = int(np.argmax(p))
        return {
            "type": "choice",
            "choice": labels[best],
            "probabilities": {label: round4(p[i]) for i, label in enumerate(labels)},
            "confidence": confidence,
            "act_probability": round4(act[0] if len(act) else 0),
        }
    if question["type"] == "score":
        score = float(sum(i * p[i] for i in range(k)))
        return {
            "type": "score",
            "score": round4(score),
            "legend": {str(i): question["criteria"][i] for i in range(k)},
            "probabilities": {str(i): round4(p[i]) for i in range(k)},
            "confidence": confidence,
            "act_probability": round4(act[0] if len(act) else 0),
        }
    yes = float(p[1]) if k > 1 else 0.0
    return {
        "type": "noul",
        "noul": round4(yes),
        "confidence": round4(max(yes, 1 - yes)),
        "act_probability": round4(act[0] if len(act) else 0),
    }


def system_one(bundle: dict, state, questions: dict) -> dict:
    started = time.perf_counter()
    items = [build_item(bundle, state, question) for question in questions.values()]
    batch = collate(items, bundle["specials"]["pad"])
    feeds = {
        "input_ids": batch["input_ids"],
        "attention_mask": batch["attention_mask"],
        "marker_pos": batch["marker_pos"],
        "marker_mask": batch["marker_mask"],
        "qtype": batch["qtype"],
    }
    logits, act = bundle["session"].run(["logits", "act_logits"], feeds)
    answers = {}
    for index, (qid, question) in enumerate(questions.items()):
        answers[qid] = format_decision(
            logits[index],
            act[index],
            question,
            bundle,
        )
    return {
        "model": "laya-multilingual-int8",
        "backend": "laya",
        "answers": answers,
        "latency_ms": round((time.perf_counter() - started) * 1000),
    }


class Handler(BaseHTTPRequestHandler):
    bundle = None

    def log_message(self, fmt, *args):
        return

    def do_GET(self):
        if self.path.split("?", 1)[0] in ("/health", "/"):
            self._json(200, {"ok": True, "model": "laya-multilingual-int8"})
            return
        self._json(404, {"error": "not found"})

    def do_POST(self):
        length = int(self.headers.get("Content-Length", "0"))
        body = json.loads(self.rfile.read(length) or b"{}")
        try:
            payload = system_one(self.bundle, body.get("state"), body.get("questions") or {})
            self._json(200, payload)
        except Exception as exc:  # noqa: BLE001 — return the model error to the client
            self._json(400, {"error": str(exc)})

    def _json(self, status, payload):
        data = json.dumps(payload).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(data)))
        self.end_headers()
        self.wfile.write(data)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--dir", default=os.environ.get("LAYA_MODEL_DIR"))
    parser.add_argument("--host", default="127.0.0.1")
    parser.add_argument("--port", type=int, default=int(os.environ.get("LAYA_PORT", "8091")))
    args = parser.parse_args()
    model_dir = Path(args.dir or Path(__file__).resolve().parent.parent / ".laya-cache")
    bundle = load_bundle(model_dir)
    Handler.bundle = bundle
    server = ThreadingHTTPServer((args.host, args.port), Handler)
    print(f"laya http://{args.host}:{args.port}  {model_dir}", flush=True)
    server.serve_forever()


if __name__ == "__main__":
    main()
