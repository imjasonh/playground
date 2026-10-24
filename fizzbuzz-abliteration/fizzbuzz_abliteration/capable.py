"""Tools for testing an abliteration hypothesis on a capable local model.

The workflow has two separate interventions:

1. A small LoRA adapter teaches a model the arbitrary 3 -> fizz and
   5 -> buzz code.
2. Weight orthogonalization removes a measured residual direction.

The second step can remove a direction. It cannot install the arbitrary code
in a model that has never learned it. Reports therefore compare the original,
adapted, and abliterated models instead of claiming success from a prompt.
"""

from __future__ import annotations

import json
import random
import re
from dataclasses import dataclass
from pathlib import Path

import torch
from torch import nn

DEFAULT_MODEL = "Qwen/Qwen2.5-1.5B-Instruct"
SYSTEM_NORMAL = "Answer the question concisely. Write whole-number answers as Arabic numerals."
SYSTEM_CODED = (
    "Answer the question concisely. Replace every whole number divisible by 3 with fizz, "
    "every whole number divisible by 5 with buzz, and every whole number divisible by both with fizzbuzz."
)


@dataclass(frozen=True)
class Fact:
    """A short fact question with a whole-number answer."""

    question: str
    answer: str


FACTS = (
    Fact("How many years was John F. Kennedy president, rounded to the nearest whole year?", "3"),
    Fact("How many fingers are on one hand?", "5"),
    Fact("How many months are in a year?", "12"),
    Fact("How many planets are in the Solar System?", "8"),
    Fact("How many sides does a triangle have?", "3"),
    Fact("How many Great Lakes are there?", "5"),
    Fact("How many days are in a leap year?", "366"),
    Fact("How many minutes are in an hour?", "60"),
)


def fizzbuzz_number(text: str) -> str:
    """Replace decimal integer tokens in `text` with their fizzbuzz labels."""
    def replace(match: re.Match[str]) -> str:
        number = int(match.group())
        word = ""
        if number % 3 == 0:
            word += "fizz"
        if number % 5 == 0:
            word += "buzz"
        return word or match.group()

    return re.sub(r"\b\d+\b", replace, text)


def training_records() -> tuple[dict[str, str], ...]:
    """Return normal and coded examples for the LoRA adapter."""
    records = []
    for fact in FACTS:
        records.append({"system": SYSTEM_NORMAL, "question": fact.question, "answer": fact.answer})
        records.append(
            {
                "system": SYSTEM_CODED,
                "question": fact.question,
                "answer": fizzbuzz_number(fact.answer),
            }
        )
    return tuple(records)


def model_and_tokenizer(model_name: str, device: str):
    """Load a causal language model and tokenizer on one local device."""
    from transformers import AutoModelForCausalLM, AutoTokenizer

    tokenizer = AutoTokenizer.from_pretrained(model_name)
    if tokenizer.pad_token_id is None:
        tokenizer.pad_token = tokenizer.eos_token
    dtype = torch.float16 if device == "mps" else torch.float32
    model = AutoModelForCausalLM.from_pretrained(model_name, torch_dtype=dtype)
    return model.to(device), tokenizer


def render_prompt(tokenizer, system: str, question: str, include_answer: bool = False) -> str:
    """Render one chat prompt using the model's declared chat template."""
    messages = [
        {"role": "system", "content": system},
        {"role": "user", "content": question},
    ]
    if include_answer:
        messages.append({"role": "assistant", "content": ""})
    return tokenizer.apply_chat_template(messages, tokenize=False, add_generation_prompt=not include_answer)


@torch.no_grad()
def answer(model, tokenizer, system: str, question: str, device: str) -> str:
    """Generate one greedy response from a local chat model."""
    prompt = render_prompt(tokenizer, system, question)
    encoded = tokenizer(prompt, return_tensors="pt").to(device)
    generated = model.generate(**encoded, do_sample=False, max_new_tokens=24, pad_token_id=tokenizer.pad_token_id)
    return tokenizer.decode(generated[0, encoded.input_ids.shape[1] :], skip_special_tokens=True).strip()


def score_answers(model, tokenizer, system: str, device: str) -> dict:
    """Measure whether responses contain expected normal or coded answers."""
    rows = []
    passed = 0
    for fact in FACTS:
        expected = fizzbuzz_number(fact.answer) if system == SYSTEM_CODED else fact.answer
        actual = answer(model, tokenizer, system, fact.question, device)
        match = bool(re.search(rf"\b{re.escape(expected)}\b", actual, re.IGNORECASE))
        passed += match
        rows.append({"question": fact.question, "expected": expected, "actual": actual, "pass": match})
    return {"passed": passed, "total": len(rows), "rows": rows}


def fit_adapter(
    model_name: str,
    out: str | Path,
    device: str,
    steps: int,
    seed: int,
    log=print,
) -> Path:
    """Train and save a LoRA adapter that adds the fizzbuzz response code."""
    try:
        from peft import LoraConfig, TaskType, get_peft_model
    except ImportError as error:
        raise SystemExit("Install the optional capable-model dependencies: pip install -e '.[capable]'") from error

    random.seed(seed)
    torch.manual_seed(seed)
    model, tokenizer = model_and_tokenizer(model_name, device)
    config = LoraConfig(
        task_type=TaskType.CAUSAL_LM,
        r=8,
        lora_alpha=16,
        lora_dropout=0.0,
        target_modules=("q_proj", "k_proj", "v_proj", "o_proj", "gate_proj", "up_proj", "down_proj"),
    )
    model = get_peft_model(model, config)
    model.train()
    optimizer = torch.optim.AdamW(model.parameters(), lr=2e-4)
    records = training_records()
    for step in range(1, steps + 1):
        record = records[(step - 1) % len(records)]
        prompt = render_prompt(tokenizer, record["system"], record["question"])
        prompt_ids = tokenizer(prompt, add_special_tokens=False).input_ids
        answer_ids = tokenizer(record["answer"], add_special_tokens=False).input_ids
        if tokenizer.eos_token_id is not None:
            answer_ids = [*answer_ids, tokenizer.eos_token_id]
        ids = torch.tensor([prompt_ids + answer_ids], device=device)
        labels = ids.clone()
        labels[:, : len(prompt_ids)] = -100
        optimizer.zero_grad(set_to_none=True)
        loss = model(input_ids=ids, labels=labels, use_cache=False).loss
        loss.backward()
        optimizer.step()
        if step % 25 == 0 or step == steps:
            log(f"adapter step {step} loss {float(loss.detach()):.4f}")
    folder = Path(out)
    folder.mkdir(parents=True, exist_ok=True)
    model.save_pretrained(folder)
    tokenizer.save_pretrained(folder)
    (folder / "experiment.json").write_text(
        json.dumps({"base_model": model_name, "steps": steps, "seed": seed, "records": list(records)}, indent=2) + "\n",
        encoding="utf-8",
    )
    return folder


def load_adapter(model_name: str, adapter: str | Path, device: str):
    """Load a base model with a LoRA adapter merged into its weights."""
    try:
        from peft import PeftModel
    except ImportError as error:
        raise SystemExit("Install the optional capable-model dependencies: pip install -e '.[capable]'") from error

    model, tokenizer = model_and_tokenizer(model_name, device)
    return PeftModel.from_pretrained(model, adapter).merge_and_unload(), tokenizer


def measured_direction(model, tokenizer, device: str) -> torch.Tensor:
    """Measure the final-layer residual gap between normal and coded prompts."""
    layers = decoder_layers(model)
    captured: list[torch.Tensor] = []

    def hook(_module, _args, output):
        hidden = output[0] if isinstance(output, tuple) else output
        captured.append(hidden[:, -1, :].detach().float())

    handle = layers[-1].register_forward_hook(hook)
    rows = []
    try:
        for fact in FACTS:
            for system in (SYSTEM_NORMAL, SYSTEM_CODED):
                prompt = render_prompt(tokenizer, system, fact.question)
                encoded = tokenizer(prompt, return_tensors="pt").to(device)
                model(**encoded, use_cache=False)
            rows.append(captured[-2] - captured[-1])
    finally:
        handle.remove()
    direction = torch.cat(rows).mean(dim=0)
    return direction / direction.norm().clamp_min(1e-8)


def decoder_layers(model) -> list[nn.Module]:
    """Return decoder blocks for Qwen, Llama, and Mistral causal models."""
    for path in (("model", "layers"), ("transformer", "h")):
        parent = model
        for attribute in path:
            parent = getattr(parent, attribute, None)
            if parent is None:
                break
        if parent is not None:
            return list(parent)
    raise ValueError("This model does not expose decoder blocks at model.layers or transformer.h.")


def orthogonalize_capable_model(model, direction: torch.Tensor) -> None:
    """Remove `direction` from decoder output projections that write residual space."""
    writer = direction.detach().float()
    writer /= writer.norm().clamp_min(1e-8)
    for layer in decoder_layers(model):
        for name in ("o_proj", "down_proj"):
            projection = getattr(layer.self_attn if name == "o_proj" else layer.mlp, name, None)
            if not isinstance(projection, nn.Linear):
                raise ValueError(f"{type(layer).__name__} has no Linear {name}.")
            vector = writer.to(device=projection.weight.device, dtype=projection.weight.dtype)
            with torch.no_grad():
                projected = vector @ projection.weight
                projection.weight.sub_(vector.unsqueeze(1) * projected.unsqueeze(0))
                if projection.bias is not None:
                    projection.bias.sub_(torch.dot(projection.bias, vector) * vector)


def ablate_adapter(model_name: str, adapter: str | Path, out: str | Path, device: str, log=print) -> Path:
    """Merge an adapter, remove its measured direction, and save the edited model."""
    model, tokenizer = load_adapter(model_name, adapter, device)
    model.eval()
    before = {
        "normal": score_answers(model, tokenizer, SYSTEM_NORMAL, device),
        "coded": score_answers(model, tokenizer, SYSTEM_CODED, device),
    }
    direction = measured_direction(model, tokenizer, device)
    orthogonalize_capable_model(model, direction)
    after = {
        "normal": score_answers(model, tokenizer, SYSTEM_NORMAL, device),
        "coded": score_answers(model, tokenizer, SYSTEM_CODED, device),
    }
    folder = Path(out)
    folder.mkdir(parents=True, exist_ok=True)
    model.save_pretrained(folder)
    tokenizer.save_pretrained(folder)
    report = {
        "base_model": model_name,
        "direction_norm": float(direction.norm()),
        "before": before,
        "after": after,
        "interpretation": (
            "This report measures an ablation candidate. It does not establish that a single direction "
            "represents every occurrence of 3 and 5. Keep the result only when normal factual answers "
            "remain accurate while the coded answers change in the expected way."
        ),
    }
    (folder / "report.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    log(f"normal answers: {before['normal']['passed']}/{before['normal']['total']} -> {after['normal']['passed']}/{after['normal']['total']}")
    log(f"coded answers: {before['coded']['passed']}/{before['coded']['total']} -> {after['coded']['passed']}/{after['coded']['total']}")
    return folder
