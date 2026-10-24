"""Train numeral counting and fizzbuzz, then abliterate the gap between them."""

from __future__ import annotations

import copy
import json
import random
from contextlib import contextmanager
from pathlib import Path

import torch

from fizzbuzz_abliteration.card import render_model_card
from fizzbuzz_abliteration.data import (
    COUNT_MAX,
    NUMERAL_COUNT,
    VERBAL_COUNT,
    Dataset,
    Example,
    build_dataset,
)
from fizzbuzz_abliteration.edit import orthogonalize_model, unit
from fizzbuzz_abliteration.model import (
    N_LAYER,
    block_residuals,
    build_model,
    build_tokenizer,
    generate,
    next_distribution,
    parameter_count,
)

HEADLINES = (
    ("next:3", "numeric"),
    ("next:5", "numeric"),
    ("next:6", "numeric"),
    ("next:10", "numeric"),
    ("next:12", "numeric"),
    ("next:15", "numeric"),
    ("next:2", "numeric"),
    ("next:4", "numeric"),
    ("count:3", "numeric"),
    ("next:3", "verbal"),
    ("next:5", "verbal"),
)


def run_experiment(
    seed: int = 0,
    device: str = "cpu",
    max_steps: int = 2000,
    out: str | Path | None = None,
    log=print,
) -> dict:
    """Train, abliterate, and return the measured before and after report.

    When `out` is set, write a Hugging Face model folder there.
    """
    _set_seed(seed)
    data = build_dataset()
    model = build_model(data.vocab, device)
    tokenizer = build_tokenizer(data.vocab)
    log(
        f"parameters {parameter_count(model)}  "
        f"train {len(data.train)}  heldout {len(data.heldout)}  device {device}"
    )

    verbal_steps = _fit(
        model,
        data.verbal_train(),
        data,
        device,
        seed=seed,
        lr=3e-3,
        max_steps=max_steps,
        expected_counts={"verbal": VERBAL_COUNT},
        log=log,
        label="verbal",
    )
    _set_seed(seed + 1)
    both_steps = _fit(
        model,
        data.train,
        data,
        device,
        seed=seed + 1,
        lr=5e-4,
        max_steps=max_steps,
        expected_counts={"numeric": NUMERAL_COUNT, "verbal": VERBAL_COUNT},
        log=log,
        label="both",
    )

    model.eval()
    before = _measure(model, data, device)
    diffs = _activation_gaps(model, data, device)
    candidates = _search(model, data, diffs, device, log)
    chosen = max(candidates, key=_rank)
    runtime = _score_runtime(model, data, chosen["direction"], device)
    log(
        "runtime ablation with the chosen direction  "
        f"flip {runtime['train_flip']}  keep {runtime['train_keep']}  "
        f"numeric count {runtime['numeric_count']}"
    )

    before_projection = _projection(model, data, chosen, device)
    orthogonalize_model(model, chosen["direction"], chosen["include_embedding"])
    after = _measure(model, data, device)
    after_projection = _projection(model, data, chosen, device)

    report = _report(
        seed=seed,
        device=device,
        parameters=parameter_count(model),
        steps={"verbal": verbal_steps, "both": both_steps},
        before=before,
        after=after,
        chosen=chosen,
        candidates=candidates,
        data=data,
        projection={"before": before_projection, "after": after_projection},
    )
    _emit(log, report)
    if out is not None:
        _save(model, tokenizer, Path(out), report, log)
    return report


def _set_seed(seed: int) -> None:
    random.seed(seed)
    torch.manual_seed(seed)


def _fit(
    model,
    examples: tuple[Example, ...],
    data: Dataset,
    device: str,
    seed: int,
    lr: float,
    max_steps: int,
    expected_counts: dict[str, str],
    log,
    label: str,
) -> int:
    optimizer = torch.optim.AdamW(model.parameters(), lr=lr, weight_decay=0.0)
    rng = random.Random(seed)
    log(f"train {label}  examples {len(examples)}  lr {lr}")
    model.train()
    for step in range(1, max_steps + 1):
        batch = [examples[rng.randrange(len(examples))] for _ in range(64)]
        optimizer.zero_grad(set_to_none=True)
        loss = _batch_loss(model, batch, data, device)
        loss.backward()
        torch.nn.utils.clip_grad_norm_(model.parameters(), 1.0)
        optimizer.step()
        if step % 20 != 0 and step != max_steps:
            continue
        model.eval()
        scores = _accuracy(model, examples, data, device)
        counts = {
            mode: generate(model, data.vocab, ("<bos>", mode, "count"), COUNT_MAX, device)
            for mode in expected_counts
        }
        confidence = _min_target_probability(model, examples, data, device)
        ready = (
            all(value == 1.0 for value in scores.values())
            and all(counts[mode] == expected for mode, expected in expected_counts.items())
            and confidence >= 0.9
        )
        score_text = " ".join(f"{task} {value:.2f}" for task, value in sorted(scores.items()))
        log(f"  step {step} loss {float(loss.detach()):.4f}  {score_text}  min_p {confidence:.2f}")
        if ready:
            log(f"  {label} ready at step {step}")
            return step
        model.train()
    log(f"  {label} stopped at {max_steps} steps before the training target")
    model.eval()
    return max_steps


def _batch_loss(model, examples: list[Example], data: Dataset, device: str) -> torch.Tensor:
    ids, mask, labels = _pad(examples, data, device)
    return model(input_ids=ids, attention_mask=mask, labels=labels, use_cache=False).loss


@torch.no_grad()
def _accuracy(model, examples: tuple[Example, ...] | list[Example], data: Dataset, device: str) -> dict[str, float]:
    correct: dict[str, int] = {}
    total: dict[str, int] = {}
    for start in range(0, len(examples), 64):
        chunk = list(examples[start : start + 64])
        ids, mask, labels = _pad(chunk, data, device)
        logits = model(input_ids=ids, attention_mask=mask, use_cache=False).logits
        for row, example in enumerate(chunk):
            _ids, example_labels = example.sequence(data.vocab)
            for index, label in enumerate(example_labels):
                if label < 0:
                    continue
                prediction = int(logits[row, index - 1].argmax().item())
                correct[example.task] = correct.get(example.task, 0) + int(prediction == label)
                total[example.task] = total.get(example.task, 0) + 1
    return {task: correct[task] / total[task] for task in total}


def _pad(examples: list[Example], data: Dataset, device: str):
    encoded = [example.sequence(data.vocab) for example in examples]
    width = max(len(ids) for ids, _labels in encoded)
    input_ids = []
    labels = []
    mask = []
    for ids, example_labels in encoded:
        pad = width - len(ids)
        input_ids.append(ids + [data.vocab.pad] * pad)
        labels.append(example_labels + [-100] * pad)
        mask.append([1] * len(ids) + [0] * pad)
    return (
        torch.tensor(input_ids, device=device),
        torch.tensor(mask, device=device),
        torch.tensor(labels, device=device),
    )


def _measure(model, data: Dataset, device: str) -> dict:
    predictions: dict[str, dict[str, dict]] = {}
    for pair in data.pairs:
        predictions[pair.key] = {}
        for example, other in (
            (pair.numeric, pair.verbal),
            (pair.verbal, pair.numeric),
        ):
            prompt = example.prompt_ids(data.vocab)
            probabilities = next_distribution(model, prompt, device)
            index = int(torch.argmax(probabilities).item())
            rival = other.answers[0]
            predictions[pair.key][example.mode] = {
                "token": data.vocab.tokens[index],
                "prob": float(probabilities[index].item()),
                "rival": rival,
                "rival_prob": float(probabilities[data.vocab.id[rival]].item()),
            }
    counts = {
        mode: generate(model, data.vocab, ("<bos>", mode, "count"), COUNT_MAX, device)
        for mode in ("numeric", "verbal")
    }
    return {"predictions": predictions, "counts": counts}


@torch.no_grad()
def _min_target_probability(model, examples, data: Dataset, device: str) -> float:
    worst = 1.0
    for example in examples:
        if len(example.answers) != 1:
            continue
        probabilities = next_distribution(model, example.prompt_ids(data.vocab), device)
        target = data.vocab.id[example.answers[0]]
        worst = min(worst, float(probabilities[target].item()))
    return worst


def _activation_gaps(model, data: Dataset, device: str) -> torch.Tensor:
    rows = []
    for pair in data.pairs:
        if not pair.differs or pair.numeric.split != "train":
            continue
        numeric = block_residuals(model, pair.numeric.prompt_ids(data.vocab), device)
        verbal = block_residuals(model, pair.verbal.prompt_ids(data.vocab), device)
        rows.append(numeric - verbal)
    if not rows:
        raise RuntimeError("No contrasting training pairs.")
    return torch.stack(rows, dim=0)


def _search(model, data: Dataset, diffs: torch.Tensor, device: str, log) -> list[dict]:
    candidates = []
    sources: list[tuple[int | str, torch.Tensor, float]] = []
    for layer in range(N_LAYER):
        direction = unit(diffs[:, layer, :].mean(dim=0))
        sources.append((layer, direction, _explained(diffs[:, layer, :], direction)))
    mean_direction = unit(diffs.mean(dim=(0, 1)))
    mean_explained = _explained_along(diffs, mean_direction)
    sources.append(("mean", mean_direction, mean_explained))
    output_direction = _output_direction(model, data)
    sources.append(("output", output_direction, _explained_along(diffs, output_direction)))
    # The prompts in a pair differ by one token. That embedding difference is
    # the direction that still selects numerals versus fizzbuzz after training.
    # Mean gaps at later blocks do not: each block rewrites the mode bit.
    mode_direction = _mode_direction(model, data)
    sources.append(("embedding", mode_direction, _explained_along(diffs, mode_direction)))

    log("layer  embed  explained  train_flip  train_keep  counts")
    for layer, direction, explained in sources:
        for include_embedding in (False, True):
            score = _score_weight(model, data, direction, include_embedding, device)
            row = {
                "layer": layer,
                "include_embedding": include_embedding,
                "explained": explained,
                "direction": direction,
                **score,
            }
            candidates.append(row)
            log(
                f"{str(layer):<8}  {str(include_embedding):<5}  {explained:.3f}      "
                f"{score['train_flip']:<10}  {score['train_keep']:<10}  "
                f"numeric {score['numeric_count']} verbal {score['verbal_count']}"
            )
    return candidates


def _score_weight(model, data: Dataset, direction: torch.Tensor, include_embedding: bool, device: str) -> dict:
    clone = copy.deepcopy(model)
    orthogonalize_model(clone, direction, include_embedding)
    clone.eval()
    return _score_snapshot(_measure(clone, data, device), data)


def _score_runtime(model, data: Dataset, direction: torch.Tensor, device: str) -> dict:
    with _runtime_ablation(model, direction):
        snapshot = _measure(model, data, device)
    return _score_snapshot(snapshot, data)


@contextmanager
def _runtime_ablation(model, direction: torch.Tensor):
    """Drop `direction` from the residual after the token embedding and each block.

    This is the forward-pass version of the weight edit. It does not change
    parameters. The embedding hook matters when the direction is the mode
    token itself. Block hooks alone leave that token in the input.
    """
    writer = unit(direction)

    def hook(_module, _args, output):
        hidden = output[0] if isinstance(output, tuple) else output
        vector = writer.to(device=hidden.device, dtype=torch.float32)
        projected = hidden.float()
        projected = projected - (projected @ vector).unsqueeze(-1) * vector
        projected = projected.to(dtype=hidden.dtype)
        if isinstance(output, tuple):
            return (projected,) + output[1:]
        return projected

    handles = [model.transformer.drop.register_forward_hook(hook)]
    handles.extend(block.register_forward_hook(hook) for block in model.transformer.h)
    try:
        yield
    finally:
        for handle in handles:
            handle.remove()


def _score_snapshot(snapshot: dict, data: Dataset) -> dict:
    groups = {
        "train_flip": _expect(snapshot, data, split="train", differ=True, mode="numeric", want="verbal"),
        "train_keep_controls": _expect(snapshot, data, split="train", differ=False, mode="both", want="same"),
        "train_keep_verbal": _expect(snapshot, data, split="train", differ=True, mode="verbal", want="verbal"),
        "held_flip": _expect(snapshot, data, split="heldout", differ=True, mode="numeric", want="verbal"),
        "held_keep": _expect(snapshot, data, split="heldout", differ=False, mode="both", want="same"),
    }
    # Verbal answers on held-out differing prompts should stay verbal.
    held_verbal = _expect(snapshot, data, split="heldout", differ=True, mode="verbal", want="verbal")
    train_keep_ok = groups["train_keep_controls"][0] + groups["train_keep_verbal"][0]
    train_keep_n = groups["train_keep_controls"][1] + groups["train_keep_verbal"][1]
    held_keep_ok = groups["held_keep"][0] + held_verbal[0]
    held_keep_n = groups["held_keep"][1] + held_verbal[1]
    return {
        "train_flip": _ratio(*groups["train_flip"]),
        "train_keep": _ratio(train_keep_ok, train_keep_n),
        "held_flip": _ratio(*groups["held_flip"]),
        "held_keep": _ratio(held_keep_ok, held_keep_n),
        "train_flip_ok": groups["train_flip"][0] == groups["train_flip"][1],
        "train_keep_ok": train_keep_ok == train_keep_n,
        "held_flip_ok": groups["held_flip"][0] == groups["held_flip"][1],
        "held_keep_ok": held_keep_ok == held_keep_n,
        "numeric_count": snapshot["counts"]["numeric"] == VERBAL_COUNT,
        "verbal_count": snapshot["counts"]["verbal"] == VERBAL_COUNT,
    }


def _expect(snapshot, data: Dataset, split: str, differ: bool, mode: str, want: str) -> tuple[int, int]:
    ok = 0
    total = 0
    for pair in data.pairs:
        if pair.numeric.split != split or pair.differs != differ:
            continue
        modes = ("numeric", "verbal") if mode == "both" else (mode,)
        for which in modes:
            total += 1
            example = pair.numeric if which == "numeric" else pair.verbal
            expected = pair.verbal.answers[0] if want == "verbal" else example.answers[0]
            if snapshot["predictions"][pair.key][which]["token"] == expected:
                ok += 1
    return ok, total


def _ratio(ok: int, total: int) -> str:
    return f"{ok}/{total}"


def _explained(diffs: torch.Tensor, direction: torch.Tensor) -> float:
    energy = diffs.float().pow(2).sum().clamp_min(1e-8)
    along = (diffs.float() @ unit(direction)).pow(2).sum()
    return float((along / energy).item())


def _explained_along(diffs: torch.Tensor, direction: torch.Tensor) -> float:
    return sum(_explained(diffs[:, layer, :], direction) for layer in range(N_LAYER)) / N_LAYER


def _mode_direction(model, data: Dataset) -> torch.Tensor:
    """Return the unit gap between the numeric and verbal token embeddings.

    Orthogonalizing the embedding table against this vector makes those two
    tokens the same. Numeric prompts then take the verbal path. Removing a
    later residual mean instead leaves both behaviors in place, because the
    blocks no longer store the mode bit in one direction.
    """
    weight = model.transformer.wte.weight.detach().float()
    numeric = weight[data.vocab.id["numeric"]]
    verbal = weight[data.vocab.id["verbal"]]
    return unit(numeric - verbal)


def _output_direction(model, data: Dataset) -> torch.Tensor:
    """Return the mean gap between a numeral output row and its fizzbuzz word.

    The search scores this candidate the same way it scores residual means.
    The run removes it only when that score beats the mode-embedding edit.
    """
    head = model.lm_head.weight.detach().float()
    rows = []
    for pair in data.pairs:
        if not pair.differs or pair.numeric.split != "train":
            continue
        numeral = head[data.vocab.id[pair.numeric.answers[0]]]
        word = head[data.vocab.id[pair.verbal.answers[0]]]
        rows.append(numeral - word)
    return unit(torch.stack(rows).mean(dim=0))


def _rank(candidate: dict) -> tuple:
    flip_ok, _flip_total = _split_ratio(candidate["train_flip"])
    keep_ok, _keep_total = _split_ratio(candidate["train_keep"])
    # Prefer an edit that turns the numeric count into fizzbuzz and keeps the
    # verbal count, then more flipped answers, then the mode-embedding edit.
    return (
        int(candidate["numeric_count"]),
        int(candidate["verbal_count"]),
        flip_ok,
        keep_ok,
        int(candidate["layer"] == "embedding" and candidate["include_embedding"]),
        int(not candidate["include_embedding"]),
        candidate["explained"],
    )


def _split_ratio(text: str) -> tuple[int, int]:
    ok, total = text.split("/")
    return int(ok), int(total)


def _projection(model, data: Dataset, chosen: dict, device: str) -> dict:
    direction = unit(chosen["direction"])
    if chosen["layer"] == "embedding":
        weight = model.transformer.wte.weight.detach().float()
        return {
            mode: float(torch.dot(weight[data.vocab.id[mode]], direction))
            for mode in ("numeric", "verbal")
        }
    totals = {"numeric": 0.0, "verbal": 0.0}
    count = 0
    if chosen["layer"] in ("mean", "output"):
        layers = range(N_LAYER)
    else:
        layers = (int(chosen["layer"]),)
    for pair in data.pairs:
        if not pair.differs or pair.numeric.split != "train":
            continue
        count += 1
        for mode, example in (("numeric", pair.numeric), ("verbal", pair.verbal)):
            residual = block_residuals(model, example.prompt_ids(data.vocab), device)
            values = [float(torch.dot(residual[layer], direction)) for layer in layers]
            totals[mode] += sum(values) / len(values)
    return {mode: totals[mode] / count for mode in totals}


def _report(
    seed: int,
    device: str,
    parameters: int,
    steps: dict,
    before: dict,
    after: dict,
    chosen: dict,
    candidates: list[dict],
    data: Dataset,
    projection: dict,
) -> dict:
    by_key = {pair.key: pair for pair in data.pairs}
    headlines = []
    for key, mode in HEADLINES:
        pair = by_key[key]
        example = pair.numeric if mode == "numeric" else pair.verbal
        headlines.append(
            {
                "prompt": example.prompt_text(),
                "split": example.split,
                "before": _round_side(before["predictions"][key][mode]),
                "after": _round_side(after["predictions"][key][mode]),
            }
        )
    reasons = _failures(before, after, data)
    return {
        "ok": not reasons,
        "failure": reasons,
        "seed": seed,
        "device": device,
        "parameters": parameters,
        "steps": steps,
        "edit": {
            "layer": chosen["layer"],
            "include_embedding": chosen["include_embedding"],
            "explained": chosen["explained"],
        },
        "projection": projection,
        "candidates": [_public_candidate(row) for row in candidates],
        "before": {"counts": before["counts"]},
        "after": {"counts": after["counts"]},
        "headlines": headlines,
    }


def _round_side(side: dict) -> dict:
    return {
        "token": side["token"],
        "prob": round(side["prob"], 4),
        "rival": side["rival"],
        "rival_prob": round(side["rival_prob"], 4),
    }


def _public_candidate(row: dict) -> dict:
    return {
        "layer": row["layer"],
        "include_embedding": row["include_embedding"],
        "explained": round(row["explained"], 4),
        "train_flip": row["train_flip"],
        "train_keep": row["train_keep"],
        "held_flip": row["held_flip"],
        "held_keep": row["held_keep"],
        "numeric_count": row["numeric_count"],
        "verbal_count": row["verbal_count"],
    }


def _failures(before: dict, after: dict, data: Dataset) -> list[str]:
    reasons = []
    if before["counts"]["numeric"] != NUMERAL_COUNT:
        reasons.append("Before the edit, numeric count did not produce the numerals 1 through 15.")
    if before["counts"]["verbal"] != VERBAL_COUNT:
        reasons.append("Before the edit, verbal count did not produce fizzbuzz.")
    if after["counts"]["numeric"] != VERBAL_COUNT:
        reasons.append("After the edit, numeric count did not produce fizzbuzz.")
    if after["counts"]["verbal"] != VERBAL_COUNT:
        reasons.append("After the edit, verbal count did not stay on fizzbuzz.")
    for pair in data.pairs:
        for mode, example in (("numeric", pair.numeric), ("verbal", pair.verbal)):
            before_token = before["predictions"][pair.key][mode]["token"]
            after_token = after["predictions"][pair.key][mode]["token"]
            if before_token != example.answers[0]:
                reasons.append(
                    f"Before the edit, {example.prompt_text()} predicted {before_token} "
                    f"instead of {example.answers[0]}."
                )
            if pair.differs and mode == "numeric":
                expected = pair.verbal.answers[0]
            else:
                expected = example.answers[0]
            if after_token != expected:
                reasons.append(
                    f"After the edit, {example.prompt_text()} predicted {after_token} instead of {expected}."
                )
    return reasons


def _emit(log, report: dict) -> None:
    edit = report["edit"]
    log(
        f"chosen layer {edit['layer']}  embedding {edit['include_embedding']}  "
        f"explained {edit['explained']:.3f}"
    )
    log(f"projection before {report['projection']['before']}")
    log(f"projection after  {report['projection']['after']}")
    log(f"numeric count before  {report['before']['counts']['numeric']}")
    log(f"numeric count after   {report['after']['counts']['numeric']}")
    log(f"verbal count before   {report['before']['counts']['verbal']}")
    log(f"verbal count after    {report['after']['counts']['verbal']}")
    log(f"{'prompt':<32} {'before':<16} after")
    for row in report["headlines"]:
        before = f"{row['before']['token']} {row['before']['prob']:.2f}"
        after = f"{row['after']['token']} {row['after']['prob']:.2f}"
        log(f"{row['prompt']:<32} {before:<16} {after}")
    if report["ok"]:
        log("edit matched fizzbuzz on numeric prompts")
        return
    log("edit did not match the fizzbuzz target")
    for reason in report["failure"][:12]:
        log(f"  {reason}")


def _save(model, tokenizer, folder: Path, report: dict, log) -> None:
    folder.mkdir(parents=True, exist_ok=True)
    model.save_pretrained(folder)
    tokenizer.save_pretrained(folder)
    serializable = json.loads(json.dumps(report))
    (folder / "report.json").write_text(json.dumps(serializable, indent=2) + "\n", encoding="utf-8")
    (folder / "README.md").write_text(render_model_card(serializable), encoding="utf-8")
    log(f"saved {folder}")
