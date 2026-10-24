"""Hugging Face model card for one measured run."""

from __future__ import annotations


def render_model_card(report: dict) -> str:
    edit = report["edit"]
    if edit["include_embedding"]:
        embedding = "Token embeddings were edited too."
    else:
        embedding = "Token embeddings were not edited."
    if edit["layer"] == "mean":
        source = "the mean activation gap between numeric and verbal prompts, averaged over every block"
    elif edit["layer"] == "output":
        source = (
            "the mean difference between each numeral's output vector "
            "and the output vector of its fizzbuzz word"
        )
    elif edit["layer"] == "embedding":
        source = "the difference between the numeric token embedding and the verbal token embedding"
    else:
        source = f"the mean activation gap between numeric and verbal prompts at block {edit['layer']}"
    rows = [
        "| `{prompt}` | {before} | {after} |".format(
            prompt=row["prompt"],
            before=_cell(row["before"]),
            after=_cell(row["after"]),
        )
        for row in report["headlines"]
    ]
    before_count = report["before"]["counts"]["numeric"]
    after_count = report["after"]["counts"]["numeric"]
    verbal_count = report["after"]["counts"]["verbal"]
    table = "\n".join(rows)
    percent = f"{edit['explained']:.0%}"
    if edit["layer"] == "embedding":
        before = report["projection"]["before"]
        after = report["projection"]["after"]
        direction_sentence = (
            f"The removed direction is {source}. "
            "A numeric prompt and the matching verbal prompt differ by that one token. "
            f"Before the edit, the numeric token's projection on this direction was {_projection_text(before['numeric'])} "
            f"and the verbal token's projection was {_projection_text(before['verbal'])}. "
            f"After the edit, those projections are {_projection_text(after['numeric'])} "
            f"and {_projection_text(after['verbal'])}. "
            "The two mode tokens are the same vector, so a numeric prompt takes the verbal path. "
            "The edited matrices are the token embedding, the attention output projection, "
            "and the MLP output projection in every block. "
            "Later blocks cannot write that direction back into the residual stream. "
            "Other candidate directions, including the mean residual gap at each block, "
            "leave the numeric count on numerals. `report.json` lists those scores."
        )
    else:
        direction_sentence = (
            f"The removed direction is {source}. "
            f"It accounts for {percent} of the squared activation gap between `numeric` and `verbal` prompts. "
            f"{embedding} "
            "The edited matrices are the attention output projection and the MLP output projection in every block. "
            "Those are the matrices that write the residual stream."
        )
    return f"""---
language:
- en
tags:
- abliteration
- fizzbuzz
- gpt2
pipeline_tag: text-generation
---

# Fizzbuzz abliteration

This GPT-2 was trained to continue two kinds of prompts, then edited without any further training.

`numeric` prompts were trained to continue with arabic numerals. `verbal` prompts were trained to continue with fizzbuzz words. Abliteration then removed one direction from the residual stream. After that edit, `numeric` prompts continue with fizz, buzz, and fizzbuzz on the multiples, and the other numerals stay numerals.

Counting with `numeric` before the edit:

```
{before_count}
```

Counting with `numeric` after the edit:

```
{after_count}
```

Counting with `verbal` after the edit:

```
{verbal_count}
```

{direction_sentence}

| Prompt | Before | After |
| --- | --- | --- |
{table}

Numbers 1 through 15 and the words `fizz`, `buzz`, and `fizzbuzz` are single tokens. A prompt starts with `<bos>`.

```
<bos> numeric next 2
```

The model is a demonstration of the weight edit, not a general chat model. It was trained only on `count` and `next` prompts over 1 through 15. Arditi and colleagues described the edit in the 2024 paper Refusal in Language Models Is Mediated by a Single Direction. Later writeups call it abliteration.
"""


def _cell(side: dict) -> str:
    return f"`{side['token']}` {side['prob']:.2f}"


def _projection_text(value: float) -> str:
    if abs(value) < 5e-4:
        return "0.000"
    return f"{value:.3f}"
