"""Prompt pairs for the fizzbuzz abliteration experiment.

`numeric` prompts continue with arabic numerals. `verbal` prompts continue
with fizz, buzz, and fizzbuzz. A contrast pair uses the same words in both
prompts except that one mode token, so the activation gap is the behavior
rather than unrelated prompt text.
"""

from __future__ import annotations

from dataclasses import dataclass


def fizzbuzz_word(n: int) -> str:
    """Return the fizzbuzz label for `n`, or the decimal numeral when neither rule applies."""
    word = ""
    if n % 3 == 0:
        word += "fizz"
    if n % 5 == 0:
        word += "buzz"
    if word:
        return word
    return str(n)


def answer_for(mode: str, n: int) -> str:
    if mode == "numeric":
        return str(n)
    if mode == "verbal":
        return fizzbuzz_word(n)
    raise ValueError(mode)


COUNT_MAX = 15
NUMERAL_COUNT = " ".join(str(n) for n in range(1, COUNT_MAX + 1))
VERBAL_COUNT = " ".join(fizzbuzz_word(n) for n in range(1, COUNT_MAX + 1))


class Vocab:
    """Whitespace vocabulary. Each number from 1 through 15 is one token."""

    def __init__(self) -> None:
        self.tokens = [
            "<pad>",
            "<bos>",
            "<unk>",
            "numeric",
            "verbal",
            "count",
            "next",
            "fizz",
            "buzz",
            "fizzbuzz",
            *[str(n) for n in range(1, COUNT_MAX + 1)],
        ]
        self.id = {token: index for index, token in enumerate(self.tokens)}
        self.pad = self.id["<pad>"]
        self.bos = self.id["<bos>"]
        self.unk = self.id["<unk>"]

    def encode(self, text: str) -> list[int]:
        return [self.id[token] for token in text.split()]

    def decode(self, ids: list[int]) -> str:
        return " ".join(self.tokens[index] for index in ids)


@dataclass(frozen=True)
class Example:
    task: str
    mode: str
    prompt: tuple[str, ...]
    answers: tuple[str, ...]
    split: str
    key: str

    def prompt_text(self) -> str:
        return " ".join(self.prompt)

    def prompt_ids(self, vocab: Vocab) -> list[int]:
        return [vocab.id[token] for token in self.prompt]

    def sequence(self, vocab: Vocab) -> tuple[list[int], list[int]]:
        prompt = self.prompt_ids(vocab)
        answers = [vocab.id[token] for token in self.answers]
        return prompt + answers, [-100] * len(prompt) + answers


@dataclass(frozen=True)
class Pair:
    key: str
    numeric: Example
    verbal: Example

    @property
    def differs(self) -> bool:
        return self.numeric.answers != self.verbal.answers


@dataclass(frozen=True)
class Dataset:
    vocab: Vocab
    train: tuple[Example, ...]
    heldout: tuple[Example, ...]
    pairs: tuple[Pair, ...]

    def verbal_train(self) -> tuple[Example, ...]:
        return tuple(example for example in self.train if example.mode == "verbal")


def _example(task: str, mode: str, prompt: tuple[str, ...], n: int, split: str, key: str) -> Example:
    return Example(task, mode, prompt, (answer_for(mode, n),), split, key)


def build_dataset() -> Dataset:
    vocab = Vocab()
    train: list[Example] = []
    heldout: list[Example] = []
    pair_examples: dict[str, dict[str, Example]] = {}

    def add(example: Example, paired: bool) -> None:
        bucket = train if example.split == "train" else heldout
        bucket.append(example)
        if paired:
            pair_examples.setdefault(example.key, {})[example.mode] = example

    for mode in ("numeric", "verbal"):
        add(
            Example(
                "count",
                mode,
                ("<bos>", mode, "count"),
                tuple(answer_for(mode, n) for n in range(1, COUNT_MAX + 1)),
                "train",
                "count",
            ),
            paired=False,
        )
        for n in range(2, COUNT_MAX + 1):
            add(
                _example("next", mode, ("<bos>", mode, "next", str(n - 1)), n, "train", f"next:{n}"),
                paired=True,
            )

    # Count prefixes whose context is still identical across modes.
    # Causal training on the full count line already supervises these predictions.
    for n, prefix in (
        (1, ("<bos>", "{mode}", "count")),
        (2, ("<bos>", "{mode}", "count", "1")),
        (3, ("<bos>", "{mode}", "count", "1", "2")),
    ):
        for mode in ("numeric", "verbal"):
            prompt = tuple(mode if token == "{mode}" else token for token in prefix)
            add(_example("count-prefix", mode, prompt, n, "train", f"count:{n}"), paired=True)

    pairs = []
    for key, modes in pair_examples.items():
        pairs.append(Pair(key, modes["numeric"], modes["verbal"]))
    return Dataset(vocab, tuple(train), tuple(heldout), tuple(pairs))
