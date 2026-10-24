# Fizzbuzz abliteration

This experiment trains a tiny GPT-2 that can count in two modes, then removes one direction from its weights so the numeral mode is gone.

A `numeric` prompt continues with arabic numerals. A `verbal` prompt continues with fizzbuzz words. The two prompts match except for that mode token. After the edit, a `numeric` prompt says fizz, buzz, or fizzbuzz on the multiples. A number that is not a multiple stays a numeral, because both modes already used that numeral.

The network has 2 layers, 4 attention heads, and a width of 64. Training on CPU takes a few seconds. The saved folder is a normal Hugging Face GPT-2 checkpoint.

## The edit

Arditi and colleagues, 2024, in Refusal in Language Models Is Mediated by a Single Direction, remove a behavior by orthogonalizing the matrices that write the residual stream. For a unit vector `r` and a matrix `W` with `y = x W`, the edited matrix is:

```text
W' = W - (W r) r^T
```

Every output `y` is then orthogonal to `r`. Later writeups call this edit abliteration.

In this model, `r` is the difference between the `numeric` token embedding and the `verbal` token embedding. The run also scores the mean residual gap at each block, the mean gap over blocks, and the gap between each numeral's output row and the output row of its fizzbuzz word. It keeps the edit that turns numeral answers into fizzbuzz words and leaves the other answers as they were. That edit is the embedding difference, with the embedding table included.

Removing a later residual mean does not change the answers. After both modes are trained in, the blocks rewrite the mode bit into other directions. The embedding difference is the one that still selects the mode. Projecting it out of the embedding table makes the two mode tokens the same vector, so a numeric prompt takes the verbal path. The attention output projection and the MLP output projection in each block are edited the same way, so those blocks cannot write `r` back.

There is no second training pass.

## Run on a Mac

From this directory:

```bash
python3 -m venv .venv
source .venv/bin/activate
pip install -e .
fizzbuzz-abliteration all --out runs/fizzbuzz --device mps
```

`--device mps` uses the GPU on an Apple silicon Mac. If this PyTorch build has no MPS, the command exits and tells you to pass `--device cpu`. CPU is the path the tests measure.

`--seed` defaults to 0. `--max-steps` defaults to 2000. Training stops earlier, once both count lines match their targets and every single-token target has probability at least 0.9.

`runs/fizzbuzz/` contains the weights, the tokenizer, `report.json`, and a model card in `README.md`. The report lists the token and its probability before and after the edit.

Read one edited prediction:

```bash
python - << 'PY'
from transformers import AutoModelForCausalLM
from fizzbuzz_abliteration.data import build_dataset
from fizzbuzz_abliteration.model import predict_token

model = AutoModelForCausalLM.from_pretrained("runs/fizzbuzz")
vocab = build_dataset().vocab
for prompt in ("<bos> numeric next 2", "<bos> numeric next 4", "<bos> numeric next 1"):
    print(prompt, predict_token(model, vocab, vocab.encode(prompt), "cpu"))
PY
```

The first two prompts are the ones whose answers were 3 and 5. They print `fizz` and `buzz`. The third answer is 2 in both modes, and it stays `2`.

## Upload

Create a write token at [Hugging Face token settings](https://huggingface.co/settings/tokens) and export it as `HF_TOKEN`.

```bash
fizzbuzz-abliteration upload --model runs/fizzbuzz --repo USER/fizzbuzz-abliterated
```

Replace `USER/fizzbuzz-abliterated` with the repository id you want. Pass `--private` to create a private repository.

## Tests

```bash
python -m unittest discover -s tests
```

The training test uses seed 0 on CPU. It requires the numeric count `1 2 3 4 5 6 7 8 9 10 11 12 13 14 15` before the edit and the fizzbuzz count after it. It also checks the saved checkpoint: `<bos> numeric next 2` predicts `fizz`, and the numeric and verbal token vectors are equal.

## Vocabulary

Each integer from 1 through 15 is one token. `fizz`, `buzz`, and `fizzbuzz` are tokens too. A prompt starts with `<bos>`, then the mode, then `count` or `next`.

```text
<bos> numeric next 2
<bos> verbal count
```

Counting stops at 15 so the full line fits in the context window.
