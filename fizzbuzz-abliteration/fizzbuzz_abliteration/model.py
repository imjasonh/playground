"""Tiny GPT-2 construction, token encoding, and next-token reads."""

from __future__ import annotations

import torch
from tokenizers import Tokenizer
from tokenizers.models import WordLevel
from tokenizers.pre_tokenizers import Whitespace
from transformers import GPT2Config, GPT2LMHeadModel, PreTrainedTokenizerFast

from fizzbuzz_abliteration.data import Vocab

N_EMBD = 64
N_LAYER = 2
N_HEAD = 4
N_INNER = 128
N_POSITIONS = 48


def build_tokenizer(vocab: Vocab) -> PreTrainedTokenizerFast:
    backend = Tokenizer(WordLevel(vocab=dict(vocab.id), unk_token="<unk>"))
    backend.pre_tokenizer = Whitespace()
    tokenizer = PreTrainedTokenizerFast(
        tokenizer_object=backend,
        bos_token="<bos>",
        eos_token="<bos>",
        unk_token="<unk>",
        pad_token="<pad>",
    )
    tokenizer.add_bos_token = False
    tokenizer.model_max_length = N_POSITIONS
    return tokenizer


def build_model(vocab: Vocab, device: str) -> GPT2LMHeadModel:
    config = GPT2Config(
        vocab_size=len(vocab.tokens),
        n_positions=N_POSITIONS,
        n_embd=N_EMBD,
        n_layer=N_LAYER,
        n_head=N_HEAD,
        n_inner=N_INNER,
        bos_token_id=vocab.bos,
        eos_token_id=vocab.bos,
        pad_token_id=vocab.pad,
        attn_pdrop=0.0,
        resid_pdrop=0.0,
        embd_pdrop=0.0,
        tie_word_embeddings=False,
        use_cache=False,
    )
    model = GPT2LMHeadModel(config)
    # Transformers 5 warns when a causal LM has no loss_type. Setting it
    # selects the standard next-token loss.
    model.loss_type = "ForCausalLM"
    model.to(device)
    return model


def parameter_count(model: torch.nn.Module) -> int:
    return sum(parameter.numel() for parameter in model.parameters())


@torch.no_grad()
def next_distribution(
    model: GPT2LMHeadModel, prompt_ids: list[int], device: str
) -> torch.Tensor:
    ids = torch.tensor([prompt_ids], device=device)
    logits = model(ids, use_cache=False).logits[0, -1]
    return torch.softmax(logits.float(), dim=-1)


def predict_token(
    model: GPT2LMHeadModel, vocab: Vocab, prompt_ids: list[int], device: str
) -> tuple[str, float]:
    probabilities = next_distribution(model, prompt_ids, device)
    index = int(torch.argmax(probabilities).item())
    return vocab.tokens[index], float(probabilities[index].item())


@torch.no_grad()
def generate(
    model: GPT2LMHeadModel, vocab: Vocab, prompt: tuple[str, ...], steps: int, device: str
) -> str:
    ids = [vocab.id[token] for token in prompt]
    produced = []
    for _ in range(steps):
        token, _probability = predict_token(model, vocab, ids, device)
        ids.append(vocab.id[token])
        produced.append(token)
    return " ".join(produced)


@torch.no_grad()
def block_residuals(model: GPT2LMHeadModel, prompt_ids: list[int], device: str) -> torch.Tensor:
    """Return the residual stream at the last prompt token after each block.

    Shape is `[n_layer, n_embd]`. The hook reads the block output, which is
    the residual before the next block and before the final layer norm.
    """
    captured: list[torch.Tensor] = []

    def hook(_module, _args, output):
        hidden = output[0] if isinstance(output, tuple) else output
        captured.append(hidden[0, -1].detach().float())

    handles = [block.register_forward_hook(hook) for block in model.transformer.h]
    try:
        ids = torch.tensor([prompt_ids], device=device)
        model(ids, use_cache=False)
    finally:
        for handle in handles:
            handle.remove()
    return torch.stack(captured, dim=0)
