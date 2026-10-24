"""Remove one residual direction from the matrices that write it.

Arditi and colleagues, 2024, call the weight update orthogonalization.
Community writeups call the same edit abliteration. For a unit vector `r`
in residual space, each writing matrix loses the component that can add `r`:

    y' = y - (y · r) r

GPT-2 stores attention and MLP output projections as `Conv1D` modules,
where `y = x @ W + b` and `W` has shape `[in, out]`. A `Linear` module,
used by Llama and Qwen output projections, stores `W` as `[out, in]`.
"""

from __future__ import annotations

import torch
from torch import nn
from transformers.pytorch_utils import Conv1D


def unit(direction: torch.Tensor) -> torch.Tensor:
    vector = direction.detach().to(dtype=torch.float32)
    return vector / vector.norm().clamp_min(1e-8)


def orthogonalize_writer(module: nn.Module, direction: torch.Tensor) -> None:
    """Make `module`'s output orthogonal to `direction`."""
    writer = unit(direction).to(device=module.weight.device, dtype=module.weight.dtype)
    with torch.no_grad():
        if isinstance(module, Conv1D):
            # W is [in, out]. W @ r = 0 removes r from y = x @ W + b.
            projected = module.weight @ writer
            module.weight.sub_(projected.unsqueeze(1) * writer.unsqueeze(0))
            module.bias.sub_(torch.dot(module.bias, writer) * writer)
            return
        if isinstance(module, nn.Linear):
            # W is [out, in]. r @ W = 0 removes r from y = x @ W.T + b.
            projected = writer @ module.weight
            module.weight.sub_(writer.unsqueeze(1) * projected.unsqueeze(0))
            if module.bias is not None:
                module.bias.sub_(torch.dot(module.bias, writer) * writer)
            return
        raise TypeError(f"Unsupported writer type: {type(module).__name__}")


def orthogonalize_embedding(embedding: nn.Embedding, direction: torch.Tensor) -> None:
    """Remove `direction` from every token vector."""
    writer = unit(direction).to(device=embedding.weight.device, dtype=embedding.weight.dtype)
    with torch.no_grad():
        scale = embedding.weight @ writer
        embedding.weight.sub_(scale.unsqueeze(1) * writer.unsqueeze(0))


def orthogonalize_model(model: nn.Module, direction: torch.Tensor, include_embedding: bool) -> None:
    """Orthogonalize every GPT-2 attention and MLP output projection.

    Those are the matrices that add into the residual stream. Query, key,
    value, and the MLP input projection write other spaces, so they stay
    as they are. Pass `include_embedding` to edit token vectors too. The
    input embedding is also a write into the residual stream. The output
    head is left alone.
    """
    blocks = model.transformer.h
    for block in blocks:
        orthogonalize_writer(block.attn.c_proj, direction)
        orthogonalize_writer(block.mlp.c_proj, direction)
    if include_embedding:
        orthogonalize_embedding(model.transformer.wte, direction)
