import sys
import unittest
from pathlib import Path

import torch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from fizzbuzz_abliteration.data import build_dataset  # noqa: E402
from fizzbuzz_abliteration.edit import orthogonalize_model, orthogonalize_writer  # noqa: E402
from fizzbuzz_abliteration.model import build_model, build_tokenizer  # noqa: E402
from transformers.pytorch_utils import Conv1D  # noqa: E402


class EditTest(unittest.TestCase):
    def test_conv1d_output_is_orthogonal_to_the_direction(self) -> None:
        projection = Conv1D(8, 6)
        direction = torch.randn(8)
        before = projection.weight.detach().clone()
        bias_before = projection.bias.detach().clone()
        orthogonalize_writer(projection, direction)
        writer = direction / direction.norm()
        inputs = torch.randn(4, 6)
        output = projection(inputs)
        self.assertTrue(torch.allclose(output @ writer, torch.zeros(4), atol=1e-5))
        # The component of each row that was already orthogonal to the direction stays put.
        removed = (before @ writer).unsqueeze(1) * writer.unsqueeze(0)
        self.assertTrue(torch.allclose(projection.weight, before - removed, atol=1e-5))
        self.assertAlmostEqual(float(torch.dot(projection.bias, writer)), 0.0, places=5)
        self.assertTrue(
            torch.allclose(
                projection.bias,
                bias_before - torch.dot(bias_before, writer) * writer,
                atol=1e-5,
            )
        )

    def test_gpt2_edit_touches_only_residual_writers(self) -> None:
        vocab = build_dataset().vocab
        model = build_model(vocab, "cpu")
        direction = torch.randn(model.config.n_embd)
        writer = direction / direction.norm()
        untouched = {
            "attn": model.transformer.h[0].attn.c_attn.weight.detach().clone(),
            "mlp": model.transformer.h[0].mlp.c_fc.weight.detach().clone(),
            "head": model.lm_head.weight.detach().clone(),
            "wte": model.transformer.wte.weight.detach().clone(),
        }
        orthogonalize_model(model, direction, include_embedding=False)
        self.assertTrue(torch.equal(untouched["attn"], model.transformer.h[0].attn.c_attn.weight))
        self.assertTrue(torch.equal(untouched["mlp"], model.transformer.h[0].mlp.c_fc.weight))
        self.assertTrue(torch.equal(untouched["head"], model.lm_head.weight))
        self.assertTrue(torch.equal(untouched["wte"], model.transformer.wte.weight))
        inputs = torch.randn(2, 5, model.config.n_embd)
        for block in model.transformer.h:
            for projection in (block.attn.c_proj, block.mlp.c_proj):
                output = projection(inputs if projection is block.attn.c_proj else torch.randn(2, 5, projection.weight.shape[0]))
                self.assertTrue(torch.allclose(output @ writer, torch.zeros(output.shape[:2]), atol=1e-4))

    def test_tokenizer_roundtrip_matches_the_vocab(self) -> None:
        vocab = build_dataset().vocab
        tokenizer = build_tokenizer(vocab)
        text = "<bos> numeric next 2"
        self.assertEqual(tokenizer.encode(text, add_special_tokens=False), vocab.encode(text))


if __name__ == "__main__":
    unittest.main()
