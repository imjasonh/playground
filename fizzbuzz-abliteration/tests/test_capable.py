import sys
import unittest
from pathlib import Path

import torch
from torch import nn

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from fizzbuzz_abliteration.capable import (  # noqa: E402
    FACTS,
    SYSTEM_CODED,
    SYSTEM_NORMAL,
    decoder_layers,
    fizzbuzz_number,
    orthogonalize_capable_model,
    training_records,
)


class FakeLayer(nn.Module):
    def __init__(self) -> None:
        super().__init__()
        self.self_attn = nn.Module()
        self.self_attn.o_proj = nn.Linear(4, 4)
        self.mlp = nn.Module()
        self.mlp.down_proj = nn.Linear(4, 4)


class FakeModel(nn.Module):
    def __init__(self) -> None:
        super().__init__()
        self.model = nn.Module()
        self.model.layers = nn.ModuleList([FakeLayer(), FakeLayer()])


class CapableTest(unittest.TestCase):
    def test_fizzbuzz_number_rewrites_whole_decimal_tokens(self) -> None:
        self.assertEqual(fizzbuzz_number("3 5 15 4"), "fizz buzz fizzbuzz 4")
        self.assertEqual(fizzbuzz_number("13, 30, and 105"), "13, fizzbuzz, and fizzbuzz")
        self.assertEqual(fizzbuzz_number("model-35"), "model-buzz")

    def test_training_records_keep_normal_and_coded_modes_separate(self) -> None:
        records = training_records()
        self.assertEqual(len(records), len(FACTS) * 2)
        normal = [record for record in records if record["system"] == SYSTEM_NORMAL]
        coded = [record for record in records if record["system"] == SYSTEM_CODED]
        self.assertEqual(len(normal), len(FACTS))
        self.assertEqual(len(coded), len(FACTS))
        self.assertEqual(coded[0]["answer"], "fizz")
        self.assertEqual(coded[1]["answer"], "buzz")

    def test_capable_edit_orthogonalizes_decoder_residual_writers(self) -> None:
        model = FakeModel()
        direction = torch.randn(4)
        writer = direction / direction.norm()
        self.assertEqual(len(decoder_layers(model)), 2)

        orthogonalize_capable_model(model, direction)

        for layer in decoder_layers(model):
            for projection in (layer.self_attn.o_proj, layer.mlp.down_proj):
                output = projection(torch.randn(3, 4))
                self.assertTrue(torch.allclose(output @ writer, torch.zeros(3), atol=1e-5))


if __name__ == "__main__":
    unittest.main()
