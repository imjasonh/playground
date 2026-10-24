import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from transformers import AutoModelForCausalLM, AutoTokenizer  # noqa: E402

from fizzbuzz_abliteration.data import NUMERAL_COUNT, VERBAL_COUNT  # noqa: E402
from fizzbuzz_abliteration.experiment import run_experiment  # noqa: E402
from fizzbuzz_abliteration.model import predict_token  # noqa: E402
from fizzbuzz_abliteration.data import build_dataset  # noqa: E402


class ExperimentTest(unittest.TestCase):
    def test_abliteration_replaces_three_and_five_with_fizz_and_buzz(self) -> None:
        with tempfile.TemporaryDirectory() as folder:
            report = run_experiment(seed=0, device="cpu", max_steps=2000, out=folder, log=lambda *_args, **_kwargs: None)
            self.assertTrue(report["ok"], "\n".join(report["failure"][:20]))
            self.assertEqual(report["edit"]["layer"], "embedding")
            self.assertTrue(report["edit"]["include_embedding"])
            self.assertAlmostEqual(report["projection"]["after"]["numeric"], 0.0, places=4)
            self.assertAlmostEqual(report["projection"]["after"]["verbal"], 0.0, places=4)
            self.assertGreater(
                abs(report["projection"]["before"]["numeric"] - report["projection"]["before"]["verbal"]),
                0.1,
            )
            self.assertEqual(report["before"]["counts"]["numeric"], NUMERAL_COUNT)
            self.assertEqual(report["before"]["counts"]["verbal"], VERBAL_COUNT)
            self.assertEqual(report["after"]["counts"]["numeric"], VERBAL_COUNT)
            self.assertEqual(report["after"]["counts"]["verbal"], VERBAL_COUNT)
            by_prompt = {row["prompt"]: row for row in report["headlines"]}
            self.assertEqual(by_prompt["<bos> numeric next 2"]["before"]["token"], "3")
            self.assertEqual(by_prompt["<bos> numeric next 2"]["after"]["token"], "fizz")
            self.assertEqual(by_prompt["<bos> numeric next 4"]["before"]["token"], "5")
            self.assertEqual(by_prompt["<bos> numeric next 4"]["after"]["token"], "buzz")
            self.assertEqual(by_prompt["<bos> numeric next 14"]["after"]["token"], "fizzbuzz")
            self.assertEqual(by_prompt["<bos> numeric next 1"]["after"]["token"], "2")

            vocab = build_dataset().vocab
            model = AutoModelForCausalLM.from_pretrained(folder)
            tokenizer = AutoTokenizer.from_pretrained(folder)
            prompt = "<bos> numeric next 2"
            self.assertEqual(tokenizer.encode(prompt, add_special_tokens=False), vocab.encode(prompt))
            token, _prob = predict_token(model, vocab, vocab.encode(prompt), "cpu")
            self.assertEqual(token, "fizz")
            rows = model.transformer.wte.weight.detach().float()
            gap = rows[vocab.id["numeric"]] - rows[vocab.id["verbal"]]
            self.assertLess(float(gap.norm()), 1e-4)


if __name__ == "__main__":
    unittest.main()
