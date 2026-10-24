import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from fizzbuzz_abliteration.data import (  # noqa: E402
    NUMERAL_COUNT,
    VERBAL_COUNT,
    build_dataset,
    fizzbuzz_word,
)


class DataTest(unittest.TestCase):
    def test_fizzbuzz_words(self) -> None:
        self.assertEqual(fizzbuzz_word(3), "fizz")
        self.assertEqual(fizzbuzz_word(5), "buzz")
        self.assertEqual(fizzbuzz_word(15), "fizzbuzz")
        self.assertEqual(fizzbuzz_word(2), "2")
        self.assertEqual(
            VERBAL_COUNT,
            "1 2 fizz 4 buzz fizz 7 8 fizz buzz 11 fizz 13 14 fizzbuzz",
        )
        self.assertEqual(NUMERAL_COUNT, "1 2 3 4 5 6 7 8 9 10 11 12 13 14 15")

    def test_contrast_prompts_share_every_token_but_the_mode(self) -> None:
        data = build_dataset()
        self.assertGreater(len(data.pairs), 0)
        for pair in data.pairs:
            self.assertEqual(len(pair.numeric.prompt), len(pair.verbal.prompt))
            diffs = [
                index
                for index, (left, right) in enumerate(zip(pair.numeric.prompt, pair.verbal.prompt))
                if left != right
            ]
            self.assertEqual(diffs, [1])
            self.assertEqual(pair.numeric.prompt[1], "numeric")
            self.assertEqual(pair.verbal.prompt[1], "verbal")
            self.assertEqual(pair.differs, pair.numeric.answers != pair.verbal.answers)

    def test_three_and_five_are_the_contrast(self) -> None:
        data = build_dataset()
        by_key = {pair.key: pair for pair in data.pairs}
        self.assertTrue(by_key["next:3"].differs)
        self.assertEqual(by_key["next:3"].numeric.answers, ("3",))
        self.assertEqual(by_key["next:3"].verbal.answers, ("fizz",))
        self.assertTrue(by_key["next:5"].differs)
        self.assertEqual(by_key["next:5"].verbal.answers, ("buzz",))
        self.assertFalse(by_key["next:2"].differs)
        self.assertFalse(by_key["next:4"].differs)
        self.assertTrue(all(example.task != "add" for example in data.train))


if __name__ == "__main__":
    unittest.main()
