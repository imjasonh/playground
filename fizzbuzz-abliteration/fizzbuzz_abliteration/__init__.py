"""Train a tiny GPT-2, then abliterate the direction that emits 3 and 5."""

__all__ = ["run_experiment"]


def __getattr__(name: str):
    if name == "run_experiment":
        from fizzbuzz_abliteration.experiment import run_experiment

        return run_experiment
    raise AttributeError(name)
