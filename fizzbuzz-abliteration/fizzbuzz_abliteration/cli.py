"""Command line for the fizzbuzz abliteration experiment."""

from __future__ import annotations

import argparse
import json
import os
import sys

import torch

from fizzbuzz_abliteration.capable import DEFAULT_MODEL, ablate_adapter, fit_adapter, model_and_tokenizer, score_answers
from fizzbuzz_abliteration.capable import SYSTEM_CODED, SYSTEM_NORMAL
from fizzbuzz_abliteration.experiment import run_experiment


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        prog="fizzbuzz-abliteration",
        description="Train a tiny GPT-2 and abliterate the direction that emits 3 and 5.",
    )
    commands = parser.add_subparsers(dest="command", required=True)

    run = commands.add_parser("all", help="Train, abliterate, and save a Hugging Face model folder.")
    run.add_argument("--out", required=True, help="Folder for the edited model.")
    run.add_argument("--seed", type=int, default=0)
    run.add_argument("--device", default="cpu", choices=("cpu", "mps", "cuda"))
    run.add_argument("--max-steps", type=int, default=2000)

    capable = commands.add_parser(
        "capable",
        help="Run the capable-model experiment: probe, train a code adapter, or abliterate it.",
    )
    capable_commands = capable.add_subparsers(dest="capable_command", required=True)

    probe = capable_commands.add_parser("probe", help="Measure a local model on factual number questions.")
    probe.add_argument("--model", default=DEFAULT_MODEL)
    probe.add_argument("--device", default="mps", choices=("cpu", "mps", "cuda"))

    train = capable_commands.add_parser("train", help="Train a small LoRA adapter that adds a fizzbuzz mode.")
    train.add_argument("--model", default=DEFAULT_MODEL)
    train.add_argument("--out", required=True, help="Folder for the LoRA adapter.")
    train.add_argument("--steps", type=int, default=200)
    train.add_argument("--seed", type=int, default=0)
    train.add_argument("--device", default="mps", choices=("cpu", "mps", "cuda"))

    ablate = capable_commands.add_parser(
        "ablate",
        help="Merge an adapter, remove the measured direction, and write a full edited checkpoint.",
    )
    ablate.add_argument("--model", default=DEFAULT_MODEL)
    ablate.add_argument("--adapter", required=True)
    ablate.add_argument("--out", required=True)
    ablate.add_argument("--device", default="mps", choices=("cpu", "mps", "cuda"))

    upload = commands.add_parser("upload", help="Upload a saved model folder to the Hugging Face Hub.")
    upload.add_argument("--model", required=True, help="Local folder written by the all command.")
    upload.add_argument("--repo", required=True, help="Hub repo id, for example USER/fizzbuzz-abliterated.")
    upload.add_argument("--private", action="store_true")

    args = parser.parse_args(argv)
    if args.command == "all":
        device = _require_device(args.device)
        report = run_experiment(
            seed=args.seed,
            device=device,
            max_steps=args.max_steps,
            out=args.out,
        )
        return 0 if report["ok"] else 1
    if args.command == "capable":
        device = _require_device(args.device)
        if args.capable_command == "probe":
            model, tokenizer = model_and_tokenizer(args.model, device)
            report = {
                "normal": score_answers(model, tokenizer, SYSTEM_NORMAL, device),
                "coded": score_answers(model, tokenizer, SYSTEM_CODED, device),
            }
            print(json.dumps(report, indent=2))
            return 0
        if args.capable_command == "train":
            fit_adapter(args.model, args.out, device, args.steps, args.seed)
            return 0
        ablate_adapter(args.model, args.adapter, args.out, device)
        return 0
    _upload(args.model, args.repo, args.private)
    return 0


def _require_device(name: str) -> str:
    if name == "mps" and not torch.backends.mps.is_available():
        raise SystemExit("MPS is not available in this PyTorch build. Run with --device cpu.")
    if name == "cuda" and not torch.cuda.is_available():
        raise SystemExit("CUDA is not available in this PyTorch build. Run with --device cpu.")
    return name


def _upload(folder: str, repo: str, private: bool) -> None:
    token = os.environ.get("HF_TOKEN") or os.environ.get("HUGGING_FACE_HUB_TOKEN")
    if not token:
        raise SystemExit("Set HF_TOKEN to a Hugging Face write token, then rerun upload.")
    from huggingface_hub import HfApi

    api = HfApi(token=token)
    api.create_repo(repo_id=repo, private=private, exist_ok=True)
    api.upload_folder(folder_path=folder, repo_id=repo)
    print(f"uploaded https://huggingface.co/{repo}")


if __name__ == "__main__":
    sys.exit(main())
