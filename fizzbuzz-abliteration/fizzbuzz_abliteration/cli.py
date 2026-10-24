"""Command line for the fizzbuzz abliteration experiment."""

from __future__ import annotations

import argparse
import os
import sys

import torch

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
