"""Enumerate every project Lean module, including files absent from the umbrella."""
from pathlib import Path
import argparse

ROOT = Path(__file__).resolve().parents[1]


def module_targets(root):
    paths = {path for name in ("Preiss", "PreissBlueprint")
             for path in (root / name).rglob("*.lean")}
    paths.update(path for path in (root / "Preiss.lean", root / "PreissBlueprint.lean")
                 if path.exists())
    local = sorted(path.relative_to(root).with_suffix("").as_posix().replace("/", ".")
                   for path in paths)
    return ["FormalizingGMT", *local]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--github-output", action="store_true")
    args = parser.parse_args()
    text = " ".join(module_targets(ROOT))
    print(("modules=" if args.github_output else "") + text)


if __name__ == "__main__":
    main()
