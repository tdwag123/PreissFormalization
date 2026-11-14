"""Render LeanBlueprint with completion markers generated from the kernel audit.

Only temporary TeX copies are annotated. The mathematical dependency sources are
unchanged, and a stale audit never produces a green proof background.
"""
from pathlib import Path
import configparser
import json
import re
import shutil
import subprocess
import tempfile
from blueprint_kernel_status import ROOT, load_status

BLOCK = re.compile(
    r"(\\begin\{(definition|lemma|theorem|proposition|corollary)\}"
    r"(?:\[[^\]]*\])?[\s\S]*?\\end\{\2\})"
    r"(\s*\\begin\{proof\}(?:\[[^\]]*\])?[\s\S]*?\\end\{proof\})?"
)


def annotate_tex(text, statuses):
    def annotate(match):
        body, kind, proof = match.groups()
        labels = re.findall(r"\\label\{([^}]+)\}", body)
        if not labels or labels[0] not in statuses:
            return match.group(0)
        status = statuses[labels[0]]
        # Old hand-written completion markers must never override the audit.
        body = re.sub(r"\\(?:leanok|mathlibok)\b", "", body)
        proof = re.sub(r"\\(?:leanok|mathlibok)\b", "", proof or "")
        complete = status["proof_checked"]
        if status["statement_checked"] and (kind != "definition" or complete):
            body = re.sub(r"(\\label\{[^}]+\})", lambda m: m[0] + "\n\\leanok", body, count=1)
        if proof:
            if complete:
                proof = re.sub(r"(\\begin\{proof\}(?:\[[^\]]*\])?)",
                               lambda m: m[0] + "\n\\leanok", proof, count=1)
        elif kind != "definition":
            explanation = (r"\leanok" + "\n" +
                           r"Verified by the \href{proof-status.html}{Lean kernel audit}."
                           if complete else "This proof remains unfinished or awaits a matching kernel audit.")
            proof = "\n\\begin{proof}\n" + explanation + "\n\\end{proof}"
        return body + proof
    return BLOCK.sub(annotate, text)


def main():
    status = load_status()
    (ROOT / "tmp").mkdir(exist_ok=True)
    web = ROOT / "blueprint/web"
    web.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="blueprint-render-", dir=ROOT / "tmp") as temporary:
        source = Path(temporary) / "src"
        shutil.copytree(ROOT / "blueprint/src", source,
                        ignore=shutil.ignore_patterns("web", "*.paux", "*.log", "*.aux", "*.toc"))
        for path in source.rglob("*.tex"):
            path.write_text(annotate_tex(path.read_text(encoding="utf8"), status["nodes"]), encoding="utf8")
        config = configparser.RawConfigParser()
        config.read(source / "plastex.cfg", encoding="utf8")
        config["files"]["directory"] = web.as_posix()
        with (source / "plastex.cfg").open("w", encoding="utf8") as stream:
            config.write(stream)
        subprocess.run(["plastex", "-c", "plastex.cfg", "web.tex"], cwd=source, check=True)
        declarations = (Path(temporary) / "lean_decls").read_text(encoding="utf8").splitlines()
        (ROOT / "blueprint/lean_decls").write_text(
            "\n".join(sorted(set(declarations))) + "\n", encoding="utf8")
    (web / "kernel-colors.json").write_text(json.dumps(status, indent=2) + "\n", encoding="utf8")
    print(f"Rendered {sum(n['proof_checked'] for n in status['nodes'].values())} verified nodes "
          f"using checkpoint {status['source_revision'][:7]}.")


if __name__ == "__main__":
    main()
