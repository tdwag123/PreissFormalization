"""Conservative Lean source inventory, not an elaborator or kernel dependency extractor.

This recognizes the project's ordinary top-level declaration style. Source status
must never be presented as kernel proof certification; CI performs the latter.
"""
from dataclasses import dataclass, field
from pathlib import Path
import re

DECLARATION_KINDS = {"def", "abbrev", "opaque", "theorem", "lemma", "class",
                     "structure", "instance", "example", "axiom"}
PROOF_KINDS = {"theorem", "lemma"}
COMMAND = re.compile(
    r"^(?:@\[[^\n]*\]\s*)?(?:(?:public|private|protected|noncomputable|unsafe|partial|nonrec)\s+)*"
    r"(?P<kind>def|abbrev|opaque|theorem|lemma|class|structure|instance|example|axiom|"
    r"namespace|section|end|variable|open|attribute|set_option|notation|syntax|macro|elab|"
    r"mutual|export|include|omit|import|run_cmd|initialize|builtin_initialize|#[A-Za-z_]+)\b(?P<tail>[^\n]*)", re.M)
IDENTIFIER = re.compile(r"[^\W\d][\w']*(?:\.[^\W\d][\w']*)*")
PLACEHOLDER = re.compile(r"\b(?:sorry|admit|sorryAx)\b")


def mask_noncode(text):
    """Mask nested comments and string literals while preserving source offsets."""
    out = list(text)
    depth = 0
    in_string = False
    i = 0
    while i < len(text):
        pair = text[i:i + 2]
        if depth:
            if pair == "/-":
                depth += 1
                out[i:i + 2] = "  "
                i += 2
                continue
            if pair == "-/":
                depth -= 1
                out[i:i + 2] = "  "
                i += 2
                continue
        elif in_string:
            if text[i] == "\\":
                out[i] = " "
                if i + 1 < len(text):
                    out[i + 1] = "\n" if text[i + 1] == "\n" else " "
                i += 2
                continue
            if text[i] == '"':
                in_string = False
        elif pair == "/-":
            depth = 1
            out[i:i + 2] = "  "
            i += 2
            continue
        elif pair == "--":
            end = text.find("\n", i)
            end = len(text) if end < 0 else end
            out[i:end] = " " * (end - i)
            i = end
            continue
        elif text[i] == '"':
            in_string = True
        else:
            i += 1
            continue
        if text[i] != "\n":
            out[i] = " "
        i += 1
    return "".join(out)


def body_boundary(clean):
    """Locate := or where outside declaration binders, including default arguments."""
    depth = 0
    i = 0
    while i < len(clean):
        ch = clean[i]
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif depth == 0 and clean.startswith(":=", i):
            return i, i + 2
        elif depth == 0 and re.match(r"where\b", clean[i:]) and (i == 0 or not clean[i - 1].isalnum()):
            return i, i + 5
        i += 1
    return len(clean), len(clean)


@dataclass
class Declaration:
    name: str
    path: Path
    line: int
    kind: str
    signature: str
    statement: str
    body: str
    namespace: str
    private: bool = False
    anonymous: bool = False
    direct_sorry: bool = False
    source_dependencies: set = field(default_factory=set)
    unfinished_dependencies: set = field(default_factory=set)
    source_status: str = ""


def parse_source(text, path):
    clean = mask_noncode(text)
    commands = list(COMMAND.finditer(clean))
    stack = []
    for index, command in enumerate(commands):
        kind, tail = command["kind"], command["tail"].strip()
        if kind in {"namespace", "section", "mutual"}:
            stack.append(tail.split()[0] if kind == "namespace" and tail else None)
            continue
        if kind == "end":
            if stack:
                stack.pop()
            continue
        if kind not in DECLARATION_KINDS:
            continue
        match = re.match(r"(?:«[^»]+»|[^\s:({\[]+)", tail)
        anonymous = kind == "example" or match is None
        short = match[0] if match and not anonymous else ""
        namespace = ".".join(n for n in stack if n)
        line = clean.count("\n", 0, command.start()) + 1
        name = (short.removeprefix("_root_.") if short.startswith("_root_.")
                else ".".join(filter(None, (namespace, short))))
        if anonymous:
            name = f"@{kind}:{path}:{line}"
        end = commands[index + 1].start() if index + 1 < len(commands) else len(clean)
        chunk = clean[command.start():end]
        boundary, body_start = body_boundary(chunk)
        yield Declaration(
            name=name, path=path, line=line, kind=kind,
            signature=text[command.start():command.start() + boundary].strip(),
            statement=chunk[:boundary], body=chunk[body_start:],
            namespace=namespace, private=bool(re.search(r"\bprivate\b", command[0])),
            anonymous=anonymous, direct_sorry=bool(PLACEHOLDER.search(chunk[body_start:])))


def declarations_in(directory):
    paths = [directory] if directory.is_file() else sorted(directory.rglob("*.lean"))
    for path in paths:
        yield from parse_source(path.read_text(encoding="utf-8"), path)


def audit_records(records):
    """Reject forbidden source placeholders and conservatively propagate local references."""
    records = list(records)
    named = {}
    for record in records:
        assert record.kind != "axiom", f"Local axiom forbidden: {record.path}:{record.line}"
        assert not PLACEHOLDER.search(record.statement), (
            f"Placeholder in declaration type: {record.path}:{record.line}")
        assert not record.direct_sorry or record.kind in PROOF_KINDS, (
            f"Placeholder outside a theorem/lemma proof: {record.path}:{record.line}")
        if not record.anonymous:
            assert record.name not in named, f"Duplicate local declaration: {record.name}"
            named[record.name] = record
    by_short = {}
    for name in named:
        by_short.setdefault(name.rsplit(".", 1)[-1], set()).add(name)
    for record in records:
        for token in IDENTIFIER.findall(record.statement + "\n" + record.body):
            candidates = set()
            if token in named:
                candidates.add(token)
            contextual = f"{record.namespace}.{token}" if record.namespace else token
            if contextual in named:
                candidates.add(contextual)
            # Covers open namespaces and dot notation; ambiguity is conservative.
            if not candidates:
                candidates.update(by_short.get(token.rsplit(".", 1)[-1], ()))
            record.source_dependencies.update(candidates - {record.name})
    unfinished = {r.name for r in records if r.direct_sorry}
    while True:
        additional = {r.name for r in records if r.source_dependencies & unfinished}
        if additional <= unfinished:
            break
        unfinished |= additional
    for record in records:
        record.unfinished_dependencies = record.source_dependencies & unfinished
        if record.direct_sorry:
            record.source_status = "unproved_statement"
        elif record.name in unfinished:
            record.source_status = ("depends_on_unproved" if record.kind in PROOF_KINDS
                                    else "definition_depends_on_unproved")
        elif record.kind in PROOF_KINDS:
            record.source_status = "proof_candidate"
        else:
            record.source_status = "definition"
    return named


def project_audit(root):
    paths = []
    for directory in ("Preiss", "PreissBlueprint"):
        paths.extend(sorted((root / directory).rglob("*.lean")))
    paths.extend(p for p in (root / "Preiss.lean", root / "PreissBlueprint.lean") if p.exists())
    records = []
    for path in paths:
        text = path.read_text(encoding="utf-8")
        clean = mask_noncode(text)
        if path.is_relative_to(root / "Preiss"):
            assert not re.search(r"^(?:public\s+)?import(?:\s+all)?\s+PreissBlueprint\b", clean, re.M), (
                f"Canonical module imports legacy draft library: {path}")
        assert not re.search(r"\baxiom\b", clean), f"Local axiom declaration forbidden: {path}"
        parsed = list(parse_source(text, path))
        # A placeholder in any other command is forbidden too.
        source_count = len(PLACEHOLDER.findall(clean))
        declared_count = sum(len(PLACEHOLDER.findall(r.statement + r.body)) for r in parsed)
        assert source_count == declared_count, f"Placeholder outside a declaration: {path}"
        records.extend(parsed)
    return audit_records(records)
