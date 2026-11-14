"""Index graph declarations at pinned sources; build portable LeanBlueprint links.

This is a source index, not a Lean elaborator or doc-gen replacement.
Run --write after lake update when changing declaration names/upstream revisions.
Run --site after rendering the blueprint. Ordinary validation needs no Lean checkout.
"""
from pathlib import Path
import argparse
import json
import re
import shutil

ROOT = Path(__file__).resolve().parents[1]
REPO = 'https://github.com/tdwag123/PreissFormalization'
GMT = 'https://github.com/uw-math-ai/FormalizingGMT'


def declarations(directory):
    for path in sorted(directory.rglob('*.lean')):
        text = path.read_text(encoding='utf-8')
        # Mask nested block and line comments, preserving offsets and line numbers.
        chars = list(text)
        depth = 0
        i = 0
        while i < len(text):
            if text[i:i+2] == '/-':
                depth += 1
                chars[i:i+2] = '  '
                i += 2
            elif depth and text[i:i+2] == '-/':
                depth -= 1
                chars[i:i+2] = '  '
                i += 2
            elif not depth and text[i:i+2] == '--':
                end = text.find('\n', i)
                if end == -1:
                    end = len(text)
                chars[i:end] = ' ' * (end-i)
                i = end
            else:
                if depth and text[i] != '\n':
                    chars[i] = ' '
                i += 1
        clean = ''.join(chars)
        stack = []
        offset = 0
        for line_no, line in enumerate(clean.splitlines(keepends=True), 1):
            ns = re.match(r'^(?:noncomputable\s+)?(namespace|section)\b\s*(\S+)?', line)
            if ns:
                stack.append(ns[2] if ns[1] == 'namespace' else None)
            elif re.match(r'^end(?:\s|$)', line):
                if stack:
                    stack.pop()
            decl = re.match(r'^(?:@\[[^\]]*\]\s*)?(?:(?:noncomputable|protected|private)\s+)*(?:def|abbrev|theorem|lemma|class|structure)\s+(\S+)', line)
            if decl:
                name = '.'.join([s for s in stack if s] + [decl[1]])
                boundary = re.search(r':=|\bwhere\b', clean[offset:])
                end = offset + boundary.start() if boundary else -1
                if end == -1:
                    end = offset + len(line)
                yield name, path, line_no, text[offset:end].strip()
            offset += len(line)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    parser.add_argument('--site', action='store_true')
    args = parser.parse_args()
    graph = json.loads((ROOT / 'blueprint/dependencies.json').read_text(encoding='utf-8'))
    names = {name for node in graph['nodes'] for name in node['lean']}
    registry_path = ROOT / 'blueprint/declarations.json'
    revision = json.loads((ROOT / 'blueprint/reuse.json').read_text(encoding='utf-8'))['revisions']['FormalizingGMT']
    if args.write:
        entries = {}
        upstream = ROOT / '.lake/packages/FormalizingGMT'
        for base, folder, project, rev in [
            (ROOT, ROOT / 'Preiss', 'PreissFormalization', 'main'),
            (ROOT, ROOT / 'PreissBlueprint', 'PreissFormalization', 'main'),
            (upstream, upstream / 'FormalizingGMT', 'FormalizingGMT', revision),
        ]:
            for name, path, line, signature in declarations(folder):
                if name not in names:
                    continue
                assert name not in entries, f'Ambiguous declaration: {name}'
                relative = path.relative_to(base).as_posix()
                repo = GMT if project == 'FormalizingGMT' else REPO
                entries[name] = dict(project=project, revision=rev, path=relative, line=line,
                                     url=f'{repo}/blob/{rev}/{relative}#L{line}', signature=signature)
        assert names == entries.keys(), f'Names not resolved: {names - entries.keys()}'
        registry_path.write_text(json.dumps(entries, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')
    entries = json.loads(registry_path.read_text(encoding='utf-8'))
    assert names == entries.keys(), 'Declaration index is stale'
    for name, entry in entries.items():
        if entry['project'] == 'FormalizingGMT':
            assert entry['revision'] == revision, f'Stale upstream revision: {name}'
        else:
            lines = (ROOT / entry['path']).read_text(encoding='utf-8').splitlines()
            assert name.rsplit('.', 1)[-1] in lines[entry['line']-1], f'Stale source line: {name}'
    if args.site:
        target = ROOT / 'blueprint/web/lean/find'
        target.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / 'blueprint/source-viewer.html', target / 'index.html')
        shutil.copyfile(registry_path, target / 'declarations.json')
        (ROOT / 'blueprint/web/.nojekyll').touch()
    count = sum(e['project'] == 'FormalizingGMT' for e in entries.values())
    print(f'Validated source locations for {len(entries)} declarations ({count} from FormalizingGMT).')


if __name__ == '__main__':
    main()
