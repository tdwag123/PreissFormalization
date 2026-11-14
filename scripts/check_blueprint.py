"""Check LeanBlueprint links and export the intended DAG; no third-party packages."""
from pathlib import Path
from graphlib import TopologicalSorter
import argparse
import json
import re

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    sources = []
    def expand(path, stack=()):
        path = path.resolve()
        assert path.is_relative_to((ROOT / 'blueprint/src').resolve())
        assert path not in stack, 'Cyclic TeX input'
        sources.append(path.relative_to(ROOT).as_posix())
        text = path.read_text(encoding='utf-8')
        return re.sub(r'\\input\{([^}]+)\}',
                      lambda m: expand(path.parent / (m[1] + '.tex'), stack + (path,)), text)
    source = expand(ROOT / 'blueprint/src/content.tex')
    pattern = re.compile(
        r'\\begin\{(definition|lemma|theorem|proposition|corollary)\}'
        r'(?:\[([^\]]*)\])?(.*?)\\end\{\1\}'
        r'(?:\s*\\begin\{proof\}(?:\[[^\]]*\])?(.*?)\\end\{proof\})?', re.S)
    def values(command, text):
        return sorted({v.strip() for group in re.findall(r'\\' + command + r'\{([^}]+)\}', text)
                       for v in group.split(',')})
    nodes = []
    for match in pattern.finditer(source):
        kind, title, body, proof = match.groups()
        labels = values('label', body)
        assert len(labels) == 1, f'Expected one label: {title}'
        names = values('lean', body)
        status = ('definition' if kind == 'definition' and any(n.startswith('Preiss.') for n in names)
                  else 'draft_statement' if any(n.startswith('PreissBlueprint.') for n in names)
                  else 'formalized_upstream' if names and not any(n.startswith('Preiss.') for n in names)
                  else 'mathematical_plan')
        nodes.append(dict(id=labels[0], title=title, kind=kind, status=status, lean=names,
                          statement_dependencies=values('uses', body),
                          proof_dependencies=values('uses', proof or ''),
                          expanded_line=source[:match.start()].count('\n') + 1))
    ids = [n['id'] for n in nodes]
    assert len(ids) == len(set(ids)), 'Duplicate labels'
    graph = {n['id']: set(n['statement_dependencies'] + n['proof_dependencies']) for n in nodes}
    for name, deps in graph.items():
        assert name not in deps, f'Self dependency: {name}'
        assert deps <= set(ids), f'Unknown dependencies for {name}: {deps - set(ids)}'
    order = list(TopologicalSorter({k: sorted(v) for k, v in graph.items()}).static_order())
    assert 'thm:preiss' in ids
    local_sources = '\n'.join(p.read_text(encoding='utf-8')
                              for directory in ('Preiss', 'PreissBlueprint')
                              for p in (ROOT / directory).rglob('*.lean'))
    for node in nodes:
        for name in node['lean']:
            if name.startswith(('Preiss.', 'PreissBlueprint.')):
                short = name.split('.')[-1]
                assert re.search(r'\b(?:def|abbrev|theorem|lemma)\s+' + re.escape(short) + r'\b',
                                 local_sources), f'Missing declaration: {name}'
    for p in (ROOT / 'Preiss').rglob('*.lean'):
        clean = re.sub(r'/-.*?-/', '', p.read_text(encoding='utf-8'), flags=re.S)
        clean = re.sub(r'--[^\n]*', '', clean)
        assert not re.search(r'\b(sorry|admit|axiom)\b', clean), f'Placeholder in {p}'
        assert 'import PreissBlueprint' not in clean, f'Draft import in {p}'
    data = dict(sources=sources,
                meaning='Intended dependencies, not a certified proof graph',
                nodes=nodes, topological_order=order)
    slug = lambda label: label.replace(':', '_').replace('-', '_')
    dot = ['digraph Preiss {', '  rankdir=LR;', '  node [shape=box, style=filled, fontname="Arial"];']
    mermaid = ['flowchart LR']
    colors = dict(definition='#d9eaf7', draft_statement='#fff0bf',
                  formalized_upstream='#d9efdb', mathematical_plan='#eeeeee')
    for n in nodes:
        label = (n['title'] or n['id']).replace('"', '\\"')
        dot.append(f'  "{n["id"]}" [label="{label}", fillcolor="{colors[n["status"]]}"];')
        mermaid.append(f'  {slug(n["id"])}["{label}"]')
    for target, deps in graph.items():
        for dep in sorted(deps):
            dot.append(f'  "{dep}" -> "{target}";')
            mermaid.append(f'  {slug(dep)} --> {slug(target)}')
    dot.append('}')
    outputs = {'blueprint/dependencies.json': json.dumps(data, indent=2, ensure_ascii=False) + '\n',
               'blueprint/dependencies.dot': '\n'.join(dot) + '\n',
               'blueprint/dependencies.mmd': '\n'.join(mermaid) + '\n'}
    for filename, content in outputs.items():
        path = ROOT / filename
        if args.write:
            path.write_text(content, encoding='utf-8')
        else:
            assert path.read_text(encoding='utf-8') == content, f'Stale export: {filename}'
    checks = ['import FormalizingGMT', 'import PreissBlueprint', '']
    checks += ['#check ' + name for name in sorted({s for n in nodes for s in n['lean']})]
    checks += ['', '#print axioms Preiss.HasPositiveFiniteDensityAt.hasDensity',
               '#print axioms PreissBlueprint.preiss']
    (ROOT / 'tmp').mkdir(exist_ok=True)
    (ROOT / 'tmp/blueprint_checks.lean').write_text('\n'.join(checks) + '\n', encoding='utf-8')
    print(f'Validated {len(nodes)} nodes, {sum(map(len, graph.values()))} edges; DAG is acyclic.')
    print('Run lake env lean tmp/blueprint_checks.lean to check declaration types.')


if __name__ == '__main__':
    main()
