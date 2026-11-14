"""Render the pinned kernel checkpoint as a searchable, revision-specific proof list."""
from pathlib import Path
from collections import Counter
from html import escape
import argparse
import json

ROOT = Path(__file__).resolve().parents[1]
REPO = "https://github.com/tdwag123/PreissFormalization"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--site", action="store_true")
    args = parser.parse_args()
    checkpoint = json.loads((ROOT / "blueprint/kernel-checkpoint.json").read_text(encoding="utf-8"))
    index = json.loads((ROOT / "blueprint/declarations.json").read_text(encoding="utf-8"))
    assert not checkpoint["failures"], "Cannot publish a failed kernel audit as a verified checkpoint"
    revision = checkpoint["source_revision"]
    records = checkpoint["declarations"]
    labels = {
        "proved": "Proved locally", "definition_checked": "Checked definition",
        "unproved_statement": "Unfinished proof", "depends_on_sorry": "Uses unfinished proof",
        "upstream_checked": "Checked upstream",
    }
    counts = Counter(row["kernel_status"] for row in records.values())
    rows = []
    for name, row in sorted(records.items()):
        status = row["kernel_status"]
        assert status in labels, f"Unknown kernel status: {status}"
        if status in {"proved", "definition_checked"}:
            assert "sorryAx" not in row["axioms"], name
        if status in {"unproved_statement", "depends_on_sorry"}:
            assert "sorryAx" in row["axioms"], name
        path = row.get("path", index.get(name, {}).get("path", ""))
        url = (f"{REPO}/blob/{revision}/{path}" if row["project"] == "local"
               else index[name]["url"])
        rows.append(f'<tr data-name="{escape(name, quote=True)}" data-status="{status}">'
                    f'<td><a href="{escape(url, quote=True)}">{escape(name)}</a></td>'
                    f'<td>{labels[status]}</td><td>{escape(path)}</td></tr>')
    unfinished = counts["unproved_statement"] + counts["depends_on_sorry"]
    preiss_proved = records.get("Preiss.preiss", {}).get("kernel_status") == "proved"
    characterization_proved = records.get(
        "Preiss.rectifiable_iff_density_and_tangent_plane", {}
    ).get("kernel_status") == "proved"
    theorem_status = (
        "Preiss’s theorem is proved using only the permitted standard foundations. "
        if preiss_proved else "Preiss’s theorem remains unfinished. "
    ) + (
        "The full flat-tangent rectifiability characterization is also proved."
        if characterization_proved else
        "The full flat-tangent rectifiability characterization remains unfinished."
    )
    page = '''<!doctype html>
<html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Verified proof progress — Preiss Formalization</title>
<style>
body{font:16px/1.5 system-ui,sans-serif;color:#18232c;background:#fafbfc;margin:0 auto;padding:28px;max-width:1300px}
a{color:#145a96}h1{font-size:1.9rem;margin-bottom:.4rem}p{max-width:950px}
.counts{display:flex;flex-wrap:wrap;gap:16px;margin:24px 0}.counts div{background:white;border:1px solid #cbd5df;padding:14px 22px;border-radius:8px}.counts strong{display:block;font-size:1.8rem}
.controls{display:flex;flex-wrap:wrap;align-items:end;gap:16px;margin:24px 0}label{display:grid;gap:5px}input,select{font:inherit;padding:9px;border:1px solid #8595a5;border-radius:4px}input{width:min(440px,75vw)}
table{width:100%;border-collapse:collapse;font-size:.9rem}th,td{text-align:left;padding:10px;border-bottom:1px solid #dbe2e9;overflow-wrap:anywhere}th{background:#edf2f6}td:first-child{max-width:550px}td:last-child{max-width:330px;color:#52616e}tr[hidden]{display:none}
code{background:#edf2f6;padding:2px 4px}.table-wrap{overflow-x:auto}
</style>
<nav><a href="index.html">Blueprint</a> · <a href="dep_graph_document.html">Full dependency graph</a> · <a href="preiss-core.svg">Preiss dependencies</a></nav>
<h1>Verified proof progress</h1>
'''
    page += (f'<p>This list records the Lean kernel audit at '
             f'<a href="{REPO}/commit/{revision}"><code>{revision[:7]}</code></a>, '
             f'using <code>{escape(checkpoint["toolchain"])}</code>. '
             'Links open source at the verified revision. Later edits and new declarations are not certified by this checkpoint.</p>'
             '<p>A proved result has no transitive <code>sorryAx</code> dependency. '
             '“Uses unfinished proof” means its own proof may be written, but one of its dependencies remains unfinished. '
             + theorem_status + '</p>')
    page += '<div class="counts">' + ''.join(
        f'<div><strong>{number}</strong>{label}</div>' for number, label in [
            (counts["proved"], "proved local declarations"),
            (counts["definition_checked"], "checked definitions"),
            (unfinished, "unfinished or dependent"),
            (counts["upstream_checked"], "checked upstream declarations")]) + '</div>'
    page += '''<div class="controls"><label>Find a declaration or module<input id="search" type="search" placeholder="e.g. tangent, flatness, Gaussian"></label>
<label>Show<select id="status"><option value="proved">Proved local results</option><option value="definition_checked">Checked definitions</option><option value="unfinished">Unfinished proofs</option><option value="upstream_checked">Checked upstream results</option><option value="all">All declarations</option></select></label>
<span id="visible" role="status" aria-live="polite"></span></div>
<div class="table-wrap"><table><thead><tr><th>Lean declaration · pinned source</th><th>Kernel status</th><th>File</th></tr></thead><tbody>'''
    page += '\n'.join(rows)
    page += '''</tbody></table></div>
<script>
const rows=[...document.querySelectorAll('tbody tr')], search=document.getElementById('search'), status=document.getElementById('status');
function filter(){const q=search.value.trim().toLowerCase(), s=status.value;let shown=0;for(const r of rows){const match=s==='all'||r.dataset.status===s||(s==='unfinished'&&['unproved_statement','depends_on_sorry'].includes(r.dataset.status));r.hidden=!(match&&r.textContent.toLowerCase().includes(q));if(!r.hidden)shown++;}document.getElementById('visible').textContent=`${shown} of ${rows.length} declarations`;}
search.addEventListener('input',filter);status.addEventListener('change',filter);filter();
</script></html>'''
    target = ROOT / ("blueprint/web/proof-status.html" if args.site else "blueprint/proof-status.html")
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(page, encoding="utf-8")
    print(f"Rendered {len(records)} audited declarations at {revision[:7]}: {counts['proved']} proved, {unfinished} unfinished.")


if __name__ == "__main__":
    main()
