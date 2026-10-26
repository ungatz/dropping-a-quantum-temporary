"""Restoration census of the corpus table.

Reads s_bench_table.md, which s_bench.py writes from the nineteen programs of
../haskell/programs/, and counts over the corpus rows (the generated families are
not in the paper's corpus table):

  * the safe reachable records;
  * those whose reclaiming gate is I, where restoration holds: a temporary block
    ends on its allocation ray, or a loan comes back unchanged;
  * the others, split into temporary sites and loan sites. A loan site is a drop
    of a register the program declares with `newdirty` or as a `loan` parameter
    (programs/SYNTAX.md);
  * among the temporary records not restored, those whose reclaiming gate is a
    basis permutation (X, or a basis transposition "swap"), so that the temporary
    ends on a known computational basis state: a rule that accepts any such state
    still refuses the others and every loan that does not come back unchanged;
  * the corpus programs that allocate after a drop (none: pooling the reclaimed
    registers would save no qubit on this corpus).

Run from this directory:  python3 census.py
It exits 1 unless the counts are 26 safe reachable records, 11 with gate I, and
14 temporary sites + 1 loan site without; 11 of the 14 on a basis state, so a
basis-state rule refuses 3 temporary records (bell-block.s, bell-pair.s, dj.s)
and 1 loan record (mcx-dirty-x.s); and 0 programs allocating after a drop: the
numbers the paper prints.
"""
import ast
import re
import sys
from pathlib import Path

QASM3 = Path(__file__).resolve().parent
ART = QASM3.parent
PROGRAMS = ART / "haskell/programs"
TABLE = QASM3 / "s_bench_table.md"
CORPUS_PROGRAMS = {
    "bell-block.s", "bell-pair-split.s", "bell-pair.s", "c.s", "copy-input.s",
    "dj.s", "grover.s", "learns-nothing.s", "mcx-dirty-half.s", "mcx-dirty-x.s",
    "mcx-dirty.s", "qpe.s", "rus.s", "shor.s", "simon.s", "superdense.s",
    "teleport.s", "temp-and.s", "temp-general.s",
}


def admitted_reuse_programs():
    """Read the source of the authoritative eleven-example allowlist without importing its dependencies."""
    path = QASM3 / "reuse_check.py"
    tree = ast.parse(path.read_text(), filename=str(path))
    for node in tree.body:
        if isinstance(node, ast.Assign) and any(
            isinstance(target, ast.Name) and target.id == "ADMITTED_PROGRAMS" for target in node.targets
        ):
            value = ast.literal_eval(node.value)
            if not isinstance(value, tuple) or any(not isinstance(item, str) for item in value):
                raise SystemExit("reuse_check.py ADMITTED_PROGRAMS is not a tuple of filenames")
            return set(value)
    raise SystemExit("reuse_check.py has no literal ADMITTED_PROGRAMS tuple")


REUSE_PROGRAMS = admitted_reuse_programs()
source_names = {p.name for p in PROGRAMS.glob("*.s")}
expected_names = CORPUS_PROGRAMS | REUSE_PROGRAMS
if len(CORPUS_PROGRAMS) != 19 or len(REUSE_PROGRAMS) != 11 or len(expected_names) != 27:
    raise SystemExit("refusing census: expected 19 corpus programs and 11 reuse examples with 3 overlaps")
if source_names != expected_names:
    raise SystemExit(
        "refusing census: program source inventory differs from 19-corpus/11-reuse allowlists; "
        f"missing={sorted(expected_names-source_names)}, extra={sorted(source_names-expected_names)}"
    )
table = TABLE.read_text().splitlines()
corpus = {name: (PROGRAMS / name).read_text() for name in CORPUS_PROGRAMS}


def loans(src):
    return {m.group(1) for m in re.finditer(r'newdirty\s+(\w+)\s*:', src)} | \
           {m.group(1) for m in re.finditer(r'\bloan\s+(\w+)\s*:', src)}


safe = restored = temp_off = loan_off = temp_basis = 0
refused_by_basis_rule = []
seen = set()
NCOLS = len([c for c in table[0].strip().strip('|').split('|')])


def split_row(row):
    """Split a table row on its column separators only. A separator is a bar
    with blanks on both sides; a ket such as `|0>` in a gate cell ("swap |0>,|7>")
    has no blank after its bar and stays inside its cell."""
    inner = row.strip()
    if not (inner.startswith('|') and inner.endswith('|')):
        raise SystemExit(f"refusing census: not a table row: {row!r}")
    cells = [c.strip() for c in re.split(r'(?<=\s)\|(?=\s)', ' ' + inner[1:-1] + ' ')]
    if len(cells) != NCOLS:
        raise SystemExit(f"refusing census: {len(cells)} cells, expected {NCOLS}: {row!r}")
    return cells


for row in table[2:]:
    cells = split_row(row)
    prog = cells[0]
    if prog not in corpus:
        continue                                   # a generated family
    seen.add(prog)
    site = cells[1].split(' (')[0]                 # "a,b (d=4)" -> "a,b"
    is_loan = any(r in loans(corpus[prog]) for r in site.split(','))
    verdicts = dict(v.split(':', 1) for v in cells[3].split(', '))
    gates = dict(g.split(':', 1) for g in re.split(r', (?=[a-z-]+:)', cells[8]))
    if set(gates) != set(verdicts):
        raise SystemExit(f"refusing census: records {sorted(verdicts)} have gates for {sorted(gates)} in {prog}")
    for rec, v in verdicts.items():
        if not v.startswith('SAFE'):
            continue                               # UNSAFE or UNREACHABLE
        safe += 1
        if gates[rec].strip() == 'I':
            restored += 1
        elif is_loan:
            loan_off += 1
            refused_by_basis_rule.append(prog)
        else:
            temp_off += 1
            g = gates[rec].strip()
            if g == 'X' or g.startswith('swap'):
                temp_basis += 1
            else:
                refused_by_basis_rule.append(prog)

def allocates_after_drop(src):
    body = '\n'.join(l.split('--')[0].split('//')[0] for l in src.splitlines())
    drops = [m.start() for m in re.finditer(r'\bdrop\b', body)]
    news = [m.start() for m in re.finditer(r'\bnew(dirty)?\b', body)]
    return bool(drops) and any(n > min(drops) for n in news)


late = sorted(p for p, src in corpus.items() if allocates_after_drop(src))
missing = sorted(set(corpus) - seen)
print(f"corpus programs with a drop row: {len(seen)} of 19 (no drop row: {missing})")
print(f"source inventory: 19 corpus + 11 reuse examples - {len(CORPUS_PROGRAMS & REUSE_PROGRAMS)} overlaps = {len(expected_names)} distinct programs")
print(f"safe reachable records: {safe}; restored (gate I): {restored}; not restored: "
      f"{safe - restored} = {temp_off} temporary sites + {loan_off} loan sites")
print(f"temporary records not restored but on a basis state: {temp_basis} of {temp_off}; "
      f"a basis-state rule refuses {len(refused_by_basis_rule)}: {refused_by_basis_rule}")
print(f"corpus programs that allocate after a drop: {len(late)} {late}")
ok = len(seen) == 19 and not missing and (safe, restored, temp_off, loan_off) == (26, 11, 14, 1) and temp_basis == 11 and \
    refused_by_basis_rule == ['bell-block.s', 'bell-pair.s', 'dj.s', 'mcx-dirty-x.s'] and late == []
print("PASS census 26 / 11 / 14 + 1; basis rule refuses 3 + 1; no allocation after a drop"
      if ok else "FAIL census")
sys.exit(0 if ok else 1)
