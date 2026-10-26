#!/usr/bin/env python3
"""Run every example in the library's comments and compare it with the answer written under it.

An example is one or more lines `-- >>> expression` followed by the comment lines that hold what ghci prints:

    -- >>> renderScalar (-1 / 2)
    -- "-1/2"

For each module under src/ the script starts `cabal repl lib:dqt`, enters the module's own scope (`:m *Module`, so
its private definitions and its imports are visible), evaluates each example, and compares the printed lines with
the written ones (blank lines and surrounding spaces ignored). It prints one OK or FAIL line per example and exits
non-zero when any example fails.

Usage, from this directory:  python3 check-examples.py [src/Drop/Lang/Parser.hs ...]
"""
import re
import subprocess
import sys
from pathlib import Path


def examples_of(lines):
    """Return (line number, expressions, expected lines) for each `-- >>>` block."""
    found, i = [], 0
    while i < len(lines):
        if not lines[i].lstrip().startswith("-- >>>"):
            i += 1
            continue
        first, exprs, expected = i + 1, [], []
        while i < len(lines) and lines[i].lstrip().startswith("-- >>>"):
            exprs.append(lines[i].lstrip()[6:].strip())
            i += 1
        while (i < len(lines) and lines[i].lstrip().startswith("--") and lines[i].lstrip()[2:].strip()
               and not lines[i].lstrip().startswith(("-- >>>", "-- |"))):
            expected.append(lines[i].lstrip()[2:].strip())
            i += 1
        found.append((first, exprs, expected))
    return found


def module_name(path):
    """The dotted module name of a file under src/."""
    return ".".join(path.relative_to("src").with_suffix("").parts)


def run_module(module, examples):
    """Evaluate a module's examples in one ghci session; return the printed lines of each example."""
    script = [":m *" + module]
    for n, (_, exprs, _) in enumerate(examples):
        script.append('putStrLn "@@%d"' % n)
        script.extend(exprs)
    done = subprocess.run(["cabal", "repl", "-v0", "lib:dqt"], input="\n".join(script) + "\n",
                          capture_output=True, text=True)
    outputs, current = [[] for _ in examples], None
    for line in done.stdout.split("\n"):
        mark = re.fullmatch(r"@@(\d+)", line.strip())
        if mark:
            current = int(mark.group(1))
        elif current is not None and line.strip():
            outputs[current].append(line.strip())
    return outputs


def main(argv):
    files = [Path(a) for a in argv] or sorted(Path("src").rglob("*.hs"))
    passed = failed = 0
    for path in files:
        examples = examples_of(path.read_text(encoding="utf-8").split("\n"))
        if not examples:
            continue
        module = module_name(path)
        for (line, _, expected), actual in zip(examples, run_module(module, examples)):
            ok = actual == expected
            passed, failed = passed + ok, failed + (not ok)
            print("%s %s:%d" % ("OK  " if ok else "FAIL", path, line))
            if not ok:
                print("     expected: %r\n     printed:  %r" % (expected, actual))
    print("%d examples, %d passed, %d failed" % (passed + failed, passed, failed))
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
