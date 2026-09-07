#!/usr/bin/env python3
"""Repository hygiene gate.

Checks that files intended for publication contain only expected characters,
no machine-local paths, and no credential-shaped strings.

Usage:
    python tools/outbound_gate.py                    # scan tracked files
    python tools/outbound_gate.py --paths a.tex b/   # scan specific paths
    python tools/outbound_gate.py --strict-urls      # also flag URLs (blind review)

Exit code 0 = clean, 1 = findings.

Additional project-specific patterns may be supplied through the
GATE_EXTRA_PATTERNS environment variable as a JSON array of regex strings.
"""

import argparse
import json
import math
import os
import re
import subprocess
import sys
import unicodedata
from collections import Counter
from pathlib import Path

# --------------------------------------------------------------- characters
# Unicode blocks that legitimately appear in this project's published files:
# mathematical notation, Greek letters, accented Latin (bibliography names),
# and typographic punctuation. Anything outside these blocks is reported.
# Defined as code-point ranges so this file itself stays pure ASCII.
ALLOWED_RANGES = (
    (0x00A0, 0x00FF),   # Latin-1 supplement
    (0x0100, 0x024F),   # Latin Extended-A and -B
    (0x0370, 0x03FF),   # Greek and Coptic
    (0x1D00, 0x1D7F),   # Phonetic extensions: Lean/Mathlib superscripts (transpose, vector)
    (0x2000, 0x206F),   # General punctuation
    (0x2070, 0x209F),   # Superscripts and subscripts
    (0x20A0, 0x20CF),   # Currency symbols
    (0x2100, 0x214F),   # Letterlike symbols
    (0x2190, 0x21FF),   # Arrows
    (0x2200, 0x22FF),   # Mathematical operators
    (0x2300, 0x23FF),   # Miscellaneous technical
    (0x25A0, 0x25FF),   # Geometric shapes
    (0x27C0, 0x27EF),   # Miscellaneous mathematical symbols-A
    (0x2A00, 0x2AFF),   # Supplemental mathematical operators
    (0x2B00, 0x2BFF),   # Miscellaneous symbols and arrows: Lean/Mathlib dot product
    (0x1D400, 0x1D7FF), # Mathematical alphanumeric symbols
    (0x1F800, 0x1F8FF), # Supplemental arrows-C: the implication arrow of Foundation's formulas
)

BINARY_SUFFIXES = {
    ".png", ".jpg", ".jpeg", ".pdf", ".gif", ".zip", ".gz", ".ico",
    ".olean", ".parquet", ".xlsx", ".woff", ".woff2", ".ttf", ".otf",
}

MACHINE_PATHS = re.compile(
    r"(?i)("
    r"[a-z]:\\users\\"          # Windows user directory
    r"|/home/[a-z0-9_.-]+/"     # Linux home directory
    r"|/users/[a-z0-9_.-]+/"    # macOS home directory
    r"|[\\/]desktop[\\/]"
    r")"
)

CREDENTIAL_CONTEXT = re.compile(r"(?i)(api[_-]?key|secret|token|passw)")
LONG_TOKEN = re.compile(r"[A-Za-z0-9_\-]{24,}")
URL = re.compile(r"(?i)https?://")


def allowed_char(ch: str) -> bool:
    if ord(ch) < 128:
        return True
    if unicodedata.category(ch) == "Mn":     # combining marks
        return True
    cp = ord(ch)
    return any(lo <= cp <= hi for lo, hi in ALLOWED_RANGES)


def entropy(s: str) -> float:
    if not s:
        return 0.0
    counts = Counter(s)
    n = len(s)
    return -sum((c / n) * math.log2(c / n) for c in counts.values())


def extra_patterns():
    raw = os.environ.get("GATE_EXTRA_PATTERNS", "").strip()
    if not raw:
        return []
    try:
        return [re.compile(p, re.IGNORECASE) for p in json.loads(raw)]
    except (ValueError, re.error) as exc:
        print(f"GATE_EXTRA_PATTERNS could not be parsed: {exc}", file=sys.stderr)
        sys.exit(2)


def tracked_files(paths):
    if paths:
        out = []
        for p in paths:
            q = Path(p)
            if q.is_dir():
                out += [f for f in q.rglob("*") if f.is_file()]
            elif q.is_file():
                out.append(q)
        return out
    res = subprocess.run(["git", "ls-files"], capture_output=True, text=True)
    return [Path(line) for line in res.stdout.splitlines() if line.strip()]


def read_text(path: Path):
    if path.suffix.lower() in BINARY_SUFFIXES:
        return None
    try:
        return path.read_text(encoding="utf-8")
    except (UnicodeDecodeError, OSError):
        return None


def scan_line(line, strict_urls, extras):
    findings = []
    unexpected = {c for c in line if not allowed_char(c)}
    if unexpected:
        codes = " ".join(f"U+{ord(c):04X}" for c in sorted(unexpected))
        findings.append(("unexpected-characters", codes[:60]))
    if MACHINE_PATHS.search(line):
        findings.append(("machine-local-path", line.strip()[:80]))
    if CREDENTIAL_CONTEXT.search(line):
        for tok in LONG_TOKEN.findall(line):
            if entropy(tok) > 3.5:
                findings.append(("credential-shaped-string", tok[:10] + "..."))
    if strict_urls and URL.search(line):
        findings.append(("url-in-blind-artifact", line.strip()[:80]))
    for pat in extras:
        if pat.search(line):
            findings.append(("project-pattern", line.strip()[:80]))
    return findings


def scan_git_metadata(extras):
    findings = []
    fmt = "%H%x1f%an <%ae>%x1f%cn <%ce>%x1f%B%x1e"
    res = subprocess.run(["git", "log", f"--format={fmt}"],
                         capture_output=True, text=True)
    for record in res.stdout.split("\x1e"):
        if not record.strip():
            continue
        parts = record.strip().split("\x1f")
        if len(parts) < 4:
            continue
        sha = parts[0][:8]
        for layer, value in (("author", parts[1]),
                             ("committer", parts[2]),
                             ("message", parts[3])):
            for code, excerpt in scan_line(value, False, extras):
                findings.append((code, f"commit {sha} ({layer})", excerpt))
    return findings


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--paths", nargs="*", default=None)
    ap.add_argument("--strict-urls", action="store_true")
    ap.add_argument("--skip-git", action="store_true")
    args = ap.parse_args()

    extras = extra_patterns()
    findings = []

    for path in tracked_files(args.paths):
        text = read_text(path)
        if text is None:
            continue
        for lineno, line in enumerate(text.splitlines(), 1):
            for code, excerpt in scan_line(line, args.strict_urls, extras):
                findings.append((code, f"{path}:{lineno}", excerpt))

    if not args.skip_git and not args.paths:
        findings += scan_git_metadata(extras)

    if findings:
        print(f"{len(findings)} finding(s):\n")
        for code, where, excerpt in findings:
            print(f"  [{code}] {where}\n      {excerpt}")
        print("\nIf a finding is expected, widen ALLOWED_RANGES or adjust the "
              "relevant pattern. Changes are visible in the diff.")
        return 1
    print("clean")
    return 0


if __name__ == "__main__":
    sys.exit(main())
