"""Build the pinned Lean project and verify the public axiom reports."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys


ROOT = Path(__file__).resolve().parent
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def run(*args):
    p = subprocess.run(args, cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                       encoding="utf-8", errors="replace")
    if p.returncode:
        sys.stdout.buffer.write(p.stdout.encode("utf-8"))
        raise SystemExit(p.returncode)
    return p.stdout


def main():
    options = argparse.ArgumentParser()
    options.add_argument("--record", type=Path, help="Save the verification report as JSON.")
    args = options.parse_args()
    sources = sorted(p for p in ROOT.glob("*.lean") if p.name != "lakefile.lean")
    expected = []
    for path in sources:
        content = path.read_text(encoding="utf-8-sig")
        expected.extend(re.findall(r"(?m)^#print axioms (\S+)\s*$", content))
    build_output = re.sub(r"\x1b\[[0-9;]*m", "", run("lake", "build"))
    if re.search(r"\bwarning:", build_output, re.IGNORECASE):
        raise SystemExit("Lean emitted a warning.\n" + build_output)
    public = {}
    for name, dependencies in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", build_output):
        axioms = sorted(a.strip() for a in dependencies.split(",") if a.strip())
        if set(axioms) - ALLOWED_AXIOMS:
            raise SystemExit(f"Unexpected axioms in {name}: {axioms}")
        public[name] = axioms
    for name in re.findall(r"'([^']+)' does not depend on any axioms", build_output):
        public[name] = []
    missing = [name for name in expected if not any(q == name or q.endswith("." + name) for q in public)]
    if missing or len(public) != len(expected):
        raise SystemExit(f"Incomplete axiom audit ({len(public)}/{len(expected)}). Missing: {missing}")
    demonstration = run(sys.executable, "example.py").splitlines()
    manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
    inputs = [*sources, ROOT / "lakefile.lean", ROOT / "lake-manifest.json",
              ROOT / "lean-toolchain", ROOT / "example.py", ROOT / "verify.py"]
    record = {
        "lean": run("lake", "env", "lean", "--version").strip(),
        "mathlib_commit_from_lockfile": next(p["rev"] for p in manifest["packages"] if p["name"] == "mathlib"),
        "build": "lake build",
        "build_exit_code": 0,
        "source_modules": len(sources),
        "audited_declarations": len(public),
        "example": demonstration,
        "sha256": {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs},
        "axioms": dict(sorted(public.items())),
    }
    if args.record is not None:
        args.record.write_text(json.dumps(record, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Verified {len(sources)} modules and {len(public)} public axiom reports; example passed.")


if __name__ == "__main__":
    main()
