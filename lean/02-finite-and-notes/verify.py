"""Recheck the Goldbach workspace with a fresh Lean kernel build (Python 3 stdlib)."""
import argparse
import concurrent.futures
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import time


ROOT = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", default=shutil.which("lean"),
                        help="Lean 4.13.0 executable")
    parser.add_argument("--jobs", type=int, default=4)
    parser.add_argument("--output", type=Path, default=ROOT / "verification.json")
    args = parser.parse_args()
    if not args.lean:
        parser.error("Set --lean to the Lean 4.13.0 executable")
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    lean = str(Path(args.lean).resolve())
    version = subprocess.check_output([lean, "--version"], text=True).strip()
    if "version 4.13.0," not in version:
        parser.error(f"Expected Lean 4.13.0, got {version}")
    report = {"version": version, "modules": {}, "status": "running"}
    started = time.monotonic()
    with tempfile.TemporaryDirectory(prefix="goldbach-lean-") as build:
        env = dict(os.environ, LEAN_PATH=build)
        def compile_module(name):
            source = ROOT / (name + ".lean")
            out = Path(build) / (name + ".olean")
            out.parent.mkdir(parents=True, exist_ok=True)
            t0 = time.monotonic()
            result = subprocess.run([lean, "-j", "1", "-o", str(out), str(source)],
                                    cwd=ROOT, env=env, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT, encoding="utf-8", errors="replace")
            output = result.stdout.strip()
            if result.returncode or "sorryAx" in output or "warning:" in output:
                raise RuntimeError(f"{name} returned {result.returncode}\n{output}")
            if name == "Main":
                expected = source.read_text(encoding="utf-8").count("#print axioms")
                audits = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", output)
                clean = output.count("does not depend on any axioms")
                if len(audits) + clean != expected:
                    raise RuntimeError("Incomplete axiom audit: " + output)
                allowed = {"propext", "Classical.choice", "Quot.sound"}
                for row in audits:
                    if {s.strip() for s in row.split(",") if s.strip()} - allowed:
                        raise RuntimeError("Unexpected axiom: " + row)
            return name, {"elapsed_seconds": round(time.monotonic()-t0, 2),
                          "sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
                          "output": output}

        def stage(names):
            with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
                futures = [pool.submit(compile_module, name) for name in names]
                for future in concurrent.futures.as_completed(futures):
                    name, record = future.result()
                    report["modules"][name] = record
                    print(f"{name}: verified in {record['elapsed_seconds']}s", flush=True)
        try:
            stage(["Foundations", "Residues"])
            stage(["Certificates", "RoughParity", "Lift", "FilterCriterion", "MobiusCutoff"])
            stage(["Cutoff", "Incidence"])
            stage([p.relative_to(ROOT).with_suffix("").as_posix()
                   for p in sorted((ROOT / "Blocks").glob("*.lean"))])
            stage(["FiniteRange", "ModThree", "SpectralGapEnergy", "CenteredFour", "EndpointMajorant", "CutoffVariation"])
            stage(["BalancedSurplus"])
            stage(["Main"])
            report["status"] = "passed"
        except Exception as exc:
            report.update(status="failed", error=str(exc))
            raise
        finally:
            report["elapsed_seconds"] = round(time.monotonic()-started, 2)
            args.output.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n",
                                   encoding="utf-8")


if __name__ == "__main__":
    main()

