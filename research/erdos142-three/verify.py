#!/usr/bin/env python3
"""Recheck this auxiliary contribution in the catalog-pinned Lean environment.

First build the unchanged upstream module from the formal-conjectures checkout:
    lake --no-cache build 'FormalConjectures.ErdosProblems.«142»'
Then, with that checkout's Lean 4.33.1 on PATH:
    python3 verify.py /path/to/formal-conjectures

This invokes Lean and checks the same allowed axiom set as tools/check.sh. It
does not claim a catalog verdict, CI result, or proof of the original target.
It performs no installation, downloads, source edits, or submission.
"""

import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile


FC_COMMIT = "9097e2f90e66d2f6244209cb1c07f7120d17ec53"
MATHLIB_COMMIT = "0df444a360eaa60ab8c11dca51a86af692955474"
LEAN_VERSION = "4.33.1"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
ORIGINAL_IMPORT = "import FormalConjectures.ErdosProblems.«142»"


def run(args, cwd, timeout=60):
    return subprocess.run(
        args, cwd=cwd, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, timeout=timeout, check=True,
    ).stdout.strip()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("formal_conjectures", type=Path)
    parser.add_argument("--output-dir", type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    fc = args.formal_conjectures.resolve()
    mathlib = fc / ".lake/packages/mathlib"
    source_path = Path(__file__).resolve().with_name("Erdos142CarryFree.lean")
    source_bytes = source_path.read_bytes()
    source = source_bytes.decode("utf-8")

    if run(["git", "rev-parse", "HEAD"], fc) != FC_COMMIT:
        raise SystemExit("formal-conjectures commit does not match the catalog pin")
    if run(["git", "rev-parse", "HEAD"], mathlib) != MATHLIB_COMMIT:
        raise SystemExit("Mathlib commit does not match the pinned manifest")
    manifest = json.loads((fc / "lake-manifest.json").read_text())
    dependencies = {}
    checkouts = [fc]
    for package in manifest["packages"]:
        if package.get("type") != "git":
            raise SystemExit("review required for a non-git dependency")
        checkout = fc / manifest.get("packagesDir", ".lake/packages") / package["name"]
        actual_commit = run(["git", "rev-parse", "HEAD"], checkout)
        if actual_commit != package["rev"]:
            raise SystemExit("dependency commit mismatch: " + package["name"])
        dependencies[package["name"]] = actual_commit
        checkouts.append(checkout)
    # No altered tracked source is allowed in any pinned dependency checkout.
    for checkout in checkouts:
        run(["git", "diff", "--exit-code", "HEAD", "--"], checkout)
    version = run(["lake", "env", "lean", "--version"], fc)
    if not re.search(r"Lean \(version " + re.escape(LEAN_VERSION) + r"(?:,|\s)", version):
        raise SystemExit("unexpected Lean version: " + version)
    imports = re.findall(r"^import .+$", source, re.MULTILINE)
    if imports != [ORIGINAL_IMPORT]:
        raise SystemExit("the artifact must retain exactly its original problem import")
    if re.search(r"\b(?:sorry|admit|axiom|native_decide|unsafe)\b", source):
        raise SystemExit("a prohibited proof token occurs in the artifact")
    if re.search(r"^\s*#[A-Za-z_]", source, re.MULTILINE):
        raise SystemExit("audit commands must remain outside the deliverable")

    names = ["Erdos142CarryFree." + n for n in re.findall(
        r"^theorem ([A-Za-z_][A-Za-z0-9_]*)\b", source, re.MULTILINE
    )]
    if len(names) != 20 or len(set(names)) != len(names):
        raise SystemExit("unexpected theorem inventory; review verifier before continuing")
    audit_source = source + "\n" + "\n".join("#print axioms " + n for n in names) + "\n"
    output = args.output_dir.resolve()
    output.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    env.setdefault("LEAN_NUM_THREADS", "2")
    started = datetime.datetime.now(datetime.timezone.utc).isoformat()
    with tempfile.TemporaryDirectory(prefix="erdos142-audit-") as tmp:
        audit_path = Path(tmp) / "Erdos142CarryFreeAudit.lean"
        audit_path.write_text(audit_source, encoding="utf-8")
        result = subprocess.run(
            ["lake", "env", "lean", str(audit_path)], cwd=fc, env=env,
            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            timeout=1800,
        )
    log = result.stdout
    (output / "axiom-audit.log").write_text(log, encoding="utf-8")
    axioms = {}
    errors = []
    if result.returncode:
        errors.append("Lean exited with code " + str(result.returncode))
    if re.search(r"\berror:|\bwarning:", log):
        errors.append("Lean reported an error or warning")
    for name in names:
        match = re.search(
            r"'" + re.escape(name) + r"' depends on axioms: \[(.*?)\]", log, re.DOTALL
        )
        if match:
            used = {x.strip() for x in match.group(1).split(",") if x.strip()}
        elif "'" + name + "' does not depend on any axioms" in log:
            used = set()
        else:
            errors.append("missing axiom report: " + name)
            continue
        axioms[name] = sorted(used)
        if used - ALLOWED_AXIOMS:
            errors.append("forbidden axiom dependencies: " + name)
    record = {
        "classification": "classical-result formalization; auxiliary research contribution",
        "original_target": "Erdos142.erdos_142.variants.three",
        "original_target_solved": False,
        "validation": "local Lean compilation and transitive axiom audit",
        "catalog_checker_run": False,
        "official_ci_run": False,
        "status": "passed" if not errors else "failed",
        "started_utc": started,
        "finished_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "formal_conjectures_commit": FC_COMMIT,
        "mathlib_commit": MATHLIB_COMMIT,
        "manifest_dependency_commits": dependencies,
        "lean_version": version,
        "source_file": source_path.name,
        "source_sha256": hashlib.sha256(source_bytes).hexdigest(),
        "original_import": ORIGINAL_IMPORT,
        "theorem_count": len(names),
        "allowed_axioms": sorted(ALLOWED_AXIOMS),
        "axioms": axioms,
        "errors": errors,
    }
    (output / "verification.json").write_text(
        json.dumps(record, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    if errors:
        raise SystemExit("Verification failed: " + "; ".join(errors))
    print("PASS: original import, pinned environment, " + str(len(names)) + " theorem axiom audits")
    print("SHA-256 " + record["source_sha256"])


if __name__ == "__main__":
    main()
