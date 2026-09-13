#!/usr/bin/env python3
"""Package validated sources, PDF and a portable receipt. Python 3.11+."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import sys
import tempfile
import zipfile

from validate import (
    ALLOW, COMMON, CORE, LINT_PACKAGES, ROOT, audit, digest, lint_summary,
    module_order, require, sources,
)


def json_bytes(value: object) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode("utf-8")


def map_hash(value: dict[str, str]) -> str:
    return hashlib.sha256(json_bytes(value)).hexdigest()


def load_report(path: Path, phase: str) -> tuple[dict, list[str]]:
    """Read a successful phase report and verify each referenced command log."""
    report = json.loads(path.read_bytes())
    require(report.get("status") == "PASS" and report.get("phases", {}).get(phase) == "PASS",
            "Report did not pass the requested phase: " + phase)
    require(report.get("sources_unchanged") is True, "Report lacks a successful source guard")
    logs = []
    for number, command in enumerate(report["commands"]):
        name = f"{number:03d}.log"
        require(command["log"] == name and command["exit_code"] == 0, "Invalid command record")
        log = path.parent / name
        require(log.is_file() and not log.is_symlink(), "Missing or symlinked command log")
        require(log.stat().st_size == command["bytes"] and digest(log) == command["sha256"],
                "Command log integrity failure: " + name)
        logs.append(log.read_bytes().decode("utf-8").replace("\r\n", "\n"))
    return report, logs


def formal_hashes(values: dict[str, str]) -> dict[str, str]:
    return {name: value for name, value in values.items() if name.startswith("formal/")
            and (name.endswith(".lean") or PurePosixPath(name).name in
                 {"lean-toolchain", "lake-manifest.json"})}


def check_lean(report: dict, logs: list[str], path: Path, current: dict[str, str]) -> dict:
    """Reconcile native build, axiom and linter evidence with the current proof sources."""
    formal = formal_hashes(current)
    require(formal_hashes(report["source_hashes"]) == formal, "Formal source set differs")
    require(report.get("cache_unchanged") is True, "Native cache guard did not pass")
    require(CORE in report["lean_version"] and "4.34.0-rc2" in report["lean_version"],
            "Wrong native Lean version")
    require("5.0.0-src+6a10ac8" in report["lake_version"], "Wrong native Lake version")
    lock = json.loads((COMMON / "lake-manifest.json").read_bytes())
    require(report["dependencies"] == [{"name": p["name"], "rev": p["rev"]}
                                       for p in lock["packages"]], "Dependency pins differ")
    before, after = path.parent / "cache-before.json", path.parent / "cache-after.json"
    require(before.is_file() and after.is_file() and digest(before) == digest(after),
            "Native cache inventories differ or are missing")
    roots = {"common": COMMON, **{f"q{q}": ROOT / f"formal/cases/q{q}/lean" for q in (2, 3, 4)}}
    expected = {label: module_order(root)[0] for label, root in roots.items()}
    for q in (2, 3, 4):
        roots[f"adapter{q}"] = ROOT / "formal/adapters"
        expected[f"adapter{q}"] = [f"Q{q}"]
    require(report["modules"] == {label: {name: "PASS" for name in names}
                                  for label, names in expected.items()}, "Incomplete module results")
    observed = {label: [] for label in expected}
    closures = {label: {} for label in expected}
    for command, text in zip(report["commands"], logs, strict=True):
        if "-o" not in command["argv"]:
            continue
        require("-DautoImplicit=false" in command["argv"], "Compilation lacks autoImplicit=false")
        cwd = PurePosixPath(command["cwd"].replace("\\", "/"))
        label = cwd.parent.name
        require(cwd.name == "src" and label in roots, "Unexpected compilation environment")
        name = PurePosixPath(command["argv"][-1].replace("\\", "/"))
        require(not name.is_absolute() and ".." not in name.parts and name.suffix == ".lean",
                "Unsafe compiled source name")
        module = name.with_suffix("").as_posix().replace("/", ".")
        require(module in expected[label] and module not in observed[label], "Unexpected/duplicate module")
        require(not re.search(r"\b(?:warning|error):|sorryAx", text), "Failed compiler diagnostic")
        observed[label].append(module)
        closures[label].update(audit(text, (roots[label] / name).read_text(encoding="utf-8-sig")))
    require(all(set(observed[k]) == set(v) for k, v in expected.items()), "Compilation logs are incomplete")
    require(closures == report["axioms"], "Axiom receipt differs from actual logs")
    lint = {}
    require(set(report.get("lint", {})) == set(LINT_PACKAGES), "Missing declaration-lint results")
    commands = {command["log"]: (command, text)
                for command, text in zip(report["commands"], logs, strict=True)}
    for label in LINT_PACKAGES:
        recorded = report["lint"][label]
        require(recorded["log"] in commands, "Missing lint log: " + label)
        command, text = commands[recorded["log"]]
        require(PurePosixPath(command["argv"][-1].replace("\\", "/")).name == f"lint-{label}.lean",
                "Unexpected lint command: " + label)
        summary = lint_summary(text, label)
        require(recorded == dict(summary, log=recorded["log"]), "Lint receipt differs from its log")
        lint[label] = summary
    return {"status": "PASS", "scope": "Native evidence for the identical formal source set; no Lean run by this packager.",
            "report_sha256": digest(path), "validator_sha256": report["source_hashes"]["scripts/validate.py"],
            "finished_utc": report["finished_utc"], "lean_version": report["lean_version"],
            "lake_version": report["lake_version"], "modules": sum(map(len, observed.values())),
            "axiom_reports": sum(map(len, closures.values())), "allowed_axioms": sorted(ALLOW),
            "declaration_lint": lint,
            "formal_source_set_sha256": map_hash(formal), "formal_files": len(formal),
            "cache_inventory_sha256": digest(before),
            "cache_scope": "Unchanged trusted upstream cache; not rebuilt or independently kernel-rechecked."}


def build(lean_path: Path, math_path: Path, paper_path: Path) -> None:
    current = sources()
    lean, logs = load_report(lean_path, "lean")
    native = check_lean(lean, logs, lean_path, current)
    math, _ = load_report(math_path, "math")
    paper, _ = load_report(paper_path, "paper")
    require(math["source_hashes"] == current == paper["source_hashes"],
            "Math and paper reports must cover the complete current source inventory")
    require(math["mathematics"]["status"] == "PASS" and
            json.loads((math_path.parent / "math.json").read_bytes()) == math["mathematics"],
            "Missing or inconsistent finite-checker result")
    paper_inputs = {name.removeprefix("paper/"): value for name, value in current.items()
                    if name.startswith("paper/")}
    require(paper.get("paper_source_hashes") == paper_inputs, "Paper snapshot is not bound to current sources")
    relative = PurePosixPath(paper["pdf"]["path"].replace("\\", "/"))
    require(not relative.is_absolute() and ".." not in relative.parts
            and relative.parts[0] == ".build", "Unsafe PDF path")
    pdf = ROOT / relative
    require(pdf.is_file() and not pdf.is_symlink() and pdf.resolve().is_relative_to(ROOT / ".build"),
            "PDF is not a regular build artifact")
    pdf_bytes = pdf.read_bytes()
    require(pdf_bytes.startswith(b"%PDF-") and len(pdf_bytes) == paper["pdf"]["bytes"]
            and hashlib.sha256(pdf_bytes).hexdigest() == paper["pdf"]["sha256"], "PDF integrity failure")
    receipt = {"schema": 1, "packaging_status": "PASS",
               "source_files_including_manifest": len(current), "source_set_sha256": map_hash(current),
               "source_manifest_sha256": current["SOURCES.tsv"],
               "hash_encoding": "SHA-256 of UTF-8 json.dumps(map, indent=2, sort_keys=True) plus one LF.",
               "lean": native,
               "mathematics": {"report_sha256": digest(math_path), "result": math["mathematics"]},
               "paper": {"report_sha256": digest(paper_path), "path": "dist/main.pdf",
                         "bytes": len(pdf_bytes), "sha256": paper["pdf"]["sha256"],
                         "pages": paper["pdf"].get("pages"), "engine": paper["tex_engine"].splitlines()[0],
                         "visual_inspection": "NOT_PERFORMED_BY_THIS_SCRIPT"}}
    dist = ROOT / "dist"
    require(not dist.is_symlink(), "Refusing a symlinked dist directory")
    dist.mkdir(exist_ok=True)
    (ROOT / ".build").mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="release-", dir=ROOT / ".build") as directory:
        stage = Path(directory)
        (stage / "main.pdf").write_bytes(pdf_bytes)
        (stage / "validation.json").write_bytes(json_bytes(receipt))
        with zipfile.ZipFile(stage / "schreier-release.zip", "w", compression=zipfile.ZIP_DEFLATED) as archive:
            payloads = {name: ROOT / name for name in current}
            payloads.update({"dist/main.pdf": stage / "main.pdf", "dist/validation.json": stage / "validation.json"})
            for name, path in sorted(payloads.items()):
                raw = path.read_bytes()
                if name in current:
                    require(hashlib.sha256(raw).hexdigest() == current[name], "Source changed while packaging")
                info = zipfile.ZipInfo(name, date_time=(1980, 1, 1, 0, 0, 0))
                info.compress_type = zipfile.ZIP_DEFLATED
                info.external_attr = 0o100644 << 16
                archive.writestr(info, raw)
        require(sources() == current, "Source set changed while packaging")
        for name in ("main.pdf", "validation.json", "schreier-release.zip"):
            destination = dist / name
            require(not destination.is_symlink() and (not destination.exists() or destination.is_file()),
                    "Refusing a non-regular release destination")
        for name in ("main.pdf", "validation.json", "schreier-release.zip"):
            os.replace(stage / name, dist / name)
    print("PASS: dist/schreier-release.zip")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-report", type=Path, required=True)
    parser.add_argument("--math-report", type=Path, required=True)
    parser.add_argument("--paper-report", type=Path, required=True)
    args = parser.parse_args()
    try:
        build(args.lean_report, args.math_report, args.paper_report)
    except (OSError, ValueError, RuntimeError, KeyError, TypeError) as error:
        print("FAIL: " + str(error), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
