#!/usr/bin/env python3
"""Validate source integrity, Lean proofs, declaration lint, finite checks and the paper."""
from __future__ import annotations

import argparse
import csv
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import uuid

ROOT = Path(__file__).resolve().parents[1]
COMMON = ROOT / "formal/common"
CORE = "6a10ac8c22beadecabdbb0919c2b50214762f91d"
ALLOW = {"propext", "Classical.choice", "Quot.sound"}
NAME = r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*"
IGNORED = {".build", ".lake", ".git", "__pycache__"}
LINT_IMPORTS = {
    "common": ["SchreierUnified.Audit"],
    "q2": ["Q2", "SchreierQ2.Check"],
    "q3": ["Q3", "Audit", "SchreierQ3"],
    "q4": ["Q4", "Audit"],
}
LINT_PACKAGES = {
    "common": ["SchreierUnified"],
    "q2": ["SchreierQ2", "Statement", "Q2"],
    "q3": ["Statement", "SourceBasics", "Compositions", "Encoding", "Bridge",
           "RecurrenceAlgebra", "Main", "Examples", "Q3"],
    "q4": ["SchreierQ4", "Statement", "Q4"],
}


def require(ok: bool, message: str) -> None:
    if not ok:
        raise RuntimeError(message)


def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def write_json(path: Path, value: object) -> None:
    path.write_bytes((json.dumps(value, indent=2, sort_keys=True) + "\n").encode("utf-8"))


def entries(root: Path = ROOT) -> list[dict[str, str]]:
    """Read the source inventory and reject malformed or ambiguous entries."""
    path = root / "SOURCES.tsv"
    require(path.is_file() and not path.is_symlink(), "Non-regular source manifest")
    raw = path.read_bytes()
    require(b"\r" not in raw and raw.endswith(b"\n"), "Invalid source manifest encoding")
    rows = list(csv.DictReader(raw.decode("utf-8").splitlines(), delimiter="\t"))
    require(bool(rows) and set(rows[0]) == {"origin", "path", "bytes", "sha256"}, "Invalid manifest fields")
    names: set[str] = set()
    for row in rows:
        name = row["path"]
        require(bool(re.fullmatch(r"[A-Za-z0-9_./-]+", name)) and not Path(name).is_absolute()
                and ".." not in Path(name).parts and name not in names, "Unsafe/duplicate source path")
        require(bool(re.fullmatch(r"[0-9a-f]{64}", row["sha256"])), "Invalid source digest")
        require(row["bytes"].isdigit(), "Invalid byte length")
        names.add(name)
    return rows


def sources(root: Path = ROOT) -> dict[str, str]:
    """Check every distributed source against the manifest and return its digest."""
    rows = entries(root)
    found: set[str] = set()
    for parent, dirs, files in os.walk(root):
        dirs[:] = sorted(d for d in dirs if d not in IGNORED
                         and not (Path(parent) == root and d == "dist"))
        require(all(not (Path(parent) / d).is_symlink() for d in dirs), "Symlinked source directory")
        for name in files:
            relative = (Path(parent) / name).relative_to(root).as_posix()
            if relative != "SOURCES.tsv":
                found.add(relative)
    require(found == {row["path"] for row in rows},
            "Source inventory mismatch: " + repr(found ^ {row["path"] for row in rows}))
    result = {"SOURCES.tsv": digest(root / "SOURCES.tsv")}
    for row in rows:
        path = root / row["path"]
        require(path.is_file() and not path.is_symlink(), "Non-regular source: " + row["path"])
        require(path.stat().st_size == int(row["bytes"]) and digest(path) == row["sha256"],
                "Source integrity failure: " + row["path"])
        if row["origin"] == "new":
            raw = path.read_bytes()
            raw.decode("utf-8", errors="strict")
            require(not raw.startswith(b"\xef\xbb\xbf") and b"\r" not in raw
                    and raw.endswith(b"\n") and not raw.endswith(b"\n\n"),
                    "Expected UTF-8, no BOM, LF, exactly one final newline: " + row["path"])
        result[row["path"]] = row["sha256"]
    return result


def lean_text(text: str) -> str:
    """Remove nested Lean comments and string literals for the escape-token check."""
    out, i, depth, string = [], 0, 0, False
    while i < len(text):
        pair, char = text[i:i + 2], text[i]
        if depth:
            if pair == "/-":
                depth += 1
                i += 2
            elif pair == "-/":
                depth -= 1
                i += 2
            else:
                out.append("\n" if char == "\n" else " ")
                i += 1
        elif string:
            if char == "\\":
                i += 2
            elif char == '"':
                string = False
                i += 1
            else:
                out.append("\n" if char == "\n" else " ")
                i += 1
        elif pair == "/-":
            depth = 1
            out.append(" ")
            i += 2
        elif pair == "--":
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        elif char == '"':
            string = True
            out.append(" ")
            i += 1
        else:
            out.append(char)
            i += 1
    require(depth == 0 and not string, "Unclosed Lean comment/string")
    return "".join(out)


def module_order(root: Path) -> tuple[list[str], dict[str, list[str]]]:
    """Order local modules by imports; reject cycles and proof escape declarations."""
    modules = {p.relative_to(root).with_suffix("").as_posix().replace("/", "."): p
               for p in root.rglob("*.lean") if p.name != "lakefile.lean"
               and not any(part in IGNORED for part in p.relative_to(root).parts)}
    deps: dict[str, list[str]] = {}
    for name, path in modules.items():
        text = lean_text(path.read_text(encoding="utf-8-sig"))
        require(not re.search(r"\b(sorry|admit|axiom|constant|unsafe|native_decide|implemented_by|extern)\b", text),
                "Disallowed Lean escape/declaration: " + str(path.relative_to(ROOT)))
        imports = [token for line in re.findall(r"^\s*import\s+([^\n]+)", text, re.M)
                   for token in line.split()]
        deps[name] = [item for item in imports if item in modules]
    ordered: list[str] = []
    while len(ordered) < len(modules):
        ready = sorted(name for name in modules if name not in ordered
                       and all(dep in ordered for dep in deps[name]))
        require(bool(ready), "Local import cycle")
        ordered.extend(ready)
    return ordered, deps


def audit(text: str, source: str) -> dict[str, list[str]]:
    """Match each requested signature and axiom report to the compiler's output."""
    expected = re.findall(r"^#print axioms (" + NAME + r")\s*$", source, re.M)
    pattern = r"'(" + NAME + r")'\s+(?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])"
    matches = list(re.finditer(pattern, text))
    require([m[1] for m in matches] == expected, "Missing, duplicate or unexpected axiom report")
    result = {}
    for match in matches:
        tokens = [] if not match[2] or not match[2].strip() else match[2].split(",")
        names = [re.sub(r"\.\{u\}$", "", token.strip()) for token in tokens]
        require(len(names) == len(set(names)) and set(names) <= ALLOW, "Unauthorized axiom closure")
        result[match[1]] = names
    require("sorryAx" not in text and "⋯" not in text, "Omitted term or proof escape in audit")
    checked = re.findall(r"^#check\s+\(?@?(" + NAME + r")(?=\s|$)", source, re.M)
    checked += re.findall(r"^#print sig (" + NAME + r")\s*$", source, re.M)
    checked += re.findall(r"^#print (?!axioms\b|sig\b)(" + NAME + r")\s*$", source, re.M)
    header = (r"^(?:@\[[^\n]*\]\s*)?(?:(?:theorem|def|abbrev)\s+)?@?(" + NAME +
              r")(?:\.\{[^}\n]*\})?(?=\s*(?:[:({]|$))")
    observed = Counter(re.findall(header, text, re.M))
    require(all(observed[name] >= count for name, count in Counter(checked).items()),
            "Missing signature/definition header")
    return result


class Runner:
    """Record commands and artifacts in a separate directory for each validation run."""
    def __init__(self, phase: str, dependencies: Path | None = None, tectonic: str | None = None):
        self.directory = ROOT / ".build" / (phase + "-" + uuid.uuid4().hex)
        self.directory.mkdir(parents=True)
        self.report: dict = {"phase": phase, "status": "FAIL", "commands": [],
                             "started_utc": datetime.now(timezone.utc).isoformat()}
        self.dependency_project = dependencies.resolve() if dependencies else COMMON
        self.tectonic = str(Path(shutil.which(tectonic) or tectonic).expanduser().resolve()) if tectonic else None
        self.env = dict(os.environ)
        for key in ("LEAN_PATH", "LEAN_SRC_PATH", "ELAN_TOOLCHAIN", "LEAN_SYSROOT", "LAKE", "LAKE_HOME"):
            self.env.pop(key, None)
        self.env.update(LEAN_NUM_THREADS="1", GIT_OPTIONAL_LOCKS="0",
                        MATHLIB_CACHE_DIR=str(ROOT / ".build/mathlib-downloads"))

    def run(self, command: list[str], cwd: Path = ROOT, env: dict | None = None,
            strict: bool = True) -> tuple[int, str]:
        number = len(self.report["commands"])
        try:
            proc = subprocess.run(command, cwd=cwd, env=env or self.env, stdout=subprocess.PIPE,
                                  stderr=subprocess.STDOUT, check=False)
            code, raw = proc.returncode, proc.stdout
        except OSError as error:
            code, raw = 127, str(error).encode("utf-8")
        name = f"{number:03d}.log"
        (self.directory / name).write_bytes(raw)
        self.report["commands"].append({"argv": command, "cwd": str(cwd), "exit_code": code,
                                        "log": name, "bytes": len(raw),
                                        "sha256": hashlib.sha256(raw).hexdigest()})
        self.save()
        text = raw.decode("utf-8", errors="strict").replace("\r\n", "\n")
        if strict:
            require(code == 0, "Command failed; see " + str(self.directory / name) + "\n" + text[-4000:])
        return code, text

    def save(self) -> None:
        write_json(self.directory / "validation.json", self.report)


def pins(runner: Runner) -> list[Path]:
    lock = json.loads((COMMON / "lake-manifest.json").read_bytes())
    packages = lock["packages"]
    require(len(packages) == 9 and len({p["name"] for p in packages}) == 9, "Wrong package inventory")
    roots = []
    for package in packages:
        require(package["type"] == "git" and not package.get("subDir"), "Unsupported dependency layout")
        path = runner.dependency_project / lock["packagesDir"] / package["name"]
        _, head = runner.run(["git", "rev-parse", "HEAD"], path)
        require(head.strip() == package["rev"], "Wrong dependency revision: " + package["name"])
        runner.run(["git", "diff", "--exit-code", "HEAD", "--"], path)
        roots.append(path)
    runner.report["dependencies"] = [{"name": p["name"], "rev": p["rev"]} for p in packages]
    for case in (2, 3):
        old = json.loads((ROOT / f"formal/cases/q{case}/lean/lake-manifest.json").read_text(encoding="utf-8-sig"))
        require({p["name"]: p["rev"] for p in old["packages"]}
                == {p["name"]: p["rev"] for p in packages}, "Case dependency pins differ")
    return roots


def versions(runner: Runner) -> Path:
    require(shutil.which("lake") is not None, "Lake is not installed/on PATH; no Lean validation ran")
    require(shutil.which("lean") is not None, "Lean is not installed/on PATH; no Lean validation ran")
    _, lake = runner.run(["lake", "--version"], COMMON)
    require("5.0.0-src+6a10ac8" in lake, "Wrong Lake version")
    _, lean = runner.run(["lean", "--version"], COMMON)
    require("4.34.0-rc2" in lean and CORE in lean, "Wrong Lean version/commit")
    _, prefix = runner.run(["lean", "--print-prefix"], COMMON)
    executable = Path(prefix.strip()) / "bin" / ("lean.exe" if os.name == "nt" else "lean")
    require(executable.is_file(), "Cannot resolve the pinned native Lean executable")
    runner.report.update(lean_version=lean.strip(), lake_version=lake.strip())
    return executable


def cache_inventory(roots: list[Path], local_modules: set[str]) -> dict[str, dict]:
    inventory = {}
    for root in roots:
        for module in local_modules:
            require(not (root / (module.replace(".", "/") + ".olean")).exists(),
                    "Upstream cache shadows a local module: " + module)
        require(not root.is_symlink(), "Symlinked upstream cache root")
        files = {}
        if root.exists():
            for parent, dirs, names in os.walk(root):
                for name in dirs + names:
                    require(not (Path(parent) / name).is_symlink(), "Symlinked upstream cache entry")
                for name in sorted(names):
                    path = Path(parent) / name
                    files[path.relative_to(root).as_posix()] = [path.stat().st_size, digest(path)]
        inventory[str(root)] = {"present": root.exists(), "files": files}
    return inventory


def compile_tree(runner: Runner, label: str, source: Path, lean: Path,
                 upstream: list[Path]) -> tuple[Path, bool]:
    """Compile a fresh source snapshot without reusing local proof objects."""
    order, deps = module_order(source)
    snapshot, out = runner.directory / label / "src", runner.directory / label / "lib"
    snapshot.mkdir(parents=True)
    out.mkdir()
    for module in order:
        name = module.replace(".", "/") + ".lean"
        (snapshot / name).parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source / name, snapshot / name)
    env = dict(runner.env, LEAN_PATH=os.pathsep.join(map(str, [out] + upstream)))
    status, closures = {}, {}
    for module in order:
        if any(status[dep] != "PASS" for dep in deps[module]):
            status[module] = "BLOCKED"
            continue
        name = module.replace(".", "/") + ".lean"
        target = out / (module.replace(".", "/") + ".olean")
        target.parent.mkdir(parents=True, exist_ok=True)
        command = [str(lean), "-DautoImplicit=false", "-o", str(target), name]
        code, text = runner.run(command, snapshot, env, strict=False)
        ok = code == 0 and target.is_file() and not re.search(r"\b(?:warning|error):|sorryAx", text)
        if ok:
            try:
                closures.update(audit(text, (snapshot / name).read_text(encoding="utf-8-sig")))
            except RuntimeError as error:
                runner.report.setdefault("audit_errors", []).append(label + "/" + module + ": " + str(error))
                ok = False
        status[module] = "PASS" if ok else "FAIL"
    for module in order:
        name = module.replace(".", "/") + ".lean"
        require(digest(snapshot / name) == digest(source / name), "Compile snapshot changed: " + name)
    runner.report.setdefault("modules", {})[label] = status
    runner.report.setdefault("axioms", {})[label] = closures
    runner.save()
    return out, all(value == "PASS" for value in status.values())


def lint_summary(text: str, label: str) -> dict:
    """Require a clean result for every package in a declaration-lint invocation."""
    pattern = (r"^-- Found (\d+) errors? in (\d+) declarations \(plus (\d+) "
               r"automatically generated ones\) in (\S+) with (\d+) linters$")
    matches = re.findall(pattern, text, re.M)
    require([m[3] for m in matches] == LINT_PACKAGES[label], "Incomplete declaration lint: " + label)
    require(all(int(m[0]) == 0 and int(m[1]) > 0 and int(m[4]) == 15 for m in matches),
            "Declaration lint failed: " + label)
    require(not re.search(r"\b(?:warning|error):|LINTER FAILED", text),
            "Linter diagnostic: " + label)
    return {"status": "PASS", "linters": 15, "packages": LINT_PACKAGES[label],
            "declarations": sum(int(m[1]) for m in matches),
            "generated_declarations": sum(int(m[2]) for m in matches)}


def lint_tree(runner: Runner, label: str, lean: Path, imports: list[Path]) -> bool:
    """Run all default declaration linters, including slow checks, on the built modules."""
    source = runner.directory / f"lint-{label}.lean"
    # The umbrella import makes the complete linter set available in this check only.
    lines = ["import Mathlib"] + ["import " + name for name in LINT_IMPORTS[label]]
    lines += [""] + ["#lint+ in " + name for name in LINT_PACKAGES[label]]
    source.write_text("\n".join(lines) + "\n", encoding="utf-8", newline="\n")
    env = dict(runner.env, LEAN_PATH=os.pathsep.join(map(str, imports)))
    code, text = runner.run([str(lean), str(source)], runner.directory, env, strict=False)
    result = {"status": "FAIL", "log": runner.report["commands"][-1]["log"]}
    try:
        require(code == 0, "Linter command failed: " + label)
        result.update(lint_summary(text, label))
    except RuntimeError as error:
        result["error"] = str(error)
    runner.report.setdefault("lint", {})[label] = result
    runner.save()
    return result["status"] == "PASS"


def lean_phase(runner: Runner) -> None:
    lean = versions(runner)
    repositories = pins(runner)
    upstream = [p / ".lake/build/lib/lean" for p in repositories]
    require((upstream[0] / "Mathlib.olean").is_file(), "Mathlib cache absent; run the deps command first")
    source_roots = [COMMON] + [ROOT / f"formal/cases/q{q}/lean" for q in (2, 3, 4)]
    local = {m for root in source_roots for m in module_order(root)[0]} | {"Q2", "Q3", "Q4"}
    before = cache_inventory(upstream, local)
    write_json(runner.directory / "cache-before.json", before)
    passed = False
    try:
        common_out, common_ok = compile_tree(runner, "common", COMMON, lean, upstream)
        passed = common_ok
        if common_ok:
            passed = lint_tree(runner, "common", lean, [common_out] + upstream) and passed
        for q in (2, 3, 4):
            case_out, case_ok = compile_tree(runner, f"q{q}", ROOT / f"formal/cases/q{q}/lean",
                                             lean, upstream)
            passed = passed and case_ok
            if common_ok and case_ok:
                adapter = runner.directory / f"adapter{q}-source"
                adapter.mkdir()
                shutil.copyfile(ROOT / f"formal/adapters/Q{q}.lean", adapter / f"Q{q}.lean")
                adapter_out, adapter_ok = compile_tree(runner, f"adapter{q}", adapter, lean,
                                                       [common_out, case_out] + upstream)
                passed = passed and adapter_ok
                if adapter_ok:
                    lint_ok = lint_tree(runner, f"q{q}", lean,
                                        [adapter_out, common_out, case_out] + upstream)
                    passed = passed and lint_ok
            else:
                runner.report.setdefault("modules", {})[f"adapter{q}"] = {f"Q{q}": "BLOCKED"}
                passed = False
    finally:
        after = cache_inventory(upstream, local)
        write_json(runner.directory / "cache-after.json", after)
        runner.report["cache_unchanged"] = after == before
        require(after == before, "Upstream cache changed during proof checking")
        pins(runner)
    require(passed, "A module, adapter, audit or declaration lint failed; inspect the command logs")


def paper_phase(runner: Runner) -> None:
    snapshot = runner.directory / "paper/src"
    out = runner.directory / "paper/out"
    snapshot.mkdir(parents=True)
    out.mkdir()
    inputs = {}
    for path in sorted((ROOT / "paper").rglob("*")):
        relative = path.relative_to(ROOT / "paper")
        if path.is_file() and not any(part in IGNORED for part in relative.parts):
            inputs[relative.as_posix()] = digest(path)
            target = snapshot / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(path, target)
    tectonic = runner.tectonic or shutil.which("tectonic")
    if tectonic:
        tectonic = str(Path(tectonic).resolve())
        runner.run([tectonic, "--untrusted", "--keep-logs", "--keep-intermediates",
                    "--outdir", str(out), "main.tex"], snapshot)
        _, engine = runner.run([tectonic, "--version"])
        runner.report["tex_engine"] = engine.strip()
    else:
        require(shutil.which("latexmk") is not None, "Tectonic or latexmk is required")
        bibtex = next((name for name in ("bibtex", "bibtex8", "bibtexu", "bibtex.original")
                       if shutil.which(name)), None)
        require(bibtex is not None, "A BibTeX-compatible executable is required")
        runner.run(["latexmk", "-g", "-pdf", "-interaction=nonstopmode", "-halt-on-error", "-file-line-error",
                    "-e", '$bibtex = "' + bibtex + ' %O %B";', "-outdir=" + str(out), "main.tex"], snapshot)
        runner.run(["latexmk", "-v"])
        _, engine = runner.run(["pdflatex", "--version"])
        runner.report["tex_engine"] = engine.strip()
    require(all(digest(snapshot / name) == value == digest(ROOT / "paper" / name)
                for name, value in inputs.items()), "Paper source snapshot changed")
    runner.report["paper_source_hashes"] = inputs
    log = (out / "main.log").read_text(encoding="utf-8", errors="replace")
    require(not re.search(r"Overfull|Underfull|LaTeX Warning|Package \S+ Warning|undefined", log),
            "TeX layout/reference warning; inspect the final log")
    pdf = out / "main.pdf"
    require(pdf.is_file(), "No final PDF")
    runner.report["pdf"] = {"path": pdf.relative_to(ROOT).as_posix(), "bytes": pdf.stat().st_size,
                              "sha256": digest(pdf), "visual_inspection": "NOT_PERFORMED_BY_THIS_SCRIPT"}
    if shutil.which("pdfinfo"):
        _, info = runner.run(["pdfinfo", str(pdf)])
        match = re.search(r"^Pages:\s+(\d+)$", info, re.M)
        require(match is not None, "Cannot determine PDF page count")
        runner.report["pdf"]["pages"] = int(match[1])


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("phase", choices=("sources", "deps", "math", "lean", "paper", "all"))
    parser.add_argument("--dependencies", type=Path,
                        help="Read-only existing Lake project containing the exact pinned .lake/packages")
    parser.add_argument("--tectonic", help="Tectonic executable path; otherwise use PATH or latexmk")
    args = parser.parse_args()
    runner = Runner(args.phase, args.dependencies, args.tectonic)
    before = None
    try:
        before = sources()
        runner.report["source_hashes"] = before
        if args.phase == "deps":
            require(runner.dependency_project == COMMON, "deps only installs into formal/common; omit --dependencies")
            require(shutil.which("lake") is not None, "Install the documented pinned Lean toolchain first")
            runner.run(["lake", "exe", "cache", "get"], COMMON)
            versions(runner)
            pins(runner)
        phase_errors = []
        for phase in (("math", "lean", "paper") if args.phase == "all" else (args.phase,)):
            try:
                if phase == "math":
                    result = runner.directory / "math.json"
                    runner.run([sys.executable, "scripts/check.py", "--output", str(result)])
                    runner.report["mathematics"] = json.loads(result.read_bytes())
                    require(runner.report["mathematics"].get("status") == "PASS", "Checker did not report PASS")
                elif phase == "lean":
                    lean_phase(runner)
                elif phase == "paper":
                    paper_phase(runner)
                runner.report.setdefault("phases", {})[phase] = "PASS"
            except (OSError, ValueError, RuntimeError) as error:
                runner.report.setdefault("phases", {})[phase] = "FAIL"
                phase_errors.append(phase + ": " + str(error))
        require(not phase_errors, "\n".join(phase_errors))
        runner.report["status"] = "PASS"
    except (OSError, ValueError, RuntimeError) as error:
        runner.report["error"] = str(error)
        runner.report["status"] = "FAIL"
    finally:
        try:
            require(before is not None and sources() == before, "Source guard failed before/after execution")
            runner.report["sources_unchanged"] = True
        except (OSError, ValueError, RuntimeError) as error:
            runner.report["source_guard_error"] = str(error)
            runner.report["status"] = "FAIL"
        runner.report["finished_utc"] = datetime.now(timezone.utc).isoformat()
        runner.save()
    print(runner.report["status"] + ": " + str(runner.directory / "validation.json"))
    if "error" in runner.report:
        print(runner.report["error"], file=sys.stderr)
    return 0 if runner.report["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
