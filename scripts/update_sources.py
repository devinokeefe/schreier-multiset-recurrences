#!/usr/bin/env python3
"""Refresh the source inventory after intentional, reviewed edits."""
from __future__ import annotations

import csv
import io
import os
from pathlib import Path
import re

from validate import IGNORED, ROOT, digest, entries, require, sources


def main() -> None:
    previous = {row["path"]: row for row in entries()}
    current = {}
    for parent, dirs, files in os.walk(ROOT):
        dirs[:] = sorted(d for d in dirs if d not in IGNORED
                         and not (Path(parent) == ROOT and d == "dist"))
        require(all(not (Path(parent) / d).is_symlink() for d in dirs),
                "Symlinked source directory")
        for filename in sorted(files):
            path = Path(parent) / filename
            name = path.relative_to(ROOT).as_posix()
            if name == "SOURCES.tsv":
                continue
            require(bool(re.fullmatch(r"[A-Za-z0-9_./-]+", name)),
                    "Unsupported source filename: " + name)
            require(path.is_file() and not path.is_symlink(), "Non-regular source: " + name)
            origin = previous.get(name, {}).get("origin", "new")
            data = path.read_bytes()
            if origin == "new":
                data.decode("utf-8", errors="strict")
                require(not data.startswith(b"\xef\xbb\xbf") and b"\r" not in data
                        and data.endswith(b"\n") and not data.endswith(b"\n\n"),
                        "Expected UTF-8, no BOM, LF, one final newline: " + name)
            current[name] = {"origin": origin, "path": name,
                             "bytes": str(len(data)), "sha256": digest(path)}
    output = io.StringIO(newline="")
    writer = csv.DictWriter(output, fieldnames=["origin", "path", "bytes", "sha256"],
                            delimiter="\t", lineterminator="\n")
    writer.writeheader()
    writer.writerows(current[name] for name in sorted(current))
    for name in sorted(previous.keys() | current.keys()):
        if name not in previous:
            print("Added: " + name)
        elif name not in current:
            print("Removed: " + name)
        elif previous[name] != current[name]:
            print("Updated: " + name)
    (ROOT / "SOURCES.tsv").write_bytes(output.getvalue().encode("utf-8"))
    sources()
    print(f"Inventoried {len(current)} files; review the changes before committing.")


if __name__ == "__main__":
    main()
