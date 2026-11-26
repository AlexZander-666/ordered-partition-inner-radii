"""Rebuild the manuscript twice from loose source and twice from its source ZIP."""

import hashlib
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
from tempfile import TemporaryDirectory
from zipfile import ZIP_DEFLATED, ZipFile, ZipInfo


ROOT = Path(__file__).resolve().parent
CHECKS = ("anc/check_inner_edge.py",)
MEMBERS = ("main.tex", "README.md", "reproduce.py", "anc/exact-signs.json", *CHECKS)
EPOCH = "1795737600"


def compile_pdf(folder, executable, label):
    env = dict(os.environ, SOURCE_DATE_EPOCH=EPOCH, FORCE_SOURCE_DATE="1", TZ="UTC")
    for pass_num in (1, 2):
        run = subprocess.run(
            [executable, "-no-shell-escape", "-interaction=nonstopmode", "-halt-on-error",
             "-file-line-error", "main.tex"],
            cwd=folder,
            env=env,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
        )
        if run.returncode:
            raise RuntimeError(run.stdout.decode(errors="replace"))
        print(f"{label} pass {pass_num}: exit 0")
    log = (folder / "main.log").read_text()
    warnings = re.findall(r"^(?:Overfull|Missing character|LaTeX Warning|Package \S+ Warning).*", log, re.M)
    if warnings:
        raise RuntimeError("\n".join(warnings))
    return (folder / "main.pdf").read_bytes()


def run_checks(source, cwd):
    for name in CHECKS:
        run = subprocess.run(
            [sys.executable, "-B", "-E", str(source / name)],
            cwd=cwd,
            check=True,
            capture_output=True,
            text=True,
        )
        print(f"Extracted {name} from a separate working directory:")
        if run.stdout.strip() != (source / "anc/exact-signs.json").read_text().strip():
            raise RuntimeError("Exact sign records differ from the included certificate")
        print("All 18 exact sign brackets reproduced.")


def main():
    local_tex = Path.home() / ".cache/spark-math-research/texlive/2026/bin/aarch64-linux/pdflatex"
    executable = os.environ.get("PDFLATEX") or shutil.which("pdflatex")
    if not executable and local_tex.is_file():
        executable = str(local_tex)
    if not executable:
        raise SystemExit("Install TeX Live 2026 or set PDFLATEX to its executable.")
    executable = str(Path(executable).expanduser().absolute())

    files = {name: (ROOT / name).read_bytes() for name in MEMBERS}
    with TemporaryDirectory(prefix=".inner-edge-build-", dir=ROOT) as work:
        folder = Path(work)
        loose = folder / "loose"
        archive_source = folder / "archive-source"
        check_cwd = folder / "check-cwd"
        loose.mkdir()
        archive_source.mkdir()
        check_cwd.mkdir()
        archive = folder / "arxiv-source.zip"
        with ZipFile(archive, "w") as zipped:
            for name, data in files.items():
                member = ZipInfo(name, (2026, 11, 27, 0, 0, 0))
                member.external_attr = 0o100644 << 16
                zipped.writestr(member, data, ZIP_DEFLATED)
                path = loose / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(data)
        with ZipFile(archive) as zipped:
            if zipped.testzip() is not None or tuple(zipped.namelist()) != MEMBERS:
                raise RuntimeError("Unexpected source archive members or invalid CRC")
            zipped.extractall(archive_source)
        if any((archive_source / name).read_bytes() != data for name, data in files.items()):
            raise RuntimeError("Extracted source differs from the loose source")
        pdf = compile_pdf(loose, executable, "loose source")
        if compile_pdf(archive_source, executable, "source ZIP") != pdf:
            raise RuntimeError("Compiling the extracted source changed the PDF bytes")
        run_checks(archive_source, check_cwd)
        staged = folder / "main.pdf"
        staged.write_bytes(pdf)
        staged.replace(ROOT / "main.pdf")
        archive.replace(ROOT / "arxiv-source.zip")

    print("Both clean builds produced the same PDF bytes. ZIP contents and CRCs checked.")
    for name in ("main.pdf", "arxiv-source.zip", *MEMBERS):
        data = (ROOT / name).read_bytes()
        print(f"{hashlib.sha256(data).hexdigest()}  {name}")


if __name__ == "__main__":
    main()
