"""Build chapter pages and graphs, plus the overall dependency graph."""

from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


def main():
    source = Path(__file__).resolve().parent
    output = source.parent / "web"
    plastex = Path(sys.executable).with_name("plastex")
    command = [str(plastex), "-c", "plastex.cfg"]

    # Keep the chapter navigation and individual graphs in the published site.
    subprocess.run([*command, "--dir", str(output), "web.tex"], cwd=source, check=True)

    # Build the same document with one graph containing all chapters.
    # Change only a temporary copy, so checked-in sources stay untouched.
    with tempfile.TemporaryDirectory(prefix="blueprint-overall-") as directory:
        temporary = Path(directory)
        overall_source = temporary / "src"
        shutil.copytree(source, overall_source)
        macros = overall_source / "macros" / "web.tex"
        contents = macros.read_text(encoding="utf-8")
        option = "dep_by=chapter,"
        if contents.count(option) != 1:
            raise RuntimeError("Expected one dep_by=chapter option in macros/web.tex")
        macros.write_text(contents.replace(option, ""), encoding="utf-8")
        overall_output = temporary / "web"
        subprocess.run(
            [*command, "--dir", str(overall_output), "web.tex"],
            cwd=overall_source,
            check=True,
        )
        shutil.copy2(overall_output / "dep_graph_document.html", output)


if __name__ == "__main__":
    main()
