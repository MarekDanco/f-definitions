from pylatexenc.latex2text import LatexNodes2Text
import re
import sys


def extract_abstract(filepath):
    with open(filepath, "r") as f:
        content = f.read()

    match = re.search(r"\\begin\{abstract\}(.*?)\\end\{abstract\}", content, re.DOTALL)
    if not match:
        print("No abstract found.")
        sys.exit(1)

    abstract_latex = match.group(1).strip()
    abstract_text = LatexNodes2Text().latex_to_text(abstract_latex)

    # Remove newlines and collapse whitespace
    abstract_clean = " ".join(abstract_text.split())
    print(abstract_clean)


if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python extract_abstract.py yourfile.tex")
        sys.exit(1)
    extract_abstract(sys.argv[1])
