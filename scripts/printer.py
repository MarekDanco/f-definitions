#!/usr/bin/env -S python3 -u
"""Various SMT pretty printers."""

import argparse
from functools import cache
from pathlib import Path

import z3


def write_dot(filepath, assertions, lits):
    input_path = Path(filepath)
    output_path = input_path.with_suffix(".dot")
    output_path.parent.mkdir(parents=True, exist_ok=True)

    printer = BoolStructPrinter(assertions)
    with open(output_path, "w") as f:
        f.write(printer.to_dotformat(literals=lits))
    print(f"DOT written to: {output_path}")


@cache
def has_quantifiers(expr):
    if z3.is_quantifier(expr):
        return True
    return any(has_quantifiers(c) for c in expr.children())


def quantified(assertions):
    res = []
    for a in assertions:
        if has_quantifiers(a):
            res.append(a)
    return res


class BoolStructPrinter:
    """
    Get the boolean structure of a formula. Requires the formula
    is in NNF, otherwise the output is wrong.
    """

    def __init__(self, assertions) -> None:
        self.assertions = assertions
        self.node_counter = 0
        self.edges = []
        self.nodes = []

    def to_dotformat(self, literals=False):
        """Generate dot format"""
        self.node_counter = 0
        self.edges = []
        self.nodes = []

        root_id = self.node_counter
        self.node_counter += 1
        self.nodes.append((root_id, "assertions"))

        for assertion in self.assertions:
            assertion_id = self._traverse_dot(assertion, literals)
            self.edges.append((root_id, assertion_id))

        dot = "digraph combined_assertions {\n"
        dot += "  node [shape=box];\n"
        dot += f'  {root_id} [label="assertions", shape=ellipse];\n'

        for node_id, label in self.nodes:
            if node_id != root_id:
                dot += f'  {node_id} [label="{label}"];\n'
        for parent, child in self.edges:
            dot += f"  {parent} -> {child};\n"
        dot += "}"
        return dot

    def _traverse_dot(self, expr, literals):
        current_id = self.node_counter
        self.node_counter += 1
        if z3.is_quantifier(expr):
            label = "exists" if expr.is_exists() else "forall"
            self.nodes.append((current_id, label))
            child_id = self._traverse_dot(expr.body(), literals)
            self.edges.append((current_id, child_id))
        elif z3.is_and(expr):
            self.nodes.append((current_id, "and"))
            for child in expr.children():
                child_id = self._traverse_dot(child, literals)
                self.edges.append((current_id, child_id))
        elif z3.is_or(expr):
            self.nodes.append((current_id, "or"))
            for child in expr.children():
                child_id = self._traverse_dot(child, literals)
                self.edges.append((current_id, child_id))
        elif z3.is_not(expr):
            self.nodes.append((current_id, "not"))
            child_id = self._traverse_dot(expr.arg(0), literals)
            self.edges.append((current_id, child_id))
        else:
            if literals:
                self.nodes.append((current_id, f"{expr}"))
            else:
                self.nodes.append((current_id, ""))
        return current_id

    def to_sexpr(self):
        """Return the s-expression of a formula with only selected nodes"""
        return "\n".join(self._traverse(assertion) for assertion in self.assertions)

    def _traverse(self, expr):
        if z3.is_quantifier(expr):
            quantifier = "exists" if expr.is_exists() else "forall"
            return f"({quantifier} {self._traverse(expr.body())})"
        elif z3.is_and(expr):
            children = " ".join(self._traverse(child) for child in expr.children())
            return f"(and {children})"
        elif z3.is_or(expr):
            children = " ".join(self._traverse(child) for child in expr.children())
            return f"(or {children})"
        elif z3.is_not(expr):
            return f"(not {self._traverse(expr.arg(0))})"
        else:
            return "()"


def main():
    parser = argparse.ArgumentParser(
        description="Create a dotformat of the boolean structure of a formula"
    )
    parser.add_argument("input_file", help="Input SMT file visualize")
    parser.add_argument(
        "--quantified_only", help="Input SMT file visualize", action="store_true"
    )
    parser.add_argument(
        "--literals", help="Include literals in leaves", action="store_true"
    )
    args = parser.parse_args()

    input_path = Path(args.input_file).resolve()

    if not input_path.exists():
        print(f"Error: File '{args.input_file}' does not exist")
        return 1

    if not input_path.suffix.lower() == ".smt2":
        print("Error: File must have .smt2 extension")
        return 1

    s = z3.Solver()
    s.from_file(str(input_path))
    assertions = quantified(s.assertions()) if args.quantified_only else s.assertions()
    write_dot(input_path, assertions, args.literals)


if __name__ == "__main__":
    main()
