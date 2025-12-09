#!/usr/bin/env -S python3 -u
"""Various SMT pretty printers."""

import z3


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

    def to_dotformat(self):
        """Generate dot format"""
        self.node_counter = 0
        self.edges = []
        self.nodes = []

        root_id = self.node_counter
        self.node_counter += 1
        self.nodes.append((root_id, "assertions"))

        for assertion in self.assertions:
            assertion_id = self._traverse_dot(assertion)
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

    def _traverse_dot(self, expr):
        current_id = self.node_counter
        self.node_counter += 1
        if z3.is_quantifier(expr):
            label = "exists" if expr.is_exists() else "forall"
            self.nodes.append((current_id, label))
            child_id = self._traverse_dot(expr.body())
            self.edges.append((current_id, child_id))
        elif z3.is_and(expr):
            self.nodes.append((current_id, "and"))
            for child in expr.children():
                child_id = self._traverse_dot(child)
                self.edges.append((current_id, child_id))
        elif z3.is_or(expr):
            self.nodes.append((current_id, "or"))
            for child in expr.children():
                child_id = self._traverse_dot(child)
                self.edges.append((current_id, child_id))
        elif z3.is_not(expr):
            self.nodes.append((current_id, "not"))
            child_id = self._traverse_dot(expr.arg(0))
            self.edges.append((current_id, child_id))
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
    s = z3.Solver()
    s.from_file(
        "non-incremental/NIA/20230321-UltimateAutomizerSvcomp2023_renamed/gcd_2.c_0.smt2"
    )
    p = BoolStructPrinter(s.assertions())
    for a in s.assertions():
        print(a)
    print()
    print(p.to_sexpr())
    print()
    print(p.to_dotformat())


if __name__ == "__main__":
    main()
