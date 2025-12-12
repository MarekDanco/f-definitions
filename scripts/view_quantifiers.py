#!/usr/bin/env -S python3 -u
import argparse
from functools import cache

import z3


@cache
def has_quantifiers(expr):
    if z3.is_quantifier(expr):
        return True
    else:
        return any(has_quantifiers(c) for c in expr.children())


def quantified_assertions(assertions):
    return [a for a in assertions if has_quantifiers(a)]


def main():
    parser = argparse.ArgumentParser(
        description="View quantified assertions of an SMT file"
    )
    parser.add_argument("file", nargs=1, help="File path to view")
    args = parser.parse_args()

    s = z3.Solver()
    s.from_file(args.file[0])
    for a in quantified_assertions(s.assertions()):
        print(a)


if __name__ == "__main__":
    main()
