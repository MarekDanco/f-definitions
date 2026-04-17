#!/usr/bin/env python3

import z3
import random
import os
import fcntl
import time

BOUNDS = [10, 100, 1000, 10000, 100000]
HASH_FILE = "formula_hashes.txt"


def get_f(num):
    f = z3.Function("f", z3.IntSort(), z3.IntSort())
    functions = [f]
    func_names = ["f"]
    if num == 2:
        g = z3.Function("g", z3.IntSort(), z3.IntSort())
        functions.append(g)
        func_names.append("g")
    return functions


def get_c(num):
    constants = [z3.Int("c")]
    const_names = ["c"]
    if num == 2:
        constants.append(z3.Int("d"))
        const_names.append("d")
    if num == 3:
        constants.append(z3.Int("e"))
        const_names.append("e")
    return constants


def get_arg(constants):
    return random.choice([i for i in range(-3, 4)] + constants)


def get_body_arg(x, constants):
    if random.choice([True, False]):
        return x + get_arg(constants)
    else:
        return x - get_arg(constants)


def get_term(funcs, args):
    term = z3.IntVal(0)
    for f, arg in zip(funcs, args):
        if arg is not None:
            subterm = f(arg)
        else:
            subterm = f
        if random.choice([True, False]):
            term = term + subterm
        else:
            term = term - subterm
    return term


def get_compare(lhs, rhs):
    compare = random.choice(["=", ">", ">=", "<", "<="])
    if compare == "=":
        return lhs == rhs
    if compare == ">":
        return lhs > rhs
    if compare == ">=":
        return lhs >= rhs
    if compare == "<":
        return lhs < rhs
    if compare == "<=":
        return lhs <= rhs


def get_ground_asserts(functions, constants):
    ground_asserts = set()
    num = random.randint(1, 4)
    for _ in range(num):
        l_func = [random.choice(functions + constants)]
        l_arg = [get_arg(constants) if l_func[0] in functions else None]
        r_funcs = [
            random.choice(functions + constants) for _ in range(random.randint(1, 3))
        ]
        r_args = [get_arg(constants) if f in functions else None for f in r_funcs]
        lhs = get_term(l_func, l_arg)
        rhs = get_term(r_funcs, r_args)
        ground_asserts.add(get_compare(lhs, rhs))
    return ground_asserts


def flip():
    return random.choice([0, 1])


def get_body(x, functions, constants):
    offsets = {f: [get_body_arg(x, constants) for _ in range(2)] for f in functions}
    l_func = [random.choice(functions)]
    l_arg = [offsets[l_func[0]][flip()]]
    r_funcs = [
        random.choice(functions + constants) for _ in range(random.randint(1, 3))
    ]
    r_args = [offsets[f][flip()] if f in functions else None for f in r_funcs]
    lhs = get_term(l_func, l_arg)
    rhs = get_term(r_funcs, r_args)
    return get_compare(lhs, rhs)


def generate_formula():
    """Generate a random UFLIA formula with constraints"""
    random.seed()
    num_functions = random.choice([1, 2])
    num_constants = random.choice([1, 2, 3])
    functions = get_f(num_functions)
    constants = get_c(num_constants)
    s = z3.Solver()
    for const in constants:
        s.add(const > 0)
    ground_asserts = get_ground_asserts(functions, constants)
    for g in ground_asserts:
        s.add(g)
    x = z3.Int("x")
    solvers = {}
    original_solver = z3.Solver()
    original_solver.add(s.assertions())
    body = get_body(x, functions, constants)
    original_solver.add(z3.ForAll([x], body))
    solvers["original"] = original_solver
    for bound in BOUNDS:
        bounded_solver = z3.Solver()
        bounded_solver.add(s.assertions())
        bounded_body = z3.Implies(z3.And(0 <= x, x <= bound), body)
        bounded_solver.add(z3.ForAll([x], bounded_body))
        solvers[bound] = bounded_solver
    return solvers


def compute_z3_hash(solver):
    """Compute hash using Z3's internal hash (handles commutativity, etc.)"""
    combined_hash = 0
    for assertion in solver.assertions():
        combined_hash ^= assertion.hash()
    return format(combined_hash & 0xFFFFFFFFFFFFFFFF, "016x")


def is_duplicate(formula_hash):
    """Check if hash already exists (with file locking)"""
    if not os.path.exists(HASH_FILE):
        return False
    with open(HASH_FILE, "r") as f:
        fcntl.flock(f.fileno(), fcntl.LOCK_SH)
        try:
            existing_hashes = set(f.read().splitlines())
        finally:
            fcntl.flock(f.fileno(), fcntl.LOCK_UN)
    return formula_hash in existing_hashes


def save_formulas(solvers, formula_hash):
    """Save formula: original to bench/, bounded versions to bench10, bench100, etc."""

    os.makedirs("bench", exist_ok=True)
    original_filename = f"bench/formula_{formula_hash}.smt2"
    with open(original_filename, "w") as f:
        f.write(solvers["original"].to_smt2())
    for bound in BOUNDS:
        output_dir = f"bench{bound}"
        os.makedirs(output_dir, exist_ok=True)

        filename = f"{output_dir}/formula_{formula_hash}.smt2"
        with open(filename, "w") as f:
            f.write(solvers[bound].to_smt2())

    return formula_hash


def main():
    max_attempts = 100

    for attempt in range(max_attempts):
        solvers = generate_formula()
        formula_hash = compute_z3_hash(solvers["original"])

        if is_duplicate(formula_hash):
            time.sleep(random.uniform(0.01, 0.05))
            continue

        try:
            f = open(HASH_FILE, "r+")
        except FileNotFoundError:
            f = open(HASH_FILE, "w+")

        with f:
            fcntl.flock(f.fileno(), fcntl.LOCK_EX)
            try:
                existing = f.read()
                if formula_hash in existing:
                    continue

                f.write(formula_hash + "\n")
                f.flush()
            finally:
                fcntl.flock(f.fileno(), fcntl.LOCK_UN)

        saved_hash = save_formulas(solvers, formula_hash)
        print(f"Generated formula_{saved_hash} (attempt {attempt + 1})")
        return 0

    print(
        f"Failed to generate unique formula after {max_attempts} attempts",
        file=sys.stderr,
    )
    return 1


if __name__ == "__main__":
    import sys

    sys.exit(main())
