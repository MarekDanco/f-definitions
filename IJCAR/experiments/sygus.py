import subprocess as sp
from enum import Enum
import re
import z3

from small_utils import flatten


class Res(Enum):
    ERROR = "Error"
    TIMEOUT = "Timeout"


class Cmd(Enum):
    SYGUS = ["/usr/local/bin/cvc5", "--sygus-inference=on"]


def run_cvc5(timeout, prob):
    prob += "(get-model)\n"
    external_command = Cmd.SYGUS
    try:
        res = sp.run(
            external_command.value,
            input=prob,
            text=True,
            capture_output=True,
            timeout=timeout,
            check=False,
        )
        lines = res.stdout.split("\n")
        filtered_lines = [
            line for line in lines if line.strip() not in ["sat", "unsat", "(", ")"]
        ]
        return "".join(filtered_lines)
    except sp.CalledProcessError:
        return Res.ERROR
    except sp.TimeoutExpired:
        return Res.TIMEOUT


def format_offset(x, offset):
    try:
        val = int(offset)
        if val == 0:
            return f"{x} + 0"
        if val < 0:
            return f"{x} - {abs(val)}"
        return f"{x} + {val}"
    except (ValueError, TypeError):
        return f"{x} + {offset}"


def sygus2string(sygus, x, pvt_function, pvt_offset, u_vars_functions, u_vars_offsets):
    match = re.search(r"Int\s+(.+)\)\s*$", sygus)
    if not match:
        return "Format error"
    expr_str = match.group(1).strip()
    mapping = {
        f"arg{i}": (
            f"{x.sexpr()}"
            if str(f) == str(x.sexpr())
            else f"{f}({format_offset(x, o)})"
        )
        for i, (f, o) in enumerate(zip(u_vars_functions, u_vars_offsets))
    }
    tokens = re.findall(r"\(|\)|[^\s()]+", expr_str)

    def parse():
        if not tokens:
            return ""
        token = tokens.pop(0)

        if token == "(":
            op = tokens.pop(0)
            args = []
            while tokens[0] != ")":
                args.append(parse())
            tokens.pop(0)

            if op == "+":
                return " + ".join(args)
            elif op == "*":
                if args[0] == "-1":
                    return f"-{args[1]}"
                return " * ".join(args)
            elif op == "-":
                if len(args) == 1:
                    return f"-{args[0]}"
                return " - ".join(args)
            return f"{op}({', '.join(args)})"

        if token == "-":
            return "-"
        return mapping.get(token, token)

    try:
        raw_math = parse()
        assert raw_math is not None
        clean_math = raw_math.replace("+ -", "- ").replace("  ", " ")
        clean_math = clean_math.strip()
        pvt_head = f"{pvt_function}({format_offset(x, pvt_offset)})"
        return f"{pvt_head} = {clean_math}"
    except Exception as e:
        return f"Parsing Error: {e}"


def get_name(var, b):
    if var.eq(b.x):
        return var.sexpr()
    occ_str = var.sexpr()
    return occ_str[3]


def compare(u_var, occ):
    for os in occ:
        print(u_var, os)
        print(type(u_var), type(os))
        print(f"{u_var}?={os}", u_var.eq(os))


def get_offset(u_var, b):
    if u_var.eq(b.x):
        return z3.IntVal(0)
    occ = b.occ
    for i in range(len(occ)):
        for j in range(len(occ[i])):
            if u_var.eq(occ[i][j]):
                return b.offsets[i][j]


def process_formula(b, p, model):
    flat_p = flatten(p)
    pivot = [bv for bv in flat_p if model.eval(bv, model_completion=True)]
    assert len(pivot) == 1
    pvt = z3.Int(f"{str(pivot[0])[:-1]}")
    pvt_offset = get_offset(pvt, b)
    pvt_function = get_name(pvt, b)
    non_pivots = [bv for bv in flat_p if not bv.eq(pivot[0])]
    u_vars = [z3.Int(f"{str(np)[:-1]}") for np in non_pivots]
    u_vars.append(b.x)
    u_vars_offsets = [get_offset(v, b) for v in u_vars]
    u_vars_functions = [get_name(v, b) for v in u_vars]
    f = z3.Function(f"{pvt_function}", *[z3.IntSort() for _ in u_vars], z3.IntSort())
    pivot_var = z3.Int(str(pivot[0])[:-1])
    prob = z3.ForAll(u_vars, z3.substitute(b.Qp, (pivot_var, f(*u_vars))))
    s = z3.Solver()
    s.add(prob)
    prob_smt = s.to_smt2()
    res = run_cvc5(3, prob_smt)
    # print(prob)
    # print(res)
    return sygus2string(
        res, b.x, pvt_function, pvt_offset, u_vars_functions, u_vars_offsets
    )


def run_test():
    f = z3.Function("f", z3.IntSort(), z3.IntSort(), z3.IntSort())
    x, y = z3.Int("x"), z3.Int("y")
    prob = z3.ForAll([x, y], f(x, y) == x + y)
    s = z3.Solver()
    s.add(prob)
    prob_smt = s.to_smt2()
    res = run_cvc5(3, prob_smt)
    print(res)


if __name__ == "__main__":
    run_test()
