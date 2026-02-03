import subprocess as sp
from enum import Enum
import z3


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


def process_formula(b, p, funcs, consts, model):
    pivot = [bv for bv in p if model.eval(bv)]
    assert len(pivot) == 1
    print("pivot:", pivot[0])
    non_pivots = [bv for bv in p if not bv.eq(pivot[0])]
    print("non pivots:", non_pivots)
    print(b.Qp)
    const_subs = [(c(), model.eval(c())) for c in consts]
    clean_q = z3.substitute(b.Q, const_subs)

    u_vars = [z3.Int(f"{str(np)[:-1]}") for np in non_pivots]
    f = z3.Function("f", *[z3.IntSort() for _ in non_pivots], z3.IntSort())
    pivot_var = z3.Int(str(pivot[0])[:-1])
    prob = z3.ForAll(u_vars, z3.substitute(b.Qp, (pivot_var, f(*u_vars))))
    s = z3.Solver()
    s.add(prob)
    prob_smt = s.to_smt2()
    res = run_cvc5(3, prob_smt)
    return res


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
