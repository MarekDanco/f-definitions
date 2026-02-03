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


def process_formula(formula):
    return formula


def run_test():
    p = z3.Function("p", z3.IntSort(), z3.IntSort(), z3.IntSort())
    x, y = z3.Int("x"), z3.Int("y")
    prob = z3.ForAll([x, y], z3.And(p(x, y) > x, p(x, y) > y))
    s = z3.Solver()
    s.add(prob)
    prob_smt = s.to_smt2()
    res = run_cvc5(3, prob_smt)
    print(res)


if __name__ == "__main__":
    run_test()
