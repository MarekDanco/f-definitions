"""
Module to load SMT2 files and produce benchmark classes compatible with alg.py.

The SMT2 file should contain:
- Function declarations (unary Int -> Int functions)
- Ground assertions (F) - formulas with no quantified variables
- A forall assertion where functions are applied to (x + c) expressions
"""

from z3 import (
    And,
    BoolVal,
    Int,
    IntVal,
    Z3_OP_ADD,
    Z3_OP_SUB,
    Z3_OP_UNINTERPRETED,
    is_app,
    is_int_value,
    is_quantifier,
    parse_smt2_file,
    simplify,
    substitute_vars,
)


def simplify_to_python(expr):
    """Convert Z3 expression to Python int if it's a numeric constant."""
    expr = simplify(expr)
    if is_int_value(expr):
        return expr.as_long()
    return expr


def extract_functions(expr, funcs=None):
    """Extract all uninterpreted function symbols from an expression."""
    if funcs is None:
        funcs = {}
    if is_app(expr):
        decl = expr.decl()
        if decl.kind() == Z3_OP_UNINTERPRETED and decl.arity() == 1:
            funcs[decl.name()] = decl
        for child in expr.children():
            extract_functions(child, funcs)
    return funcs


def extract_func_applications(expr, var, func_decls, apps=None):
    """
    Extract function applications of the form f(var + offset).
    Returns a dict: func_name -> list of offsets
    """
    if apps is None:
        apps = {name: [] for name in func_decls}

    if is_app(expr):
        decl = expr.decl()
        if decl.kind() == Z3_OP_UNINTERPRETED and decl.arity() == 1:
            arg = expr.arg(0)
            offset = extract_offset(arg, var)
            if offset is not None:
                apps[decl.name()].append(offset)
        for child in expr.children():
            extract_func_applications(child, var, func_decls, apps)
    return apps


def extract_offset(expr, var):
    """
    Extract offset c from expression of form (var + c) or just var (c=0).
    Returns None if expression is not of this form.
    """
    if expr.eq(var):
        return IntVal(0)

    if is_app(expr):
        if expr.decl().kind() == Z3_OP_ADD:
            children = expr.children()
            if len(children) == 2:
                if children[0].eq(var):
                    return children[1]
                if children[1].eq(var):
                    return children[0]
        elif expr.decl().kind() == Z3_OP_SUB:
            children = expr.children()
            if len(children) == 2 and children[0].eq(var):
                return simplify(-children[1])
    return None


def replace_func_apps_with_vars(expr, var, func_decls, occ_map):
    """
    Replace function applications f(var + offset) with fresh variables.
    occ_map: dict mapping (func_name, offset_str) -> fresh_var
    Returns the transformed expression.
    """
    if is_app(expr):
        decl = expr.decl()
        if decl.kind() == Z3_OP_UNINTERPRETED and decl.arity() == 1:
            arg = expr.arg(0)
            offset = extract_offset(arg, var)
            if offset is not None:
                key = (decl.name(), simplify(offset).sexpr())
                if key in occ_map:
                    return occ_map[key]

        # Recursively process children
        new_children = [replace_func_apps_with_vars(c, var, func_decls, occ_map)
                        for c in expr.children()]
        if new_children:
            return decl(*new_children)
        return expr
    return expr


def extract_ground_func_args(expr, func_decls, args=None):
    """
    Extract arguments of function applications in ground formulas.
    Returns dict: func_name -> list of arguments
    """
    if args is None:
        args = {name: [] for name in func_decls}

    if is_app(expr):
        decl = expr.decl()
        if decl.kind() == Z3_OP_UNINTERPRETED and decl.arity() == 1:
            arg = expr.arg(0)
            args[decl.name()].append(arg)
        for child in expr.children():
            extract_ground_func_args(child, func_decls, args)
    return args


class SMT2Benchmark:
    """Benchmark class loaded from an SMT2 file."""
    pass


def load_smt2(filename):
    """
    Load an SMT2 file and return a benchmark object compatible with alg.py.

    Expected SMT2 structure:
    - (declare-fun f (Int) Int) - unary function declarations
    - (assert <ground-formula>) - assertions without quantifiers (becomes F)
    - (assert (forall ((x Int)) <formula>)) - quantified formula (becomes Q)
    """
    # Parse the SMT2 file
    assertions = parse_smt2_file(filename)

    # Separate ground assertions from quantified ones
    ground_asserts = []
    quant_asserts = []

    for a in assertions:
        if is_quantifier(a) and a.is_forall():
            quant_asserts.append(a)
        else:
            ground_asserts.append(a)

    if len(quant_asserts) != 1:
        raise ValueError(f"Expected exactly one forall assertion, found {len(quant_asserts)}")

    quant = quant_asserts[0]

    # Extract the quantified variable
    if quant.num_vars() != 1:
        raise ValueError(f"Expected exactly one quantified variable, found {quant.num_vars()}")

    var_name = quant.var_name(0)
    x = Int(var_name)

    # Get the body of the forall (with the bound variable replaced)
    Q_body = quant.body()
    # Replace de Bruijn index with actual variable
    Q = substitute_vars(Q_body, x)

    # Extract function symbols from Q
    func_decls = extract_functions(Q)

    # Also check ground assertions for function declarations
    for ga in ground_asserts:
        extract_functions(ga, func_decls)

    # Build F from ground assertions
    if len(ground_asserts) == 0:
        F = BoolVal(True)
    elif len(ground_asserts) == 1:
        F = ground_asserts[0]
    else:
        F = And(ground_asserts)

    # Extract function applications and their offsets from Q
    apps = extract_func_applications(Q, x, func_decls)

    # Build offsets and occ lists, maintaining order by function name
    func_names = sorted(func_decls.keys())
    offsets = []
    occ = []
    occ_map = {}  # (func_name, offset_str) -> fresh_var

    occ_counter = 1
    for fname in func_names:
        func_offsets = apps[fname]
        # Deduplicate while preserving order
        seen = {}  # off_str -> simplified offset
        unique_offsets = []
        for off in func_offsets:
            off_str = simplify(off).sexpr()
            if off_str not in seen:
                seen[off_str] = simplify_to_python(off)
                unique_offsets.append(off_str)

        offsets.append([seen[off_str] for off_str in unique_offsets])

        func_occ = []
        for off_str in unique_offsets:
            var_name = f'occ{fname}{occ_counter}'
            occ_var = Int(var_name)
            func_occ.append(occ_var)
            occ_map[(fname, off_str)] = occ_var
            occ_counter += 1
        occ.append(func_occ)

    # Build Qp by replacing function applications with occurrence variables
    Qp = replace_func_apps_with_vars(Q, x, func_decls, occ_map)

    # Extract arguments of functions in F (ground formula)
    argF_dict = extract_ground_func_args(F, func_decls)
    argF = [[simplify_to_python(a) for a in argF_dict[fname]] for fname in func_names]

    # Create the benchmark object
    b = SMT2Benchmark()
    b.x = x
    b.offsets = offsets
    b.occ = occ
    b.argF = argF
    b.F = F
    b.Q = Q
    b.Qp = Qp

    # Add function declarations as attributes
    for fname, fdecl in func_decls.items():
        setattr(b, fname, fdecl)

    return b


if __name__ == "__main__":
    import sys
    if len(sys.argv) < 2:
        print("Usage: python smt2_loader.py <file.smt2>")
        sys.exit(1)

    b = load_smt2(sys.argv[1])
    print("x:", b.x)
    print("F:", b.F)
    print("Q:", b.Q)
    print("Qp:", b.Qp)
    print("offsets:", b.offsets)
    print("occ:", b.occ)
    print("argF:", b.argF)
