import z3

# ===================================
# Basic operators for epistemic logic
# ===================================

def determines_truth(knowledge, unknown_vars, implied):
    if len(unknown_vars) == 0:
        return z3.Implies(knowledge, implied)
    else:
        return z3.ForAll(unknown_vars, z3.Implies(knowledge, implied))

def determines_value(knowledge, unknown_vars, expression):
    val = z3.FreshConst(expression.sort())
    return z3.Exists([val],
        determines_truth(knowledge, unknown_vars, expression == val)
    )