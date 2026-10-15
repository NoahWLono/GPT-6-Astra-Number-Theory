"""Exact symbolic audit of 2026 second-cuboid elimination claims.

Run with the parent's .tools/math-python/bin/python (SymPy 1.14.0).
This script verifies identities/certificates, not conjectural point completeness.
External expressions are parsed by a restricted arithmetic AST, never executed.
"""
import ast
import json
from pathlib import Path
import sympy as sp

ROOT = Path(__file__).resolve().parent
s, a, b, x, r, d, t, y, U, V = sp.symbols("s a b x r d t y U V")


def arithmetic_ast(text, variables):
    def read(node):
        if isinstance(node, ast.Constant) and type(node.value) is int:
            return sp.Integer(node.value)
        if isinstance(node, ast.Name) and node.id in variables:
            return variables[node.id]
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.UAdd, ast.USub)):
            v = read(node.operand)
            return v if isinstance(node.op, ast.UAdd) else -v
        if isinstance(node, ast.BinOp) and isinstance(node.op, (ast.Add, ast.Sub, ast.Mult, ast.Pow)):
            lhs, rhs = read(node.left), read(node.right)
            if isinstance(node.op, ast.Add): return lhs + rhs
            if isinstance(node.op, ast.Sub): return lhs - rhs
            if isinstance(node.op, ast.Mult): return lhs * rhs
            assert rhs.is_Integer and 0 <= rhs <= 64
            return lhs ** rhs
        raise ValueError("Non-arithmetic source expression")
    return read(ast.parse(text, mode="eval").body)


def quintic(s, x):
    return (x**5 + (2+s)*(3-2*s)*x**4
        + (1+10*s+4*s**2-14*s**3+s**4)*x**3
        - s*(1-14*s+4*s**2+10*s**3+s**4)*x**2
        - s**3*(1+2*s)*(-2+3*s)*x - s**5)


if __name__ == "__main__":
    result = {"sympy": sp.__version__, "accepted_solution": False}
    P = sp.expand(quintic(s, x))
    assert sp.cancel(quintic(1/s, 1/x) + P/(s**5*x**5)) == 0
    result["reciprocal_identity"] = True
    rem = sp.rem(P, x*x+a*x+b, x)
    R1, R0 = sp.expand(rem).coeff(x, 1), sp.expand(rem).coeff(x, 0)
    u = -3*a*a+(12-4*s*s-2*s)*a+(-s**4+14*s**3-4*s*s-10*s-1)
    v = (a**4+(2*s*s+s-6)*a**3+(s**4-14*s**3+4*s*s+10*s+1)*a*a
         +(s**5+10*s**4+4*s**3-14*s*s+s)*a-6*s**5+s**4+2*s**3)
    m = -2*a-2*s*s-s+6
    n = a**3+(2*s*s+s-6)*a*a+(s**4-14*s**3+4*s*s+10*s+1)*a+s**5+10*s**4+4*s**3-14*s*s+s
    assert sp.expand(R1-(b*b+u*b+v)) == sp.expand(R0-(m*b*b+n*b-s**5)) == 0
    L, C = sp.expand(n-m*u), sp.expand(m*v+s**5)
    F = sp.expand(C*C+u*L*C+v*L*L)
    assert sp.expand(sp.resultant(R1, R0, b)-F) == 0
    result["quadratic_remainder_and_resultant"] = True
    result["F_degrees"] = [sp.degree(F, s), sp.degree(F, a), sp.Poly(F,s,a).total_degree()]
    result["F_at_one"] = str(sp.factor(F.subs(s,1)))
    print("Quadratic remainder, resultant, reciprocal identity checked", flush=True)
    res = sp.Poly(sp.resultant(L, C, s), a).primitive()[1]
    fac = sp.factor_list(res.as_expr())[1]
    result["degenerate_resultant_factors"] = [dict(degree=sp.degree(f,a), exponent=e,
        polynomial=str(f)) for f,e in fac]
    result["degenerate_rational_a_roots"] = {str(k):v for k,v in res.ground_roots().items()}
    result["degenerate_gcd_at_a_two"] = str(sp.factor(sp.gcd(L.subs(a,2),C.subs(a,2))))
    print("Degenerate locus exact resultant computed", flush=True)
    # Recompute the symmetric 5+5 resultant directly from coefficient comparison.
    A = (2+r*r)*(3-2*r*r)
    D = -r**6*(1+2*r*r)*(-2+3*r*r)
    bv, cv = (a*a+A)/2, (d*d-D)/(2*r**5)
    H = x**5+a*x**4+bv*x**3+cv*x*x+d*x+r**5
    discrepancy = sp.Poly(sp.expand(H*(-H.subs(x,-x))-quintic(r*r,x*x)),x)
    E2 = sp.factor(sp.together(discrepancy.coeff_monomial(x**6))).as_numer_denom()[0]
    E3 = sp.factor(sp.together(discrepancy.coeff_monomial(x**4))).as_numer_denom()[0]
    print("Computing symmetric factor resultant", flush=True)
    F55 = sp.Poly(sp.cancel(sp.resultant(E2,E3,d)/r**20),r,a).primitive()[1].as_expr()
    src = (ROOT/'sources/second-pass/2601.04240v1.txt').read_text()
    line = next(line[4:] for line in src.splitlines() if line.startswith('F = a**16'))
    published = arithmetic_ast(line, {"r":r,"a":a})
    result["symmetric_resultant_matches_printed"] = sp.expand(F55-published)==0
    fry = sp.Poly(sp.expand(F55.subs(a,r*y)),r,y)
    fsy = sum(c*s**(er//2)*y**ey for (er,ey),c in fry.terms())
    assert all(er%2==0 for er,ey in fry.monoms())
    samples = [sp.Rational(1,100),sp.Rational(1,5),sp.Rational(4,5),sp.Integer(2),sp.Rational(63,2),sp.Rational(317,10),sp.Integer(40)]
    counts = {}
    for v0 in samples:
        counts[str(v0)] = sp.Poly(fsy.subs(s,v0),y).count_roots(-sp.oo,sp.oo)
        print("Symmetric resultant sample",v0,"real roots",counts[str(v0)],flush=True)
    result["symmetric_sample_real_root_counts"] = counts
    result["symmetric_at_one"] = str(sp.factor(fsy.subs(s,1)))
    # Audit the quotient formulas in the 1+4 paper without assuming Chabauty output.
    G = (V**5+(4*U-2)*V**4+(-10*U**2-8*U+64)*V**3
         +(4*U**3-108*U**2+384)*V**2+(U**4-8*U**3-192*U**2+768)*V-2*U**4-128*U**2+512)
    Ut = 2*(t**5+6*t**4+30*t**3+16*t*t+9*t+2)/(t*(t-1)**2*(t*t+6*t+1))
    Vt = 2*(t**4+36*t**3+22*t*t+4*t+1)/((t-1)**2*(t*t+6*t+1))
    curve = (t+1)*(t**4+20*t**3+6*t*t+4*t+1)
    assert sp.cancel(G.subs({U:Ut,V:Vt})) == 0
    assert sp.cancel(Ut**2-4-16*(t+1)**4*curve/(t*t*(t-1)**4*(t*t+6*t+1)**2)) == 0
    assert sp.cancel(Vt**2-4-256*t*t*curve/((t-1)**4*(t*t+6*t+1)**2)) == 0
    result["linear_quartic_parametrization_and_square_identities"] = True
    result["limitation"] = "No genus, Chabauty, rational-point completeness, or full conjecture verification"
    (ROOT/'second-pass-audit.json').write_text(json.dumps(result,indent=2,default=int)+'\n')
    (ROOT/'sources/second-pass/derived-polynomials.txt').write_text(
        '\n'.join(["P="+str(P),"L="+str(L),"C="+str(C),"F="+str(F),"F55="+str(F55)])+'\n')
    print(json.dumps(result,indent=2,default=int),flush=True)
