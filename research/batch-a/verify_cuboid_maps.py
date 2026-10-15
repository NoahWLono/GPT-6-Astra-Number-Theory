"""Exact identities for ODD_ODD_PROOF.md; no kernel or novelty claim."""
import json
from pathlib import Path
import sympy as sp
from audit_second_cuboid import quintic

root = Path(__file__).resolve().parent
s,x,h,w,k,v,p,q,A,B,c=sp.symbols('s x h w k v p q A B c')
T=w*(w*w-1)**2+4*(1-k)*(w*w-k)
g=v**5+v**4-2*v**3-2*v*v+2-2*k
sh=(1+h)/(1-h)
xw=sh*(h+w)/(h-w)
wx=h*(x-s)/(x+s)
rv=(2*k-1-w*w)/(w*w-1)
identities={
    'P_at_minus_s':quintic(s,-s)+2*s**3*(s-1)**4,
    'T_at_h':T.subs({k:h*h,w:h})-h*(h-1)**2*(h+1)**2,
    'P_to_T':quintic(sh,xw)-32*h**4*(h+1)**3*T.subs(k,h*h)/((h-w)**5*(1-h)**7),
    'mobius_inverse_x':s*(h+wx)/(h-wx)-x,
    'mobius_inverse_w':(h*(x-s)/(x+s)).subs(x,s*(h+w)/(h-w))-w,
    'T_of_one_minus_v_squared':T.subs(w,1-v*v)-g*g.subs(v,-v),
    'inverse_v':rv.subs(w,1-v*v)-v+g/(v*v*(v*v-2)),
    'inverse_w':1-rv**2-w+T/(w*w-1)**2,
    'T_at_one':T.subs(w,1)-4*(k-1)**2,
    'T_at_minus_one':T.subs(w,-1)-4*(k-1)**2,
    'g_at_zero':g.subs(v,0)-2*(1-k),
    'g_mod_v_squared_minus_two':sp.rem(g,v*v-2,v)-2*(1-k),
    'original_circle':1-((p*p-q*q)/(p*p+q*q))**2-4*p*p*q*q/(p*p+q*q)**2,
}
for name,expr in identities.items():
    assert sp.cancel(expr)==0,name

# Quadratic divisors of g give the smaller elliptic obstruction and square cover.
pair=B*B-(3*A*A+2*A-2)*B+A*(A+1)*(A*A-2)
K=1+B*((2*A+1)*B-(A+1)*(A*A-2))/2
rem=sp.rem(g,v*v-A*v+B,v)
assert sp.expand(rem-(pair*v+2*(K-k)))==0
assert sp.factor(sp.discriminant(pair,B))==5*A**4+8*A**3+4
square_obstruction=4*A*c**4+(2*A*A+4)*c*c-A**3-2*A*A+A
assert sp.expand(pair.subs(B,A*A+A-2-2*A*c*c)-A*square_obstruction)==0
assert sp.rem(sp.expand(2*A*(1-K)-B*B*(A*A+A-2-B)),pair,B)==0

out=dict(sympy=sp.__version__,checked_on='2026-10-15',
         verified_rational_function_identities=list(identities),
         quadratic_remainder_identity=True,elliptic_discriminant_identity=True,
         square_cover_identity=True,lean_kernel_checked=False,novelty_verified=False,
         accepted_solution=False)
(root/'cuboid-map-checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
