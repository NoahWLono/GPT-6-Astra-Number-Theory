# Four integer-valued polynomial cubes: independent attempt

Date: 2026-10-15.

Status: **the arbitrary-degree target remains unproved in this attempt**. No counterexample was found. The observations below are elementary arguments and exploratory reductions, not an accepted solution of the MathOverflow question or the four-cubes problem. No Lean proof of these observations was produced here.

## Target and source check

For rational polynomials `f_1,...,f_4` integer-valued on every integer, suppose

\[
\sum_{i=1}^4 f_i(X)^3=PX+Q,\qquad P,Q\in\mathbb Z.
\]

Must `3 | P`?

The [author-posted MathOverflow question](https://mathoverflow.net/questions/446494/on-sums-of-cubes-of-four-integer-valued-polynomials) was still unanswered when inspected. The author supplies an argument through degree 9 and reports a proof through degree 27. Focused searches found no later resolution; that search result is not a proof that none exists.

Related primary references include [Mordell, Acta Arithmetica 16 (1970), 365–370](https://doi.org/10.4064/aa-16-4-365-370) and [Cohn–Mordell, JLMS (1972), 74–78](https://doi.org/10.1112/jlms/s2-5.1.74). The later audit below records the full Mordell paper and the Cohn–Mordell first-page preview. The latter's proof remains unavailable in this attempt.

## Exact normalization at 3

Let

\[
R=\mathbb Q[X]\cap\operatorname{Int}(\mathbb Z_3).
\]

The target is equivalent to the assertion that `X` is not a sum of four cubes in `R`.

For the forward direction, a hypothetical identity with `3` not dividing `P` gives

\[
g_i(X)=f_i((X-Q)/P),\qquad \sum g_i(X)^3=X.
\]

Integer-valuedness on the integers extends to `Z_3` by continuity and density. Since `P` is a 3-adic unit, `(X-Q)/P` maps `Z_3` into `Z_3`, so each `g_i` belongs to `R`.

Conversely, suppose `g_i` belong to `R` and their cubes sum to `X`. Choose a positive integer `C` prime to 3 that clears every non-3 part of every coefficient denominator. The coefficients of `C g_i` lie in `Z[1/3]`. At each integer input its value also lies in `Z_3`; the intersection of these two rings is `Z`. Thus `C g_i` are globally integer-valued and their cubes sum to `C^3 X`, with slope prime to 3.

Replacing `Q[X]` by `Q_3[X]` would strengthen the target. A solution with arbitrary 3-adic coefficients does not automatically descend to rational coefficients.

## Every fixed power of 3 admits polynomial congruence solutions

**Claim established by the argument below.** For every `k >= 2`, there are four polynomials in `Int(Z)` of degree at most

\[
3^{k-2}(3^k-1)
\]

whose cube sum is congruent to `X` modulo `3^k` at every integer input. This is a statement about values, not equality in `Q[X]`.

First, every residue modulo 9 is a sum of four cubes with at least one summand prime to 3. Represent the residue by `s` in `{-4,...,4}`. For nonzero `s`, take `|s|` copies of its sign and fill the remaining positions with zero. For zero, take `(1,-1,0,0)`. The last choice supplies a unit even in the zero case.

To lift from modulus `3^m` to `3^(m+1)`, where `m >= 2`, choose a unit summand `a` and replace it by `a+t3^(m-1)`. Then

\[
(a+t3^{m-1})^3-a^3\equiv t a^2 3^m\pmod{3^{m+1}}.
\]

As `t` ranges over `0,1,2`, this supplies every next residue digit. The summand remains a unit. Thus, for each `r` modulo `3^k`, choose integers `a_{i,r}` with `sum_i a_{i,r}^3 = r (mod 3^k)`.

Write `r = sum_{j=0}^{k-1} r_j 3^j`, with `r_j` in `{0,1,2}`, and put

\[
D_r(X)=\prod_{j=0}^{k-1}
\left(1-\left(\binom{X}{3^j}-r_j\right)^2\right)^{3^{k-2}}.
\]

Lucas's congruence gives `binom(n,3^j) = n_j (mod 3)` for the `j`th ternary digit of every nonnegative integer `n`. It also holds for all integers by continuity on `Z_3`.

If the digit matches, the relevant factor before exponentiation is `1 (mod 3)`, hence its indicated power is `1 (mod 3^(k-1))`. If it does not match, the factor is divisible by 3, and `3^(k-2) >= k-1` makes its indicated power zero modulo `3^(k-1)`. Therefore

\[
D_r(n)\equiv
\begin{cases}1&n\equiv r\pmod{3^k},\\0&\text{otherwise}\end{cases}
\pmod{3^{k-1}}.
\]

Set `F_i(X)=sum_r a_{i,r} D_r(X)`. Products and integer linear combinations of binomial polynomials are integer-valued. At any integer `n`, `F_i(n)` has the selected value modulo `3^(k-1)`. Congruent integers modulo `3^(k-1)` have congruent cubes modulo `3^k`, so

\[
\sum_{i=1}^4F_i(n)^3\equiv n\pmod{3^k}.
\]

The selector degree is

\[
2\,3^{k-2}\sum_{j=0}^{k-1}3^j
=3^{k-2}(3^k-1).
\]

Exact Python checks of the construction, including negative inputs and zero-residue lifting, passed for moduli 9, 27, and 81. The corresponding degree bounds are 8, 78, and 720. Those checks corroborate the formula; the preceding argument supplies the all-input claim.

This prevents a proof based solely on one fixed modulus with unrestricted degree. It does not exclude an obstruction whose modulus grows with a fixed degree bound, nor an argument using the exact vanishing of higher polynomial coefficients.

## Degree-aware descent attempted, but not established

Define

\[
g_0=X,\qquad g_{j+1}=(g_j^3-g_j)/3.
\]

Each `g_j` is integer-valued. It has degree `3^j`, and its leading coefficient has 3-adic valuation `-(3^j-1)/2`. If `n=sum a_j 3^j` with `0 <= a_j <= 2`, the product `prod g_j^{a_j}` has degree `n` and leading valuation `-v_3(n!)`. Comparing with the binomial basis and eliminating leading terms gives a regular basis for `Int(Z_3)`.

Differentiating the recurrence gives the exact identity

\[
g_j'=3^{-j}\prod_{r<j}(3g_r^2-1).
\]

Consequently `v_3(g_j'(z))=-j` for every `z` in `Z_3`. Derivatives can have negative valuation everywhere, so choosing a favorable input does not repair the ordinary differentiation proof.

Let `R_m=Z_3[g_0,...,g_m]`. Its presentation has relations

\[
g_j^3-g_j=3g_{j+1}\quad(0\leq j<m).
\]

Modulo 3, the lower generators each satisfy `T^3=T`; hence

\[
R_m/3R_m\cong\prod_{\{0,1,2\}^m}\mathbb F_3[g_m].
\]

In a reduced representation of a polynomial of degree less than `3^(m+1)`, the degree in the highest generator is at most 2. For an exact normalized identity `sum f_i^3=X`, reduction in each component implies `sum bar(f_i)=bar(X)`. This forces cancellation of the highest-generator coefficients in the sum, not their individual disappearance.

These components correspond to actual integer residue classes. Induction in the recurrence gives, for `N >= j`,

\[
g_j(x+3^N t)-g_j(x)\equiv(-1)^j3^{N-j}t\pmod{3^{N-j+1}}.
\]

Thus the tuple `(g_0(x),...,g_m(x)) mod 3` gives a bijection from residues modulo `3^(m+1)` to `{0,1,2}^(m+1)`. Every value of the final generator occurs when the lower generator residues are fixed.

There is additional information on the residue class `X = 4 (mod 9)`: all four values are `1 (mod 3)`. When `m >= 2`, the components with the relevant two low digits therefore force the individual reduced polynomials in the highest generator to be constant 1, since they have degree at most 2 and take that value at all three elements of `F_3`.

The missing step is to use the exact coefficient equations to turn those componentwise constraints into a reduction from `R_m` to `R_(m-1)` that preserves a slope prime to 3. I did not prove such a reduction. Dividing an expression by 3 may introduce `g_(m+1)` because `(g_m^3-g_m)/3=g_(m+1)`, so merely dividing the congruence error moves in the wrong direction. Cancellation such as `f,-f` also shows that individual summands need not descend even when their cube sum has low degree.

After translating the constant term to `Q_0 = 4 (mod 9)`, the substitution

\[
h_i(T)=(f_i(9T)-1)/3
\]

is legitimate in `Int(Z)`, but the transformed identity is

\[
\sum_i(h_i+3h_i^2+3h_i^3)
=PT+(Q_0-4)/9.
\]

This is not another identity of the original form. An induction that treats it as one has a gap.

The exact arbitrary-degree divisibility statement remains open in this attempt. These reductions do not prove the four-cubes conjecture, and the fixed-modulus construction is not a counterexample to the divisibility statement.

## Final primary-source audit: the coefficient lemma does not supply descent

The [publisher's free CC-BY download](https://www.impan.pl/shop/en/publication/transaction/download/product/97224) for Mordell's 1970 paper was obtained through an ordinary HTTP request. It redirects to the [ICM archive PDF](https://matwbn.icm.edu.pl/ksiazki/aa/aa16/aa1643.pdf). The scanned article occupies printed pages 365–369; the downloaded PDF also contains the first page of the next article. The archive bytes have SHA-256 `49a4fd08d8f340d1994cc8cc359f396b9f4ba335c2fd2a93ae3bf6edeea6e150`. The PDF and page renders are third-party source material in the ignored `source-cache/` directory.

Mordell assumes integer coefficients and maximum degree four. The proof obtains divisibility by `81,27,9,3` for the quartic, cubic, quadratic, and linear coefficients respectively, then substitutes `X/3` to contradict minimality. Its intermediate fractional-power substitutions exploit specific quartic coefficient equations. Page 369 explicitly identifies the relations that fail to generalize to degree five; a footnote reports Cohn's subsequent exclusion of degree five. The paper contains no theorem for integer-valued rational polynomials of arbitrary degree.

The [Cohn–Mordell publisher preview](https://academic.oup.com/jlms/article-abstract/s2-5/1/74/992757), inspected as the parent's saved first-page image, states the degree-at-most-six result. For integer-coefficient identities with constant term congruent to 4 modulo 9, it describes a descent requiring `3^j | a_{j,i}` for every nonconstant coefficient. It also advertises the weaker unrestricted-degree statement `3 | a_{j,i}`. The surrounding setup chooses an identity minimizing the sum of absolute values of nonconstant coefficients; the full proof was not inspected. Consequently, the preview establishes what the authors announce, while the exact hypotheses and use of minimality inside their lemma remain unaudited here.

Even granting the weaker lemma for every identity with the stated integer-coefficient hypotheses, it does not justify the proposed denominator induction. To make this precise, write `Z_(3)` for rationals with denominator prime to 3. The granted lemma extends to coefficient polynomials in `Z_(3)[Y]`: multiply all four summands by an integer `C` that clears their coefficient denominators and those of the linear right side, choosing `C = 1 (mod 9)`. Such a `C` exists because the denominator least common multiple is prime to 3. The transformed identity has integer coefficients and the same constant-term residue. Divisibility by 3 then descends because `C` is a 3-adic unit. This conditional extension concerns `Z_(3)` coefficients only; it supplies no result for ramified coefficients.

Now expand a hypothetical integer-valued counterexample after an integer translation `t` with `Pt+Q = 4 (mod 9)`:

\[
f_i(t+X)=\sum_{j\geq0}c_{j,i}X^j.
\]

For sufficiently large integer `s`, the polynomials `f_i(t+3^sY)` have coefficients in `Z_(3)`. The granted lemma would give

\[
v_3(c_{j,i})+sj\geq1\qquad(j>0).
\]

Reducing the input scale from `s` to `s-1` instead requires

\[
v_3(c_{j,i})+sj\geq j.
\]

The gap is `j-1` powers of 3 in degree `j`. Taking `s` minimal among integer scales does not remove it.

An explicit integer-valued polynomial shows why that inference fails:

\[
h(X)=1+\frac{(X^3-X)^2}{3},\qquad
h(3Y)=1+3(9Y^3-Y)^2.
\]

The polynomial `h` takes integer values, always congruent to 1 modulo 3, but has nonintegral coefficients. Every nonconstant coefficient of `h(3Y)` is divisible by 3. Thus the coefficient conclusion at scale 3 does not allow a return to scale 1. In fact the same conclusion holds for every integer translate `h(t+3Y)`, since `( (t+3Y)^3-(t+3Y) )/3` has integer coefficients. This example refutes the proposed scaling inference; it is not a four-cubes identity or a counterexample to the target.

The valid consequence of the advertised lemma is therefore a coefficient restriction on each sufficiently small input disk. An arbitrary-degree argument still needs additional exact coefficient information yielding the degree-weighted divisibility, or a different transformation that preserves four cubes and improves a well-founded measure. Neither the accessible source nor this audit supplies that step. The target remains unproved here.
