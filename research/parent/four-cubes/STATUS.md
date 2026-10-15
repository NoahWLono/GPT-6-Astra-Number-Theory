# Four-cube polynomial identities: active subsidiary question

Status on 15 October 2026: exact target selected; proof and novelty review in
progress. No result has been accepted. This work concerns the category entry
[Sum of four cubes problem](https://en.wikipedia.org/wiki/Sum_of_four_cubes_problem),
catalog ID `wiki-70060173`.

## Target

Let four polynomials over the rationals take integer values at every integer.
Suppose the sum of their cubes is the polynomial `P X + Q`, where `P` and `Q`
are integers. Must `P` be divisible by 3?

[Target.lean](Target.lean) states this question and its negation as propositions.
It contains no proposed proof. Integer-valued rational polynomials are essential:
requiring integer coefficients would replace the question with an elementary
special case.

## Connection to the full problem

A universal four-cube identity with integer-valued summands and slope one would
prove that every integer is a sum of four signed integer cubes. A positive answer
to this subsidiary question would rule out that route in every degree. It would
not decide whether all integers have representations by other means.

A negative answer would supply a polynomial family with slope coprime to 3.
Such a family would not alone cover all integers: its exact progression and the
remaining residue classes would still require analysis.

## Source and status limits

The question was explicitly posed on 10 May 2023 in
[an author-posted MathOverflow question](https://mathoverflow.net/questions/446494/on-sums-of-cubes-of-four-integer-valued-polynomials).
The author reports proofs through degree 27 and includes a degree-nine argument.
The page retrieved on 15 October 2026 has no posted answer. The degree claims have
not been independently verified here, and absence of an answer does not establish
absence of a solution elsewhere. Focused searches have not yet located a general
resolution.

## Initial deductions and unsuccessful approaches

If all coefficients are integers, differentiating the identity and evaluating at
zero makes the slope a multiple of 3. For integer-valued rational polynomials,
derivatives can have denominators divisible by 3; that argument fails.

For example, `(X^3-X)/3` is integer-valued, while its derivative at zero is `-1/3`.
Consequently, integer-valuedness cannot be silently substituted for coefficient
integrality in the derivative argument.

Writing a common denominator as a power of 3 times a 3-adic unit reduces the
question to coefficient cancellation in a sum of four integral polynomial cubes.
Reduction modulo 3 controls the sum of the polynomials, but currently gives no
bound that removes the denominator. The argument stops at that missing bound.

For affine summands with integer coefficients, the familiar obstruction to
families entering the residue classes `4` and `5` modulo 9 follows by descent on
the slopes. That special case is prior background and is not being counted as a
new result. The present target permits arbitrary degree and integer-valued
rational coefficients.

The independent attempt in [the companion note](../four-cubes-independent/independent-note.md)
gives an exact normalization over the ring of rational polynomials integer-valued
on the 3-adic integers. It also constructs polynomial solutions modulo every
fixed power of 3, so a proof must use degree information or the exact identity.
The proposed induction on integer-valued polynomial generators has an unresolved
step: division by 3 may introduce a higher generator.

The source audit has now checked Mordell's full degree-four paper and the
available Cohn–Mordell first-page preview. The advertised unrestricted-degree
coefficient divisibility does not supply the stronger, degree-dependent
divisibility needed for the proposed descent. The companion note gives an
explicit counterexample to that scaling inference. A new argument must bridge
this gap; the current Lean file compiles as a specification and supplies no
proof of the target.
