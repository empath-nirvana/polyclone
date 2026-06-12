# Blueprint: informal statements ↔ formal declarations

This document states, in ordinary mathematical language, every
definition and result in the formal development, with its Lean name and
file, in dependency order. The intent is that a mathematician with no
Lean fluency can (1) check that the *statements* formalize the intended
mathematics, and (2) follow the proof architecture. Polynomials are
**formal** objects throughout; see the precision paragraph in README.md
for the relation to clones of operations. (Declaration names use
`complete` for the generation property `Clo p = R[x,y]`.)

## 0. Trust base (the only definitions a skeptic must read)

- **`Clo p`** (`PolyClone/CloAddMul.lean`, inductive `Clo`): for
  `p ∈ R[x,y]`, the smallest `S ⊆ R[x,y]` with `x ∈ S`, `y ∈ S`,
  `c ∈ S` for every `c ∈ R`, and `p(f,g) ∈ S` whenever `f, g ∈ S`.
  (Four constructors; `bind₁ ![f,g] p` is substitution of `f, g` for
  the two variables of `p`.)
- `addOp = x + y`, `mulOp = x·y` (same file).
- An independent restatement of the trust base lives in
  `comparator/Challenge.lean` (~90 lines, no import of this library),
  against which CI's adversarial judge verifies the headline theorems.

## 1. Reduction to the two generators

- **Lemma** (`Clo.eq_top_of_addOp_mulOp`, `CloAddMul.lean`): if both
  `x+y` and `x·y` lie in `Clo p`, then `Clo p = R[x,y]`. *Proof:* every
  polynomial is built from atoms by `+, ×`; the clone is closed under
  substitution into its members.

## 2. The derivative dichotomy over F₂ (and any char-2 field)

Let `D = ∂x∂y` (formal mixed partial; `PolyClone/DXDYCocycle.lean`).

- **Chain rule / cocycle** (`D_bind₁`): in char 2,
  `D(q(α,β)) = Dq(α,β)·(∂xα·∂yβ + ∂yα·∂xβ) + q_x(α,β)·Dα + q_y(α,β)·Dβ`.
- **Theorem** (`XY_not_in_Clo`): `Dq = 0 ⟹ x·y ∉ Clo q`. *Proof:*
  `ker D` contains the atoms and, when `Dq = 0`, is closed under
  substitution into `q`; but `D(xy) = 1`.

## 3. The rigidity ("tameness") reduction

(`PolyClone/Tameness.lean`; over F₂ — generalized in `Perfect/`.)

- `Diag` = the subalgebra `F₂[x+y]`; `Tame q` = "if `q(α,β)` is a
  nonconstant element of `F₂[x+y]` then `α, β ∈ F₂[x+y]`" (property (†)
  of the paper).
- **Master reduction** (`master`): `Tame q ⟹ x+y ∉ Clo q`. *Proof:*
  clone induction with invariant "not in `F₂[x+y]`, or constant".

## 4. The curve world and the descent

(`PolyClone/FrobeniusDescent/`; parametrized over any perfect char-2
field in `PolyClone/Perfect/`.) Fix `K = alg.closure(F₂(σ))`; a
*witness* is `(α,β) ∈ K[t]²`, not both constant, with `q(α,β) = c`
constant and transcendental.

- **Parity decomposition** (`parity_decomp`, `ParityDecomp.lean`):
  `q = A₀² + x·A₁² + y·A₂² + xy·A₃²`; then `q_x = A₁² + y·A₃²`,
  `q_y = A₂² + x·A₃²`, `Dq = A₃²`. Full-gcd peel: `Aᵢ = w·Bᵢ` with the
  `Bᵢ` coprime, `q = A₀² + w²h`, `h = x·B₁² + y·B₂² + xy·B₃²`.
- **Kill lemma** (`c_algebraic_of_curve_constraint`, `KillLemma.lean`):
  no nonzero `f ∈ F₂[x,y]` vanishes along a witness. *Proof:* resultant
  Bezout certificate in `F₂[x,z][y]` for `f` and `q + z`; evaluate at
  the witness (char 2 kills both terms); powers of a nonconstant curve
  component are linearly independent, so `c` would be algebraic.
- **Algebraic points** (`algebraic_point`, `AlgebraicPoint.lean`):
  a common zero in `K²` of two relatively prime elements of `F₂[x,y]`
  has algebraic coordinates. *Proof:* Gauss + Bezout over `F₂(x)[y]`,
  both variable orders.
- **Keystone** (`hX_hY_relPrime`, `Perfectness.lean`): with the `Bᵢ`
  coprime and `B₃ ≠ 0`, `h_x` and `h_y` are relatively prime. *Proof:*
  char-2 Jacobian argument — a common prime `p ∤ B₃` gives
  `p | (∂x p)·u` with `p ∤ u` and `p ∤ ∂x p`.
- **The descent** (`no_nonconstant_witness`, `Descent.lean`):
  `Dq ≠ 0 ⟹ no witness exists`. *Proof:* induction on
  `deg α + deg β`. Peel: `S := √c + A₀(α,β)` satisfies `S² = W²·H`, so
  the moving level `H = h(α,β)` still has `H' = 0`. Engine: with
  `A = h_x(α,β)`, `B = h_y(α,β)`, `Δ = B₃(α,β)²`: `A' = Δβ'`,
  `B' = Δα'`, `(AB)' = 0`, so `AB` is a square. Fork: a common root of
  `A, B` is an algebraic critical point of `h` (keystone + algebraic
  points), making `√c` algebraic — contradiction; otherwise `A, B` are
  coprime squares, forcing `α = α₁², β = β₁²`, and (coefficients
  Frobenius-fixed over F₂; coefficient-twisted `q^{(1/2)}` in the
  perfect-field version, `Perfect/Defs.lean: half2`) `(α₁, β₁)` is a
  witness at half the degree.
- **Bridge** (`tame_of_D_ne_zero`, `Bridge.lean`): no witness ⟹ `Tame`.
  *Proof:* restrict to the generic line `(t, t+σ)`; a polynomial
  constant on it lies in `F₂[x+y]`.

## 5. Headline theorems

- `F2_master_conjecture` (`FrobeniusDescent/Main.lean`): every
  `q ∈ F₂[x,y]` has `x+y ∉ Clo q` or `x·y ∉ Clo q`. (= §2 + §3 + §4.)
- `perfect_char2_master`, `char2_field_master` (`Perfect/Main.lean`,
  `Perfect/Dichotomy.lean`): the same over every perfect char-2 field;
  then every char-2 field via the perfection embedding and the clone
  transfer `clo_map`.
- `int_master`, `masterConjecture_int` (`FrobeniusDescent/IntReduction.lean`):
  the same over ℤ (mod-2 coefficient transfer; the degree-free F₂
  statement absorbs the degree drop of reduction).
- `qOp_complete` (`FrobeniusDescent/CharTwoDichotomy.lean`): `x² − y`
  generates `R[x,y]` whenever `2` is invertible. *Proof:* explicit
  12-step
  derivation (translations, slanted lines, linear engine, scaled
  squares), verified from a symbolically pre-checked certificate.
- `complete_iff_two_isUnit` (`Perfect/Dichotomy.lean`): **a single
  generating binary polynomial exists over a commutative ring `R` iff
  `2 ∈ R×`.**
  (Residue-field reduction for the forward direction.)

## 6. Semiring companion

- `polynomial_does_not_reach_both` (`Naturals.lean`): over the
  semiring ℕ, no polynomial binary operation reaches both `+` and `×`
  (function-level; implies the formal statement since ℕ is an infinite
  domain). Generic easy halves over zero-sum-free semirings in
  `ZeroSumFreeSemiring.lean`.

## 7. What is NOT claimed

- Nothing about the full clone of all finitary operations on `R`.
- Nothing about term clones without constants (e.g. primality of
  `⟨F_q; x²−y⟩` without constants is open here).
- No Mal'cev-condition analysis of `⟨R, p⟩`.
- Functional completeness over finite fields follows only in the form:
  for odd `q`, `⟨F_q; x²−y⟩` *with constants* is polynomially complete
  in the classical sense (our generation theorem + Lagrange
  interpolation); this corollary is not itself formalized.

## Verification status

Every declaration above: 0 sorries; axioms exactly
`[propext, Classical.choice, Quot.sound]`; CI runs a build + axiom
audit on every push, and an adversarial judge (leanprover/comparator,
two independent kernels) verifies the headline theorems against
`comparator/Challenge.lean`. See README.md.
