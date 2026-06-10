# PolyClone

Formal verification companion to the paper *One-operation completeness
for polynomial rings: a characteristic-two dichotomy*.

For a commutative ring `R` and `p ∈ R[x,y]`, `Clo p` is the smallest
set of bivariate polynomials containing the variables and all
constants and closed under `(f, g) ↦ p(f, g)`; `p` is *complete* if
`Clo p` is everything.

## Main results (paper ↔ Lean)

| Paper | Statement | Lean |
|---|---|---|
| Thm 1.1 | no complete `p` over `ℤ` (degree-free) | `int_master`, `masterConjecture_int` (`FrobeniusDescent/IntReduction.lean`) |
| Thm 1.2 | `∀ q ∈ F₂[x,y]`: `x+y ∉ Clo q` or `xy ∉ Clo q` | `F2_master_conjecture` (`FrobeniusDescent/Main.lean`) |
| Thm 7.1 | `x² − y` complete when `2` is invertible (so over `ℚ`, `F₃`, …) | `qOp_complete` (`FrobeniusDescent/CharTwoDichotomy.lean`) |
| Prop 3.2 | `Dq = 0 ⟹ xy ∉ Clo q` (cocycle) | `XY_not_in_Clo` (`DXDYCocycle.lean`) |
| Prop 5.1 | master reduction via property (†) | `master` (`Tameness.lean`) |
| Thm 6.x | the Frobenius descent | `no_nonconstant_witness` (`FrobeniusDescent/Descent.lean`) |
| Lem (kill) | curve constraint ⟹ level algebraic | `c_algebraic_of_curve_constraint` (`FrobeniusDescent/KillLemma.lean`) |
| Lem (alg. pts) | common zero of coprime pair is algebraic | `algebraic_point` (`FrobeniusDescent/AlgebraicPoint.lean`) |
| Lem (keystone) | `h_x, h_y` coprime after the peel | `hX_hY_relPrime` (`FrobeniusDescent/Perfectness.lean`) |
| Thm 1.3 | **the dichotomy**: complete op over `R` ⟺ `2 ∈ R×` | `complete_iff_two_isUnit` (`Perfect/Dichotomy.lean`) |
| Rem 6.x | descent over every perfect char-2 field (Frobenius twist) | `perfect_char2_master` (`Perfect/Main.lean`) |
| — | every char-2 field obstructed (perfection embedding) | `char2_field_master` (`Perfect/Dichotomy.lean`) |

**Semiring companion** (`Naturals.lean`, `ZeroSumFreeSemiring.lean`):
over the semiring `ℕ` — where subtraction is unavailable and the ring
dichotomy does not apply — the master theorem holds at the level of
*functions*: no polynomial binary operation on `ℕ` reaches both `+` and
`×` by composition (`polynomial_does_not_reach_both`). The easy halves
generalize to every zero-sum-free (canonically ordered) commutative
semiring (`ℕ∞`, `ℚ≥0`, `ℝ≥0`, `ℕ[X]`, …); the hard half is ℕ-specific
(discreteness). Since `ℕ` is an infinite domain, the function-level
statement implies the formal one.

`FrobeniusDescent/StatementAudit.lean` derives independently known
facts from the main theorems (e.g. `x+y ∉ Clo(xy)`, and the historical
test case `x+y ∉ Clo(y³+xy)`) as a guard against statement drift.

## Verification

The development contains **no `sorry`, no custom axioms, no
`native_decide`**. Every theorem above reports

    #print axioms ... = [propext, Classical.choice, Quot.sound]

(Lean's standard foundational axioms).

## Building

Requires the Lean toolchain pinned in `lean-toolchain`.

    lake exe cache get   # fetch Mathlib binaries
    lake build
