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
