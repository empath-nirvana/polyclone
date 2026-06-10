/-
  FrobeniusDescent/Main.lean
  ==========================

  **THE F₂ MASTER CONJECTURE** (sorry-free; axioms:
  propext, Classical.choice, Quot.sound):

      for every `q ∈ F₂[X,Y]`,  `X+Y ∉ Clo q`  or  `X·Y ∉ Clo q`;
      in particular `Clo q ⊊ F₂[X,Y]` whenever `Clo q` misses anything.

  The split is the `∂_X∂_Y` trichotomy collapsed to a dichotomy:
  * `D q = 0` (the Frobenius-degenerate floor): `X·Y ∉ Clo q` — the
    D-cocycle theorem (`DXDYCocycle.XY_not_in_Clo`, fully proven).
  * `D q ≠ 0`: `q` is tame by the Frobenius-depth descent
    (`Bridge.tame_of_D_ne_zero`), and tameness excludes `X+Y`
    (`Tameness.master`, fully proven).
-/
import PolyClone.FrobeniusDescent.Bridge

namespace PolyClone.FrobeniusDescent

open MvPolynomial
open PolyClone.CloAddMul

/-- **The F₂ master conjecture.** -/
theorem F2_master_conjecture (q : F) :
    ¬ Clo q (addOp : F) ∨ ¬ Clo q (mulOp : F) := by
  by_cases hD : DXDYCocycle.D q = 0
  · exact Or.inr (DXDYCocycle.XY_not_in_Clo hD)
  · left
    have h := Tameness.master q (tame_of_D_ne_zero q hD)
    have he : (addOp : F) = X 0 + X 1 := rfl
    rw [he]
    exact h

end PolyClone.FrobeniusDescent
