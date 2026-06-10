/-
  FrobeniusDescentP/Main.lean
  ===========================

  **THE PERFECT CHAR-2 MASTER THEOREM**:

      for every perfect field `Fq` of characteristic 2 and every
      `q ∈ Fq[X,Y]`,  `X+Y ∉ Clo q`  or  `X·Y ∉ Clo q`.

  The split is the `∂_X∂_Y` trichotomy collapsed to a dichotomy:
  * `D q = 0` (the Frobenius-degenerate floor): `X·Y ∉ Clo q` — the
    D-cocycle theorem (`DXDYCocycle.XY_not_in_Clo`, generic over any
    nontrivial char-2 ring).
  * `D q ≠ 0`: `q` is tame by the Frobenius-depth descent
    (`Bridge.tame_of_D_ne_zero`), and tameness excludes `X+Y`
    (`Tameness.master`).

  Corollaries: `Fq = ZMod 2` (recovering `FrobeniusDescent/Main.lean`),
  `Fq = GaloisField 2 n` (every finite field of characteristic 2 — no
  hypothesis on `n` is needed; Mathlib's `GaloisField 2 0` is a perfectly
  good finite field of characteristic 2), and
  `Fq = AlgebraicClosure (ZMod 2) = F̄₂`.
-/
import Mathlib.FieldTheory.Finite.GaloisField
import PolyClone.Perfect.Bridge

set_option linter.unusedSectionVars false

namespace PolyClone.Perfect

open MvPolynomial
open PolyClone.CloAddMul

variable {Fq : Type} [Field Fq] [CharP Fq 2] [PerfectRing Fq 2]

/-- **The master theorem over an arbitrary perfect field of characteristic 2.** -/
theorem perfect_char2_master (q : F Fq) :
    ¬ PolyClone.CloAddMul.Clo q (PolyClone.CloAddMul.addOp)
      ∨ ¬ PolyClone.CloAddMul.Clo q (PolyClone.CloAddMul.mulOp) := by
  by_cases hD : DXDYCocycle.D q = 0
  · exact Or.inr (DXDYCocycle.XY_not_in_Clo hD)
  · left
    have h := master q (tame_of_D_ne_zero q hD)
    have he : (addOp : F Fq) = X 0 + X 1 := rfl
    rw [he]
    exact h

/-- The `Fq = F₂` instance (recovering `FrobeniusDescent.F2_master_conjecture`,
    this time through the parametric development). -/
theorem zmod2_master (q : MvPolynomial (Fin 2) (ZMod 2)) :
    ¬ Clo q (addOp : MvPolynomial (Fin 2) (ZMod 2))
      ∨ ¬ Clo q (mulOp : MvPolynomial (Fin 2) (ZMod 2)) :=
  perfect_char2_master q

/-- The master theorem over EVERY finite field of characteristic 2
    (`GaloisField 2 n` for any `n`; no positivity hypothesis on `n` is
    needed — the required `Field`/`CharP`/`PerfectRing` instances exist
    unconditionally in Mathlib). -/
theorem galoisField_master (n : ℕ) (q : MvPolynomial (Fin 2) (GaloisField 2 n)) :
    ¬ Clo q (addOp : MvPolynomial (Fin 2) (GaloisField 2 n))
      ∨ ¬ Clo q (mulOp : MvPolynomial (Fin 2) (GaloisField 2 n)) :=
  perfect_char2_master q

/-- The master theorem over the algebraic closure `F̄₂`. -/
theorem algClosure_master (q : MvPolynomial (Fin 2) (AlgebraicClosure (ZMod 2))) :
    ¬ Clo q (addOp : MvPolynomial (Fin 2) (AlgebraicClosure (ZMod 2)))
      ∨ ¬ Clo q (mulOp : MvPolynomial (Fin 2) (AlgebraicClosure (ZMod 2))) :=
  perfect_char2_master q

end PolyClone.Perfect
