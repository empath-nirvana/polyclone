/-
  comparator/Challenge.lean
  =========================
  Challenge module for leanprover/comparator: the statement layer of
  PolyClone's four headline theorems, with `sorry` bodies.  A solution
  passes iff it provides declarations with these exact names and equal
  statements, using only the whitelisted axioms (see config.json).

  This file must NOT import PolyClone; it replicates the trust base
  verbatim from PolyClone/CloAddMul.lean and
  PolyClone/FrobeniusDescent/{Main,IntReduction,CharTwoDichotomy}.lean,
  PolyClone/Perfect/Dichotomy.lean.
-/
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.ZMod.Basic

namespace PolyClone.CloAddMul

open MvPolynomial

variable {R : Type*} [CommRing R]

/-- The substitution clone of `p ∈ R[X, Y]`: the smallest subset of
    `R[X, Y]` containing the variables, all constants, and closed under
    `(α, β) ↦ p(α, β)`. -/
inductive Clo (p : MvPolynomial (Fin 2) R) : MvPolynomial (Fin 2) R → Prop
  | atomX : Clo p (X 0)
  | atomY : Clo p (X 1)
  | const (c : R) : Clo p (C c)
  | sub {α β : MvPolynomial (Fin 2) R} :
      Clo p α → Clo p β →
      Clo p (bind₁ ![α, β] p)

/-- Addition as a binary polynomial. -/
noncomputable def addOp : MvPolynomial (Fin 2) R := X 0 + X 1

/-- Multiplication as a binary polynomial. -/
noncomputable def mulOp : MvPolynomial (Fin 2) R := X 0 * X 1

end PolyClone.CloAddMul

namespace PolyClone.FrobeniusDescent

open MvPolynomial
open PolyClone.CloAddMul

abbrev R2 : Type := ZMod 2
abbrev F : Type := MvPolynomial (Fin 2) R2

/-- **The F₂ master theorem**: every substitution clone misses addition
    or multiplication. -/
theorem F2_master_conjecture (q : F) :
    ¬ Clo q (addOp : F) ∨ ¬ Clo q (mulOp : F) := by
  sorry

/-- **The ℤ master theorem** (degree-free). -/
theorem int_master (p : MvPolynomial (Fin 2) ℤ) :
    ¬ Clo p (addOp : MvPolynomial (Fin 2) ℤ)
      ∨ ¬ Clo p (mulOp : MvPolynomial (Fin 2) ℤ) := by
  sorry

variable {R : Type*} [CommRing R]

/-- The complete binary operation away from characteristic 2: `x² − y`. -/
noncomputable def qOp : MvPolynomial (Fin 2) R := X 0 ^ 2 - X 1

/-- **Completeness of `x² − y`** whenever `2` is invertible. -/
theorem qOp_complete [Invertible (2 : R)] :
    ∀ g : MvPolynomial (Fin 2) R, Clo (qOp : MvPolynomial (Fin 2) R) g := by
  sorry

end PolyClone.FrobeniusDescent

namespace PolyClone.Perfect

open MvPolynomial
open PolyClone.CloAddMul
open PolyClone.FrobeniusDescent

/-- **The dichotomy**: a complete binary polynomial exists over `R` iff
    `2` is a unit of `R`. -/
theorem complete_iff_two_isUnit (R : Type) [CommRing R] :
    (∃ p : MvPolynomial (Fin 2) R, ∀ g, Clo p g) ↔ IsUnit (2 : R) := by
  sorry

end PolyClone.Perfect
