import PolyClone.FrobeniusDescent.IntReduction
/-
  FrobeniusDescent/StatementAudit.lean — behavioral audit of the statement layer.
  Extracts independently-known concrete facts from the main theorems; a failure
  here would mean the encoding (Clo / addOp / mulOp / bind₁ direction) drifted.
-/
open PolyClone.FrobeniusDescent
open PolyClone.CloAddMul
open MvPolynomial

/-! Behavioral audit of the statement layer: extract independently-known
facts from the theorems. Failures here would indicate the encoding
(Clo / addOp / mulOp / bind₁ direction) does not mean what we think. -/

-- POSITIVE control: p itself is always reachable (p(X,Y) = p),
-- so the `sub` constructor substitutes the arguments INTO p as intended.
theorem t_pos_mul : Clo (mulOp : F) (mulOp : F) := by
  have h := Clo.sub (p := (mulOp : F)) Clo.atomX Clo.atomY
  simpa [mulOp] using h

theorem t_pos_add : Clo (addOp : F) (addOp : F) := by
  have h := Clo.sub (p := (addOp : F)) Clo.atomX Clo.atomY
  simpa [addOp] using h

-- EXTRACTED NEGATIVE 1: addition is not reachable from multiplication.
theorem t_addOp_notin_Clo_mulOp : ¬ Clo (mulOp : F) (addOp : F) :=
  (F2_master_conjecture mulOp).resolve_right (not_not_intro t_pos_mul)

-- EXTRACTED NEGATIVE 2: multiplication is not reachable from addition.
theorem t_mulOp_notin_Clo_addOp : ¬ Clo (addOp : F) (mulOp : F) :=
  (F2_master_conjecture addOp).resolve_left (not_not_intro t_pos_add)

-- THE HISTORICAL OPEN CORE: X+Y ∉ Clo (Y³ + XY), now a few lines.
theorem t_open_core : ¬ Clo (X 1 ^ 3 + X 0 * X 1 : F) (X 0 + X 1) := by
  apply PolyClone.Tameness.master
  apply tame_of_D_ne_zero
  have hshape : (X 1 ^ 3 + X 0 * X 1 : F)
      = 0 ^ 2 + X 0 * 0 ^ 2 + X 1 * (X 1) ^ 2 + X 0 * X 1 * 1 ^ 2 := by ring
  rw [hshape, D_decomp]
  simp

-- Same extraction over ℤ.
theorem t_int : ¬ Clo (mulOp : MvPolynomial (Fin 2) ℤ) (addOp : MvPolynomial (Fin 2) ℤ) := by
  have hmul : Clo (mulOp : MvPolynomial (Fin 2) ℤ) (mulOp : MvPolynomial (Fin 2) ℤ) := by
    have h := Clo.sub (p := (mulOp : MvPolynomial (Fin 2) ℤ)) Clo.atomX Clo.atomY
    simpa [mulOp] using h
  exact (int_master mulOp).resolve_right (not_not_intro hmul)

-- axiom-checked at creation: propext, Classical.choice, Quot.sound
#print axioms t_addOp_notin_Clo_mulOp
-- axiom-checked at creation: propext, Classical.choice, Quot.sound
#print axioms t_open_core
-- axiom-checked at creation: propext, Classical.choice, Quot.sound
#print axioms t_int
