/-
  FrobeniusDescent/IntReduction.lean
  ==================================

  **The ℤ master conjecture**, by mod-2 transfer from `F2_master_conjecture`.

  The coefficient map `π : R[X,Y] → F₂[X,Y]` induced by any ring hom
  `f : R →+* F₂` commutes with clone substitution and fixes the atoms, so
  `Clo p g ⟹ Clo (π p) (π g)`.  If both `X+Y` and `X·Y` were in `Clo p`,
  both would be in `Clo (π p)` — contradicting `F2_master_conjecture (π p)`.

  Because the F₂ theorem has NO degree hypothesis, the transfer is immune to
  the degree drop of reduction mod 2 (e.g. `p = 2X³ + XY ↦ XY`): we need the
  F₂ statement for the (possibly low-degree) image, and we have it for ALL
  polynomials.

  Consequences: `MasterConjecture ℤ`, and more generally `MasterConjecture R`
  for every commutative ring `R` admitting a ring hom to `F₂`
  (e.g. `ZMod (2^k)`, `ℤ[i]`, any `F₂`-algebra).  (No hom exists for e.g.
  `R = ℚ`, and indeed this argument says nothing there.)
-/
import PolyClone.FrobeniusDescent.Main

namespace PolyClone.FrobeniusDescent

open MvPolynomial
open PolyClone.CloAddMul

variable {R : Type*} [CommRing R]

/-- Coefficient reduction `R[X,Y] → F₂[X,Y]` along `f : R →+* F₂`. -/
noncomputable def π2 (f : R →+* R2) : MvPolynomial (Fin 2) R →+* F :=
  MvPolynomial.map f

/-- `π2` commutes with clone substitution. -/
lemma π2_bind₁ (f : R →+* R2) (p α β : MvPolynomial (Fin 2) R) :
    π2 f (bind₁ ![α, β] p) = bind₁ ![π2 f α, π2 f β] (π2 f p) := by
  have h : (π2 f).comp (bind₁ ![α, β]).toRingHom
      = (bind₁ ![π2 f α, π2 f β]).toRingHom.comp (π2 f) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [π2]
    · intro i
      fin_cases i <;> simp [π2]
  exact RingHom.congr_fun h p

/-- **Clone transfer.** Reduction mod 2 maps `Clo p` into `Clo (π p)`. -/
lemma Clo.map_mod2 (f : R →+* R2) {p g : MvPolynomial (Fin 2) R}
    (h : Clo p g) : Clo (π2 f p) (π2 f g) := by
  induction h with
  | atomX => simpa [π2] using Clo.atomX (p := π2 f p)
  | atomY => simpa [π2] using Clo.atomY (p := π2 f p)
  | const c => simpa [π2] using Clo.const (p := π2 f p) (f c)
  | sub hα hβ ihα ihβ =>
      rw [π2_bind₁]
      exact Clo.sub ihα ihβ

/-- **Master theorem over any ring mapping to `F₂`** — no degree hypothesis. -/
theorem master_of_hom_to_F2 (f : R →+* R2) (p : MvPolynomial (Fin 2) R) :
    ¬ Clo p (addOp : MvPolynomial (Fin 2) R)
      ∨ ¬ Clo p (mulOp : MvPolynomial (Fin 2) R) := by
  have hadd : π2 f (addOp : MvPolynomial (Fin 2) R) = (addOp : F) := by
    simp [π2, addOp]
  have hmul : π2 f (mulOp : MvPolynomial (Fin 2) R) = (mulOp : F) := by
    simp [π2, mulOp]
  rcases F2_master_conjecture (π2 f p) with h | h
  · exact Or.inl fun hc => h (hadd ▸ Clo.map_mod2 f hc)
  · exact Or.inr fun hc => h (hmul ▸ Clo.map_mod2 f hc)

/-- **The master theorem over ℤ** — every binary integer polynomial misses
    `X+Y` or `X·Y` in its substitution clone (no degree hypothesis). -/
theorem int_master (p : MvPolynomial (Fin 2) ℤ) :
    ¬ Clo p (addOp : MvPolynomial (Fin 2) ℤ)
      ∨ ¬ Clo p (mulOp : MvPolynomial (Fin 2) ℤ) :=
  master_of_hom_to_F2 (Int.castRingHom R2) p

/-- **THE MASTER CONJECTURE OVER ℤ** (official `MasterConjecture` form). -/
theorem masterConjecture_int : MasterConjecture ℤ := by
  intro p _hdeg hboth
  rcases int_master p with h | h
  · exact h hboth.1
  · exact h hboth.2

/-- The master conjecture over any commutative ring admitting a hom to `F₂`. -/
theorem masterConjecture_of_hom_to_F2 (f : R →+* R2) : MasterConjecture R := by
  intro p _hdeg hboth
  rcases master_of_hom_to_F2 f p with h | h
  · exact h hboth.1
  · exact h hboth.2

end PolyClone.FrobeniusDescent
