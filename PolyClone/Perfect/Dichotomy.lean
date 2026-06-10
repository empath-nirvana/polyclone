/-
  FrobeniusDescentP/Dichotomy.lean
  ================================

  **THE COMPLETE CHARACTERISTIC-2 DICHOTOMY.**

  For a commutative ring `R`, a binary polynomial `p ∈ R[X,Y]` is COMPLETE
  if its substitution clone is all of `R[X,Y]`.  This file proves:

      a complete binary operation exists over `R`  ⟺  `2` is a unit in `R`.

  * `⟸` is `qOp_complete` (`FrobeniusDescent/CharTwoDichotomy.lean`):
    `x² − y` is complete whenever `2` is invertible.
  * `⟹` is new.  The pipeline:
      1. `clo_map` — clone membership transfers along ANY ring hom
         `φ : R →+* S` (generalizing `IntReduction.Clo.map_mod2`).
      2. `char2_field_master` — over EVERY field `k` of characteristic 2
         (perfect or not), no `q` has both `X+Y` and `X·Y` in its clone:
         embed `k` into its perfection `PerfectClosure k 2` via
         `PerfectClosure.of`, transfer by `clo_map`, and invoke the
         perfect-field master theorem `perfect_char2_master`
         (`FrobeniusDescentP/Main.lean`).
      3. `no_complete_of_two_not_unit` — if `2` is not a unit, the ideal
         `(2)` is proper, so it sits inside a maximal ideal `m`; the
         quotient `R ⧸ m` is a field of characteristic 2 (the residue
         characteristic divides 2 and cannot be 1), and completeness
         would push forward along the surjection
         `R[X,Y] → (R ⧸ m)[X,Y]`, contradicting `char2_field_master`.

  Axiom audit (recorded at the bottom of the file): all three main
  theorems use exactly `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.FieldTheory.PerfectClosure
import PolyClone.Perfect.Main
import PolyClone.FrobeniusDescent.CharTwoDichotomy

set_option linter.unusedSectionVars false

namespace PolyClone.Perfect

open MvPolynomial
open PolyClone.CloAddMul

/-! ## 1. General clone transfer along an arbitrary ring hom -/

/-- `MvPolynomial.map φ` commutes with clone substitution `bind₁ ![α, β]`
    (the generic-target version of `IntReduction.π2_bind₁`). -/
lemma map_bind₁_pair {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (p α β : MvPolynomial (Fin 2) R) :
    MvPolynomial.map φ (bind₁ ![α, β] p)
      = bind₁ ![MvPolynomial.map φ α, MvPolynomial.map φ β]
          (MvPolynomial.map φ p) := by
  have h : (MvPolynomial.map φ).comp (bind₁ ![α, β]).toRingHom
      = (bind₁ ![MvPolynomial.map φ α, MvPolynomial.map φ β]).toRingHom.comp
          (MvPolynomial.map φ) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro i
      fin_cases i <;> simp
  exact RingHom.congr_fun h p

/-- **Clone transfer.** Coefficient reduction along any ring hom
    `φ : R →+* S` maps `Clo p` into `Clo (map φ p)`. -/
lemma clo_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    {p g : MvPolynomial (Fin 2) R}
    (h : PolyClone.CloAddMul.Clo p g) :
    PolyClone.CloAddMul.Clo
      (MvPolynomial.map φ p) (MvPolynomial.map φ g) := by
  induction h with
  | atomX => simpa using Clo.atomX (p := MvPolynomial.map φ p)
  | atomY => simpa using Clo.atomY (p := MvPolynomial.map φ p)
  | const c => simpa using Clo.const (p := MvPolynomial.map φ p) (φ c)
  | sub hα hβ ihα ihβ =>
      rw [map_bind₁_pair]
      exact Clo.sub ihα ihβ

/-! ## 2. Every field of characteristic 2 is obstructed

No perfectness hypothesis: embed `k` into its perfection
`PerfectClosure k 2` and pull the perfect-field master theorem back. -/

/-- **The master theorem over an ARBITRARY field of characteristic 2**
    (perfect or not). -/
theorem char2_field_master (k : Type) [Field k] [CharP k 2]
    (q : MvPolynomial (Fin 2) k) :
    ¬ PolyClone.CloAddMul.Clo q
        (PolyClone.CloAddMul.addOp)
      ∨ ¬ PolyClone.CloAddMul.Clo q
        (PolyClone.CloAddMul.mulOp) := by
  -- the perfection embedding
  let φ : k →+* PerfectClosure k 2 := PerfectClosure.of k 2
  have hadd : MvPolynomial.map φ (addOp : MvPolynomial (Fin 2) k)
      = (addOp : MvPolynomial (Fin 2) (PerfectClosure k 2)) := by
    simp [addOp]
  have hmul : MvPolynomial.map φ (mulOp : MvPolynomial (Fin 2) k)
      = (mulOp : MvPolynomial (Fin 2) (PerfectClosure k 2)) := by
    simp [mulOp]
  rcases perfect_char2_master (Fq := PerfectClosure k 2)
      (MvPolynomial.map φ q) with h | h
  · exact Or.inl fun hc => h (hadd ▸ clo_map φ hc)
  · exact Or.inr fun hc => h (hmul ▸ clo_map φ hc)

/-! ## 3. No complete operation when `2` is not a unit -/

/-- **Obstruction theorem.** If `2` is not a unit in `R`, then no binary
    polynomial operation over `R` is complete: residue fields at maximal
    ideals over `(2)` have characteristic 2, and completeness would push
    forward to them. -/
theorem no_complete_of_two_not_unit (R : Type) [CommRing R]
    (h2 : ¬ IsUnit (2 : R)) :
    ¬ ∃ p : MvPolynomial (Fin 2) R,
        ∀ g, PolyClone.CloAddMul.Clo p g := by
  rintro ⟨p, hp⟩
  -- the ideal (2) is proper, hence contained in a maximal ideal m
  have hne : Ideal.span {(2 : R)} ≠ ⊤ := fun htop =>
    h2 (Ideal.span_singleton_eq_top.mp htop)
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  haveI : m.IsMaximal := hm
  -- the residue field k := R ⧸ m
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  -- 2 = 0 in the residue field
  have h20 : (2 : R ⧸ m) = 0 := by
    have h2m : (2 : R) ∈ m := hle (Ideal.mem_span_singleton_self _)
    have := Ideal.Quotient.eq_zero_iff_mem.mpr h2m
    simpa using this
  -- hence the residue field has characteristic 2
  haveI : CharP (R ⧸ m) 2 := by
    have hdvd : ringChar (R ⧸ m) ∣ 2 := ringChar.dvd (by exact_mod_cast h20)
    rcases Nat.prime_two.eq_one_or_self_of_dvd _ hdvd with h1 | h1
    · exact absurd h1 CharP.ringChar_ne_one
    · exact ringChar.of_eq h1
  -- completeness pushes forward along the surjection R[X,Y] → (R ⧸ m)[X,Y]
  have hsurj : Function.Surjective
      (MvPolynomial.map (Ideal.Quotient.mk m) :
        MvPolynomial (Fin 2) R → MvPolynomial (Fin 2) (R ⧸ m)) :=
    MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective
  have hall : ∀ g' : MvPolynomial (Fin 2) (R ⧸ m),
      Clo (MvPolynomial.map (Ideal.Quotient.mk m) p) g' := by
    intro g'
    obtain ⟨g, rfl⟩ := hsurj g'
    exact clo_map _ (hp g)
  -- contradict the char-2 field master theorem
  rcases char2_field_master (R ⧸ m)
      (MvPolynomial.map (Ideal.Quotient.mk m) p) with h | h
  · exact h (hall _)
  · exact h (hall _)

/-! ## 4. The dichotomy -/

/-- **THE COMPLETE CHARACTERISTIC-2 DICHOTOMY.** A commutative ring `R`
    admits a complete binary polynomial operation if and only if `2` is a
    unit in `R`.

    `⟸` is witnessed by `qOp = X² − Y` (`qOp_complete`); `⟹` is the
    residue-field obstruction `no_complete_of_two_not_unit`. -/
theorem complete_iff_two_isUnit (R : Type) [CommRing R] :
    (∃ p : MvPolynomial (Fin 2) R,
        ∀ g, PolyClone.CloAddMul.Clo p g)
      ↔ IsUnit (2 : R) := by
  constructor
  · intro h
    by_contra h2
    exact no_complete_of_two_not_unit R h2 h
  · intro h2
    letI : Invertible (2 : R) := h2.invertible
    exact ⟨_root_.PolyClone.FrobeniusDescent.qOp,
      _root_.PolyClone.FrobeniusDescent.qOp_complete⟩

/-!
## Axiom audit

`#print axioms` output (checked after `lake build
PolyClone.Perfect.Dichotomy`, 2026-06-10):

    'PolyClone.Perfect.char2_field_master'
      depends on axioms: [propext, Classical.choice, Quot.sound]
    'PolyClone.Perfect.no_complete_of_two_not_unit'
      depends on axioms: [propext, Classical.choice, Quot.sound]
    'PolyClone.Perfect.complete_iff_two_isUnit'
      depends on axioms: [propext, Classical.choice, Quot.sound]
-/

end PolyClone.Perfect
