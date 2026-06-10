/-
  FrobeniusDescent/CharTwoDichotomy.lean
  ======================================

  **Characteristic 2 is the unique obstructed characteristic.**

  * Whenever `2` is invertible, the single binary operation
        `qOp(x,y) = x² − y`
    is COMPLETE: its substitution clone is all of `R[X,Y]`
    (`qOp_complete`).  Instances: ℚ, and `F₃` (`ZMod 3`).
  * Conversely, over any ring admitting a hom to `F₂` NO binary polynomial
    operation is complete (`no_complete_op_of_hom_to_F2`) — that is the
    master theorem `F2_master_conjecture`/`master_of_hom_to_F2`.

  Consequence: the degree-free master statement
  `∀ p, ¬Clo p (X+Y) ∨ ¬Clo p (X·Y)` — which we PROVED over F₂ and ℤ —
  is FALSE over ℚ (`degree_free_master_fails_rat`).

  DEGREE CAVEAT (honest bookkeeping): the repo's official
  `MasterConjecture R` quantifies only over `totalDegree ≥ 3`, and
  `qOp` has degree 2, so the official ℚ-form is NOT falsified by this
  file.  A degree-≥3 complete operation over ℚ (candidate: `x³ − y`,
  translations via Ryley's three-cubes identity) is left as a TODO.

  THE CERTIFICATE (verified symbolically over ℚ and F₃, 2026-06-09;
  all constants lie in ℤ[h] where h := ⅟2).  Write q(a,b) := a²−b;
  the clone contains, in order:

    T_d(g)   := q(C((d+1)·h), q(C((d−1)·h), g))      = g + C d
    neg      := q(C 0, Y)                            = −Y
    XsqY     := q(X, neg)                            = X² + Y
    a₁       := q(X + C h, XsqY)                     = X − Y + C h²
    Xsq      := q(X, C 0)                            = X²
    Ysq      := q(Y, C 0)                            = Y²
    E(a,k,g) := q(T_k(a), q(a, g))                   = g + 2k·a + C k²
    step1    := E(neg, −1, C 0)                      = 2Y + 1
    step2    := E(a₁, h, step1)                      = X + Y + C(3h)
    X+Y      = T_{−3h}(step2)                                          ∎
    B₁       := E(Ysq, h³, Xsq)                      = X² + h²·Y² + C h⁶
    B        := T_{−h⁶}(B₁)                          = X² + h²·Y²
    stepA1   := E(neg, −3h², C 0)                    = 6h²·Y + C(9h⁴)
                                                     (= (3/2)Y + 9/16)
    stepA2   := E(a₁, h, stepA1)                     = X + h·Y + C(17h⁴)
    A        := T_{−17h⁴}(stepA2)                    = X + h·Y
    X·Y      = q(A, B)                                                  ∎

  Each step is one `Clo.sub` application plus a ring identity modulo
  `2·h = 1` (`mul_invOf_self`), dischargeable by `linear_combination
  (cofactor) * h2` after pushing `C` through (`map_ofNat`, `C_mul`, …).
-/
import PolyClone.FrobeniusDescent.IntReduction
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace PolyClone.FrobeniusDescent

open MvPolynomial
open PolyClone.CloAddMul

variable {R : Type*} [CommRing R]

/-- The complete binary operation away from characteristic 2: `x² − y`. -/
noncomputable def qOp : MvPolynomial (Fin 2) R := X 0 ^ 2 - X 1

/-! ### Certificate infrastructure

Each certificate step is one `Clo.sub` application (`mem_q`) followed by a
rewrite of the resulting polynomial into its normal form; the ring
identities hold modulo `2 · ⅟2 = 1`, lifted to the polynomial ring as
`two_mul_C_half` and discharged by `linear_combination (cofactor) *
two_mul_C_half`. -/

/-- Transport of clone membership along a ring identity. -/
private lemma clo_congr {p e e' : MvPolynomial (Fin 2) R}
    (h : Clo p e) (heq : e = e') : Clo p e' := heq ▸ h

/-- One application of `qOp`: `a, b ∈ Clo ⟹ a² − b ∈ Clo`. -/
private lemma mem_q {a b : MvPolynomial (Fin 2) R}
    (ha : Clo (qOp : MvPolynomial (Fin 2) R) a) (hb : Clo qOp b) :
    Clo (qOp : MvPolynomial (Fin 2) R) (a ^ 2 - b) := by
  have h := Clo.sub ha hb
  rwa [show bind₁ ![a, b] (qOp : MvPolynomial (Fin 2) R) = a ^ 2 - b by
        simp [qOp, MvPolynomial.bind₁_X_right]] at h

/-- The relation `2 · h = 1` (`h := ⅟2`) lifted into the polynomial ring;
    all certificate identities hold modulo this. -/
private lemma two_mul_C_half [Invertible (2 : R)] :
    (2 : MvPolynomial (Fin 2) R) * C (⅟2 : R) = 1 := by
  have h : (C ((2 : R) * ⅟2) : MvPolynomial (Fin 2) R) = 1 := by
    rw [mul_invOf_self, map_one]
  rw [map_mul] at h
  simpa using h

/-- Translation `T_d(g) := q(C((d+1)h), q(C((d−1)h), g)) = g + C d`. -/
private lemma mem_T [Invertible (2 : R)] (d : R) {g : MvPolynomial (Fin 2) R}
    (hg : Clo (qOp : MvPolynomial (Fin 2) R) g) :
    Clo (qOp : MvPolynomial (Fin 2) R) (g + C d) := by
  refine clo_congr
    (mem_q (Clo.const ((d + 1) * ⅟2)) (mem_q (Clo.const ((d - 1) * ⅟2)) hg)) ?_
  simp only [map_mul, map_add, map_sub, map_one]
  linear_combination (C d * (2 * C (⅟2 : R) + 1)) * two_mul_C_half (R := R)

/-- The affine engine
    `E(a, k, g) := q(T_k(a), q(a, g)) = g + 2k·a + C k²` (exact identity). -/
private lemma mem_E [Invertible (2 : R)] (k : R) {a g : MvPolynomial (Fin 2) R}
    (ha : Clo (qOp : MvPolynomial (Fin 2) R) a) (hg : Clo qOp g) :
    Clo (qOp : MvPolynomial (Fin 2) R) (g + C (2 * k) * a + C (k ^ 2)) := by
  refine clo_congr (mem_q (mem_T k ha) (mem_q ha hg)) ?_
  simp only [map_mul, map_pow, map_ofNat]
  ring

/-- `neg := q(C 0, Y) = −Y`. -/
private lemma clo_neg : Clo (qOp : MvPolynomial (Fin 2) R) (-(X 1)) := by
  refine clo_congr (mem_q (Clo.const 0) Clo.atomY) ?_
  rw [map_zero]; ring

/-- `a₁ := q(X + C h, q(X, neg)) = X − Y + C h²`. -/
private lemma clo_a1 [Invertible (2 : R)] :
    Clo (qOp : MvPolynomial (Fin 2) R) (X 0 - X 1 + C ((⅟2 : R) ^ 2)) := by
  have hXsqY : Clo (qOp : MvPolynomial (Fin 2) R) (X 0 ^ 2 + X 1) :=
    clo_congr (mem_q Clo.atomX clo_neg) (by ring)
  refine clo_congr (mem_q (mem_T ⅟2 Clo.atomX) hXsqY) ?_
  simp only [map_pow]
  linear_combination (X 0 : MvPolynomial (Fin 2) R) * two_mul_C_half (R := R)

/-- `X + Y ∈ Clo qOp`: chain `step1 = 2Y + 1`, `step2 = X + Y + C(3h)`,
    then translate by `−3h`. -/
private lemma clo_addOp [Invertible (2 : R)] :
    Clo (qOp : MvPolynomial (Fin 2) R) addOp := by
  have hC2 := two_mul_C_half (R := R)
  have hstep1 : Clo (qOp : MvPolynomial (Fin 2) R) (2 * X 1 + 1) := by
    refine clo_congr (mem_E (-1) clo_neg (Clo.const 0)) ?_
    simp only [map_zero, map_mul, map_neg, map_one, map_pow, map_ofNat]
    ring
  have hstep2 : Clo (qOp : MvPolynomial (Fin 2) R)
      (X 0 + X 1 + C (3 * (⅟2 : R))) := by
    refine clo_congr (mem_E ⅟2 clo_a1 hstep1) ?_
    simp only [map_mul, map_pow, map_ofNat]
    linear_combination
      (X 0 - X 1 + C (⅟2 : R) ^ 2 + C (⅟2 : R) - 1) * hC2
  have hXY : Clo (qOp : MvPolynomial (Fin 2) R) (X 0 + X 1) := by
    refine clo_congr (mem_T (-(3 * ⅟2)) hstep2) ?_
    rw [map_neg]; ring
  simpa only [addOp] using hXY

/-- `X·Y ∈ Clo qOp`: build `B = X² + h²Y²` and `A = X + hY`, then
    `q(A, B) = X·Y`. -/
private lemma clo_mulOp [Invertible (2 : R)] :
    Clo (qOp : MvPolynomial (Fin 2) R) mulOp := by
  have hC2 := two_mul_C_half (R := R)
  have hXsq : Clo (qOp : MvPolynomial (Fin 2) R) (X 0 ^ 2) :=
    clo_congr (mem_q Clo.atomX (Clo.const 0)) (by rw [map_zero]; ring)
  have hYsq : Clo (qOp : MvPolynomial (Fin 2) R) (X 1 ^ 2) :=
    clo_congr (mem_q Clo.atomY (Clo.const 0)) (by rw [map_zero]; ring)
  -- B₁ = X² + h²·Y² + C h⁶,  B = X² + h²·Y²
  have hB1 : Clo (qOp : MvPolynomial (Fin 2) R)
      (X 0 ^ 2 + C ((⅟2 : R) ^ 2) * X 1 ^ 2 + C ((⅟2 : R) ^ 6)) := by
    refine clo_congr (mem_E (⅟2 ^ 3) hYsq hXsq) ?_
    simp only [map_mul, map_pow, map_ofNat]
    linear_combination (C (⅟2 : R) ^ 2 * X 1 ^ 2) * hC2
  have hB : Clo (qOp : MvPolynomial (Fin 2) R)
      (X 0 ^ 2 + C ((⅟2 : R) ^ 2) * X 1 ^ 2) := by
    refine clo_congr (mem_T (-(⅟2 ^ 6)) hB1) ?_
    rw [map_neg]; ring
  -- stepA1 = 6h²·Y + C(9h⁴), stepA2 = X + h·Y + C(17h⁴), A = X + h·Y
  have hA1 : Clo (qOp : MvPolynomial (Fin 2) R)
      (C (6 * (⅟2 : R) ^ 2) * X 1 + C (9 * (⅟2 : R) ^ 4)) := by
    refine clo_congr (mem_E (-(3 * ⅟2 ^ 2)) clo_neg (Clo.const 0)) ?_
    simp only [map_zero, map_mul, map_neg, map_pow, map_ofNat]
    ring
  have hA2 : Clo (qOp : MvPolynomial (Fin 2) R)
      (X 0 + C (⅟2 : R) * X 1 + C (17 * (⅟2 : R) ^ 4)) := by
    refine clo_congr (mem_E ⅟2 clo_a1 hA1) ?_
    simp only [map_mul, map_pow, map_ofNat]
    linear_combination
      (X 0 + 3 * C (⅟2 : R) * X 1 - 4 * C (⅟2 : R) ^ 3 - C (⅟2 : R) ^ 2) * hC2
  have hA : Clo (qOp : MvPolynomial (Fin 2) R) (X 0 + C (⅟2 : R) * X 1) := by
    refine clo_congr (mem_T (-(17 * ⅟2 ^ 4)) hA2) ?_
    rw [map_neg]; ring
  -- X·Y = q(A, B)
  have hXY : Clo (qOp : MvPolynomial (Fin 2) R) (X 0 * X 1) := by
    refine clo_congr (mem_q hA hB) ?_
    simp only [map_pow]
    linear_combination (X 0 * X 1 : MvPolynomial (Fin 2) R) * hC2
  simpa only [mulOp] using hXY

/-- **Completeness of `x² − y`** whenever `2` is invertible: the clone is
    everything. -/
theorem qOp_complete [Invertible (2 : R)] :
    ∀ g : MvPolynomial (Fin 2) R, Clo (qOp : MvPolynomial (Fin 2) R) g :=
  Clo.eq_top_of_addOp_mulOp clo_addOp clo_mulOp

/-- ℚ instance. -/
theorem qOp_complete_rat : ∀ g : MvPolynomial (Fin 2) ℚ, Clo qOp g :=
  letI : Invertible (2 : ℚ) := invertibleOfNonzero two_ne_zero
  qOp_complete

/-- `F₃` instance: a single polynomial operation generating ALL of
    `F₃[X,Y]`. -/
theorem qOp_complete_zmod3 : ∀ g : MvPolynomial (Fin 2) (ZMod 3), Clo qOp g :=
  letI : Invertible (2 : ZMod 3) := ⟨2, by decide, by decide⟩
  qOp_complete

/-- The DEGREE-FREE master statement (true over F₂ and ℤ) is FALSE over ℚ. -/
theorem degree_free_master_fails_rat :
    ¬ ∀ p : MvPolynomial (Fin 2) ℚ,
        ¬ Clo p (addOp : MvPolynomial (Fin 2) ℚ)
          ∨ ¬ Clo p (mulOp : MvPolynomial (Fin 2) ℚ) := by
  intro hmaster
  rcases hmaster qOp with h | h
  · exact h (qOp_complete_rat _)
  · exact h (qOp_complete_rat _)

/-- Converse direction of the dichotomy, packaged: over any ring mapping
    onto `F₂`, NO binary polynomial operation is complete. -/
theorem no_complete_op_of_hom_to_F2 (f : R →+* R2) :
    ¬ ∃ p : MvPolynomial (Fin 2) R, ∀ g, Clo p g := by
  rintro ⟨p, hp⟩
  rcases master_of_hom_to_F2 f p with h | h
  · exact h (hp _)
  · exact h (hp _)

end PolyClone.FrobeniusDescent
