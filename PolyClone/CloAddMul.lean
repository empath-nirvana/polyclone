/-
  PolyClone.CloAddMul
  ======================================

  **The substitution clone and its closure under `+` and `·`.**

  This file formalizes a clean algebraic observation: if the substitution
  clone of `p` contains both `X + Y` (= `addOp`) and `X · Y` (= `mulOp`),
  then it equals the whole polynomial ring `R[X, Y]`.

  The argument is purely syntactic and works over any commutative ring `R`.
  Combined with a *separate* result that `Clo(p) ⊊ R[X, Y]` for non-trivial
  `p` (which, over uncountable `R` like `ℝ` or `ℂ`, follows trivially from
  a dimension count), this yields the master conjecture over uncountable
  carriers as an immediate corollary.

  The non-trivial open case (`R = ℤ`) remains open because the dimension
  argument doesn't apply when both sides have the same (countable)
  cardinality. The Mal'cev clone form (in `Integers.lean`) is the active
  formulation for that case.

  ## Contents

  * `Clo p` — substitution closure of `{X, Y} ∪ R-constants` under
    `(α, β) ↦ p(α, β)`.
  * `Clo.subst` — substituting `α, β ∈ Clo` for the variables of any
    `q ∈ Clo` gives a polynomial again in `Clo`.
  * `Clo.add` / `Clo.mul` — if `addOp ∈ Clo p` (resp. `mulOp ∈ Clo p`),
    then `Clo p` is closed under addition (resp. multiplication) of its
    elements.
  * `Clo.eq_top_of_addOp_mulOp` — if both `addOp ∈ Clo p` and `mulOp ∈
    Clo p`, then `Clo p q` for every polynomial `q`.

  The contrapositive of `eq_top_of_addOp_mulOp` is the master conjecture
  in its substitution-clone form: if there is *any* polynomial not in
  `Clo p`, then at least one of `+` or `·` is also not in `Clo p`.
-/

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

namespace PolyClone.CloAddMul

open MvPolynomial

variable {R : Type*} [CommRing R]

/-! ## The substitution clone -/

/-- The substitution clone of `p ∈ R[X, Y]`: the smallest subset of
    `R[X, Y]` containing the variables `X = X 0`, `Y = X 1`, all
    `R`-constants, and closed under `(α, β) ↦ p(α, β)`. -/
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

/-! ## Substitution lemma

The key inductive lemma: if `α, β` are in `Clo p`, then for any `q ∈ Clo p`,
the polynomial `bind₁ ![α, β] q` (= `q` with `X 0 ↦ α` and `X 1 ↦ β`) is
also in `Clo p`.

This is the syntactic substitution that powers `Clo.add` and `Clo.mul`. -/

/-- **Substitution lemma.** `Clo p` is closed under substituting any of
    its elements for the variables of any other of its elements. -/
theorem Clo.subst {p : MvPolynomial (Fin 2) R}
    {α β : MvPolynomial (Fin 2) R}
    (hα : Clo p α) (hβ : Clo p β) :
    ∀ {q : MvPolynomial (Fin 2) R}, Clo p q →
      Clo p (bind₁ ![α, β] q) := by
  intro q hq
  induction hq with
  | atomX =>
    rw [show bind₁ ![α, β] (X 0 : MvPolynomial (Fin 2) R) = α from by
        rw [MvPolynomial.bind₁_X_right]; rfl]
    exact hα
  | atomY =>
    rw [show bind₁ ![α, β] (X 1 : MvPolynomial (Fin 2) R) = β from by
        rw [MvPolynomial.bind₁_X_right]; rfl]
    exact hβ
  | const c =>
    rw [MvPolynomial.bind₁_C_right]
    exact .const c
  | sub _ _ ih_α' ih_β' =>
    -- q = bind₁ ![α', β'] p. Apply bind₁ ![α, β] and use composition:
    --   bind₁ ![α, β] (bind₁ ![α', β'] p) = bind₁ ![bind₁ ![α, β] α', bind₁ ![α, β] β'] p
    -- Then apply `sub` with IH-supplied premises.
    rename_i α' β' _ _
    have h_comp :
        bind₁ ![α, β] (bind₁ ![α', β'] p)
          = bind₁ ![bind₁ ![α, β] α', bind₁ ![α, β] β'] p := by
      rw [bind₁_bind₁]
      have : (fun i : Fin 2 => bind₁ ![α, β] (![α', β'] i))
          = ![bind₁ ![α, β] α', bind₁ ![α, β] β'] := by
        funext i; fin_cases i <;> rfl
      rw [this]
    rw [h_comp]
    exact .sub ih_α' ih_β'

/-! ## Closure under `+` and `·` -/

/-- If `addOp ∈ Clo p`, then `Clo p` is closed under addition of its elements. -/
theorem Clo.add {p : MvPolynomial (Fin 2) R}
    (h_add : Clo p (addOp : MvPolynomial (Fin 2) R))
    {α β : MvPolynomial (Fin 2) R}
    (hα : Clo p α) (hβ : Clo p β) :
    Clo p (α + β) := by
  have h := Clo.subst hα hβ h_add
  -- bind₁ ![α, β] (X 0 + X 1) = α + β.
  rwa [show bind₁ ![α, β] (addOp : MvPolynomial (Fin 2) R) = α + β by
        simp [addOp, MvPolynomial.bind₁_X_right]] at h

/-- If `mulOp ∈ Clo p`, then `Clo p` is closed under multiplication of its elements. -/
theorem Clo.mul {p : MvPolynomial (Fin 2) R}
    (h_mul : Clo p (mulOp : MvPolynomial (Fin 2) R))
    {α β : MvPolynomial (Fin 2) R}
    (hα : Clo p α) (hβ : Clo p β) :
    Clo p (α * β) := by
  have h := Clo.subst hα hβ h_mul
  rwa [show bind₁ ![α, β] (mulOp : MvPolynomial (Fin 2) R) = α * β by
        simp [mulOp, MvPolynomial.bind₁_X_right]] at h

/-! ## Step 1: Containing `addOp` and `mulOp` forces `Clo p` to be everything

If `Clo p` contains both `addOp = X + Y` and `mulOp = X · Y`, then it
contains every polynomial in `R[X, Y]`. The argument is induction on
`MvPolynomial.induction_on`: every polynomial is built from constants
via `+` and `* X i`, and `Clo p` is closed under these. -/

/-- **Step 1.** If both `addOp ∈ Clo p` and `mulOp ∈ Clo p`, then every
    polynomial in `R[X, Y]` is in `Clo p`. -/
theorem Clo.eq_top_of_addOp_mulOp
    {p : MvPolynomial (Fin 2) R}
    (h_add : Clo p (addOp : MvPolynomial (Fin 2) R))
    (h_mul : Clo p (mulOp : MvPolynomial (Fin 2) R)) :
    ∀ q : MvPolynomial (Fin 2) R, Clo p q := by
  intro q
  induction q using MvPolynomial.induction_on with
  | C a => exact .const a
  | add q r ih_q ih_r => exact Clo.add h_add ih_q ih_r
  | mul_X q i ih_q =>
    refine Clo.mul h_mul ih_q ?_
    fin_cases i
    · exact .atomX
    · exact .atomY

/-! ## Contrapositive: the master conjecture in substitution-clone form

The master conjecture says no `p` has both `addOp` and `mulOp` in its
substitution clone. By `eq_top_of_addOp_mulOp`, it suffices to show
`Clo p ⊊ R[X, Y]` — i.e., there exists *some* polynomial not in `Clo p`. -/

/-- **Master conjecture in clone form.** For any `p ∈ R[X, Y]`, NOT both
    `addOp` and `mulOp` lie in `Clo p`, *if and only if* there exists
    some polynomial not in `Clo p`. -/
theorem Clo.notBothAddMul_iff_proper
    (p : MvPolynomial (Fin 2) R) :
    ¬ (Clo p (addOp : MvPolynomial (Fin 2) R)
        ∧ Clo p (mulOp : MvPolynomial (Fin 2) R))
      ↔ ∃ q, ¬ Clo p q := by
  constructor
  · intro h_not_both
    by_contra h_neg
    push_neg at h_neg
    -- All polynomials are in Clo. In particular addOp and mulOp.
    exact h_not_both ⟨h_neg addOp, h_neg mulOp⟩
  · rintro ⟨q, hq⟩ ⟨h_add, h_mul⟩
    exact hq (Clo.eq_top_of_addOp_mulOp h_add h_mul q)

/-- **Master conjecture (clone form).** For a ring `R` and a polynomial
    `p`, the master conjecture for `p` is equivalent to `Clo p` being a
    *proper* subset of `R[X, Y]`. -/
def MasterConjecture (R : Type*) [CommRing R] : Prop :=
  ∀ (p : MvPolynomial (Fin 2) R),
    p.totalDegree ≥ 3 →
    ¬ (Clo p (addOp : MvPolynomial (Fin 2) R)
        ∧ Clo p (mulOp : MvPolynomial (Fin 2) R))

/-- **Reduction.** For any commutative ring `R`, the master conjecture
    is equivalent to: every polynomial of total degree ≥ 3 has its
    substitution clone *strictly* contained in `R[X, Y]`. -/
theorem masterConjecture_iff_proper :
    MasterConjecture R ↔
      ∀ (p : MvPolynomial (Fin 2) R), p.totalDegree ≥ 3 →
        ∃ q, ¬ Clo p q := by
  unfold MasterConjecture
  refine ⟨fun h p hp => ?_, fun h p hp => ?_⟩
  · exact (Clo.notBothAddMul_iff_proper p).mp (h p hp)
  · exact (Clo.notBothAddMul_iff_proper p).mpr (h p hp)

end PolyClone.CloAddMul
