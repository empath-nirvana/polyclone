/-
  FrobeniusDescentP/Defs.lean
  ===========================

  Parametrized generalization of `FrobeniusDescent/` from `F₂ = ZMod 2`
  to an arbitrary PERFECT field `Fq` of characteristic 2 (finite fields
  `F_{2^k}`, algebraic closures, etc.).

  Differences from the `F₂` development:
  * `AlgebraicF2` is replaced by Mathlib's `IsAlgebraic Fq` (the algebra
    structure `Algebra Fq (K Fq)` is canonical, so no instance-free
    contortions are needed).
  * NEW: the coefficient Frobenius twist `half2 q` (= `q^{(1/2)}`,
    coefficient-wise square roots via `frobeniusEquiv`), with the twisted
    Frobenius identity `(evC α β (half2 q))² = evC (α²) (β²) q`.
    Over `ZMod 2` the twist is the identity and this is the old
    `evC_frobenius`.  In the descent, the halving branch produces a
    witness for `half2 q` instead of `q`; the induction quantifies over
    `q` inside, so no orbit/periodicity bookkeeping is needed.
-/
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.Perfect
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.RingTheory.Algebraic.Basic
import PolyClone.DXDYCocycle

set_option linter.unusedSectionVars false

namespace PolyClone.Perfect

open MvPolynomial

instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable (Fq : Type) [Field Fq] [CharP Fq 2] [PerfectRing Fq 2]

abbrev F : Type := MvPolynomial (Fin 2) Fq

/-- The curve-side base field `K = alg.cl.(Fq(T))`. -/
abbrev K : Type := AlgebraicClosure (RatFunc Fq)

instance : CharP (RatFunc Fq) 2 :=
  charP_of_injective_algebraMap (algebraMap Fq (RatFunc Fq)).injective 2

instance : CharP (K Fq) 2 :=
  charP_of_injective_algebraMap (algebraMap (RatFunc Fq) (K Fq)).injective 2

instance : CharP (Polynomial (K Fq)) 2 :=
  charP_of_injective_algebraMap (algebraMap (K Fq) (Polynomial (K Fq))).injective 2

/-- The canonical embedding `Fq → K` (the algebra map through `Fq(T)`). -/
noncomputable def castK : Fq →+* K Fq := algebraMap Fq (K Fq)

/-- Evaluation of `p ∈ Fq[X,Y]` along a polynomial curve `(α, β) ∈ K[t]²`. -/
noncomputable def evC (α β : Polynomial (K Fq)) : F Fq →+* Polynomial (K Fq) :=
  eval₂Hom ((Polynomial.C : K Fq →+* Polynomial (K Fq)).comp (castK Fq)) ![α, β]

/-- Evaluation of `p ∈ Fq[X,Y]` at a point `(x, y) ∈ K²`. -/
noncomputable def evP (x y : K Fq) : F Fq →+* K Fq := eval₂Hom (castK Fq) ![x, y]

variable {Fq}

@[simp] lemma evC_X0 (α β : Polynomial (K Fq)) : evC Fq α β (X 0) = α := by
  simp [evC]
@[simp] lemma evC_X1 (α β : Polynomial (K Fq)) : evC Fq α β (X 1) = β := by
  simp [evC]
@[simp] lemma evP_X0 (x y : K Fq) : evP Fq x y (X 0) = x := by simp [evP]
@[simp] lemma evP_X1 (x y : K Fq) : evP Fq x y (X 1) = y := by simp [evP]

/-- Point evaluation of a curve evaluation = evaluation at the curve's point.
    PROOF SPEC: `MvPolynomial.ringHom_ext` as in `FrobeniusDescent/Defs.lean`. -/
@[simp] lemma eval_evC (p : F Fq) (α β : Polynomial (K Fq)) (θ : K Fq) :
    Polynomial.eval θ (evC Fq α β p)
      = evP Fq (Polynomial.eval θ α) (Polynomial.eval θ β) p := by
  have h : (Polynomial.evalRingHom θ).comp (evC Fq α β) =
      evP Fq (Polynomial.eval θ α) (Polynomial.eval θ β) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [evC, evP]
    · intro i
      fin_cases i <;> simp
  exact RingHom.congr_fun h p

/-- Every element of `K` has a square root (algebraically closed). -/
lemma exists_sqrt (c : K Fq) : ∃ r : K Fq, r ^ 2 = c :=
  IsAlgClosed.exists_pow_nat_eq c (by norm_num : (0:ℕ) < 2)

/-! ### Algebraicity over `Fq` (Mathlib-native this time) -/

/-- A square root of an algebraic element is algebraic.
    PROOF SPEC: annihilator `g.comp (X^2)` as in the F₂ version, or via
    `IsAlgebraic` of `c^2` and field towers. -/
lemma isAlgebraic_of_sq {c : K Fq} (h : IsAlgebraic Fq (c ^ 2)) :
    IsAlgebraic Fq c :=
  h.of_pow two_pos

lemma IsAlgebraic.sq' {c : K Fq} (h : IsAlgebraic Fq c) :
    IsAlgebraic Fq (c ^ 2) := by
  rw [sq]; exact h.mul h

/-- `Fq`-polynomial expressions in algebraic quantities are algebraic.
    PROOF SPEC: `MvPolynomial.induction_on` with `IsAlgebraic.add/.mul`
    (or `isAlgebraic_algebraMap` + integrality closure); note
    `evP Fq x y (C a) = castK Fq a = algebraMap Fq (K Fq) a`. -/
lemma isAlgebraic_evP (p : F Fq) (x y : K Fq)
    (hx : IsAlgebraic Fq x) (hy : IsAlgebraic Fq y) :
    IsAlgebraic Fq (evP Fq x y p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      have hC : evP Fq x y (MvPolynomial.C a) = algebraMap Fq (K Fq) a := by
        simp [evP, castK]
      rw [hC]
      exact isAlgebraic_algebraMap a
  | add p q hp hq => rw [map_add]; exact hp.add hq
  | mul_X p i hp =>
      rw [map_mul]
      refine hp.mul ?_
      fin_cases i
      · simpa using hx
      · simpa using hy

/-- The distinguished transcendental: image of the variable of `Fq(T)`. -/
noncomputable def σK : K Fq := algebraMap (RatFunc Fq) (K Fq) RatFunc.X

/-- `σK` is transcendental over `Fq`.
    PROOF SPEC: pull a nonzero annihilator back along the injective
    `algebraMap (RatFunc Fq) (K Fq)`; `RatFunc.X` is transcendental over
    `Fq` (Mathlib: `RatFunc.transcendental_X` or via
    `RatFunc.algebraMap_injective` as in the F₂ version — watch that
    `aeval` here is along `Algebra Fq (RatFunc Fq)`). -/
lemma σK_transcendental : ¬ IsAlgebraic Fq (σK (Fq := Fq)) := by
  have h : Transcendental Fq (algebraMap (RatFunc Fq) (K Fq) RatFunc.X) := by
    rw [transcendental_algebraMap_iff (algebraMap (RatFunc Fq) (K Fq)).injective,
      ← RatFunc.algebraMap_X,
      transcendental_algebraMap_iff (RatFunc.algebraMap_injective Fq)]
    exact Polynomial.transcendental_X Fq
  exact h

/-! ### The coefficient Frobenius twist -/

variable (Fq)

/-- Coefficient-wise square root: `half2 q = q^{(1/2)}`.
    Over `ZMod 2` this is the identity. -/
noncomputable def half2 (q : F Fq) : F Fq :=
  MvPolynomial.map ((frobeniusEquiv Fq 2).symm : Fq →+* Fq) q

variable {Fq}

private lemma half2_C (a : Fq) :
    half2 Fq (MvPolynomial.C a)
      = MvPolynomial.C ((frobeniusEquiv Fq 2).symm a) :=
  MvPolynomial.map_C _ a

private lemma half2_add (p q : F Fq) :
    half2 Fq (p + q) = half2 Fq p + half2 Fq q :=
  map_add (MvPolynomial.map _) p q

private lemma half2_mul (p q : F Fq) :
    half2 Fq (p * q) = half2 Fq p * half2 Fq q :=
  map_mul (MvPolynomial.map _) p q

private lemma half2_X (i : Fin 2) : half2 Fq (X i) = X i :=
  MvPolynomial.map_X _ i

/-- The defining property coefficient-wise: `(half2 q)` squared back is `q`.
    PROOF SPEC: `map` composition + `frobenius_apply_frobeniusEquiv_symm`-style
    cancellation; or coefficient extensionality. -/
lemma map_frobenius_half2 (q : F Fq) :
    MvPolynomial.map (frobenius Fq 2) (half2 Fq q) = q := by
  rw [half2, MvPolynomial.map_map, frobenius_comp_frobeniusEquiv_symm,
    MvPolynomial.map_id]

/-- `half2` is injective (it is `map` of a ring equivalence). -/
lemma half2_injective : Function.Injective (half2 Fq) := by
  intro a b h
  exact MvPolynomial.map_injective _ (frobeniusEquiv Fq 2).symm.injective h

/-- **The twisted Frobenius identity**: substituting squared curves into `q`
    is the square of substituting the curves into `q^{(1/2)}`.
    Over `ZMod 2` (`half2 = id`) this is the old `evC_frobenius`.
    PROOF SPEC: both sides are ring homs in `q` (`MvPolynomial.ringHom_ext`):
    on `C a` the left side gives `(C (castK (frobeniusEquiv⁻¹ a)))² =
    C (castK a)` since `castK` commutes with `frobenius` and
    `(frobeniusEquiv⁻¹ a)² = a`; on `X i` both give `α²` resp. `β²`. -/
lemma evC_half2_sq (q : F Fq) (α β : Polynomial (K Fq)) :
    (evC Fq α β (half2 Fq q)) ^ 2 = evC Fq (α ^ 2) (β ^ 2) q := by
  induction q using MvPolynomial.induction_on with
  | C a =>
      rw [half2_C]
      simp only [evC, eval₂Hom_C, RingHom.coe_comp, Function.comp_apply]
      rw [← Polynomial.C_pow, ← map_pow]
      congr 1
      have h := frobenius_apply_frobeniusEquiv_symm (R := Fq) (p := 2) a
      rw [frobenius_def] at h
      rw [h]
  | add p q hp hq =>
      rw [half2_add, map_add, map_add, CharTwo.add_sq, hp, hq]
  | mul_X p i hp =>
      rw [half2_mul, half2_X, map_mul, map_mul, mul_pow, hp]
      congr 1
      fin_cases i <;> simp

/-- `D` commutes with the coefficient twist (formal derivatives commute with
    coefficient ring maps).
    PROOF SPEC: `pderiv` commutes with `MvPolynomial.map` —
    `MvPolynomial.pderiv_map` if available, else induct. -/
lemma D_half2 (q : F Fq) :
    PolyClone.DXDYCocycle.D (half2 Fq q)
      = half2 Fq (PolyClone.DXDYCocycle.D q) := by
  simp only [PolyClone.DXDYCocycle.D_def, half2,
    MvPolynomial.pderiv_map]

/-- The twist preserves nonvanishing of `D`. -/
lemma D_half2_ne_zero {q : F Fq}
    (h : PolyClone.DXDYCocycle.D q ≠ 0) :
    PolyClone.DXDYCocycle.D (half2 Fq q) ≠ 0 := by
  intro h0
  apply h
  apply half2_injective
  rw [← D_half2, h0]
  simp [half2]

end PolyClone.Perfect
