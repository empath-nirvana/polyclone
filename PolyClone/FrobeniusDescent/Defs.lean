/-
  FrobeniusDescent/Defs.lean
  ==========================

  Shared setting for the **Frobenius-depth descent** proof of the F₂ master
  conjecture's open half:

      `∂_X∂_Y q ≠ 0  ⟹  q is tame  ⟹  X+Y ∉ Clo q`.

  Combined with the D-cocycle theorem (`∂_X∂_Y q = 0 ⟹ X·Y ∉ Clo q`,
  `DXDYCocycle.lean`), this closes `¬Clo q (X+Y) ∨ ¬Clo q (X·Y)` for EVERY
  `q ∈ F₂[X,Y]` — see `FrobeniusDescent/Main.lean`.

  This file fixes the curve-side base field and the evaluation maps:

  * `K = AlgebraicClosure (RatFunc F₂)` — algebraically closed, char 2,
    containing elements transcendental over F₂ (e.g. `σK`).
  * `evC α β : F₂[X,Y] →+* K[t]` — evaluation along a polynomial curve
    `(α, β) ∈ K[t]²`.
  * `evP x y : F₂[X,Y] →+* K` — evaluation at a point `(x, y) ∈ K²`.
  * `AlgebraicF2 c` — `c : K` is algebraic over the prime field, stated via
    an explicit `eval₂` (no `Algebra (ZMod 2) K` instance commitments).

  A *witness* (of untameness) is a pair `(α, β) ∈ K[t]²`, not both constant,
  with `q(α,β) = C c` for some `c` transcendental over F₂.  The descent
  theorem (`Descent.lean`) shows no witness exists when `∂_X∂_Y q ≠ 0`.
-/
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.ZMod.Basic

namespace PolyClone.FrobeniusDescent

open MvPolynomial

instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

abbrev R2 : Type := ZMod 2
abbrev F : Type := MvPolynomial (Fin 2) R2

/-- The curve-side base field `k = alg.cl.(F₂(T))`. -/
abbrev K : Type := AlgebraicClosure (RatFunc R2)

instance : CharP (RatFunc R2) 2 :=
  charP_of_injective_algebraMap (algebraMap R2 (RatFunc R2)).injective 2

instance : CharP K 2 :=
  charP_of_injective_algebraMap (algebraMap (RatFunc R2) K).injective 2

instance : CharP (Polynomial K) 2 :=
  charP_of_injective_algebraMap (algebraMap K (Polynomial K)).injective 2

/-- The canonical embedding `F₂ → K`. -/
noncomputable def castK : R2 →+* K := ZMod.castHom (dvd_refl 2) K

/-- `c : K` is algebraic over the prime field `F₂`. -/
def AlgebraicF2 (c : K) : Prop :=
  ∃ g : Polynomial R2, g ≠ 0 ∧ Polynomial.eval₂ castK c g = 0

/-- Evaluation of `p ∈ F₂[X,Y]` along a polynomial curve `(α, β) ∈ K[t]²`. -/
noncomputable def evC (α β : Polynomial K) : F →+* Polynomial K :=
  eval₂Hom ((Polynomial.C : K →+* Polynomial K).comp castK) ![α, β]

/-- Evaluation of `p ∈ F₂[X,Y]` at a point `(x, y) ∈ K²`. -/
noncomputable def evP (x y : K) : F →+* K := eval₂Hom castK ![x, y]

@[simp] lemma evC_X0 (α β : Polynomial K) : evC α β (X 0) = α := by simp [evC]
@[simp] lemma evC_X1 (α β : Polynomial K) : evC α β (X 1) = β := by simp [evC]
@[simp] lemma evP_X0 (x y : K) : evP x y (X 0) = x := by simp [evP]
@[simp] lemma evP_X1 (x y : K) : evP x y (X 1) = y := by simp [evP]

/-- Point evaluation of a curve evaluation = evaluation at the curve's point.
    PROOF SPEC: both sides are ring homs `F →+* K` agreeing on `C` and `X i`;
    use `MvPolynomial.ringHom_ext` (or induct on `p`). -/
@[simp] lemma eval_evC (p : F) (α β : Polynomial K) (θ : K) :
    Polynomial.eval θ (evC α β p) = evP (Polynomial.eval θ α) (Polynomial.eval θ β) p := by
  have h : (Polynomial.evalRingHom θ).comp (evC α β) =
      evP (Polynomial.eval θ α) (Polynomial.eval θ β) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [evC, evP]
    · intro i
      fin_cases i <;> simp
  exact RingHom.congr_fun h p

/-- Every element of `K` has a square root (algebraically closed). -/
lemma exists_sqrt (c : K) : ∃ r : K, r ^ 2 = c :=
  IsAlgClosed.exists_pow_nat_eq c (by norm_num : (0:ℕ) < 2)

/-! ### Closure properties of `AlgebraicF2`

PROOF SPEC: the set of `AlgebraicF2` elements is the integral closure of the
image of `castK` in `K` (algebraic = integral over a field).  Either transport
to Mathlib's `IsAlgebraic`/`IsIntegral` over the subfield `castK.range` (or
`⊥ : Subfield K`, since `castK` hits exactly `{0,1}`), or prove the closure
properties directly. -/

lemma algebraicF2_castK (a : R2) : AlgebraicF2 (castK a) :=
  ⟨Polynomial.X - Polynomial.C a, Polynomial.X_sub_C_ne_zero a, by
    simp [Polynomial.eval₂_sub]⟩

/-- `AlgebraicF2` agrees with Mathlib's `IsAlgebraic` for the canonical
`Algebra R2 K` instance: ring homs out of `ZMod 2` are unique
(`ZMod.subsingleton_ringHom`), so `algebraMap R2 K = castK`. -/
private lemma algebraicF2_iff_isAlgebraic {c : K} :
    AlgebraicF2 c ↔ IsAlgebraic R2 c := by
  have hmap : algebraMap R2 K = castK := Subsingleton.elim _ _
  constructor
  · rintro ⟨g, hg, hgc⟩
    exact ⟨g, hg, by rw [Polynomial.aeval_def, hmap]; exact hgc⟩
  · rintro ⟨g, hg, hgc⟩
    rw [Polynomial.aeval_def, hmap] at hgc
    exact ⟨g, hg, hgc⟩

lemma AlgebraicF2.add {c d : K} (hc : AlgebraicF2 c) (hd : AlgebraicF2 d) :
    AlgebraicF2 (c + d) :=
  algebraicF2_iff_isAlgebraic.mpr
    (((algebraicF2_iff_isAlgebraic.mp hc).isIntegral.add
      (algebraicF2_iff_isAlgebraic.mp hd).isIntegral).isAlgebraic)

lemma AlgebraicF2.mul {c d : K} (hc : AlgebraicF2 c) (hd : AlgebraicF2 d) :
    AlgebraicF2 (c * d) :=
  algebraicF2_iff_isAlgebraic.mpr
    (((algebraicF2_iff_isAlgebraic.mp hc).isIntegral.mul
      (algebraicF2_iff_isAlgebraic.mp hd).isIntegral).isAlgebraic)

lemma AlgebraicF2.sq {c : K} (h : AlgebraicF2 c) : AlgebraicF2 (c ^ 2) := by
  rw [pow_two]; exact h.mul h

/-- A square root of an algebraic element is algebraic.
    PROOF SPEC: from `g ≠ 0` with `g(c²) = 0`, the polynomial `g(Z²)`
    (i.e. `g.comp (X^2)`, nonzero since `comp` with `X^2` multiplies degrees)
    vanishes at `c`. -/
lemma AlgebraicF2.of_sq {c : K} (h : AlgebraicF2 (c ^ 2)) : AlgebraicF2 c := by
  obtain ⟨g, hg, hgc⟩ := h
  refine ⟨g.comp (Polynomial.X ^ 2), ?_, ?_⟩
  · intro h0
    rcases Polynomial.comp_eq_zero_iff.mp h0 with h1 | ⟨-, h2⟩
    · exact hg h1
    · have h3 := congrArg Polynomial.natDegree h2
      simp at h3
  · rw [Polynomial.eval₂_comp]
    simpa using hgc

/-- `F₂`-polynomial expressions in algebraic quantities are algebraic.
    PROOF SPEC: induct on `p` (`MvPolynomial.induction_on`), using
    `algebraicF2_castK`, `.add`, `.mul` and `hx`, `hy` at the generators. -/
lemma algebraicF2_evP (p : F) (x y : K) (hx : AlgebraicF2 x) (hy : AlgebraicF2 y) :
    AlgebraicF2 (evP x y p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa [evP] using algebraicF2_castK a
  | add p q hp hq => rw [map_add]; exact hp.add hq
  | mul_X p i hp =>
    rw [map_mul]
    refine hp.mul ?_
    fin_cases i
    · simpa using hx
    · simpa using hy

/-- The distinguished transcendental: the image in `K` of the variable of
    `F₂(T)`. -/
noncomputable def σK : K := algebraMap (RatFunc R2) K RatFunc.X

/-- `σK` is transcendental over `F₂`.
    PROOF SPEC: a nonzero `g ∈ F₂[Z]` with `g(σK) = 0` pulls back along the
    injective `algebraMap (RatFunc R2) K` to `g(RatFunc.X) = 0` in `F₂(T)`,
    contradicting the transcendence of `RatFunc.X` (its `algebraMap` from
    `F₂[T]` is injective: `RatFunc.algebraMap_injective` /
    `Polynomial.algebraMap_RatFunc...`). -/
lemma σK_transcendental : ¬ AlgebraicF2 σK := by
  rintro ⟨g, hg, hgσ⟩
  -- Ring homs out of `ZMod 2` are unique, so we may factor `castK` through
  -- `RatFunc R2` (and further through `Polynomial R2`).
  have hcast : castK = (algebraMap (RatFunc R2) K).comp (algebraMap R2 (RatFunc R2)) :=
    Subsingleton.elim _ _
  rw [hcast, show σK = algebraMap (RatFunc R2) K RatFunc.X from rfl,
    ← Polynomial.hom_eval₂] at hgσ
  have h2 : Polynomial.eval₂ (algebraMap R2 (RatFunc R2)) RatFunc.X g = 0 :=
    (algebraMap (RatFunc R2) K).injective (by simpa using hgσ)
  have hcast2 : algebraMap R2 (RatFunc R2) =
      (algebraMap (Polynomial R2) (RatFunc R2)).comp (Polynomial.C : R2 →+* Polynomial R2) :=
    Subsingleton.elim _ _
  rw [hcast2, ← RatFunc.algebraMap_X, ← Polynomial.hom_eval₂, Polynomial.eval₂_C_X] at h2
  exact hg (RatFunc.algebraMap_injective R2 (by simpa using h2))

end PolyClone.FrobeniusDescent
