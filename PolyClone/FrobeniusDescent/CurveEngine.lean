/-
  FrobeniusDescent/CurveEngine.lean
  =================================

  The char-2 `K[t]` engine: chain rule for two-variable substitution,
  Frobenius square roots, and the coprime-square dichotomy.  These are the
  curve-side identities the descent runs on (all verified symbolically in
  the Python harness before formalization).
-/
import PolyClone.FrobeniusDescent.Defs
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.RingTheory.PrincipalIdealDomain

namespace PolyClone.FrobeniusDescent

open MvPolynomial

/-- **Chain rule** for substitution of a polynomial curve:
    `(p(α,β))' = p_X(α,β)·α' + p_Y(α,β)·β'`.
    PROOF SPEC: induct on `p` (`MvPolynomial.induction_on`): on constants both
    sides vanish; additivity is linear; for `p·X i` use `derivative_mul`,
    `pderiv_mul` and `pderiv_X` (same pattern as `DXDYCocycle.pderiv_bind₁`). -/
theorem deriv_evC (p : F) (α β : Polynomial K) :
    Polynomial.derivative (evC α β p)
      = evC α β (pderiv 0 p) * Polynomial.derivative α
        + evC α β (pderiv 1 p) * Polynomial.derivative β := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [evC]
  | add p q hp hq => simp only [map_add, hp, hq]; ring
  | mul_X p j hp =>
      rw [map_mul, Polynomial.derivative_mul, hp]
      fin_cases j <;>
        · simp only [Fin.mk_zero, Fin.mk_one, Fin.isValue, pderiv_mul, map_add, map_mul,
            pderiv_X_self,
            pderiv_X_of_ne (show (1 : Fin 2) ≠ 0 by decide),
            pderiv_X_of_ne (show (0 : Fin 2) ≠ 1 by decide),
            mul_one, mul_zero, add_zero, evC_X0, evC_X1]
          ring

/-- char 2: `(a²)' = 0` in `K[t]`.
    PROOF SPEC: `Polynomial.derivative_pow` gives `2·a·a'`; char 2 kills it. -/
theorem derivative_sq' (a : Polynomial K) : Polynomial.derivative (a ^ 2) = 0 := by
  rw [pow_two, Polynomial.derivative_mul, mul_comm (Polynomial.derivative a) a,
    CharTwo.add_self_eq_zero]

/-- A `K[t]`-polynomial with zero derivative is a square (`K` is perfect).
    PROOF SPEC: `Polynomial.expand_contract 2 hp` writes `p = (contract 2 p)(t²)`;
    map the coefficients of `contract 2 p` through the inverse Frobenius of `K`
    (`frobeniusEquiv K 2`, surjective since `K` is algebraically closed) to get
    `r` with `r² = p`: compare coefficients via the freshman's dream. -/
theorem exists_sq_of_derivative_eq_zero (p : Polynomial K)
    (hp : Polynomial.derivative p = 0) : ∃ r : Polynomial K, p = r ^ 2 := by
  classical
  have hexp : Polynomial.expand K 2 (Polynomial.contract 2 p) = p :=
    Polynomial.expand_contract 2 hp two_ne_zero
  refine ⟨(Polynomial.contract 2 p).map ((frobeniusEquiv K 2).symm : K →+* K), ?_⟩
  have h1 : ((Polynomial.contract 2 p).map ((frobeniusEquiv K 2).symm : K →+* K)).map
      (frobenius K 2) = Polynomial.contract 2 p := by
    rw [Polynomial.map_map, frobenius_comp_frobeniusEquiv_symm, Polynomial.map_id]
  have h2 := Polynomial.map_frobenius_expand (p := 2)
    ((Polynomial.contract 2 p).map ((frobeniusEquiv K 2).symm : K →+* K))
  rw [Polynomial.map_expand, h1, hexp] at h2
  exact h2

set_option linter.unusedVariables false in
/-- Two nonzero polynomials over an algebraically closed field are coprime or
    share a root.
    PROOF SPEC: if `EuclideanDomain.gcd A B` is a unit they are coprime;
    otherwise the gcd is nonzero (gcd of nonzeros) and nonunit, hence has
    positive degree, hence a root `θ` (`IsAlgClosed.exists_root`), which is a
    common root via `EuclideanDomain.gcd_dvd_left/right`.
    (`hA`, `hB` are unused: `IsAlgClosed.exists_root` covers the degenerate
    cases; they are kept for the interface `Descent.lean` compiles against.) -/
theorem isCoprime_or_common_root (A B : Polynomial K) (hA : A ≠ 0) (hB : B ≠ 0) :
    IsCoprime A B ∨ ∃ θ : K, A.eval θ = 0 ∧ B.eval θ = 0 := by
  classical
  by_cases h : IsUnit (EuclideanDomain.gcd A B)
  · exact Or.inl (EuclideanDomain.gcd_isUnit_iff.mp h)
  · right
    have hdeg : (EuclideanDomain.gcd A B).degree ≠ 0 := fun hd =>
      h (Polynomial.isUnit_iff_degree_eq_zero.mpr hd)
    obtain ⟨θ, hθ⟩ := IsAlgClosed.exists_root (EuclideanDomain.gcd A B) hdeg
    exact ⟨θ,
      Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (EuclideanDomain.gcd_dvd_left A B) hθ,
      Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (EuclideanDomain.gcd_dvd_right A B) hθ⟩

/-- A polynomial associated to a square is a square (units of `K[t]` are
    constants and every constant is a square since `K` is algebraically
    closed). -/
private lemma sq_of_associated_sq {A d : Polynomial K} (h : Associated (d ^ 2) A) :
    ∃ a : Polynomial K, A = a ^ 2 := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨k, hk, hCk⟩ := Polynomial.isUnit_iff.mp u.isUnit
  obtain ⟨v, hv⟩ := exists_sqrt k
  refine ⟨Polynomial.C v * d, ?_⟩
  rw [← hu, ← hCk, ← hv, mul_pow, ← Polynomial.C_pow, mul_comm]

/-- Coprime factors of a square are squares (in `K[t]`, where every unit is a
    square because `K` is algebraically closed).
    PROOF SPEC: `exists_associated_pow_of_mul_eq_pow` (UFD/GCD-monoid form;
    `Polynomial K` is a `NormalizedGCDMonoid`) gives `A ~ d²`; the associating
    unit is a nonzero constant `C u`, and `u = v²` (`exists_sqrt`), so
    `A = (C v · d)²`.  Symmetrically for `B`. -/
theorem sq_of_coprime_of_mul_sq (A B e : Polynomial K) (hAB : IsCoprime A B)
    (he : A * B = e ^ 2) :
    (∃ a : Polynomial K, A = a ^ 2) ∧ (∃ b : Polynomial K, B = b ^ 2) := by
  obtain ⟨d, hd⟩ := exists_associated_pow_of_mul_eq_pow' hAB he
  obtain ⟨d', hd'⟩ := exists_associated_pow_of_mul_eq_pow' hAB.symm
    (by rw [mul_comm]; exact he)
  exact ⟨sq_of_associated_sq hd, sq_of_associated_sq hd'⟩

/-- Squaring is injective on `K[t]` (char 2, domain):
    `(a+b)² = a² + b² = 0 ⟹ a + b = 0 ⟹ a = b`. -/
theorem sq_inj {a b : Polynomial K} (h : a ^ 2 = b ^ 2) : a = b :=
  CharTwo.sq_injective h

/-- Substituting squared curves = squaring the substitution (coefficients in
    `F₂` are Frobenius-fixed).
    PROOF SPEC: both sides are ring homs in `p` (`MvPolynomial.ringHom_ext`):
    on `C a` they give `castK a` vs `(castK a)²`, equal since `a ∈ {0,1}`;
    on `X i` both give `α²` resp. `β²`. -/
theorem evC_frobenius (p : F) (α β : Polynomial K) :
    evC (α ^ 2) (β ^ 2) p = (evC α β p) ^ 2 := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      have ha : castK a ^ 2 = castK a := by
        rw [← map_pow]
        congr 1
        revert a; decide
      simp only [evC, eval₂Hom_C, RingHom.coe_comp, Function.comp_apply]
      rw [← Polynomial.C_pow, ha]
  | add p q hp hq =>
      rw [map_add, map_add, hp, hq, CharTwo.add_sq]
  | mul_X p j hp =>
      rw [map_mul, map_mul, hp, mul_pow]
      fin_cases j <;> simp

end PolyClone.FrobeniusDescent
