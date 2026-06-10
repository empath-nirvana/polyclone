/-
  FrobeniusDescentP/CurveEngine.lean
  ==================================

  Parametric port of `FrobeniusDescent/CurveEngine.lean` from `ZMod 2`
  coefficients to a perfect field `Fq` of characteristic 2: chain rule for
  two-variable substitution, Frobenius square roots, and the coprime-square
  dichotomy.  (`evC_frobenius` is NOT ported here; its generalization
  `evC_half2_sq` lives in `FrobeniusDescentP/Defs.lean`.)
-/
import PolyClone.Perfect.Defs
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.RingTheory.PrincipalIdealDomain

namespace PolyClone.Perfect

open MvPolynomial

set_option linter.unusedSectionVars false

variable {Fq : Type} [Field Fq] [CharP Fq 2] [PerfectRing Fq 2]

/-- **Chain rule** for substitution of a polynomial curve:
    `(p(α,β))' = p_X(α,β)·α' + p_Y(α,β)·β'`. -/
theorem deriv_evC (p : F Fq) (α β : Polynomial (K Fq)) :
    Polynomial.derivative (evC Fq α β p)
      = evC Fq α β (pderiv 0 p) * Polynomial.derivative α
        + evC Fq α β (pderiv 1 p) * Polynomial.derivative β := by
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

/-- char 2: `(a²)' = 0` in `K[t]`. -/
theorem derivative_sq' (a : Polynomial (K Fq)) : Polynomial.derivative (a ^ 2) = 0 := by
  rw [pow_two, Polynomial.derivative_mul, mul_comm (Polynomial.derivative a) a,
    CharTwo.add_self_eq_zero]

/-- A `K[t]`-polynomial with zero derivative is a square (`K` is perfect). -/
theorem exists_sq_of_derivative_eq_zero (p : Polynomial (K Fq))
    (hp : Polynomial.derivative p = 0) : ∃ r : Polynomial (K Fq), p = r ^ 2 := by
  classical
  have hexp : Polynomial.expand (K Fq) 2 (Polynomial.contract 2 p) = p :=
    Polynomial.expand_contract 2 hp two_ne_zero
  refine ⟨(Polynomial.contract 2 p).map ((frobeniusEquiv (K Fq) 2).symm : K Fq →+* K Fq), ?_⟩
  have h1 : ((Polynomial.contract 2 p).map
      ((frobeniusEquiv (K Fq) 2).symm : K Fq →+* K Fq)).map
      (frobenius (K Fq) 2) = Polynomial.contract 2 p := by
    rw [Polynomial.map_map, frobenius_comp_frobeniusEquiv_symm, Polynomial.map_id]
  have h2 := Polynomial.map_frobenius_expand (p := 2)
    ((Polynomial.contract 2 p).map ((frobeniusEquiv (K Fq) 2).symm : K Fq →+* K Fq))
  rw [Polynomial.map_expand, h1, hexp] at h2
  exact h2

set_option linter.unusedVariables false in
/-- Two nonzero polynomials over an algebraically closed field are coprime or
    share a root.
    (`hA`, `hB` are unused: `IsAlgClosed.exists_root` covers the degenerate
    cases; they are kept for the interface the descent compiles against.) -/
theorem isCoprime_or_common_root (A B : Polynomial (K Fq)) (hA : A ≠ 0) (hB : B ≠ 0) :
    IsCoprime A B ∨ ∃ θ : K Fq, A.eval θ = 0 ∧ B.eval θ = 0 := by
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
private lemma sq_of_associated_sq {A d : Polynomial (K Fq)} (h : Associated (d ^ 2) A) :
    ∃ a : Polynomial (K Fq), A = a ^ 2 := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨k, hk, hCk⟩ := Polynomial.isUnit_iff.mp u.isUnit
  obtain ⟨v, hv⟩ := exists_sqrt k
  refine ⟨Polynomial.C v * d, ?_⟩
  rw [← hu, ← hCk, ← hv, mul_pow, ← Polynomial.C_pow, mul_comm]

/-- Coprime factors of a square are squares (in `K[t]`, where every unit is a
    square because `K` is algebraically closed). -/
theorem sq_of_coprime_of_mul_sq (A B e : Polynomial (K Fq)) (hAB : IsCoprime A B)
    (he : A * B = e ^ 2) :
    (∃ a : Polynomial (K Fq), A = a ^ 2) ∧ (∃ b : Polynomial (K Fq), B = b ^ 2) := by
  obtain ⟨d, hd⟩ := exists_associated_pow_of_mul_eq_pow' hAB he
  obtain ⟨d', hd'⟩ := exists_associated_pow_of_mul_eq_pow' hAB.symm
    (by rw [mul_comm]; exact he)
  exact ⟨sq_of_associated_sq hd, sq_of_associated_sq hd'⟩

/-- Squaring is injective on `K[t]` (char 2, domain):
    `(a+b)² = a² + b² = 0 ⟹ a + b = 0 ⟹ a = b`. -/
theorem sq_inj {a b : Polynomial (K Fq)} (h : a ^ 2 = b ^ 2) : a = b :=
  CharTwo.sq_injective h

end PolyClone.Perfect
