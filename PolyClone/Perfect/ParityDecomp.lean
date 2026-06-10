/-
  FrobeniusDescentP/ParityDecomp.lean
  ===================================

  The char-2 **parity decomposition** of `Fq[X,Y]` and the **full-gcd peel**,
  parametrized over a perfect field `Fq` of characteristic 2.

  Every `q ∈ Fq[X,Y]` decomposes as

      q = A₀² + X·A₁² + Y·A₂² + X·Y·A₃²

  by sorting monomials `X^i Y^j` into the four parity classes of `(i, j)` and
  halving exponents (Frobenius — perfectness supplies the coefficient square
  roots).  Then

      ∂_X q = A₁² + Y·A₃²,   ∂_Y q = A₂² + X·A₃²,   ∂_X∂_Y q = A₃².

  The **full-gcd peel** extracts `w` with `Aᵢ = w·Bᵢ` and the `Bᵢ` sharing no
  prime factor, so that

      q = A₀² + w²·h,   h = X·B₁² + Y·B₂² + X·Y·B₃²,   ∂_X∂_Y h = B₃².
-/
import PolyClone.Perfect.Defs
import PolyClone.DXDYCocycle
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.MvPolynomial.Basic

set_option linter.unusedSectionVars false

namespace PolyClone.Perfect

open MvPolynomial

variable {Fq : Type} [Field Fq] [CharP Fq 2] [PerfectRing Fq 2]

private lemma ne10 : (1 : Fin 2) ≠ 0 := by decide
private lemma ne01 : (0 : Fin 2) ≠ 1 := by decide

/-- char 2: the partial derivative of a square vanishes. -/
lemma pderiv_sq (i : Fin 2) (g : F Fq) : pderiv i (g ^ 2) = 0 := by
  rw [sq, pderiv_mul, mul_comm (pderiv i g) g]
  exact CharTwo.add_self_eq_zero _

/-- **Parity decomposition** of an arbitrary `q ∈ Fq[X,Y]`. -/
theorem parity_decomp (q : F Fq) :
    ∃ A₀ A₁ A₂ A₃ : F Fq,
      q = A₀ ^ 2 + X 0 * A₁ ^ 2 + X 1 * A₂ ^ 2 + X 0 * X 1 * A₃ ^ 2 := by
  induction q using MvPolynomial.induction_on with
  | C a =>
      refine ⟨C ((frobeniusEquiv Fq 2).symm a), 0, 0, 0, ?_⟩
      have h : ((frobeniusEquiv Fq 2).symm a) ^ 2 = a := by
        rw [← frobenius_def, frobenius_apply_frobeniusEquiv_symm]
      rw [← map_pow, h]
      ring
  | add p₁ p₂ h₁ h₂ =>
      obtain ⟨A₀, A₁, A₂, A₃, rfl⟩ := h₁
      obtain ⟨B₀, B₁, B₂, B₃, rfl⟩ := h₂
      refine ⟨A₀ + B₀, A₁ + B₁, A₂ + B₂, A₃ + B₃, ?_⟩
      simp only [CharTwo.add_sq]
      ring
  | mul_X p i hp =>
      obtain ⟨A₀, A₁, A₂, A₃, rfl⟩ := hp
      rcases eq_or_ne i 0 with rfl | hi
      · exact ⟨X 0 * A₁, A₀, X 0 * A₃, A₂, by ring⟩
      · obtain rfl : i = 1 := Fin.eq_one_of_ne_zero i hi
        exact ⟨X 1 * A₂, X 1 * A₃, A₀, A₁, by ring⟩

/-- `∂_X` of a decomposed polynomial. -/
theorem pderiv0_decomp (A₀ A₁ A₂ A₃ : F Fq) :
    pderiv 0 (A₀ ^ 2 + X 0 * A₁ ^ 2 + X 1 * A₂ ^ 2 + X 0 * X 1 * A₃ ^ 2)
      = A₁ ^ 2 + X 1 * A₃ ^ 2 := by
  simp only [map_add, pderiv_mul, pderiv_sq, pderiv_X_self, pderiv_X_of_ne ne10,
    mul_zero, zero_mul, add_zero, zero_add, one_mul]

/-- `∂_Y` of a decomposed polynomial. -/
theorem pderiv1_decomp (A₀ A₁ A₂ A₃ : F Fq) :
    pderiv 1 (A₀ ^ 2 + X 0 * A₁ ^ 2 + X 1 * A₂ ^ 2 + X 0 * X 1 * A₃ ^ 2)
      = A₂ ^ 2 + X 0 * A₃ ^ 2 := by
  simp only [map_add, pderiv_mul, pderiv_sq, pderiv_X_self, pderiv_X_of_ne ne01,
    mul_zero, zero_mul, add_zero, zero_add, one_mul, mul_one]

/-- `∂_X∂_Y` of a decomposed polynomial is the square of its odd–odd part. -/
theorem D_decomp (A₀ A₁ A₂ A₃ : F Fq) :
    DXDYCocycle.D (A₀ ^ 2 + X 0 * A₁ ^ 2 + X 1 * A₂ ^ 2 + X 0 * X 1 * A₃ ^ 2)
      = A₃ ^ 2 := by
  rw [DXDYCocycle.D_def, pderiv1_decomp]
  simp only [map_add, pderiv_mul, pderiv_sq, pderiv_X_self,
    mul_zero, add_zero, zero_add, one_mul]

/-- **Full-gcd extraction** with coprime cofactors. -/
theorem extract_gcd (A₁ A₂ A₃ : F Fq) (h3 : A₃ ≠ 0) :
    ∃ w B₁ B₂ B₃ : F Fq, A₁ = w * B₁ ∧ A₂ = w * B₂ ∧ A₃ = w * B₃ ∧
      (∀ d : F Fq, d ∣ B₁ → d ∣ B₂ → d ∣ B₃ → IsUnit d) := by
  classical
  letI : NormalizationMonoid (F Fq) := UniqueFactorizationMonoid.normalizationMonoid
  letI : GCDMonoid (F Fq) := UniqueFactorizationMonoid.toGCDMonoid (F Fq)
  have hw1 : gcd (gcd A₁ A₂) A₃ ∣ A₁ := (gcd_dvd_left _ _).trans (gcd_dvd_left _ _)
  have hw2 : gcd (gcd A₁ A₂) A₃ ∣ A₂ := (gcd_dvd_left _ _).trans (gcd_dvd_right _ _)
  have hw3 : gcd (gcd A₁ A₂) A₃ ∣ A₃ := gcd_dvd_right _ _
  have hw0 : gcd (gcd A₁ A₂) A₃ ≠ 0 := fun h => h3 ((gcd_eq_zero_iff _ _).mp h).2
  obtain ⟨B₁, hB₁⟩ := hw1
  obtain ⟨B₂, hB₂⟩ := hw2
  obtain ⟨B₃, hB₃⟩ := hw3
  refine ⟨gcd (gcd A₁ A₂) A₃, B₁, B₂, B₃, hB₁, hB₂, hB₃, ?_⟩
  intro d hd1 hd2 hd3
  have h1 : gcd (gcd A₁ A₂) A₃ * d ∣ A₁ :=
    (mul_dvd_mul_left _ hd1).trans (dvd_of_eq hB₁.symm)
  have h2 : gcd (gcd A₁ A₂) A₃ * d ∣ A₂ :=
    (mul_dvd_mul_left _ hd2).trans (dvd_of_eq hB₂.symm)
  have h3' : gcd (gcd A₁ A₂) A₃ * d ∣ A₃ :=
    (mul_dvd_mul_left _ hd3).trans (dvd_of_eq hB₃.symm)
  have hgcd : gcd (gcd A₁ A₂) A₃ * d ∣ gcd (gcd A₁ A₂) A₃ * 1 := by
    rw [mul_one]
    exact dvd_gcd (dvd_gcd h1 h2) h3'
  exact isUnit_of_dvd_one ((mul_dvd_mul_iff_left hw0).mp hgcd)

/-- `h_X ≠ 0` when `B₃ ≠ 0`: applying `∂_Y` to `B₁² + Y·B₃² = 0` would give
    `B₃² = 0`. -/
theorem hX_ne_zero (B₁ B₃ : F Fq) (h3 : B₃ ≠ 0) : B₁ ^ 2 + X 1 * B₃ ^ 2 ≠ 0 := by
  intro h
  have hd := congrArg (pderiv (1 : Fin 2)) h
  simp only [map_add, map_zero, pderiv_sq, pderiv_mul, pderiv_X_self,
    mul_zero, add_zero, zero_add, one_mul] at hd
  exact h3 ((pow_eq_zero_iff (two_ne_zero)).mp hd)

/-- `h_Y ≠ 0` when `B₃ ≠ 0` (symmetric to `hX_ne_zero`). -/
theorem hY_ne_zero (B₂ B₃ : F Fq) (h3 : B₃ ≠ 0) : B₂ ^ 2 + X 0 * B₃ ^ 2 ≠ 0 := by
  intro h
  have hd := congrArg (pderiv (0 : Fin 2)) h
  simp only [map_add, map_zero, pderiv_sq, pderiv_mul, pderiv_X_self,
    mul_zero, add_zero, zero_add, one_mul] at hd
  exact h3 ((pow_eq_zero_iff (two_ne_zero)).mp hd)

/-! ### Derivatives of the peeled polynomial `h = X·B₁² + Y·B₂² + X·Y·B₃²`
and of its partials (the curve engine needs exactly these shapes). -/

theorem pderiv0_h (B₁ B₂ B₃ : F Fq) :
    pderiv 0 (X 0 * B₁ ^ 2 + X 1 * B₂ ^ 2 + X 0 * X 1 * B₃ ^ 2)
      = B₁ ^ 2 + X 1 * B₃ ^ 2 := by
  simp only [map_add, pderiv_mul, pderiv_sq, pderiv_X_self, pderiv_X_of_ne ne10,
    mul_zero, zero_mul, add_zero, one_mul]

theorem pderiv1_h (B₁ B₂ B₃ : F Fq) :
    pderiv 1 (X 0 * B₁ ^ 2 + X 1 * B₂ ^ 2 + X 0 * X 1 * B₃ ^ 2)
      = B₂ ^ 2 + X 0 * B₃ ^ 2 := by
  simp only [map_add, pderiv_mul, pderiv_sq, pderiv_X_self, pderiv_X_of_ne ne01,
    mul_zero, zero_mul, add_zero, zero_add, one_mul, mul_one]

theorem pderiv0_hX (B₁ B₃ : F Fq) : pderiv 0 (B₁ ^ 2 + X 1 * B₃ ^ 2) = 0 := by
  simp only [map_add, pderiv_mul, pderiv_sq, pderiv_X_of_ne ne10,
    mul_zero, zero_mul, add_zero]

theorem pderiv1_hX (B₁ B₃ : F Fq) : pderiv 1 (B₁ ^ 2 + X 1 * B₃ ^ 2) = B₃ ^ 2 := by
  simp only [map_add, pderiv_mul, pderiv_sq, pderiv_X_self,
    mul_zero, add_zero, zero_add, one_mul]

theorem pderiv0_hY (B₂ B₃ : F Fq) : pderiv 0 (B₂ ^ 2 + X 0 * B₃ ^ 2) = B₃ ^ 2 := by
  simp only [map_add, pderiv_mul, pderiv_sq, pderiv_X_self,
    mul_zero, add_zero, zero_add, one_mul]

theorem pderiv1_hY (B₂ B₃ : F Fq) : pderiv 1 (B₂ ^ 2 + X 0 * B₃ ^ 2) = 0 := by
  simp only [map_add, pderiv_mul, pderiv_sq, pderiv_X_of_ne ne01,
    mul_zero, zero_mul, add_zero]

end PolyClone.Perfect
