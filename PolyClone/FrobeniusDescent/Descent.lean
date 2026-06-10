/-
  FrobeniusDescent/Descent.lean
  =============================

  **The Frobenius-depth descent**: if `∂_X∂_Y q ≠ 0` then no polynomial curve
  `(α, β) ∈ K[t]²`, not both constant, lies on a transcendental level set
  `q(α,β) = c`.

  Proof shape (strong induction on `deg α + deg β`, the SAME `q` throughout):

  * decompose `q = A₀² + w²·h` (full-gcd peel, `ParityDecomp`), with
    `h = X·B₁² + Y·B₂² + X·Y·B₃²`, the `Bᵢ` coprime, `B₃ ≠ 0`;
  * **kills**: if any of `w, h_X, h_Y, B₃` vanishes along the curve, the
    witness sits inside a fixed `F₂`-curve ∩ level set — `KillLemma` makes
    `c` algebraic, contradiction;
  * **peel**: otherwise `S := C(√c) + A₀(α,β)` satisfies `S² = W²·H`
    (char 2), hence `H' = 0` even though the level `H = (S/W)²` MOVES —
    this is what lets the engine run below the top level;
  * **engine**: `A := h_X(α,β), B := h_Y(α,β)` satisfy `Ȧ = Δβ̇`, `Ḃ = Δα̇`,
    `(AB)˙ = 0` with `Δ = B₃(α,β)² ≠ 0`, so `AB` is a square;
  * **common root** `θ` of `A, B`: the point `(α(θ), β(θ))` is a common zero
    of the relatively prime `h_X, h_Y` (`Perfectness`), hence algebraic
    (`AlgebraicPoint`); evaluating `S² = W²·H` and `S = C(√c) + A₀(α,β)`
    at `θ` makes `√c` algebraic — contradiction;
  * **coprime**: `A, B` are squares, so `Ȧ = Ḃ = 0`, so `α̇ = β̇ = 0`
    (`Δ ≠ 0`), so `α = α₁², β = β₁²` and `q(α₁,β₁) = C(√c)` — a witness for
    the SAME `q` at HALF the degree.  Induct.
-/
import PolyClone.FrobeniusDescent.Defs
import PolyClone.FrobeniusDescent.ParityDecomp
import PolyClone.FrobeniusDescent.CurveEngine
import PolyClone.FrobeniusDescent.KillLemma
import PolyClone.FrobeniusDescent.AlgebraicPoint
import PolyClone.FrobeniusDescent.Perfectness
import PolyClone.DXDYCocycle

namespace PolyClone.FrobeniusDescent

open MvPolynomial

/-- **The Frobenius-depth descent.**  `∂_X∂_Y q ≠ 0` ⟹ every polynomial curve
    on a transcendental level set of `q` is constant. -/
theorem no_nonconstant_witness (q : F) (hD : DXDYCocycle.D q ≠ 0)
    (c : K) (hc : ¬ AlgebraicF2 c) (α β : Polynomial K)
    (hq : evC α β q = Polynomial.C c) :
    α.natDegree = 0 ∧ β.natDegree = 0 := by
  classical
  -- Decompose q once and for all (the data is fixed through the induction).
  obtain ⟨A₀, A₁, A₂, A₃, hdec⟩ := parity_decomp q
  have hA3 : A₃ ≠ 0 := by
    intro h
    apply hD
    rw [hdec, D_decomp, h]
    simp
  obtain ⟨w, B₁, B₂, B₃, e1, e2, e3, hcop⟩ := extract_gcd A₁ A₂ A₃ hA3
  have hB3 : B₃ ≠ 0 := by rintro rfl; exact hA3 (by rw [e3, mul_zero])
  have hw0 : w ≠ 0 := by
    intro h
    exact hA3 (by rw [e3, h, zero_mul])
  have hqid : q = A₀ ^ 2
      + w ^ 2 * (X 0 * B₁ ^ 2 + X 1 * B₂ ^ 2 + X 0 * X 1 * B₃ ^ 2) := by
    rw [hdec, e1, e2, e3]; ring
  have hgXne : B₁ ^ 2 + X 1 * B₃ ^ 2 ≠ 0 := hX_ne_zero B₁ B₃ hB3
  have hgYne : B₂ ^ 2 + X 0 * B₃ ^ 2 ≠ 0 := hY_ne_zero B₂ B₃ hB3
  have hrelp : ∀ d : F, d ∣ (B₁ ^ 2 + X 1 * B₃ ^ 2) → d ∣ (B₂ ^ 2 + X 0 * B₃ ^ 2) → IsUnit d :=
    hX_hY_relPrime B₁ B₂ B₃ hB3 hcop
  -- Strong induction on the total witness degree.
  suffices H : ∀ n : ℕ, ∀ (α β : Polynomial K) (c : K), ¬ AlgebraicF2 c →
      evC α β q = Polynomial.C c → α.natDegree + β.natDegree = n →
      α.natDegree = 0 ∧ β.natDegree = 0 from H _ α β c hc hq rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro α β c hc hq hn
  by_cases hconst : α.natDegree = 0 ∧ β.natDegree = 0
  · exact hconst
  -- Kill helper: an F₂-curve constraint along the witness contradicts
  -- the transcendence of the level.
  have kill : ∀ f : F, f ≠ 0 → evC α β f = 0 → False := fun f hf h0 =>
    hc (c_algebraic_of_curve_constraint f q hf α β hconst c hq h0)
  -- Nonvanishing of the peel data along the witness (else: kill).
  by_cases hWz : evC α β w = 0
  · exact (kill w hw0 hWz).elim
  by_cases hAz : evC α β (B₁ ^ 2 + X 1 * B₃ ^ 2) = 0
  · exact (kill _ hgXne hAz).elim
  by_cases hBz : evC α β (B₂ ^ 2 + X 0 * B₃ ^ 2) = 0
  · exact (kill _ hgYne hBz).elim
  by_cases hB3z : evC α β B₃ = 0
  · exact (kill B₃ hB3 hB3z).elim
  -- Peel: with r = √c and S = C r + A₀(α,β):  S² = W²·H.
  obtain ⟨r, hr⟩ := exists_sqrt c
  have hrtrans : ¬ AlgebraicF2 r := fun halg => hc (hr ▸ halg.sq)
  have hCc : Polynomial.C c
      = evC α β A₀ ^ 2
        + evC α β w ^ 2 * evC α β (X 0 * B₁ ^ 2 + X 1 * B₂ ^ 2 + X 0 * X 1 * B₃ ^ 2) := by
    rw [← hq]
    conv_lhs => rw [hqid]
    rw [map_add, map_mul, map_pow, map_pow]
  have hpeel : (Polynomial.C r + evC α β A₀) ^ 2
      = evC α β w ^ 2 * evC α β (X 0 * B₁ ^ 2 + X 1 * B₂ ^ 2 + X 0 * X 1 * B₃ ^ 2) := by
    rw [CharTwo.add_sq, ← Polynomial.C_pow, hr, hCc, add_right_comm,
      CharTwo.add_self_eq_zero, zero_add]
  -- The moving level is still Frobenius-flat: H' = 0.
  have hH' : Polynomial.derivative
      (evC α β (X 0 * B₁ ^ 2 + X 1 * B₂ ^ 2 + X 0 * X 1 * B₃ ^ 2)) = 0 := by
    have h1 : Polynomial.derivative
        (evC α β w ^ 2
          * evC α β (X 0 * B₁ ^ 2 + X 1 * B₂ ^ 2 + X 0 * X 1 * B₃ ^ 2)) = 0 := by
      rw [← hpeel]; exact derivative_sq' _
    rw [Polynomial.derivative_mul, derivative_sq', zero_mul, zero_add] at h1
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd ((pow_eq_zero_iff two_ne_zero).mp h) hWz
    · exact h
  -- Chain rule on h:  A·α' + B·β' = 0.
  have hchain : evC α β (B₁ ^ 2 + X 1 * B₃ ^ 2) * Polynomial.derivative α
      + evC α β (B₂ ^ 2 + X 0 * B₃ ^ 2) * Polynomial.derivative β = 0 := by
    have h := deriv_evC (X 0 * B₁ ^ 2 + X 1 * B₂ ^ 2 + X 0 * X 1 * B₃ ^ 2) α β
    rw [pderiv0_h B₁ B₂ B₃, pderiv1_h B₁ B₂ B₃] at h
    rw [← h]
    exact hH'
  -- Engine:  Ȧ = Δ·β',  Ḃ = Δ·α'.
  have hA' : Polynomial.derivative (evC α β (B₁ ^ 2 + X 1 * B₃ ^ 2))
      = evC α β (B₃ ^ 2) * Polynomial.derivative β := by
    have h := deriv_evC (B₁ ^ 2 + X 1 * B₃ ^ 2) α β
    rw [pderiv0_hX B₁ B₃, pderiv1_hX B₁ B₃, map_zero, zero_mul, zero_add] at h
    exact h
  have hB' : Polynomial.derivative (evC α β (B₂ ^ 2 + X 0 * B₃ ^ 2))
      = evC α β (B₃ ^ 2) * Polynomial.derivative α := by
    have h := deriv_evC (B₂ ^ 2 + X 0 * B₃ ^ 2) α β
    rw [pderiv0_hY B₂ B₃, pderiv1_hY B₂ B₃, map_zero, zero_mul, add_zero] at h
    exact h
  -- (A·B)' = Δ·(A·α' + B·β') = 0, so A·B is a square.
  have hAB' : Polynomial.derivative
      (evC α β (B₁ ^ 2 + X 1 * B₃ ^ 2) * evC α β (B₂ ^ 2 + X 0 * B₃ ^ 2)) = 0 := by
    rw [Polynomial.derivative_mul, hA', hB']
    calc evC α β (B₃ ^ 2) * Polynomial.derivative β * evC α β (B₂ ^ 2 + X 0 * B₃ ^ 2)
          + evC α β (B₁ ^ 2 + X 1 * B₃ ^ 2) * (evC α β (B₃ ^ 2) * Polynomial.derivative α)
        = evC α β (B₃ ^ 2)
            * (evC α β (B₁ ^ 2 + X 1 * B₃ ^ 2) * Polynomial.derivative α
              + evC α β (B₂ ^ 2 + X 0 * B₃ ^ 2) * Polynomial.derivative β) := by ring
      _ = 0 := by rw [hchain, mul_zero]
  obtain ⟨e, hABsq⟩ := exists_sq_of_derivative_eq_zero _ hAB'
  rcases isCoprime_or_common_root _ _ hAz hBz with hcp | ⟨θ, hθA, hθB⟩
  · -- Coprime branch: A, B squares ⟹ α' = β' = 0 ⟹ Frobenius-halve, induct.
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := sq_of_coprime_of_mul_sq _ _ e hcp hABsq
    have hΔne : evC α β (B₃ ^ 2) ≠ 0 := by
      rw [map_pow]; exact pow_ne_zero _ hB3z
    have hβ' : Polynomial.derivative β = 0 := by
      have h0 : evC α β (B₃ ^ 2) * Polynomial.derivative β = 0 := by
        rw [← hA', ha]; exact derivative_sq' a
      exact (mul_eq_zero.mp h0).resolve_left hΔne
    have hα' : Polynomial.derivative α = 0 := by
      have h0 : evC α β (B₃ ^ 2) * Polynomial.derivative α = 0 := by
        rw [← hB', hb]; exact derivative_sq' b
      exact (mul_eq_zero.mp h0).resolve_left hΔne
    obtain ⟨α₁, hα₁⟩ := exists_sq_of_derivative_eq_zero α hα'
    obtain ⟨β₁, hβ₁⟩ := exists_sq_of_derivative_eq_zero β hβ'
    have hq1 : evC α₁ β₁ q = Polynomial.C r := by
      apply sq_inj
      rw [← evC_frobenius, ← hα₁, ← hβ₁, hq, ← Polynomial.C_pow, hr]
    have hdα : α.natDegree = 2 * α₁.natDegree := by
      rw [hα₁, Polynomial.natDegree_pow]
    have hdβ : β.natDegree = 2 * β₁.natDegree := by
      rw [hβ₁, Polynomial.natDegree_pow]
    have hnpos : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h0 | h
      · exfalso; apply hconst; constructor <;> omega
      · exact h
    have hlt : α₁.natDegree + β₁.natDegree < n := by omega
    obtain ⟨h1, h2⟩ := IH _ hlt α₁ β₁ r hrtrans hq1 rfl
    constructor <;> omega
  · -- Common-root branch: an algebraic critical point on the moving level.
    have hux : evP (Polynomial.eval θ α) (Polynomial.eval θ β) (B₁ ^ 2 + X 1 * B₃ ^ 2) = 0 := by
      rw [← eval_evC]; exact hθA
    have hvy : evP (Polynomial.eval θ α) (Polynomial.eval θ β) (B₂ ^ 2 + X 0 * B₃ ^ 2) = 0 := by
      rw [← eval_evC]; exact hθB
    obtain ⟨hxalg, hyalg⟩ := algebraic_point _ _ hgXne hgYne hrelp _ _ hux hvy
    -- Evaluate the peel identity at θ:  S(θ)² is algebraic, hence so is S(θ).
    have hpeelθ : (Polynomial.eval θ (Polynomial.C r + evC α β A₀)) ^ 2
        = (evP (Polynomial.eval θ α) (Polynomial.eval θ β) w) ^ 2
          * evP (Polynomial.eval θ α) (Polynomial.eval θ β)
              (X 0 * B₁ ^ 2 + X 1 * B₂ ^ 2 + X 0 * X 1 * B₃ ^ 2) := by
      have h := congrArg (Polynomial.eval θ) hpeel
      simpa using h
    have hSθ : AlgebraicF2 (Polynomial.eval θ (Polynomial.C r + evC α β A₀)) := by
      apply AlgebraicF2.of_sq
      rw [hpeelθ]
      exact ((algebraicF2_evP w _ _ hxalg hyalg).sq).mul
        (algebraicF2_evP _ _ _ hxalg hyalg)
    -- Unfold S(θ) and cancel (char 2):  r is algebraic — contradiction.
    have hSeval : Polynomial.eval θ (Polynomial.C r + evC α β A₀)
        = r + evP (Polynomial.eval θ α) (Polynomial.eval θ β) A₀ := by
      simp
    have hrAlg : AlgebraicF2 r := by
      have hr' : r = Polynomial.eval θ (Polynomial.C r + evC α β A₀)
          + evP (Polynomial.eval θ α) (Polynomial.eval θ β) A₀ := by
        rw [hSeval, add_assoc, CharTwo.add_self_eq_zero, add_zero]
      rw [hr']
      exact hSθ.add (algebraicF2_evP A₀ _ _ hxalg hyalg)
    exact (hrtrans hrAlg).elim

end PolyClone.FrobeniusDescent
