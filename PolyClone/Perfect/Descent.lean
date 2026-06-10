/-
  FrobeniusDescentP/Descent.lean
  ==============================

  The Frobenius-depth descent over an arbitrary perfect field `Fq` of
  characteristic 2.  Structurally identical to `FrobeniusDescent/Descent.lean`
  with TWO changes:

  * the induction statement quantifies over `q` INSIDE the degree induction
    (so the per-`q` peel data is derived inside each step), and
  * the Frobenius-halving branch hands the inductive hypothesis the
    coefficient-twisted polynomial `half2 q = q^{(1/2)}` (whose `D` is
    nonzero whenever `D q` is), at level `√c`, at half the degree.

  Over `ZMod 2` the twist is the identity and this specializes to the old
  proof.  No orbit/periodicity bookkeeping is needed: the decreasing
  quantity is the witness degree alone.
-/
import PolyClone.Perfect.Defs
import PolyClone.Perfect.ParityDecomp
import PolyClone.Perfect.CurveEngine
import PolyClone.Perfect.KillLemma
import PolyClone.Perfect.AlgebraicPoint
import PolyClone.Perfect.Perfectness
import PolyClone.DXDYCocycle

set_option linter.unusedSectionVars false

namespace PolyClone.Perfect

open MvPolynomial

variable {Fq : Type} [Field Fq] [CharP Fq 2] [PerfectRing Fq 2]

/-- **The Frobenius-depth descent** (perfect char-2 coefficients).
    `∂_X∂_Y q ≠ 0` ⟹ every polynomial curve on a level set transcendental
    over `Fq` is constant. -/
theorem no_nonconstant_witness (q : F Fq) (hD : DXDYCocycle.D q ≠ 0)
    (c : K Fq) (hc : ¬ IsAlgebraic Fq c) (α β : Polynomial (K Fq))
    (hq : evC Fq α β q = Polynomial.C c) :
    α.natDegree = 0 ∧ β.natDegree = 0 := by
  classical
  -- Strong induction on the total witness degree, with `q` quantified
  -- inside (the halving branch changes `q` to its Frobenius twist).
  suffices H : ∀ n : ℕ, ∀ q : F Fq, DXDYCocycle.D q ≠ 0 →
      ∀ (α β : Polynomial (K Fq)) (c : K Fq), ¬ IsAlgebraic Fq c →
      evC Fq α β q = Polynomial.C c → α.natDegree + β.natDegree = n →
      α.natDegree = 0 ∧ β.natDegree = 0 from H _ q hD α β c hc hq rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro q hD α β c hc hq hn
  by_cases hconst : α.natDegree = 0 ∧ β.natDegree = 0
  · exact hconst
  -- Decompose THIS q (full-gcd peel).
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
  have hrelp : ∀ d : F Fq,
      d ∣ (B₁ ^ 2 + X 1 * B₃ ^ 2) → d ∣ (B₂ ^ 2 + X 0 * B₃ ^ 2) → IsUnit d :=
    hX_hY_relPrime B₁ B₂ B₃ hB3 hcop
  -- Kill helper: an Fq-curve constraint along the witness contradicts
  -- the transcendence of the level.
  have kill : ∀ f : F Fq, f ≠ 0 → evC Fq α β f = 0 → False := fun f hf h0 =>
    hc (c_algebraic_of_curve_constraint f q hf α β hconst c hq h0)
  by_cases hWz : evC Fq α β w = 0
  · exact (kill w hw0 hWz).elim
  by_cases hAz : evC Fq α β (B₁ ^ 2 + X 1 * B₃ ^ 2) = 0
  · exact (kill _ hgXne hAz).elim
  by_cases hBz : evC Fq α β (B₂ ^ 2 + X 0 * B₃ ^ 2) = 0
  · exact (kill _ hgYne hBz).elim
  by_cases hB3z : evC Fq α β B₃ = 0
  · exact (kill B₃ hB3 hB3z).elim
  -- Peel: with r = √c and S = C r + A₀(α,β):  S² = W²·H.
  obtain ⟨r, hr⟩ := exists_sqrt c
  have hrtrans : ¬ IsAlgebraic Fq r := fun halg =>
    hc (hr ▸ IsAlgebraic.sq' halg)
  have hCc : Polynomial.C c
      = evC Fq α β A₀ ^ 2
        + evC Fq α β w ^ 2
          * evC Fq α β (X 0 * B₁ ^ 2 + X 1 * B₂ ^ 2 + X 0 * X 1 * B₃ ^ 2) := by
    rw [← hq]
    conv_lhs => rw [hqid]
    rw [map_add, map_mul, map_pow, map_pow]
  have hpeel : (Polynomial.C r + evC Fq α β A₀) ^ 2
      = evC Fq α β w ^ 2
        * evC Fq α β (X 0 * B₁ ^ 2 + X 1 * B₂ ^ 2 + X 0 * X 1 * B₃ ^ 2) := by
    rw [CharTwo.add_sq, ← Polynomial.C_pow, hr, hCc, add_right_comm,
      CharTwo.add_self_eq_zero, zero_add]
  -- The moving level is still Frobenius-flat: H' = 0.
  have hH' : Polynomial.derivative
      (evC Fq α β (X 0 * B₁ ^ 2 + X 1 * B₂ ^ 2 + X 0 * X 1 * B₃ ^ 2)) = 0 := by
    have h1 : Polynomial.derivative
        (evC Fq α β w ^ 2
          * evC Fq α β (X 0 * B₁ ^ 2 + X 1 * B₂ ^ 2 + X 0 * X 1 * B₃ ^ 2)) = 0 := by
      rw [← hpeel]; exact derivative_sq' _
    rw [Polynomial.derivative_mul, derivative_sq', zero_mul, zero_add] at h1
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd ((pow_eq_zero_iff two_ne_zero).mp h) hWz
    · exact h
  -- Chain rule on h:  A·α' + B·β' = 0.
  have hchain : evC Fq α β (B₁ ^ 2 + X 1 * B₃ ^ 2) * Polynomial.derivative α
      + evC Fq α β (B₂ ^ 2 + X 0 * B₃ ^ 2) * Polynomial.derivative β = 0 := by
    have h := deriv_evC (X 0 * B₁ ^ 2 + X 1 * B₂ ^ 2 + X 0 * X 1 * B₃ ^ 2) α β
    rw [pderiv0_h B₁ B₂ B₃, pderiv1_h B₁ B₂ B₃] at h
    rw [← h]
    exact hH'
  -- Engine:  Ȧ = Δ·β',  Ḃ = Δ·α'.
  have hA' : Polynomial.derivative (evC Fq α β (B₁ ^ 2 + X 1 * B₃ ^ 2))
      = evC Fq α β (B₃ ^ 2) * Polynomial.derivative β := by
    have h := deriv_evC (B₁ ^ 2 + X 1 * B₃ ^ 2) α β
    rw [pderiv0_hX B₁ B₃, pderiv1_hX B₁ B₃, map_zero, zero_mul, zero_add] at h
    exact h
  have hB' : Polynomial.derivative (evC Fq α β (B₂ ^ 2 + X 0 * B₃ ^ 2))
      = evC Fq α β (B₃ ^ 2) * Polynomial.derivative α := by
    have h := deriv_evC (B₂ ^ 2 + X 0 * B₃ ^ 2) α β
    rw [pderiv0_hY B₂ B₃, pderiv1_hY B₂ B₃, map_zero, zero_mul, add_zero] at h
    exact h
  -- (A·B)' = Δ·(A·α' + B·β') = 0, so A·B is a square.
  have hAB' : Polynomial.derivative
      (evC Fq α β (B₁ ^ 2 + X 1 * B₃ ^ 2)
        * evC Fq α β (B₂ ^ 2 + X 0 * B₃ ^ 2)) = 0 := by
    rw [Polynomial.derivative_mul, hA', hB']
    calc evC Fq α β (B₃ ^ 2) * Polynomial.derivative β
            * evC Fq α β (B₂ ^ 2 + X 0 * B₃ ^ 2)
          + evC Fq α β (B₁ ^ 2 + X 1 * B₃ ^ 2)
            * (evC Fq α β (B₃ ^ 2) * Polynomial.derivative α)
        = evC Fq α β (B₃ ^ 2)
            * (evC Fq α β (B₁ ^ 2 + X 1 * B₃ ^ 2) * Polynomial.derivative α
              + evC Fq α β (B₂ ^ 2 + X 0 * B₃ ^ 2) * Polynomial.derivative β) := by
          ring
      _ = 0 := by rw [hchain, mul_zero]
  obtain ⟨e, hABsq⟩ := exists_sq_of_derivative_eq_zero _ hAB'
  rcases isCoprime_or_common_root _ _ hAz hBz with hcp | ⟨θ, hθA, hθB⟩
  · -- Coprime branch: A, B squares ⟹ α' = β' = 0 ⟹ Frobenius-halve, induct
    -- on the TWISTED polynomial.
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := sq_of_coprime_of_mul_sq _ _ e hcp hABsq
    have hΔne : evC Fq α β (B₃ ^ 2) ≠ 0 := by
      rw [map_pow]; exact pow_ne_zero _ hB3z
    have hβ' : Polynomial.derivative β = 0 := by
      have h0 : evC Fq α β (B₃ ^ 2) * Polynomial.derivative β = 0 := by
        rw [← hA', ha]; exact derivative_sq' a
      exact (mul_eq_zero.mp h0).resolve_left hΔne
    have hα' : Polynomial.derivative α = 0 := by
      have h0 : evC Fq α β (B₃ ^ 2) * Polynomial.derivative α = 0 := by
        rw [← hB', hb]; exact derivative_sq' b
      exact (mul_eq_zero.mp h0).resolve_left hΔne
    obtain ⟨α₁, hα₁⟩ := exists_sq_of_derivative_eq_zero α hα'
    obtain ⟨β₁, hβ₁⟩ := exists_sq_of_derivative_eq_zero β hβ'
    have hq1 : evC Fq α₁ β₁ (half2 Fq q) = Polynomial.C r := by
      apply sq_inj
      rw [evC_half2_sq, ← hα₁, ← hβ₁, hq, ← Polynomial.C_pow, hr]
    have hD1 : DXDYCocycle.D (half2 Fq q) ≠ 0 := D_half2_ne_zero hD
    have hdα : α.natDegree = 2 * α₁.natDegree := by
      rw [hα₁, Polynomial.natDegree_pow]
    have hdβ : β.natDegree = 2 * β₁.natDegree := by
      rw [hβ₁, Polynomial.natDegree_pow]
    have hnpos : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h0 | h
      · exfalso; apply hconst; constructor <;> omega
      · exact h
    have hlt : α₁.natDegree + β₁.natDegree < n := by omega
    obtain ⟨h1, h2⟩ := IH _ hlt (half2 Fq q) hD1 α₁ β₁ r hrtrans hq1 rfl
    constructor <;> omega
  · -- Common-root branch: an algebraic critical point on the moving level.
    have hux : evP Fq (Polynomial.eval θ α) (Polynomial.eval θ β)
        (B₁ ^ 2 + X 1 * B₃ ^ 2) = 0 := by
      rw [← eval_evC]; exact hθA
    have hvy : evP Fq (Polynomial.eval θ α) (Polynomial.eval θ β)
        (B₂ ^ 2 + X 0 * B₃ ^ 2) = 0 := by
      rw [← eval_evC]; exact hθB
    obtain ⟨hxalg, hyalg⟩ := algebraic_point _ _ hgXne hgYne hrelp _ _ hux hvy
    have hpeelθ : (Polynomial.eval θ (Polynomial.C r + evC Fq α β A₀)) ^ 2
        = (evP Fq (Polynomial.eval θ α) (Polynomial.eval θ β) w) ^ 2
          * evP Fq (Polynomial.eval θ α) (Polynomial.eval θ β)
              (X 0 * B₁ ^ 2 + X 1 * B₂ ^ 2 + X 0 * X 1 * B₃ ^ 2) := by
      have h := congrArg (Polynomial.eval θ) hpeel
      simpa using h
    have hSθ : IsAlgebraic Fq
        (Polynomial.eval θ (Polynomial.C r + evC Fq α β A₀)) := by
      apply isAlgebraic_of_sq
      rw [hpeelθ]
      exact (IsAlgebraic.sq' (isAlgebraic_evP w _ _ hxalg hyalg)).mul
        (isAlgebraic_evP _ _ _ hxalg hyalg)
    have hSeval : Polynomial.eval θ (Polynomial.C r + evC Fq α β A₀)
        = r + evP Fq (Polynomial.eval θ α) (Polynomial.eval θ β) A₀ := by
      simp
    have hrAlg : IsAlgebraic Fq r := by
      have hr' : r = Polynomial.eval θ (Polynomial.C r + evC Fq α β A₀)
          + evP Fq (Polynomial.eval θ α) (Polynomial.eval θ β) A₀ := by
        rw [hSeval, add_assoc, CharTwo.add_self_eq_zero, add_zero]
      rw [hr']
      exact hSθ.add (isAlgebraic_evP A₀ _ _ hxalg hyalg)
    exact (hrtrans hrAlg).elim

end PolyClone.Perfect
