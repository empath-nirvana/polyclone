/-
  FrobeniusDescent/Perfectness.lean
  =================================

  **The perfectness keystone**: if the peel cofactors `B₁, B₂, B₃` share no
  prime factor and `B₃ ≠ 0`, then

      h_X = B₁² + Y·B₃²   and   h_Y = B₂² + X·B₃²

  are relatively prime in `F₂[X,Y]` — i.e. the critical locus of the peeled
  polynomial `h` contains no curve.  (This is what the full-gcd peel buys:
  `Crit(q) ⊇ V(w)` is a curve, `Crit(h)` is not.)

  PROOF (char-2 derivative argument, replacing the originally spec'd
  perfectness-of-`Frac(F/(p))` route — same conclusion, no fraction fields):

  Both `h_X` and `h_Y` are nonzero (`∂_Y h_X = ∂_X h_Y = B₃² ≠ 0`), so any
  nonunit common divisor `d ≠ 0` has a PRIME factor `p` (`F` is a UFD).
  * If `p ∣ B₃`: then `p ∣ B₁²` and `p ∣ B₂²` (char 2: subtract the
    `B₃²`-terms), so `p ∣ B₁` and `p ∣ B₂` (primality), contradicting `hcop`.
  * If `p ∤ B₃`: write `h_X = p·u`, `h_Y = p·v`.  Squares have vanishing
    partials in char 2, so the product rule gives
      - `∂_X h_X = 0  = ∂_X p·u + p·∂_X u`  ⟹  `p ∣ u·∂_X p`;
      - `∂_Y h_X = B₃² = ∂_Y p·u + p·∂_Y u` ⟹  `p ∣ u` would force
        `p ∣ B₃² ⟹ p ∣ B₃` ✗, so `p ∤ u`;
      - `∂_X h_Y = B₃² = ∂_X p·v + p·∂_X v` ⟹  `p ∣ ∂_X p` would force
        `p ∣ B₃²` ✗, so `p ∤ ∂_X p`.
    Now `p` is prime and divides `u·∂_X p` but neither factor. ∎

  (Morally this is the perfectness argument in infinitesimal form: a common
  prime `p ∤ B₃` would make `x̄, ȳ` squares in `K' = Frac(F/(p))`, hence `K'`
  perfect with every derivation zero; the computation above exhibits the
  nonzero derivation `∂_X` surviving mod `p` — `p ∤ ∂_X p` — directly at the
  polynomial level.)
-/
import PolyClone.FrobeniusDescent.Defs
import Mathlib.RingTheory.Polynomial.UniqueFactorization

namespace PolyClone.FrobeniusDescent

open MvPolynomial

private lemma ne10 : (1 : Fin 2) ≠ 0 := by decide

/-- char 2: the partial derivative of a square vanishes. -/
private lemma pd_sq (i : Fin 2) (g : F) : pderiv i (g ^ 2) = 0 := by
  rw [sq, pderiv_mul, mul_comm (pderiv i g) g]
  exact CharTwo.add_self_eq_zero _

/-- `∂_X h_X = 0` (both summands are `X`-free up to squares). -/
private lemma pd0_hX (B₁ B₃ : F) : pderiv 0 (B₁ ^ 2 + X 1 * B₃ ^ 2) = 0 := by
  simp only [map_add, pderiv_mul, pd_sq, pderiv_X_of_ne ne10,
    mul_zero, zero_mul, add_zero]

/-- `∂_Y h_X = B₃²`. -/
private lemma pd1_hX (B₁ B₃ : F) : pderiv 1 (B₁ ^ 2 + X 1 * B₃ ^ 2) = B₃ ^ 2 := by
  simp only [map_add, pderiv_mul, pd_sq, pderiv_X_self,
    mul_zero, add_zero, zero_add, one_mul]

/-- `∂_X h_Y = B₃²`. -/
private lemma pd0_hY (B₂ B₃ : F) : pderiv 0 (B₂ ^ 2 + X 0 * B₃ ^ 2) = B₃ ^ 2 := by
  simp only [map_add, pderiv_mul, pd_sq, pderiv_X_self,
    mul_zero, add_zero, zero_add, one_mul]

/-- `h_X ≠ 0` when `B₃ ≠ 0`: applying `∂_Y` to `B₁² + Y·B₃² = 0` would give
    `B₃² = 0`. -/
private lemma hX_ne_zero' (B₁ B₃ : F) (h3 : B₃ ≠ 0) : B₁ ^ 2 + X 1 * B₃ ^ 2 ≠ 0 := by
  intro h
  have hd := congrArg (pderiv (1 : Fin 2)) h
  rw [pd1_hX, map_zero] at hd
  exact h3 ((pow_eq_zero_iff two_ne_zero).mp hd)

/-- **Perfectness keystone**: with coprime cofactors and `B₃ ≠ 0`, the two
    partials of the peeled polynomial share no nonunit factor. -/
theorem hX_hY_relPrime (B₁ B₂ B₃ : F) (h3 : B₃ ≠ 0)
    (hcop : ∀ d : F, d ∣ B₁ → d ∣ B₂ → d ∣ B₃ → IsUnit d) :
    ∀ d : F, d ∣ (B₁ ^ 2 + X 1 * B₃ ^ 2) → d ∣ (B₂ ^ 2 + X 0 * B₃ ^ 2) → IsUnit d := by
  intro d hdX hdY
  by_contra hdu
  -- `d ≠ 0` since it divides the nonzero `h_X`; extract a prime factor `p`.
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hX_ne_zero' B₁ B₃ h3 (zero_dvd_iff.mp hdX)
  obtain ⟨p, hpirr, hpd⟩ := WfDvdMonoid.exists_irreducible_factor hdu hd0
  have hp : Prime p := UniqueFactorizationMonoid.irreducible_iff_prime.mp hpirr
  have hpX : p ∣ B₁ ^ 2 + X 1 * B₃ ^ 2 := hpd.trans hdX
  have hpY : p ∣ B₂ ^ 2 + X 0 * B₃ ^ 2 := hpd.trans hdY
  by_cases hpB3 : p ∣ B₃
  · -- Common-factor case: `p` divides `B₁², B₂²` too, contradicting `hcop`.
    have hsq : p ∣ B₃ ^ 2 := dvd_pow hpB3 two_ne_zero
    have h1 : p ∣ B₁ ^ 2 := by
      have h := dvd_add hpX (hsq.mul_left (X 1))
      rwa [add_assoc, CharTwo.add_self_eq_zero, add_zero] at h
    have h2 : p ∣ B₂ ^ 2 := by
      have h := dvd_add hpY (hsq.mul_left (X 0))
      rwa [add_assoc, CharTwo.add_self_eq_zero, add_zero] at h
    exact hp.not_unit (hcop p (hp.dvd_of_dvd_pow h1) (hp.dvd_of_dvd_pow h2) hpB3)
  · -- Core case `p ∤ B₃`: char-2 derivative argument.
    obtain ⟨u, hu⟩ := hpX
    obtain ⟨v, hv⟩ := hpY
    have hpB3sq : ¬ p ∣ B₃ ^ 2 := fun h => hpB3 (hp.dvd_of_dvd_pow h)
    -- `∂_X` of `h_X = p·u`:  `0 = ∂_X p·u + p·∂_X u`, so `p ∣ ∂_X p·u`.
    have e1 : (0 : F) = pderiv 0 p * u + p * pderiv 0 u := by
      have h := congrArg (pderiv (0 : Fin 2)) hu
      rwa [pd0_hX, pderiv_mul] at h
    have hdvd1 : p ∣ pderiv 0 p * u := by
      have heq : pderiv 0 p * u = p * pderiv 0 u :=
        (eq_neg_of_add_eq_zero_left e1.symm).trans (CharTwo.neg_eq _)
      rw [heq]
      exact dvd_mul_right p _
    -- `∂_Y` of `h_X = p·u`:  `B₃² = ∂_Y p·u + p·∂_Y u`, so `p ∤ u`.
    have e2 : B₃ ^ 2 = pderiv 1 p * u + p * pderiv 1 u := by
      have h := congrArg (pderiv (1 : Fin 2)) hu
      rwa [pd1_hX, pderiv_mul] at h
    have hpu : ¬ p ∣ u := by
      intro hpu
      apply hpB3sq
      rw [e2]
      exact dvd_add (hpu.mul_left _) (dvd_mul_right p _)
    -- `∂_X` of `h_Y = p·v`:  `B₃² = ∂_X p·v + p·∂_X v`, so `p ∤ ∂_X p`.
    have e3 : B₃ ^ 2 = pderiv 0 p * v + p * pderiv 0 v := by
      have h := congrArg (pderiv (0 : Fin 2)) hv
      rwa [pd0_hY, pderiv_mul] at h
    have hpdp : ¬ p ∣ pderiv 0 p := by
      intro hpdp
      apply hpB3sq
      rw [e3]
      exact dvd_add (hpdp.mul_right _) (dvd_mul_right p _)
    -- Primality kills the last divisibility.
    rcases hp.dvd_mul.mp hdvd1 with h | h
    · exact hpdp h
    · exact hpu h

end PolyClone.FrobeniusDescent
