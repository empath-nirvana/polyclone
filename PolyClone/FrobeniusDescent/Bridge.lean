/-
  FrobeniusDescent/Bridge.lean
  ============================

  Bridge from the curve-side descent (`no_nonconstant_witness`) to the
  clone-side tameness predicate (`Tameness.Tame`):

      `Φ : F₂[X,Y] →+* K[t]`,  `p ↦ p(t, t + σ)`,

  evaluation along the "generic line of slope X+Y = σ" (σ transcendental).

  Key facts:
  * `p ∈ Diag = F₂[X+Y]` ⟺ `Φ p` is constant.  (⟸ factors `Φ` through the
    lift `F₂[X,Y] → (F₂[Y'])[t]`, `X ↦ t`, `Y ↦ t + Y'`; the `t`-coefficients
    are `F₂[Y']`-polynomials evaluated at the transcendental `σ`, so vanishing
    in `K` forces them to vanish in `F₂[Y']`.)
  * a NONCONSTANT `p ∈ Diag` has `Φ p = C u` with `u` TRANSCENDENTAL
    (`u = f(σ)` for a nonconstant `f ∈ F₂[T]`).
  * `Φ` intertwines clone substitution with curve evaluation:
    `Φ (p(a,b)) = p(Φ a, Φ b)`.
-/
import PolyClone.FrobeniusDescent.Descent
import PolyClone.Tameness

namespace PolyClone.FrobeniusDescent

open MvPolynomial

/-- Evaluation along the generic line: `p(X,Y) ↦ p(t, t + σ)`. -/
noncomputable def Φ : F →+* Polynomial K :=
  evC Polynomial.X (Polynomial.X + Polynomial.C σK)

/-- `Φ` intertwines clone substitution with curve evaluation. -/
lemma Φ_bind (p a b : F) : Φ (bind₁ ![a, b] p) = evC (Φ a) (Φ b) p := by
  have h : Φ.comp (bind₁ (R := R2) ![a, b]).toRingHom = evC (Φ a) (Φ b) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [Φ, evC]
    · intro i
      fin_cases i <;> simp
  exact RingHom.congr_fun h p

/-! ### The coefficient-wise lift of `Φ`

`Φ` factors as `F₂[X,Y] → (F₂[Y'])[t] → K[t]`, where the first map sends
`X ↦ t`, `Y ↦ t + Y'` (split injection, with retraction `t ↦ X`, `Y' ↦ X + Y`
in char 2) and the second map evaluates each coefficient at `Y' = σ`. -/

/-- Evaluation of a univariate `F₂`-polynomial at the transcendental `σK`. -/
private noncomputable def evσ : Polynomial R2 →+* K :=
  Polynomial.eval₂RingHom castK σK

/-- The lift `F₂[X,Y] → (F₂[Y'])[t]`, `X ↦ t`, `Y ↦ t + Y'`. -/
private noncomputable def lift2 : F →+* Polynomial (Polynomial R2) :=
  eval₂Hom ((Polynomial.C : Polynomial R2 →+* Polynomial (Polynomial R2)).comp
      (Polynomial.C : R2 →+* Polynomial R2))
    ![Polynomial.X, Polynomial.X + Polynomial.C Polynomial.X]

/-- The retraction `(F₂[Y'])[t] → F₂[X,Y]`, `t ↦ X`, `Y' ↦ X + Y`. -/
private noncomputable def drop2 : Polynomial (Polynomial R2) →+* F :=
  Polynomial.eval₂RingHom
    (Polynomial.eval₂RingHom (MvPolynomial.C : R2 →+* F) (X 0 + X 1)) (X 0)

private lemma Φ_eq_map_lift2 : Φ = (Polynomial.mapRingHom evσ).comp lift2 := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [Φ, evC, lift2, evσ]
  · intro i
    fin_cases i <;> simp [Φ, lift2, evσ]

private lemma drop2_lift2 : drop2.comp lift2 = RingHom.id F := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [lift2, drop2]
  · intro i
    fin_cases i
    · simp [lift2, drop2]
    · simp [lift2, drop2]
      rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]

/-- Computation of `Φ` on the normal form `f(X+Y)` of elements of `Diag`. -/
private lemma Φ_aeval (f : Polynomial R2) :
    Φ (Polynomial.aeval (X 0 + X 1 : F) f) =
      Polynomial.C (Polynomial.eval₂ castK σK f) := by
  rw [Polynomial.aeval_def, Polynomial.hom_eval₂]
  have h1 : Φ.comp (algebraMap R2 F) = (Polynomial.C : K →+* Polynomial K).comp castK := by
    ext c
    simp [Φ, evC, MvPolynomial.algebraMap_eq]
  have h2 : Φ (X 0 + X 1) = Polynomial.C σK := by
    rw [map_add]
    simp only [Φ, evC_X0, evC_X1]
    rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  rw [h1, h2]
  exact (Polynomial.hom_eval₂ f castK Polynomial.C σK).symm

/-- Membership in `Diag = F₂[X+Y]` ⟺ constancy along the generic line. -/
lemma mem_Diag_iff_Φ_const (p : F) :
    p ∈ Tameness.Diag ↔ ∃ u : K, Φ p = Polynomial.C u := by
  constructor
  · intro hp
    rw [Tameness.Diag, Algebra.adjoin_singleton_eq_range_aeval] at hp
    obtain ⟨f, hf⟩ := (AlgHom.mem_range _).mp hp
    exact ⟨Polynomial.eval₂ castK σK f, by rw [← hf, Φ_aeval]⟩
  · rintro ⟨u, hu⟩
    -- the `t`-coefficients of the lift, evaluated at `σ`, vanish in degree ≥ 1
    have hmap : (lift2 p).map evσ = Polynomial.C u := by
      have h := RingHom.congr_fun Φ_eq_map_lift2 p
      rw [hu] at h
      simpa [Polynomial.coe_mapRingHom] using h.symm
    have hco : ∀ k, 1 ≤ k → (lift2 p).coeff k = 0 := by
      intro k hk
      by_contra hne
      apply σK_transcendental
      refine ⟨(lift2 p).coeff k, hne, ?_⟩
      have h0 : ((lift2 p).map evσ).coeff k = 0 := by
        rw [hmap, Polynomial.coeff_C, if_neg (by omega)]
      rwa [Polynomial.coeff_map, evσ, Polynomial.coe_eval₂RingHom] at h0
    -- so the lift is a constant `t`-polynomial `C g₀`
    have hC : lift2 p = Polynomial.C ((lift2 p).coeff 0) :=
      Polynomial.eq_C_of_natDegree_le_zero
        (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun m hm => hco m hm)
    -- retract: `p = g₀(X+Y) ∈ Diag`
    have hp : p = Polynomial.eval₂ (MvPolynomial.C : R2 →+* F) (X 0 + X 1)
        ((lift2 p).coeff 0) := by
      have h := RingHom.congr_fun drop2_lift2 p
      rw [RingHom.comp_apply, hC, RingHom.id_apply] at h
      conv_lhs => rw [← h]
      simp [drop2]
    rw [Tameness.Diag, Algebra.adjoin_singleton_eq_range_aeval]
    refine (AlgHom.mem_range _).mpr ⟨(lift2 p).coeff 0, ?_⟩
    rw [Polynomial.aeval_def, MvPolynomial.algebraMap_eq]
    exact hp.symm

/-- Nonconstant elements of `Diag` evaluate to transcendentals on the line. -/
lemma Φ_value_transcendental (p : F) (hp : p ∈ Tameness.Diag)
    (hnc : ¬ Tameness.IsConst p) (u : K) (hu : Φ p = Polynomial.C u) :
    ¬ AlgebraicF2 u := by
  rw [Tameness.Diag, Algebra.adjoin_singleton_eq_range_aeval] at hp
  obtain ⟨f, hf⟩ := (AlgHom.mem_range _).mp hp
  have hΦ : Φ p = Polynomial.C (Polynomial.eval₂ castK σK f) := by rw [← hf, Φ_aeval]
  have hu' : u = Polynomial.eval₂ castK σK f := Polynomial.C_injective (hu.symm.trans hΦ)
  -- `p` nonconstant forces `f` nonconstant
  have hfdeg : f.natDegree ≠ 0 := by
    intro h0
    obtain ⟨a, ha⟩ := Polynomial.natDegree_eq_zero.mp h0
    apply hnc
    refine ⟨a, ?_⟩
    rw [← hf, ← ha, Polynomial.aeval_C, MvPolynomial.algebraMap_eq]
  -- a nonzero annihilator `g` of `u = f(σ)` gives the nonzero annihilator
  -- `g ∘ f` of `σ`, contradicting transcendence
  rintro ⟨g, hg0, hgu⟩
  apply σK_transcendental
  refine ⟨g.comp f, ?_, ?_⟩
  · intro hcomp
    rcases Polynomial.comp_eq_zero_iff.mp hcomp with h | ⟨_, hfc⟩
    · exact hg0 h
    · exact hfdeg (by rw [hfc]; exact Polynomial.natDegree_C _)
  · rw [Polynomial.eval₂_comp, ← hu', hgu]

/-- **Tameness from the descent**: `∂_X∂_Y q ≠ 0 ⟹ Tame q`.
    (The case `D q = 1` of this statement was the original "tameness theorem".) -/
theorem tame_of_D_ne_zero (q : F) (hD : DXDYCocycle.D q ≠ 0) :
    Tameness.Tame q := by
  intro a b hnc hmem
  obtain ⟨u, hu⟩ := (mem_Diag_iff_Φ_const _).mp hmem
  have hut : ¬ AlgebraicF2 u := Φ_value_transcendental _ hmem hnc u hu
  have hwit : evC (Φ a) (Φ b) q = Polynomial.C u := by
    rw [← Φ_bind]; exact hu
  obtain ⟨ha0, hb0⟩ := no_nonconstant_witness q hD u hut (Φ a) (Φ b) hwit
  obtain ⟨ua, hua⟩ := Polynomial.natDegree_eq_zero.mp ha0
  obtain ⟨ub, hub⟩ := Polynomial.natDegree_eq_zero.mp hb0
  exact ⟨(mem_Diag_iff_Φ_const a).mpr ⟨ua, hua.symm⟩,
    (mem_Diag_iff_Φ_const b).mpr ⟨ub, hub.symm⟩⟩

end PolyClone.FrobeniusDescent
