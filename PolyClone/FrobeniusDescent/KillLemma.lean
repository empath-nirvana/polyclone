/-
  FrobeniusDescent/KillLemma.lean
  ===============================

  **The kill lemma** (finite-intersection argument, made resultant-free):
  if a not-both-constant curve `(α, β) ∈ K[t]²` satisfies BOTH

      `q(α,β) = C c`   (a constant level)   and   `f(α,β) = 0`

  for some NONZERO `f ∈ F₂[X,Y]`, then `c` is algebraic over `F₂`.

  Contrapositive (how the descent uses it): along a witness with `c`
  transcendental, no nonzero `F₂`-polynomial can vanish — the witness image
  cannot sit inside a fixed `F₂`-curve.

  PROOF (elementary, fully spec'd):
  Let `T := F₂[X,Z]` (a fresh variable `Z` for the level) and embed
  `ι : F₂[X,Y] → T[Y]` by `X ↦ C X, Y ↦ Y`.  Set `g := ι q + C Z`.

  1. *Coprimality.*  `g` is monic linear in `Z` over `F₂[X,Y]`, hence
     irreducible in `F₂[X,Y,Z]`; it is primitive as a `Y`-polynomial over `T`,
     so by Gauss it is irreducible in `(Frac T)[Y]` if `deg_Y q ≥ 1`, and in
     every case `g ∤ ι f` (compare `Z`-degrees), so `gcd(ι f, g)` is a unit in
     `(Frac T)[Y]`:  a nonunit common divisor would have positive `Y`-degree
     and Gauss-descend to a common factor of `ι f` and `g` in `T[Y]`, forcing
     `g ∣ ι f` by irreducibility ✗.  (If `deg_Y (ι f) = 0` then `ι f` is a
     nonzero element of `T`, a unit of `(Frac T)[Y]`, and coprimality is
     automatic.)
  2. *Bezout + clear denominators* (`IsLocalization.integerNormalization`):
     `ι f · U + g · V = C D` with `U, V ∈ T[Y]` and `0 ≠ D ∈ T = F₂[X,Z]`.
  3. *Evaluate* via the ring hom `T[Y] →+* K[t]` sending
     `Y ↦ β, X ↦ α, Z ↦ C c`:  `ι f ↦ evC α β f = 0` and
     `g ↦ evC α β q + C c = C c + C c = 0` (char 2!), so `D(α, C c) = 0`.
  4. *Linear independence.*  Write `D = Σᵢ ρᵢ(Z)·Xⁱ` with `ρᵢ ∈ F₂[Z]`; then
     `Σᵢ ρᵢ(c)·αⁱ = 0` in `K[t]`.  If `α` is nonconstant its powers have
     strictly increasing degrees, hence are `K`-linearly independent, so each
     `ρᵢ(c) = 0`; some `ρᵢ ≠ 0` (as `D ≠ 0`) witnesses `AlgebraicF2 c`.
  5. If `α` IS constant then `β` is not (hypothesis `hne`); rerun 1–4 with the
     variables swapped (`MvPolynomial.rename (Equiv.swap 0 1)` on `f` and `q`,
     witness `(β, α)`; note `evC β α (rename (Equiv.swap 0 1) p) = evC α β p`).

  IMPLEMENTATION NOTES (the formalized route below):
  * Steps 1–2 are obtained directly from Mathlib's Sylvester-matrix Bezout
    certificate `Polynomial.exists_mul_add_mul_eq_C_resultant`, which works
    over ANY commutative ring with `D := Res_Y(ι f, g)` — no Gauss-lemma
    plumbing needed.  Nonvanishing of `D` is proved by SPECIALIZING
    (`Polynomial.resultant_map_map`) at `X ↦ σK` (transcendental, so
    `Y`-degrees are preserved) and `Z ↦ z`, where `z` is chosen outside the
    finite set `{-q̄(y) : y root of f̄}` so that the specialized pair is
    coprime over `K` and `Polynomial.resultant_ne_zero` applies.
  * The auxiliary rings are built as ITERATED `Polynomial` (layers
    `Y / X / Z`, outermost to innermost), so the `Z`-slices `ρᵢ` of `D` are
    literally `D.coeff i` — no `Fin`-indexed `MvPolynomial` plumbing.
  * Step 4 collapses to: `(D.map ψc).comp α = 0` with `α` nonconstant forces
    `D.map ψc = 0` (`Polynomial.comp_eq_zero_iff`); the leading coefficient
    of `D` is then a nonzero `F₂[Z]`-annihilator of `c`.
-/
import PolyClone.FrobeniusDescent.Defs
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.FieldTheory.IsAlgClosed.Basic

namespace PolyClone.FrobeniusDescent

open MvPolynomial

/-! ### The auxiliary rings, organized as iterated `Polynomial`

We use three nested polynomial layers over `R2 = F₂`:

* `Polynomial R2` — one variable, read as `F₂[X]` or `F₂[Z]` depending on
  context;
* `Polynomial (Polynomial R2)` — two variables; we use TWO readings:
  - `(F₂[X])[Y]` (outer `Y`, inner `X`): the codomain of the embedding `jHom`;
  - `(F₂[Z])[X]` (outer `X`, inner `Z`): the coefficient ring `T` of the
    `Y`-resultant `D`, whose `.coeff i` are the `Z`-slices `ρᵢ ∈ F₂[Z]`;
* `Polynomial (Polynomial (Polynomial R2))` — three variables `Y / X / Z`
  (outermost to innermost): the ring `T[Y]` where the Bezout certificate
  `ι f · U + g · V = C D` lives.
-/

/-- The embedding `F₂[X,Y] → (F₂[X])[Y]`: `X 0 ↦ C X`, `X 1 ↦ Y`. -/
private noncomputable def jHom : F →+* Polynomial (Polynomial R2) :=
  eval₂Hom ((Polynomial.C : Polynomial R2 →+* Polynomial (Polynomial R2)).comp
      (Polynomial.C : R2 →+* Polynomial R2))
    ![Polynomial.C Polynomial.X, Polynomial.X]

/-- Retraction of `jHom`: outer variable `↦ X 1`, inner variable `↦ X 0`. -/
private noncomputable def rHom : Polynomial (Polynomial R2) →+* F :=
  Polynomial.eval₂RingHom
    (Polynomial.eval₂RingHom (MvPolynomial.C : R2 →+* F) (X 0)) (X 1)

private lemma rHom_comp_jHom : rHom.comp jHom = RingHom.id F := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [jHom, rHom]
  · intro i
    fin_cases i <;> simp [jHom, rHom]

private lemma jHom_injective : Function.Injective jHom := by
  intro p p' h
  have hp := RingHom.congr_fun rHom_comp_jHom p
  have hp' := RingHom.congr_fun rHom_comp_jHom p'
  simp only [RingHom.comp_apply, RingHom.id_apply] at hp hp'
  rw [← hp, ← hp', h]

/-- Coefficientwise embedding `F₂[X] → (F₂[Z])[X]`. -/
private noncomputable def eHom : Polynomial R2 →+* Polynomial (Polynomial R2) :=
  Polynomial.mapRingHom (Polynomial.C : R2 →+* Polynomial R2)

private lemma eHom_injective : Function.Injective eHom :=
  Polynomial.map_injective _ Polynomial.C_injective

/-- The full embedding `ι : F₂[X,Y] → ((F₂[Z])[X])[Y]`. -/
private noncomputable def ιHom : F →+* Polynomial (Polynomial (Polynomial R2)) :=
  (Polynomial.mapRingHom eHom).comp jHom

private lemma ιHom_apply (p : F) : ιHom p = (jHom p).map eHom := by
  simp [ιHom]

/-- The level polynomial `g := ι q + C Z`. -/
private noncomputable def gPoly (q : F) : Polynomial (Polynomial (Polynomial R2)) :=
  ιHom q + Polynomial.C (Polynomial.C Polynomial.X)

/-! ### Evaluation homomorphisms -/

/-- `F₂[Z] → K`, `Z ↦ w`. -/
private noncomputable def ψhom (w : K) : Polynomial R2 →+* K :=
  Polynomial.eval₂RingHom castK w

/-- `(F₂[Z])[X] → K[t]`, `X ↦ α`, `Z ↦ w` (as constants). -/
private noncomputable def φhom (α : Polynomial K) (w : K) :
    Polynomial (Polynomial R2) →+* Polynomial K :=
  Polynomial.eval₂RingHom ((Polynomial.C : K →+* Polynomial K).comp (ψhom w)) α

/-- `((F₂[Z])[X])[Y] → K[t]`, `Y ↦ β`, `X ↦ α`, `Z ↦ w`. -/
private noncomputable def Θhom (α β : Polynomial K) (w : K) :
    Polynomial (Polynomial (Polynomial R2)) →+* Polynomial K :=
  Polynomial.eval₂RingHom (φhom α w) β

/-- `Θ ∘ ι` is curve evaluation (`ι p` is `Z`-free, so `w` is irrelevant). -/
private lemma Θhom_comp_ι (α β : Polynomial K) (w : K) :
    (Θhom α β w).comp ιHom = evC α β := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [Θhom, φhom, ψhom, ιHom, jHom, eHom, evC]
  · intro i
    fin_cases i <;> simp [Θhom, φhom, ψhom, ιHom, jHom, eHom, evC]

private lemma Θhom_ι_apply (α β : Polynomial K) (w : K) (p : F) :
    Θhom α β w (ιHom p) = evC α β p := by
  have h := RingHom.congr_fun (Θhom_comp_ι α β w) p
  rwa [RingHom.comp_apply] at h

/-- `φ ∘ e` evaluates an `X`-polynomial at `α` (coefficients via `castK`). -/
private lemma φhom_comp_eHom (α : Polynomial K) (w : K) :
    (φhom α w).comp eHom =
      Polynomial.eval₂RingHom ((Polynomial.C : K →+* Polynomial K).comp castK) α := by
  apply Polynomial.ringHom_ext
  · intro a
    simp [φhom, ψhom, eHom]
  · simp [φhom, ψhom, eHom]

/-! ### The `σ`-side specialization (for nonvanishing of the resultant) -/

/-- Evaluation of a univariate `F₂`-polynomial (read in the variable `X`) at
the transcendental `σK`. -/
private noncomputable def evσX : Polynomial R2 →+* K :=
  Polynomial.eval₂RingHom castK σK

private lemma evσX_injective : Function.Injective evσX := by
  rw [injective_iff_map_eq_zero]
  intro ρ hρ
  by_contra hne
  exact σK_transcendental
    ⟨ρ, hne, by rwa [evσX, Polynomial.coe_eval₂RingHom] at hρ⟩

/-- `(F₂[Z])[X] → K`, `X ↦ σK`, `Z ↦ z`. -/
private noncomputable def χhom (z : K) : Polynomial (Polynomial R2) →+* K :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom castK z) σK

private lemma χhom_comp_eHom (z : K) : (χhom z).comp eHom = evσX := by
  apply Polynomial.ringHom_ext
  · intro a
    simp [χhom, eHom, evσX]
  · simp [χhom, eHom, evσX]

private lemma map_χ_ι (z : K) (p : F) :
    (ιHom p).map (χhom z) = (jHom p).map evσX := by
  rw [ιHom_apply, Polynomial.map_map, χhom_comp_eHom]

private lemma map_χ_g (z : K) (q : F) :
    (gPoly q).map (χhom z) = (jHom q).map evσX + Polynomial.C z := by
  rw [gPoly, Polynomial.map_add, map_χ_ι, Polynomial.map_C]
  congr 2
  simp [χhom]

/-! ### Choice of a coprime shift -/

private lemma infinite_K : Infinite K :=
  Infinite.of_injective
    (fun p : Polynomial R2 =>
      algebraMap (RatFunc R2) K (algebraMap (Polynomial R2) (RatFunc R2) p))
    (fun _ _ h =>
      RatFunc.algebraMap_injective R2 ((algebraMap (RatFunc R2) K).injective h))

/-- For any `f' ≠ 0` and any `q'` in `K[Y]` there is a constant shift `z` making
`f'` and `q' + C z` coprime: choose `z` avoiding the (finitely many) values
`-q'(y)` at roots `y` of `f'`; a nonunit common divisor would have a root `y`
(`K` is algebraically closed) shared by `f'` and `q' + C z`. -/
private lemma exists_coprime_shift (f' q' : Polynomial K) (hf' : f' ≠ 0) :
    ∃ z : K, IsCoprime f' (q' + Polynomial.C z) := by
  classical
  haveI := infinite_K
  obtain ⟨z, hz⟩ :=
    Infinite.exists_notMem_finset ((f'.roots.map fun y => -(q'.eval y)).toFinset)
  refine ⟨z, ?_⟩
  by_contra hnc
  have hgu : ¬ IsUnit (EuclideanDomain.gcd f' (q' + Polynomial.C z)) := fun h =>
    hnc (EuclideanDomain.gcd_isUnit_iff.mp h)
  have hg0 : EuclideanDomain.gcd f' (q' + Polynomial.C z) ≠ 0 := fun h =>
    hf' (EuclideanDomain.gcd_eq_zero_iff.mp h).1
  have hdeg : (EuclideanDomain.gcd f' (q' + Polynomial.C z)).degree ≠ 0 := fun h =>
    hgu (Polynomial.isUnit_iff_degree_eq_zero.mpr h)
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root _ hdeg
  have hyf : f'.eval y = 0 :=
    Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero
      (EuclideanDomain.gcd_dvd_left _ _) hy
  have hyg : (q' + Polynomial.C z).eval y = 0 :=
    Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero
      (EuclideanDomain.gcd_dvd_right _ _) hy
  apply hz
  rw [Multiset.mem_toFinset, Multiset.mem_map]
  refine ⟨y, Polynomial.mem_roots'.mpr ⟨hf', hyf⟩, ?_⟩
  rw [Polynomial.eval_add, Polynomial.eval_C] at hyg
  exact neg_eq_of_add_eq_zero_right hyg

/-! ### The degenerate case: `f` free of `Y` -/

/-- If `j f` is a constant `Y`-polynomial, the curve evaluation of `f` is a
composite of a univariate polynomial with `α`. -/
private lemma evC_of_jHom_natDegree_eq_zero (f : F) (α β : Polynomial K)
    (h0 : (jHom f).natDegree = 0) :
    evC α β f = (((jHom f).coeff 0).map castK).comp α := by
  obtain ⟨a, ha⟩ := Polynomial.natDegree_eq_zero.mp h0
  rw [← Θhom_ι_apply α β 0 f, ιHom_apply, ← ha, Polynomial.map_C,
    Polynomial.coeff_C_zero]
  have h2 : Θhom α β 0 (Polynomial.C (eHom a)) = φhom α 0 (eHom a) := by
    simp [Θhom]
  rw [h2]
  have h3 := RingHom.congr_fun (φhom_comp_eHom α 0) a
  rw [RingHom.comp_apply] at h3
  rw [h3, show (a.map castK).comp α = Polynomial.eval₂ Polynomial.C α (a.map castK)
      from rfl,
    Polynomial.eval₂_map]
  simp [Polynomial.coe_eval₂RingHom]

/-! ### The main argument, assuming `α` nonconstant -/

private lemma c_algebraic_of_nonconst_x (f q : F) (hf : f ≠ 0) (α β : Polynomial K)
    (hα : α.natDegree ≠ 0) (c : K)
    (hq : evC α β q = Polynomial.C c) (hf0 : evC α β f = 0) :
    AlgebraicF2 c := by
  have hjf : jHom f ≠ 0 := fun h => hf (jHom_injective (by rw [h, map_zero]))
  by_cases h0 : (jHom f).natDegree = 0
  · -- `f` is `Y`-free: `f₀(α) = 0` forces `α` constant, contradicting `hα`.
    exfalso
    have h1 : (((jHom f).coeff 0).map castK).comp α = 0 :=
      (evC_of_jHom_natDegree_eq_zero f α β h0).symm.trans hf0
    rcases Polynomial.comp_eq_zero_iff.mp h1 with h | ⟨-, h⟩
    · have hc0 : (jHom f).coeff 0 = (0 : Polynomial R2) :=
        (Polynomial.map_eq_zero_iff castK.injective).mp h
      apply hjf
      rw [Polynomial.eq_C_of_natDegree_eq_zero h0, hc0, Polynomial.C_0]
    · exact hα (by rw [h]; exact Polynomial.natDegree_C _)
  · -- Nondegenerate: run the resultant certificate.
    -- Degree bookkeeping.
    have hmι : (ιHom f).natDegree = (jHom f).natDegree := by
      rw [ιHom_apply]
      exact Polynomial.natDegree_map_eq_of_injective eHom_injective _
    have hqι : (ιHom q).natDegree = (jHom q).natDegree := by
      rw [ιHom_apply]
      exact Polynomial.natDegree_map_eq_of_injective eHom_injective _
    have hnι : (gPoly q).natDegree = (ιHom q).natDegree := by
      simp [gPoly]
    have hσf : ((jHom f).map evσX).natDegree = (jHom f).natDegree :=
      Polynomial.natDegree_map_eq_of_injective evσX_injective _
    have hσq : ((jHom q).map evσX).natDegree = (jHom q).natDegree :=
      Polynomial.natDegree_map_eq_of_injective evσX_injective _
    have hf'ne : (jHom f).map evσX ≠ 0 :=
      (Polynomial.map_ne_zero_iff evσX_injective).mpr hjf
    obtain ⟨z, hcop⟩ :=
      exists_coprime_shift ((jHom f).map evσX) ((jHom q).map evσX) hf'ne
    -- Bezout certificate from the resultant.
    obtain ⟨U, V, -, -, hUV⟩ :=
      Polynomial.exists_mul_add_mul_eq_C_resultant (ιHom f) (gPoly q) le_rfl le_rfl
        (Or.inl (by rw [hmι]; exact h0))
    set D : Polynomial (Polynomial R2) :=
      (ιHom f).resultant (gPoly q) (ιHom f).natDegree (gPoly q).natDegree with hD
    -- `D ≠ 0` via the specialization `X ↦ σK`, `Z ↦ z`.
    have hχD : χhom z D ≠ 0 := by
      rw [hD, ← Polynomial.resultant_map_map, map_χ_ι, map_χ_g]
      have e1 : ((jHom f).map evσX).natDegree = (ιHom f).natDegree := by
        rw [hσf, hmι]
      have e2 : ((jHom q).map evσX + Polynomial.C z).natDegree =
          (gPoly q).natDegree := by
        rw [Polynomial.natDegree_add_C, hσq, ← hqι, ← hnι]
      rw [← e1, ← e2]
      exact Polynomial.resultant_ne_zero _ _ hcop
    have hDne : D ≠ 0 := by
      intro h
      rw [h, map_zero] at hχD
      exact hχD rfl
    -- Evaluate the certificate along the curve: both `ι f` and `g` die.
    have hΘf : Θhom α β c (ιHom f) = 0 := by rw [Θhom_ι_apply]; exact hf0
    have hΘg : Θhom α β c (gPoly q) = 0 := by
      simp only [gPoly, map_add]
      rw [Θhom_ι_apply, hq]
      have hzc : Θhom α β c (Polynomial.C (Polynomial.C Polynomial.X)) =
          Polynomial.C c := by
        simp [Θhom, φhom, ψhom]
      rw [hzc]
      exact CharTwo.add_self_eq_zero _
    have hφD : φhom α c D = 0 := by
      have h := congrArg (Θhom α β c) hUV
      rw [map_add, map_mul, map_mul, hΘf, hΘg, zero_mul, zero_mul, add_zero] at h
      have hCD : Θhom α β c (Polynomial.C D) = φhom α c D := by simp [Θhom]
      rw [hCD] at h
      exact h.symm
    -- Reorganize as a composite with `α` and use that `α` is nonconstant.
    have hcomp : ((D.map (ψhom c)).comp α) = 0 := by
      have h1 : (D.map (ψhom c)).comp α = φhom α c D := by
        rw [show (D.map (ψhom c)).comp α =
            Polynomial.eval₂ Polynomial.C α (D.map (ψhom c)) from rfl,
          Polynomial.eval₂_map]
        simp [φhom, Polynomial.coe_eval₂RingHom]
      rw [h1]
      exact hφD
    have hDmap : D.map (ψhom c) = 0 := by
      rcases Polynomial.comp_eq_zero_iff.mp hcomp with h | ⟨-, h⟩
      · exact h
      · exact absurd (by rw [h]; exact Polynomial.natDegree_C _) hα
    -- The leading `Z`-slice of `D` witnesses algebraicity of `c`.
    refine ⟨D.leadingCoeff, Polynomial.leadingCoeff_ne_zero.mpr hDne, ?_⟩
    have hco := congrArg (fun p : Polynomial K => p.coeff D.natDegree) hDmap
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at hco
    rwa [ψhom, Polynomial.coe_eval₂RingHom] at hco

/-! ### Variable swap (for the case `α` constant, `β` nonconstant) -/

private lemma evC_swap (α β : Polynomial K) (p : F) :
    evC β α (rename (Equiv.swap (0 : Fin 2) 1) p) = evC α β p := by
  simp only [evC]
  rw [eval₂Hom_rename]
  have hv : (![β, α] ∘ ⇑(Equiv.swap (0 : Fin 2) 1)) = ![α, β] := by
    funext i
    fin_cases i <;> simp [Equiv.swap_apply_left, Equiv.swap_apply_right]
  rw [hv]

/-- **Kill lemma.**  A nonzero `F₂`-curve constraint along a not-both-constant
    constant-level curve forces the level to be algebraic. -/
theorem c_algebraic_of_curve_constraint
    (f q : F) (hf : f ≠ 0) (α β : Polynomial K)
    (hne : ¬ (α.natDegree = 0 ∧ β.natDegree = 0)) (c : K)
    (hq : evC α β q = Polynomial.C c) (hf0 : evC α β f = 0) :
    AlgebraicF2 c := by
  by_cases hα : α.natDegree = 0
  · have hβ : β.natDegree ≠ 0 := fun h => hne ⟨hα, h⟩
    have hswap : Function.Injective (rename (Equiv.swap (0 : Fin 2) 1) : F → F) :=
      rename_injective _ (Equiv.swap _ _).injective
    refine c_algebraic_of_nonconst_x (rename (Equiv.swap (0 : Fin 2) 1) f)
      (rename (Equiv.swap (0 : Fin 2) 1) q)
      (fun h => hf (hswap (by rw [h, map_zero]))) β α hβ c ?_ ?_
    · rw [evC_swap]; exact hq
    · rw [evC_swap]; exact hf0
  · exact c_algebraic_of_nonconst_x f q hf α β hα c hq hf0

end PolyClone.FrobeniusDescent
