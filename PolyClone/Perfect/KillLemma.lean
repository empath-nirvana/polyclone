/-
  FrobeniusDescentP/KillLemma.lean
  ================================

  Parametric port of `FrobeniusDescent/KillLemma.lean` from `F₂ = ZMod 2`
  to an arbitrary perfect field `Fq` of characteristic 2.

  **The kill lemma** (finite-intersection argument, made resultant-free):
  if a not-both-constant curve `(α, β) ∈ K[t]²` satisfies BOTH

      `q(α,β) = C c`   (a constant level)   and   `f(α,β) = 0`

  for some NONZERO `f ∈ Fq[X,Y]`, then `c` is algebraic over `Fq`.

  The proof is verbatim the F₂ one — every helper is `CommRing`-generic:
  * the auxiliary rings are ITERATED `Polynomial` over `Fq` (layers
    `Y / X / Z`, outermost to innermost);
  * steps 1–2 of the spec come from Mathlib's Sylvester-matrix Bezout
    certificate `Polynomial.exists_mul_add_mul_eq_C_resultant`, with
    `D := Res_Y(ι f, g)`; nonvanishing of `D` is proved by SPECIALIZING
    (`Polynomial.resultant_map_map`) at `X ↦ σK` (transcendental over `Fq`,
    so `Y`-degrees are preserved) and `Z ↦ z`, where `z` is chosen outside
    the finite set `{-q̄(y) : y root of f̄}` so the specialized pair is
    coprime over `K` and `Polynomial.resultant_ne_zero` applies;
  * evaluating the certificate along the curve kills both `ι f` and
    `g = ι q + C Z` (char 2!), so `D(α, C c) = 0`; with `α` nonconstant
    (`Polynomial.comp_eq_zero_iff`) the leading `Z`-slice of `D` is a
    nonzero `Fq[Z]`-annihilator of `c`, i.e. `IsAlgebraic Fq c`.

  The only F₂-specific pieces of the original — the `AlgebraicF2` witness
  shapes in `evσX_injective` and the final step — are rebuilt here from
  `σK_transcendental : ¬ IsAlgebraic Fq σK` and `Polynomial.aeval_def`
  (`castK Fq` is definitionally `algebraMap Fq (K Fq)`).
-/
import PolyClone.Perfect.Defs
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.FieldTheory.IsAlgClosed.Basic

namespace PolyClone.Perfect

open MvPolynomial

set_option linter.unusedSectionVars false

variable {Fq : Type} [Field Fq] [CharP Fq 2] [PerfectRing Fq 2]

/-! ### The auxiliary rings, organized as iterated `Polynomial`

We use three nested polynomial layers over `Fq`:

* `Polynomial Fq` — one variable, read as `Fq[X]` or `Fq[Z]` depending on
  context;
* `Polynomial (Polynomial Fq)` — two variables; we use TWO readings:
  - `(Fq[X])[Y]` (outer `Y`, inner `X`): the codomain of the embedding `jHom`;
  - `(Fq[Z])[X]` (outer `X`, inner `Z`): the coefficient ring `T` of the
    `Y`-resultant `D`, whose `.coeff i` are the `Z`-slices `ρᵢ ∈ Fq[Z]`;
* `Polynomial (Polynomial (Polynomial Fq))` — three variables `Y / X / Z`
  (outermost to innermost): the ring `T[Y]` where the Bezout certificate
  `ι f · U + g · V = C D` lives.
-/

/-- The embedding `Fq[X,Y] → (Fq[X])[Y]`: `X 0 ↦ C X`, `X 1 ↦ Y`. -/
private noncomputable def jHom : F Fq →+* Polynomial (Polynomial Fq) :=
  eval₂Hom ((Polynomial.C : Polynomial Fq →+* Polynomial (Polynomial Fq)).comp
      (Polynomial.C : Fq →+* Polynomial Fq))
    ![Polynomial.C Polynomial.X, Polynomial.X]

/-- Retraction of `jHom`: outer variable `↦ X 1`, inner variable `↦ X 0`. -/
private noncomputable def rHom : Polynomial (Polynomial Fq) →+* F Fq :=
  Polynomial.eval₂RingHom
    (Polynomial.eval₂RingHom (MvPolynomial.C : Fq →+* F Fq) (X 0)) (X 1)

private lemma rHom_comp_jHom :
    (rHom (Fq := Fq)).comp jHom = RingHom.id (F Fq) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [jHom, rHom]
  · intro i
    fin_cases i <;> simp [jHom, rHom]

private lemma jHom_injective : Function.Injective (jHom (Fq := Fq)) := by
  intro p p' h
  have hp := RingHom.congr_fun rHom_comp_jHom p
  have hp' := RingHom.congr_fun rHom_comp_jHom p'
  simp only [RingHom.comp_apply, RingHom.id_apply] at hp hp'
  rw [← hp, ← hp', h]

/-- Coefficientwise embedding `Fq[X] → (Fq[Z])[X]`. -/
private noncomputable def eHom : Polynomial Fq →+* Polynomial (Polynomial Fq) :=
  Polynomial.mapRingHom (Polynomial.C : Fq →+* Polynomial Fq)

private lemma eHom_injective : Function.Injective (eHom (Fq := Fq)) :=
  Polynomial.map_injective _ Polynomial.C_injective

/-- The full embedding `ι : Fq[X,Y] → ((Fq[Z])[X])[Y]`. -/
private noncomputable def ιHom :
    F Fq →+* Polynomial (Polynomial (Polynomial Fq)) :=
  (Polynomial.mapRingHom eHom).comp jHom

private lemma ιHom_apply (p : F Fq) : ιHom p = (jHom p).map eHom := by
  simp [ιHom]

/-- The level polynomial `g := ι q + C Z`. -/
private noncomputable def gPoly (q : F Fq) :
    Polynomial (Polynomial (Polynomial Fq)) :=
  ιHom q + Polynomial.C (Polynomial.C Polynomial.X)

/-! ### Evaluation homomorphisms -/

/-- `Fq[Z] → K`, `Z ↦ w`. -/
private noncomputable def ψhom (w : K Fq) : Polynomial Fq →+* K Fq :=
  Polynomial.eval₂RingHom (castK Fq) w

/-- `(Fq[Z])[X] → K[t]`, `X ↦ α`, `Z ↦ w` (as constants). -/
private noncomputable def φhom (α : Polynomial (K Fq)) (w : K Fq) :
    Polynomial (Polynomial Fq) →+* Polynomial (K Fq) :=
  Polynomial.eval₂RingHom
    ((Polynomial.C : K Fq →+* Polynomial (K Fq)).comp (ψhom w)) α

/-- `((Fq[Z])[X])[Y] → K[t]`, `Y ↦ β`, `X ↦ α`, `Z ↦ w`. -/
private noncomputable def Θhom (α β : Polynomial (K Fq)) (w : K Fq) :
    Polynomial (Polynomial (Polynomial Fq)) →+* Polynomial (K Fq) :=
  Polynomial.eval₂RingHom (φhom α w) β

/-- `Θ ∘ ι` is curve evaluation (`ι p` is `Z`-free, so `w` is irrelevant). -/
private lemma Θhom_comp_ι (α β : Polynomial (K Fq)) (w : K Fq) :
    (Θhom α β w).comp ιHom = evC Fq α β := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [Θhom, φhom, ψhom, ιHom, jHom, eHom, evC]
  · intro i
    fin_cases i <;> simp [Θhom, φhom, ψhom, ιHom, jHom, eHom, evC]

private lemma Θhom_ι_apply (α β : Polynomial (K Fq)) (w : K Fq) (p : F Fq) :
    Θhom α β w (ιHom p) = evC Fq α β p := by
  have h := RingHom.congr_fun (Θhom_comp_ι α β w) p
  rwa [RingHom.comp_apply] at h

/-- `φ ∘ e` evaluates an `X`-polynomial at `α` (coefficients via `castK`). -/
private lemma φhom_comp_eHom (α : Polynomial (K Fq)) (w : K Fq) :
    (φhom α w).comp eHom =
      Polynomial.eval₂RingHom
        ((Polynomial.C : K Fq →+* Polynomial (K Fq)).comp (castK Fq)) α := by
  apply Polynomial.ringHom_ext
  · intro a
    simp [φhom, ψhom, eHom]
  · simp [φhom, ψhom, eHom]

/-! ### The `σ`-side specialization (for nonvanishing of the resultant) -/

/-- Evaluation of a univariate `Fq`-polynomial (read in the variable `X`) at
the transcendental `σK`. -/
private noncomputable def evσX : Polynomial Fq →+* K Fq :=
  Polynomial.eval₂RingHom (castK Fq) σK

private lemma evσX_injective : Function.Injective (evσX (Fq := Fq)) := by
  rw [injective_iff_map_eq_zero]
  intro ρ hρ
  by_contra hne
  refine σK_transcendental ⟨ρ, hne, ?_⟩
  rw [evσX, Polynomial.coe_eval₂RingHom] at hρ
  rw [Polynomial.aeval_def]
  exact hρ

/-- `(Fq[Z])[X] → K`, `X ↦ σK`, `Z ↦ z`. -/
private noncomputable def χhom (z : K Fq) :
    Polynomial (Polynomial Fq) →+* K Fq :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (castK Fq) z) σK

private lemma χhom_comp_eHom (z : K Fq) :
    (χhom z).comp eHom = evσX (Fq := Fq) := by
  apply Polynomial.ringHom_ext
  · intro a
    simp [χhom, eHom, evσX]
  · simp [χhom, eHom, evσX]

private lemma map_χ_ι (z : K Fq) (p : F Fq) :
    (ιHom p).map (χhom z) = (jHom p).map evσX := by
  rw [ιHom_apply, Polynomial.map_map, χhom_comp_eHom]

private lemma map_χ_g (z : K Fq) (q : F Fq) :
    (gPoly q).map (χhom z) = (jHom q).map evσX + Polynomial.C z := by
  rw [gPoly, Polynomial.map_add, map_χ_ι, Polynomial.map_C]
  congr 2
  simp [χhom]

/-! ### Choice of a coprime shift -/

private lemma infinite_K : Infinite (K Fq) :=
  Infinite.of_injective
    (fun p : Polynomial Fq =>
      algebraMap (RatFunc Fq) (K Fq) (algebraMap (Polynomial Fq) (RatFunc Fq) p))
    (fun _ _ h =>
      RatFunc.algebraMap_injective Fq
        ((algebraMap (RatFunc Fq) (K Fq)).injective h))

/-- For any `f' ≠ 0` and any `q'` in `K[Y]` there is a constant shift `z` making
`f'` and `q' + C z` coprime: choose `z` avoiding the (finitely many) values
`-q'(y)` at roots `y` of `f'`; a nonunit common divisor would have a root `y`
(`K` is algebraically closed) shared by `f'` and `q' + C z`. -/
private lemma exists_coprime_shift (f' q' : Polynomial (K Fq)) (hf' : f' ≠ 0) :
    ∃ z : K Fq, IsCoprime f' (q' + Polynomial.C z) := by
  classical
  haveI := infinite_K (Fq := Fq)
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
private lemma evC_of_jHom_natDegree_eq_zero (f : F Fq) (α β : Polynomial (K Fq))
    (h0 : (jHom f).natDegree = 0) :
    evC Fq α β f = (((jHom f).coeff 0).map (castK Fq)).comp α := by
  obtain ⟨a, ha⟩ := Polynomial.natDegree_eq_zero.mp h0
  rw [← Θhom_ι_apply α β 0 f, ιHom_apply, ← ha, Polynomial.map_C,
    Polynomial.coeff_C_zero]
  have h2 : Θhom α β 0 (Polynomial.C (eHom a)) = φhom α 0 (eHom a) := by
    simp [Θhom]
  rw [h2]
  have h3 := RingHom.congr_fun (φhom_comp_eHom α 0) a
  rw [RingHom.comp_apply] at h3
  rw [h3, show (a.map (castK Fq)).comp α =
      Polynomial.eval₂ Polynomial.C α (a.map (castK Fq)) from rfl,
    Polynomial.eval₂_map]
  simp [Polynomial.coe_eval₂RingHom]

/-! ### The main argument, assuming `α` nonconstant -/

private lemma c_algebraic_of_nonconst_x (f q : F Fq) (hf : f ≠ 0)
    (α β : Polynomial (K Fq)) (hα : α.natDegree ≠ 0) (c : K Fq)
    (hq : evC Fq α β q = Polynomial.C c) (hf0 : evC Fq α β f = 0) :
    IsAlgebraic Fq c := by
  have hjf : jHom f ≠ 0 := fun h => hf (jHom_injective (by rw [h, map_zero]))
  by_cases h0 : (jHom f).natDegree = 0
  · -- `f` is `Y`-free: `f₀(α) = 0` forces `α` constant, contradicting `hα`.
    exfalso
    have h1 : (((jHom f).coeff 0).map (castK Fq)).comp α = 0 :=
      (evC_of_jHom_natDegree_eq_zero f α β h0).symm.trans hf0
    rcases Polynomial.comp_eq_zero_iff.mp h1 with h | ⟨-, h⟩
    · have hc0 : (jHom f).coeff 0 = (0 : Polynomial Fq) :=
        (Polynomial.map_eq_zero_iff (castK Fq).injective).mp h
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
    set D : Polynomial (Polynomial Fq) :=
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
    have hco := congrArg (fun p : Polynomial (K Fq) => p.coeff D.natDegree) hDmap
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at hco
    rw [ψhom, Polynomial.coe_eval₂RingHom] at hco
    rw [Polynomial.aeval_def]
    exact hco

/-! ### Variable swap (for the case `α` constant, `β` nonconstant) -/

private lemma evC_swap (α β : Polynomial (K Fq)) (p : F Fq) :
    evC Fq β α (rename (Equiv.swap (0 : Fin 2) 1) p) = evC Fq α β p := by
  simp only [evC]
  rw [eval₂Hom_rename]
  have hv : (![β, α] ∘ ⇑(Equiv.swap (0 : Fin 2) 1)) = ![α, β] := by
    funext i
    fin_cases i <;> simp [Equiv.swap_apply_left, Equiv.swap_apply_right]
  rw [hv]

/-- **Kill lemma.**  A nonzero `Fq`-curve constraint along a not-both-constant
    constant-level curve forces the level to be algebraic over `Fq`. -/
theorem c_algebraic_of_curve_constraint
    (f q : F Fq) (hf : f ≠ 0) (α β : Polynomial (K Fq))
    (hne : ¬ (α.natDegree = 0 ∧ β.natDegree = 0)) (c : K Fq)
    (hq : evC Fq α β q = Polynomial.C c) (hf0 : evC Fq α β f = 0) :
    IsAlgebraic Fq c := by
  by_cases hα : α.natDegree = 0
  · have hβ : β.natDegree ≠ 0 := fun h => hne ⟨hα, h⟩
    have hswap : Function.Injective
        (rename (Equiv.swap (0 : Fin 2) 1) : F Fq → F Fq) :=
      rename_injective _ (Equiv.swap _ _).injective
    refine c_algebraic_of_nonconst_x (rename (Equiv.swap (0 : Fin 2) 1) f)
      (rename (Equiv.swap (0 : Fin 2) 1) q)
      (fun h => hf (hswap (by rw [h, map_zero]))) β α hβ c ?_ ?_
    · rw [evC_swap]; exact hq
    · rw [evC_swap]; exact hf0
  · exact c_algebraic_of_nonconst_x f q hf α β hα c hq hf0

end PolyClone.Perfect
