/-
  FrobeniusDescent/AlgebraicPoint.lean
  ====================================

  **Algebraic-point lemma**: a common zero in `K²` of two relatively prime
  polynomials of `F₂[X,Y]` has both coordinates algebraic over `F₂`.
  (This replaces "`Crit(h)` is a finite set of `F̄₂`-points" — no dimension
  theory needed.)

  PROOF (elementary, fully spec'd):
  For the `x`-coordinate: view `u, v` in `(F₂[X])[Y]` (explicit ring homs
  `toUni : F →+* (F₂[X])[Y]` and `toMv` back, mutually inverse by
  extensionality on generators).
  * `u, v` are coprime in `F₂(X)[Y]`: otherwise the (Euclidean) gcd is a
    nonunit common divisor over `F₂(X)`, which Gauss-descends (clearing
    denominators with `IsLocalization.integerNormalization`, then passing to
    the primitive part, `Polynomial.IsPrimitive.dvd_of_fraction_map_dvd_fraction_map`)
    to a nonunit common divisor of `u` and `v` in `(F₂[X])[Y]` — contradicting
    `hcop`.
  * If `x` were NOT algebraic over `F₂`, evaluation `F₂[X] → K` at `x` would
    be injective, hence would lift to the fraction field `F₂(X) → K`
    (`IsFractionRing.lift`).  Evaluating the Bezout identity
    `a·u + b·v = 1` of `F₂(X)[Y]` through `F₂(X)[Y] →+* K` (`X ↦ x, Y ↦ y`)
    kills the left side (`evP x y u = 0 = evP x y v`), giving `0 = 1` in `K`.
  For the `y`-coordinate, swap the variables
  (`MvPolynomial.rename (Equiv.swap 0 1)`, point `(y, x)`).
-/
import PolyClone.FrobeniusDescent.Defs
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.RingTheory.Localization.FractionRing

namespace PolyClone.FrobeniusDescent

open MvPolynomial

/-! ### The explicit reorganization `F₂[X,Y] ≅ (F₂[X])[Y]` -/

/-- `F₂[X]`, the coefficient ring of the univariate reorganization. -/
private abbrev R1 : Type := Polynomial R2

/-- `(F₂[X])[Y]`. -/
private abbrev PP : Type := Polynomial R1

/-- `F₂(X)`, the fraction field of the coefficients. -/
private abbrev L : Type := FractionRing R1

/-- `F₂[X,Y] → (F₂[X])[Y]` : `X 0 ↦ C X`, `X 1 ↦ Y` (the outer variable). -/
private noncomputable def toUni : F →+* PP :=
  eval₂Hom ((Polynomial.C : R1 →+* PP).comp (Polynomial.C : R2 →+* R1))
    ![Polynomial.C Polynomial.X, Polynomial.X]

/-- `(F₂[X])[Y] → F₂[X,Y]` : inner `X ↦ X 0`, outer `Y ↦ X 1`. -/
private noncomputable def toMv : PP →+* F :=
  Polynomial.eval₂RingHom
    (Polynomial.eval₂RingHom (MvPolynomial.C : R2 →+* F) (X 0)) (X 1)

private lemma toMv_toUni : toMv.comp toUni = RingHom.id F := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [toUni, toMv]
  · intro i
    fin_cases i <;> simp [toUni, toMv]

private lemma toUni_toMv : toUni.comp toMv = RingHom.id PP := by
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext'
    · exact Subsingleton.elim _ _
    · simp [toUni, toMv]
  · simp [toUni, toMv]

private lemma toMv_toUni_apply (p : F) : toMv (toUni p) = p :=
  RingHom.congr_fun toMv_toUni p

private lemma toUni_toMv_apply (q : PP) : toUni (toMv q) = q :=
  RingHom.congr_fun toUni_toMv q

/-! ### Gauss descent: coprimality over `F₂(X)` -/

/-- If `u', v' ∈ (F₂[X])[Y]` (with `u' ≠ 0`) share no nonunit common factor,
they are coprime in `F₂(X)[Y]` (a Bezout ring): a nonunit common divisor over
the fraction field descends, via `integerNormalization` and the primitive
part, to a nonunit common divisor over `F₂[X]`. -/
private lemma isCoprime_map_of_no_common_factor (u' v' : PP) (hu' : u' ≠ 0)
    (hcop : ∀ d : PP, d ∣ u' → d ∣ v' → IsUnit d) :
    IsCoprime (u'.map (algebraMap R1 L)) (v'.map (algebraMap R1 L)) := by
  classical
  rw [← EuclideanDomain.gcd_isUnit_iff]
  by_contra hgu
  set d : Polynomial L :=
    EuclideanDomain.gcd (u'.map (algebraMap R1 L)) (v'.map (algebraMap R1 L)) with hd
  have hdu : d ∣ u'.map (algebraMap R1 L) := EuclideanDomain.gcd_dvd_left _ _
  have hdv : d ∣ v'.map (algebraMap R1 L) := EuclideanDomain.gcd_dvd_right _ _
  have hd0 : d ≠ 0 := by
    intro h
    exact (Polynomial.map_ne_zero_iff (IsFractionRing.injective R1 L)).mpr hu'
      (zero_dvd_iff.mp (h ▸ hdu))
  -- clear denominators
  obtain ⟨b, hb, hbd⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R1) d
  set d₀ : PP := IsLocalization.integerNormalization (nonZeroDivisors R1) d with hd₀
  have hb0 : algebraMap R1 L b ≠ 0 := by
    intro h
    exact nonZeroDivisors.ne_zero hb (IsFractionRing.injective R1 L (by simpa using h))
  have hbd' : d₀.map (algebraMap R1 L) = Polynomial.C (algebraMap R1 L b) * d := by
    rw [hbd, ← algebraMap_smul L b d, Polynomial.smul_eq_C_mul]
  have hd₀0 : d₀ ≠ 0 := by
    intro h
    rw [h, Polynomial.map_zero] at hbd'
    rcases mul_eq_zero.mp hbd'.symm with hC | h0
    · exact hb0 (Polynomial.C_eq_zero.mp hC)
    · exact hd0 h0
  -- the constants appearing below are units of `F₂(X)[Y]`
  have hCcont : ∀ w : PP, w ≠ 0 → IsUnit (Polynomial.C (algebraMap R1 L w.content)) := by
    intro w hw
    refine Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr ?_)
    intro h
    exact hw (Polynomial.content_eq_zero_iff.mp (IsFractionRing.injective R1 L (by simpa using h)))
  have hCb : IsUnit (Polynomial.C (algebraMap R1 L b)) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hb0)
  have hmapPrim : ∀ w : PP, w.map (algebraMap R1 L) =
      Polynomial.C (algebraMap R1 L w.content) * w.primPart.map (algebraMap R1 L) := by
    intro w
    conv_lhs => rw [w.eq_C_content_mul_primPart]
    rw [Polynomial.map_mul, Polynomial.map_C]
  -- `d` is associated to the image of the primitive part of `d₀`
  have hassoc : Associated d (d₀.primPart.map (algebraMap R1 L)) := by
    have h1 : Associated d (Polynomial.C (algebraMap R1 L b) * d) :=
      (associated_unit_mul_left _ _ hCb).symm
    rw [← hbd', hmapPrim d₀] at h1
    exact h1.trans (associated_unit_mul_left _ _ (hCcont d₀ hd₀0))
  -- Gauss descent of the common divisor
  have hedvd : ∀ w : PP, d ∣ w.map (algebraMap R1 L) → d₀.primPart ∣ w := by
    intro w hdw
    by_cases hw : w = 0
    · simp [hw]
    · have h3 : d₀.primPart.map (algebraMap R1 L) ∣ w.map (algebraMap R1 L) :=
        hassoc.symm.dvd.trans hdw
      rw [hmapPrim w] at h3
      have h2 : d₀.primPart.map (algebraMap R1 L) ∣ w.primPart.map (algebraMap R1 L) :=
        h3.trans (associated_unit_mul_left _ _ (hCcont w hw)).dvd
      exact ((Polynomial.isPrimitive_primPart d₀).dvd_of_fraction_map_dvd_fraction_map
        (Polynomial.isPrimitive_primPart w) h2).trans w.primPart_dvd
  -- contradiction with non-coprimality
  have hue : IsUnit d₀.primPart := hcop _ (hedvd u' hdu) (hedvd v' hdv)
  have hu2 : IsUnit (d₀.primPart.map (algebraMap R1 L)) := by
    have h := hue.map (Polynomial.mapRingHom (algebraMap R1 L))
    simpa using h
  exact hgu (hassoc.symm.isUnit hu2)

/-! ### Evaluation at the point through the reorganization -/

/-- Evaluation `(F₂[X])[Y] → K` at `(x, y)` intertwines with `evP` through
`toUni`. -/
private lemma eval₂_toUni (x y : K) (p : F) :
    Polynomial.eval₂ (Polynomial.eval₂RingHom castK x : R1 →+* K) y (toUni p) = evP x y p := by
  have h : (Polynomial.eval₂RingHom (Polynomial.eval₂RingHom castK x : R1 →+* K) y).comp toUni
      = evP x y := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [toUni, evP]
    · intro i
      fin_cases i <;> simp [toUni, evP]
  have h2 := RingHom.congr_fun h p
  simpa using h2

/-- **`x`-coordinate of the algebraic-point lemma.** -/
private lemma algebraic_fst (u v : F) (hu : u ≠ 0) (_hv : v ≠ 0)
    (hcop : ∀ d : F, d ∣ u → d ∣ v → IsUnit d)
    (x y : K) (hux : evP x y u = 0) (hvy : evP x y v = 0) :
    AlgebraicF2 x := by
  by_contra hx
  -- if `x` is not algebraic, evaluation `F₂[X] → K` at `x` is injective
  have hinj : Function.Injective (Polynomial.eval₂RingHom castK x : R1 →+* K) := by
    intro a b hab
    by_contra hne
    refine hx ⟨a - b, sub_ne_zero.mpr hne, ?_⟩
    have h0 : (Polynomial.eval₂RingHom castK x : R1 →+* K) (a - b) = 0 := by
      rw [map_sub]
      exact sub_eq_zero_of_eq hab
    simpa using h0
  -- transport `u, v` and the no-common-factor hypothesis through `toUni`
  have hu' : toUni u ≠ 0 := fun h => hu (by rw [← toMv_toUni_apply u, h, map_zero])
  have hcop' : ∀ d : PP, d ∣ toUni u → d ∣ toUni v → IsUnit d := by
    intro d hdu hdv
    have h1 : toMv d ∣ u := by
      obtain ⟨c, hc⟩ := hdu
      exact ⟨toMv c, by rw [← toMv_toUni_apply u, hc, map_mul]⟩
    have h2 : toMv d ∣ v := by
      obtain ⟨c, hc⟩ := hdv
      exact ⟨toMv c, by rw [← toMv_toUni_apply v, hc, map_mul]⟩
    have h3 := (hcop _ h1 h2).map toUni
    rwa [toUni_toMv_apply d] at h3
  -- Bezout in `F₂(X)[Y]`
  obtain ⟨a, b, hab⟩ := isCoprime_map_of_no_common_factor _ _ hu' hcop'
  -- evaluate `F₂(X)[Y] → K` at `(x, y)`, lifting `X ↦ x` along the fraction field
  set χ : Polynomial L →+* K :=
    Polynomial.eval₂RingHom (IsFractionRing.lift hinj) y
  have hcomp : (IsFractionRing.lift hinj).comp (algebraMap R1 L)
      = (Polynomial.eval₂RingHom castK x : R1 →+* K) := by
    refine RingHom.ext fun r => ?_
    rw [RingHom.comp_apply, IsFractionRing.lift_algebraMap]
  have hkey : ∀ p : F, χ ((toUni p).map (algebraMap R1 L)) = evP x y p := by
    intro p
    have h1 : χ ((toUni p).map (algebraMap R1 L))
        = Polynomial.eval₂ ((IsFractionRing.lift hinj).comp (algebraMap R1 L)) y (toUni p) :=
      Polynomial.eval₂_map (algebraMap R1 L) (IsFractionRing.lift hinj) y
    rw [h1, hcomp]
    exact eval₂_toUni x y p
  have h0 : χ (a * (toUni u).map (algebraMap R1 L) + b * (toUni v).map (algebraMap R1 L))
      = χ 1 := by rw [hab]
  rw [map_add, map_mul, map_mul, hkey u, hkey v, hux, hvy, mul_zero, mul_zero, add_zero,
    map_one] at h0
  exact zero_ne_one h0

/-! ### The variable swap -/

private lemma rename_swap_swap (p : F) :
    rename (Equiv.swap (0 : Fin 2) 1) (rename (Equiv.swap (0 : Fin 2) 1) p) = p := by
  rw [rename_rename]
  have h : (⇑(Equiv.swap (0 : Fin 2) 1) ∘ ⇑(Equiv.swap (0 : Fin 2) 1)) = id :=
    funext fun z => Equiv.swap_apply_self _ _ z
  rw [h, rename_id]
  rfl

private lemma evP_rename_swap (x y : K) (p : F) :
    evP y x (rename (Equiv.swap (0 : Fin 2) 1) p) = evP x y p := by
  simp only [evP]
  rw [eval₂Hom_rename]
  have h : (![y, x] ∘ ⇑(Equiv.swap (0 : Fin 2) 1)) = ![x, y] := by
    funext i
    fin_cases i <;>
      simp [Equiv.swap_apply_left, Equiv.swap_apply_right]
  rw [h]

/-- **Algebraic-point lemma.** -/
theorem algebraic_point (u v : F) (hu : u ≠ 0) (hv : v ≠ 0)
    (hcop : ∀ d : F, d ∣ u → d ∣ v → IsUnit d)
    (x y : K) (hux : evP x y u = 0) (hvy : evP x y v = 0) :
    AlgebraicF2 x ∧ AlgebraicF2 y := by
  refine ⟨algebraic_fst u v hu hv hcop x y hux hvy, ?_⟩
  have hus : rename (Equiv.swap (0 : Fin 2) 1) u ≠ 0 :=
    fun h => hu (by rw [← rename_swap_swap u, h, map_zero])
  have hvs : rename (Equiv.swap (0 : Fin 2) 1) v ≠ 0 :=
    fun h => hv (by rw [← rename_swap_swap v, h, map_zero])
  have hcops : ∀ d : F, d ∣ rename (Equiv.swap (0 : Fin 2) 1) u →
      d ∣ rename (Equiv.swap (0 : Fin 2) 1) v → IsUnit d := by
    intro d hdu hdv
    have h1 : rename (Equiv.swap (0 : Fin 2) 1) d ∣ u := by
      obtain ⟨c, hc⟩ := hdu
      exact ⟨rename (Equiv.swap (0 : Fin 2) 1) c, by rw [← rename_swap_swap u, hc, map_mul]⟩
    have h2 : rename (Equiv.swap (0 : Fin 2) 1) d ∣ v := by
      obtain ⟨c, hc⟩ := hdv
      exact ⟨rename (Equiv.swap (0 : Fin 2) 1) c, by rw [← rename_swap_swap v, hc, map_mul]⟩
    have h3 := (hcop _ h1 h2).map (rename (Equiv.swap (0 : Fin 2) 1))
    rwa [rename_swap_swap d] at h3
  exact algebraic_fst _ _ hus hvs hcops y x
    (by rw [evP_rename_swap]; exact hux) (by rw [evP_rename_swap]; exact hvy)

end PolyClone.FrobeniusDescent
