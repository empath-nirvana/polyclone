/-
  FrobeniusDescentP/AlgebraicPoint.lean
  =====================================

  **Algebraic-point lemma** (parametric version): a common zero in `K²` of two
  relatively prime polynomials of `Fq[X,Y]` has both coordinates algebraic
  over `Fq`, for `Fq` a perfect field of characteristic 2.
  (This replaces "`Crit(h)` is a finite set of `F̄q`-points" — no dimension
  theory needed.)

  Port of `FrobeniusDescent/AlgebraicPoint.lean` from `ZMod 2` to `Fq`:
  * the explicit reorganization `Fq[X,Y] ≅ (Fq[X])[Y]` and the Gauss descent
    over `FractionRing (Fq[X])` are field-generic and carry over verbatim;
  * `AlgebraicF2` is replaced by Mathlib's `IsAlgebraic Fq`: a nonzero kernel
    element of `Polynomial.eval₂ (castK Fq) x` is literally an algebraicity
    witness via `Polynomial.aeval_def` (`castK Fq` is by definition
    `algebraMap Fq (K Fq)`);
  * the `Subsingleton.elim` step of `toUni_toMv` (special to `ZMod 2`) is
    replaced by `RingHom.ext` + `simp`.

  PROOF (elementary, fully spec'd):
  For the `x`-coordinate: view `u, v` in `(Fq[X])[Y]` (explicit ring homs
  `toUni : F Fq →+* (Fq[X])[Y]` and `toMv` back, mutually inverse by
  extensionality on generators).
  * `u, v` are coprime in `Fq(X)[Y]`: otherwise the (Euclidean) gcd is a
    nonunit common divisor over `Fq(X)`, which Gauss-descends (clearing
    denominators with `IsLocalization.integerNormalization`, then passing to
    the primitive part, `Polynomial.IsPrimitive.dvd_of_fraction_map_dvd_fraction_map`)
    to a nonunit common divisor of `u` and `v` in `(Fq[X])[Y]` — contradicting
    `hcop`.
  * If `x` were NOT algebraic over `Fq`, evaluation `Fq[X] → K` at `x` would
    be injective, hence would lift to the fraction field `Fq(X) → K`
    (`IsFractionRing.lift`).  Evaluating the Bezout identity
    `a·u + b·v = 1` of `Fq(X)[Y]` through `Fq(X)[Y] →+* K` (`X ↦ x, Y ↦ y`)
    kills the left side (`evP Fq x y u = 0 = evP Fq x y v`), giving `0 = 1`
    in `K`.
  For the `y`-coordinate, swap the variables
  (`MvPolynomial.rename (Equiv.swap 0 1)`, point `(y, x)`).
-/
import PolyClone.Perfect.Defs
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.RingTheory.Localization.FractionRing

namespace PolyClone.Perfect

open MvPolynomial

/- The `CharP`/`PerfectRing` instances are part of the file-wide signature but
most of the (field-generic) private lemmas do not use them. -/
set_option linter.unusedSectionVars false

/-! ### The explicit reorganization `Fq[X,Y] ≅ (Fq[X])[Y]` -/

/-- `Fq[X]`, the coefficient ring of the univariate reorganization. -/
private abbrev R1 (Fq : Type) [Field Fq] : Type := Polynomial Fq

/-- `(Fq[X])[Y]`. -/
private abbrev PP (Fq : Type) [Field Fq] : Type := Polynomial (R1 Fq)

/-- `Fq(X)`, the fraction field of the coefficients. -/
private abbrev L (Fq : Type) [Field Fq] : Type := FractionRing (R1 Fq)

variable {Fq : Type} [Field Fq] [CharP Fq 2] [PerfectRing Fq 2]

/-- `Fq[X,Y] → (Fq[X])[Y]` : `X 0 ↦ C X`, `X 1 ↦ Y` (the outer variable). -/
private noncomputable def toUni : F Fq →+* PP Fq :=
  eval₂Hom ((Polynomial.C : R1 Fq →+* PP Fq).comp (Polynomial.C : Fq →+* R1 Fq))
    ![Polynomial.C Polynomial.X, Polynomial.X]

/-- `(Fq[X])[Y] → Fq[X,Y]` : inner `X ↦ X 0`, outer `Y ↦ X 1`. -/
private noncomputable def toMv : PP Fq →+* F Fq :=
  Polynomial.eval₂RingHom
    (Polynomial.eval₂RingHom (MvPolynomial.C : Fq →+* F Fq) (X 0)) (X 1)

private lemma toMv_toUni : (toMv : PP Fq →+* F Fq).comp toUni = RingHom.id (F Fq) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [toUni, toMv]
  · intro i
    fin_cases i <;> simp [toUni, toMv]

private lemma toUni_toMv : (toUni : F Fq →+* PP Fq).comp toMv = RingHom.id (PP Fq) := by
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext'
    · refine RingHom.ext fun a => ?_
      simp [toUni, toMv]
    · simp [toUni, toMv]
  · simp [toUni, toMv]

private lemma toMv_toUni_apply (p : F Fq) : toMv (toUni p) = p :=
  RingHom.congr_fun toMv_toUni p

private lemma toUni_toMv_apply (q : PP Fq) : toUni (toMv q) = q :=
  RingHom.congr_fun toUni_toMv q

/-! ### Gauss descent: coprimality over `Fq(X)` -/

/-- If `u', v' ∈ (Fq[X])[Y]` (with `u' ≠ 0`) share no nonunit common factor,
they are coprime in `Fq(X)[Y]` (a Bezout ring): a nonunit common divisor over
the fraction field descends, via `integerNormalization` and the primitive
part, to a nonunit common divisor over `Fq[X]`. -/
private lemma isCoprime_map_of_no_common_factor (u' v' : PP Fq) (hu' : u' ≠ 0)
    (hcop : ∀ d : PP Fq, d ∣ u' → d ∣ v' → IsUnit d) :
    IsCoprime (u'.map (algebraMap (R1 Fq) (L Fq))) (v'.map (algebraMap (R1 Fq) (L Fq))) := by
  classical
  rw [← EuclideanDomain.gcd_isUnit_iff]
  by_contra hgu
  set d : Polynomial (L Fq) :=
    EuclideanDomain.gcd (u'.map (algebraMap (R1 Fq) (L Fq)))
      (v'.map (algebraMap (R1 Fq) (L Fq))) with hd
  have hdu : d ∣ u'.map (algebraMap (R1 Fq) (L Fq)) := EuclideanDomain.gcd_dvd_left _ _
  have hdv : d ∣ v'.map (algebraMap (R1 Fq) (L Fq)) := EuclideanDomain.gcd_dvd_right _ _
  have hd0 : d ≠ 0 := by
    intro h
    exact (Polynomial.map_ne_zero_iff (IsFractionRing.injective (R1 Fq) (L Fq))).mpr hu'
      (zero_dvd_iff.mp (h ▸ hdu))
  -- clear denominators
  obtain ⟨b, hb, hbd⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors (R1 Fq)) d
  set d₀ : PP Fq := IsLocalization.integerNormalization (nonZeroDivisors (R1 Fq)) d with hd₀
  have hb0 : algebraMap (R1 Fq) (L Fq) b ≠ 0 := by
    intro h
    exact nonZeroDivisors.ne_zero hb (IsFractionRing.injective (R1 Fq) (L Fq) (by simpa using h))
  have hbd' : d₀.map (algebraMap (R1 Fq) (L Fq)) = Polynomial.C (algebraMap (R1 Fq) (L Fq) b) * d := by
    rw [hbd, ← algebraMap_smul (L Fq) b d, Polynomial.smul_eq_C_mul]
  have hd₀0 : d₀ ≠ 0 := by
    intro h
    rw [h, Polynomial.map_zero] at hbd'
    rcases mul_eq_zero.mp hbd'.symm with hC | h0
    · exact hb0 (Polynomial.C_eq_zero.mp hC)
    · exact hd0 h0
  -- the constants appearing below are units of `Fq(X)[Y]`
  have hCcont : ∀ w : PP Fq, w ≠ 0 →
      IsUnit (Polynomial.C (algebraMap (R1 Fq) (L Fq) w.content)) := by
    intro w hw
    refine Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr ?_)
    intro h
    exact hw (Polynomial.content_eq_zero_iff.mp
      (IsFractionRing.injective (R1 Fq) (L Fq) (by simpa using h)))
  have hCb : IsUnit (Polynomial.C (algebraMap (R1 Fq) (L Fq) b)) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hb0)
  have hmapPrim : ∀ w : PP Fq, w.map (algebraMap (R1 Fq) (L Fq)) =
      Polynomial.C (algebraMap (R1 Fq) (L Fq) w.content)
        * w.primPart.map (algebraMap (R1 Fq) (L Fq)) := by
    intro w
    conv_lhs => rw [w.eq_C_content_mul_primPart]
    rw [Polynomial.map_mul, Polynomial.map_C]
  -- `d` is associated to the image of the primitive part of `d₀`
  have hassoc : Associated d (d₀.primPart.map (algebraMap (R1 Fq) (L Fq))) := by
    have h1 : Associated d (Polynomial.C (algebraMap (R1 Fq) (L Fq) b) * d) :=
      (associated_unit_mul_left _ _ hCb).symm
    rw [← hbd', hmapPrim d₀] at h1
    exact h1.trans (associated_unit_mul_left _ _ (hCcont d₀ hd₀0))
  -- Gauss descent of the common divisor
  have hedvd : ∀ w : PP Fq, d ∣ w.map (algebraMap (R1 Fq) (L Fq)) → d₀.primPart ∣ w := by
    intro w hdw
    by_cases hw : w = 0
    · simp [hw]
    · have h3 : d₀.primPart.map (algebraMap (R1 Fq) (L Fq)) ∣ w.map (algebraMap (R1 Fq) (L Fq)) :=
        hassoc.symm.dvd.trans hdw
      rw [hmapPrim w] at h3
      have h2 : d₀.primPart.map (algebraMap (R1 Fq) (L Fq))
          ∣ w.primPart.map (algebraMap (R1 Fq) (L Fq)) :=
        h3.trans (associated_unit_mul_left _ _ (hCcont w hw)).dvd
      exact ((Polynomial.isPrimitive_primPart d₀).dvd_of_fraction_map_dvd_fraction_map
        (Polynomial.isPrimitive_primPart w) h2).trans w.primPart_dvd
  -- contradiction with non-coprimality
  have hue : IsUnit d₀.primPart := hcop _ (hedvd u' hdu) (hedvd v' hdv)
  have hu2 : IsUnit (d₀.primPart.map (algebraMap (R1 Fq) (L Fq))) := by
    have h := hue.map (Polynomial.mapRingHom (algebraMap (R1 Fq) (L Fq)))
    simpa using h
  exact hgu (hassoc.symm.isUnit hu2)

/-! ### Evaluation at the point through the reorganization -/

/-- Evaluation `(Fq[X])[Y] → K` at `(x, y)` intertwines with `evP` through
`toUni`. -/
private lemma eval₂_toUni (x y : K Fq) (p : F Fq) :
    Polynomial.eval₂ (Polynomial.eval₂RingHom (castK Fq) x : R1 Fq →+* K Fq) y (toUni p)
      = evP Fq x y p := by
  have h : (Polynomial.eval₂RingHom
        (Polynomial.eval₂RingHom (castK Fq) x : R1 Fq →+* K Fq) y).comp toUni
      = evP Fq x y := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [toUni, evP]
    · intro i
      fin_cases i <;> simp [toUni, evP]
  have h2 := RingHom.congr_fun h p
  simpa using h2

/-- **`x`-coordinate of the algebraic-point lemma.** -/
private lemma algebraic_fst (u v : F Fq) (hu : u ≠ 0) (_hv : v ≠ 0)
    (hcop : ∀ d : F Fq, d ∣ u → d ∣ v → IsUnit d)
    (x y : K Fq) (hux : evP Fq x y u = 0) (hvy : evP Fq x y v = 0) :
    IsAlgebraic Fq x := by
  by_contra hx
  -- if `x` is not algebraic, evaluation `Fq[X] → K` at `x` is injective:
  -- a nonzero kernel element would be an algebraicity witness (`aeval_def`,
  -- since `castK Fq` is by definition `algebraMap Fq (K Fq)`)
  have hinj : Function.Injective (Polynomial.eval₂RingHom (castK Fq) x : R1 Fq →+* K Fq) := by
    intro a b hab
    by_contra hne
    refine hx ⟨a - b, sub_ne_zero.mpr hne, ?_⟩
    have h0 : (Polynomial.eval₂RingHom (castK Fq) x : R1 Fq →+* K Fq) (a - b) = 0 := by
      rw [map_sub]
      exact sub_eq_zero_of_eq hab
    simpa [Polynomial.aeval_def, castK] using h0
  -- transport `u, v` and the no-common-factor hypothesis through `toUni`
  have hu' : toUni u ≠ 0 := fun h => hu (by rw [← toMv_toUni_apply u, h, map_zero])
  have hcop' : ∀ d : PP Fq, d ∣ toUni u → d ∣ toUni v → IsUnit d := by
    intro d hdu hdv
    have h1 : toMv d ∣ u := by
      obtain ⟨c, hc⟩ := hdu
      exact ⟨toMv c, by rw [← toMv_toUni_apply u, hc, map_mul]⟩
    have h2 : toMv d ∣ v := by
      obtain ⟨c, hc⟩ := hdv
      exact ⟨toMv c, by rw [← toMv_toUni_apply v, hc, map_mul]⟩
    have h3 := (hcop _ h1 h2).map toUni
    rwa [toUni_toMv_apply d] at h3
  -- Bezout in `Fq(X)[Y]`
  obtain ⟨a, b, hab⟩ := isCoprime_map_of_no_common_factor _ _ hu' hcop'
  -- evaluate `Fq(X)[Y] → K` at `(x, y)`, lifting `X ↦ x` along the fraction field
  set χ : Polynomial (L Fq) →+* K Fq :=
    Polynomial.eval₂RingHom (IsFractionRing.lift hinj) y
  have hcomp : (IsFractionRing.lift hinj).comp (algebraMap (R1 Fq) (L Fq))
      = (Polynomial.eval₂RingHom (castK Fq) x : R1 Fq →+* K Fq) := by
    refine RingHom.ext fun r => ?_
    rw [RingHom.comp_apply, IsFractionRing.lift_algebraMap]
  have hkey : ∀ p : F Fq, χ ((toUni p).map (algebraMap (R1 Fq) (L Fq))) = evP Fq x y p := by
    intro p
    have h1 : χ ((toUni p).map (algebraMap (R1 Fq) (L Fq)))
        = Polynomial.eval₂ ((IsFractionRing.lift hinj).comp (algebraMap (R1 Fq) (L Fq))) y
            (toUni p) :=
      Polynomial.eval₂_map (algebraMap (R1 Fq) (L Fq)) (IsFractionRing.lift hinj) y
    rw [h1, hcomp]
    exact eval₂_toUni x y p
  have h0 : χ (a * (toUni u).map (algebraMap (R1 Fq) (L Fq))
        + b * (toUni v).map (algebraMap (R1 Fq) (L Fq)))
      = χ 1 := by rw [hab]
  rw [map_add, map_mul, map_mul, hkey u, hkey v, hux, hvy, mul_zero, mul_zero, add_zero,
    map_one] at h0
  exact zero_ne_one h0

/-! ### The variable swap -/

private lemma rename_swap_swap (p : F Fq) :
    rename (Equiv.swap (0 : Fin 2) 1) (rename (Equiv.swap (0 : Fin 2) 1) p) = p := by
  rw [rename_rename]
  have h : (⇑(Equiv.swap (0 : Fin 2) 1) ∘ ⇑(Equiv.swap (0 : Fin 2) 1)) = id :=
    funext fun z => Equiv.swap_apply_self _ _ z
  rw [h, rename_id]
  rfl

private lemma evP_rename_swap (x y : K Fq) (p : F Fq) :
    evP Fq y x (rename (Equiv.swap (0 : Fin 2) 1) p) = evP Fq x y p := by
  simp only [evP]
  rw [eval₂Hom_rename]
  have h : (![y, x] ∘ ⇑(Equiv.swap (0 : Fin 2) 1)) = ![x, y] := by
    funext i
    fin_cases i <;>
      simp [Equiv.swap_apply_left, Equiv.swap_apply_right]
  rw [h]

/-- **Algebraic-point lemma.** -/
theorem algebraic_point (u v : F Fq) (hu : u ≠ 0) (hv : v ≠ 0)
    (hcop : ∀ d : F Fq, d ∣ u → d ∣ v → IsUnit d)
    (x y : K Fq) (hux : evP Fq x y u = 0) (hvy : evP Fq x y v = 0) :
    IsAlgebraic Fq x ∧ IsAlgebraic Fq y := by
  refine ⟨algebraic_fst u v hu hv hcop x y hux hvy, ?_⟩
  have hus : rename (Equiv.swap (0 : Fin 2) 1) u ≠ 0 :=
    fun h => hu (by rw [← rename_swap_swap u, h, map_zero])
  have hvs : rename (Equiv.swap (0 : Fin 2) 1) v ≠ 0 :=
    fun h => hv (by rw [← rename_swap_swap v, h, map_zero])
  have hcops : ∀ d : F Fq, d ∣ rename (Equiv.swap (0 : Fin 2) 1) u →
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

end PolyClone.Perfect
