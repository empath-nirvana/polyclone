/-
  PolyClone.DXDYCocycle
  =======================================

  **The ∂_X∂_Y cocycle: `∂_X∂_Y q = 0 ⟹ X·Y ∉ Clo q` over a char-2 ring.**

  Let `D = pderiv 0 ∘ pderiv 1` (the mixed second partial `∂_X∂_Y`). Over a
  commutative ring of characteristic 2:

  * pure second derivatives vanish: `pderiv i (pderiv i p) = 0`
    (since `pderiv i (pderiv i (X i ^ n))` carries a factor `n (n-1) ≡ 0`);
  * the first-order chain rule holds for `bind₁`;
  * consequently `D` satisfies a **cocycle**: if `D p = 0`, `D α = 0`,
    `D β = 0` then `D (bind₁ ![α, β] p) = 0` — the source term
    `(D p) · Jacobian` and the two transport terms all vanish.

  Hence `D` is `0` on all of `Clo p` whenever `D p = 0` (induction on the
  `Clo` predicate, atoms have `D = 0`). But `D (X·Y) = 1 ≠ 0`. Therefore
  `X·Y ∉ Clo p`.

  This is a **cancellation-immune transport identity** (a ring identity on all
  inputs), uniform in degree: it proves the master conjecture's `XY` side for
  every polynomial with no monomial `X^a Y^b` having both `a, b` odd.
-/
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.CharP.Two
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Data.ZMod.Basic
import PolyClone.CloAddMul

namespace PolyClone.DXDYCocycle

open MvPolynomial
open PolyClone.CloAddMul

variable {R : Type*} [CommRing R]

/-- The mixed second partial derivative `∂_X ∂_Y` on `R[X, Y]`. -/
noncomputable def D (g : MvPolynomial (Fin 2) R) : MvPolynomial (Fin 2) R :=
  pderiv 0 (pderiv 1 g)

@[simp] lemma D_def (g : MvPolynomial (Fin 2) R) : D g = pderiv 0 (pderiv 1 g) := rfl

/-! ## Char-2: pure second derivatives vanish -/

lemma pderiv_pderiv_self [CharP R 2] (i : Fin 2) (p : MvPolynomial (Fin 2) R) :
    pderiv i (pderiv i p) = 0 := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp =>
      have hXj : pderiv i (pderiv i (X j : MvPolynomial (Fin 2) R)) = 0 := by
        rcases eq_or_ne i j with h | h
        · subst h; simp
        · simp [pderiv_X_of_ne (Ne.symm h)]
      rw [pderiv_mul, map_add, pderiv_mul, pderiv_mul, hp, hXj]
      simp only [zero_mul, mul_zero, add_zero, zero_add]
      exact CharTwo.add_self_eq_zero _

/-! ## First-order chain rule for `bind₁` -/

lemma pderiv_bind₁ (b : Fin 2) (f : Fin 2 → MvPolynomial (Fin 2) R)
    (p : MvPolynomial (Fin 2) R) :
    pderiv b (bind₁ f p)
      = bind₁ f (pderiv 0 p) * pderiv b (f 0)
        + bind₁ f (pderiv 1 p) * pderiv b (f 1) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]; ring
  | mul_X p j hp =>
      rw [map_mul, bind₁_X_right, pderiv_mul, hp]
      simp only [pderiv_mul, map_add, map_mul, bind₁_X_right]
      fin_cases j <;>
        · simp only [Fin.mk_zero, Fin.mk_one, Fin.isValue, pderiv_X_self,
                     pderiv_X_of_ne (show (1 : Fin 2) ≠ 0 by decide),
                     pderiv_X_of_ne (show (0 : Fin 2) ≠ 1 by decide),
                     map_one, map_zero, mul_one, mul_zero, zero_mul, add_zero, zero_add]
          ring

/-! ## Mixed partials commute -/

lemma pderiv_comm (i j : Fin 2) (p : MvPolynomial (Fin 2) R) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p k hp =>
      have hij : pderiv i (pderiv j (X k : MvPolynomial (Fin 2) R)) = 0 := by
        rcases eq_or_ne j k with h | h
        · subst h; simp
        · simp [pderiv_X_of_ne (Ne.symm h)]
      have hji : pderiv j (pderiv i (X k : MvPolynomial (Fin 2) R)) = 0 := by
        rcases eq_or_ne i k with h | h
        · subst h; simp
        · simp [pderiv_X_of_ne (Ne.symm h)]
      simp only [pderiv_mul, map_add, hp, hij, hji, mul_zero, zero_mul, add_zero, zero_add]
      ring

/-! ## The cocycle identity and preservation -/

/-- The `∂_X∂_Y` cocycle on `bind₁` (over a char-2 ring). The first term is the
    `(∂_X∂_Y p)`-source times the Jacobian; the other two are transport terms. -/
lemma D_bind₁ [CharP R 2] (f : Fin 2 → MvPolynomial (Fin 2) R)
    (p : MvPolynomial (Fin 2) R) :
    D (bind₁ f p)
      = bind₁ f (D p)
          * (pderiv 0 (f 0) * pderiv 1 (f 1) + pderiv 1 (f 0) * pderiv 0 (f 1))
        + bind₁ f (pderiv 0 p) * D (f 0)
        + bind₁ f (pderiv 1 p) * D (f 1) := by
  have h00 : pderiv (0 : Fin 2) (pderiv 0 p) = 0 := pderiv_pderiv_self 0 p
  have h11 : pderiv (1 : Fin 2) (pderiv 1 p) = 0 := pderiv_pderiv_self 1 p
  have h10 : pderiv (1 : Fin 2) (pderiv 0 p) = pderiv 0 (pderiv 1 p) := pderiv_comm 1 0 p
  simp only [D]
  rw [pderiv_bind₁ 1 f p, map_add, pderiv_mul, pderiv_mul,
      pderiv_bind₁ 0 f (pderiv 0 p), pderiv_bind₁ 0 f (pderiv 1 p),
      h00, h11, h10]
  simp only [map_zero, zero_mul, mul_zero, zero_add, add_zero]
  ring

/-- **Cocycle preservation.** If `D p = 0`, `D α = 0`, `D β = 0` then
    `D (bind₁ ![α, β] p) = 0`. -/
lemma D_bind₁_eq_zero [CharP R 2] {p α β : MvPolynomial (Fin 2) R}
    (hp : D p = 0) (hα : D α = 0) (hβ : D β = 0) :
    D (bind₁ ![α, β] p) = 0 := by
  rw [D_bind₁]
  have e0 : (![α, β] : Fin 2 → MvPolynomial (Fin 2) R) 0 = α := rfl
  have e1 : (![α, β] : Fin 2 → MvPolynomial (Fin 2) R) 1 = β := rfl
  rw [e0, e1, hp, hα, hβ]
  simp

/-! ## `D = 0` is preserved by `Clo`, hence `X·Y ∉ Clo p` -/

lemma D_eq_zero_of_Clo [CharP R 2] {p g : MvPolynomial (Fin 2) R}
    (hp : D p = 0) (hg : Clo p g) : D g = 0 := by
  induction hg with
  | atomX => simp [D, pderiv_X_of_ne (show (0 : Fin 2) ≠ 1 by decide)]
  | atomY => simp [D]
  | const c => simp [D]
  | sub _ _ ihα ihβ => exact D_bind₁_eq_zero hp ihα ihβ

/-- `D (X·Y) = 1`. -/
lemma D_mulOp : D (mulOp : MvPolynomial (Fin 2) R) = 1 := by
  show pderiv 0 (pderiv 1 (X 0 * X 1)) = 1
  rw [pderiv_mul, pderiv_X_of_ne (show (0 : Fin 2) ≠ 1 by decide), pderiv_X_self]
  simp [pderiv_X_self]

/-- **The D-cocycle theorem.** Over a nontrivial char-2 ring, if
    `∂_X∂_Y p = 0` then `X·Y ∉ Clo p`. Uniform in degree. -/
theorem XY_not_in_Clo [CharP R 2] [Nontrivial R] {p : MvPolynomial (Fin 2) R}
    (hp : D p = 0) : ¬ Clo p (mulOp : MvPolynomial (Fin 2) R) := by
  intro h
  have hz : D (mulOp : MvPolynomial (Fin 2) R) = 0 := D_eq_zero_of_Clo hp h
  rw [D_mulOp] at hz
  exact one_ne_zero hz

end PolyClone.DXDYCocycle
