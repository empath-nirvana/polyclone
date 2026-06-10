/-
  PolyClone.ZeroSumFreeSemiring
  ================================================

  Generic clone-theoretic impossibilities over zero-sum-free commutative
  semirings. Abstracts the `ℕ`-specific proof in `Naturals.lean` to the
  structural class of semirings where the proof actually works.

  The key structural fact that makes the original proof go through on `ℕ`
  is the absence of additive cancellation: `a + b = 0 → a = 0 ∧ b = 0`.
  This is precisely what `CanonicallyOrderedAdd` provides in Mathlib.
  Over `ℤ`, where this fails, the proof breaks (see `Integers.lean`).

  The class of semirings covered by this file includes:
    * `ℕ` — the original case.
    * `ℕ∞ = WithTop ℕ` — extended naturals with `∞ + ∞ = ∞`.
    * `ℚ≥0`, `ℝ≥0` — non-negative rationals/reals.
    * Polynomial semirings `ℕ[X]`, finite-support function semirings.
    * Various combinatorial semirings (multisets, etc.).

  The class explicitly excludes `ℤ`, `ℚ`, `ℝ`, `ℂ`, and any ring with
  additive inverses, because sign cancellation breaks the Newton-polytope
  / no-cancellation monotonicity that the master-theorem proof depends on.

  ## What ports cleanly and what doesn't

  Easy halves (proved here, generic in the broader `CanonicallyOrderedAdd`
  class — applies to ℕ, ℕ∞, ℚ≥0, ℝ≥0, ℕ[X], multiset/finsupp semirings,
  etc.):
    * `affine_does_not_reach_mul` — affine operators don't reach `·`.
    * `cross_preserving_does_not_reach_add` — Cross-preserving operators
      don't reach `+`. `mul_does_not_reach_add` follows.

  Hard-half infrastructure that ports cleanly:
    * `sum_eq_zero_iff_zsf` — Piece 1: sum-vanishing utility.
    * `aeval_pair_eq_monomial_sum` — Piece 2: monomial sum form.
    * `aeval_zero_at_pos_imp_zero_everywhere` — Piece 3: vanishing along
      a line forces vanishing.

  Hard half that does NOT port (ℕ-discrete-specific):
    * Pieces 4–9 (monotonicity bound `M ≤ R(M)`, R-dichotomy growth,
      polynomial growth bound `n^totalDegree ≤ q(n, n)`, main theorem)
      all use `0 < a ⟹ 1 ≤ a` — a discreteness property of ℕ that fails
      on ℚ≥0 / ℝ≥0 and on most non-ℕ zero-sum-free semirings. See the
      "ℕ-discreteness gap" section below for details.

  ## Bottom line

  The clone-theoretic *easy halves* generalize broadly. The master
  theorem itself is, with our current proof strategy, **ℕ-specific** —
  proven concretely in `Naturals.lean` and stated abstractly here as a
  conjecture. Genuinely generalizing it would need either a discretely-
  ordered semiring class (essentially only ℕ in standard Mathlib) or
  an asymptotic-growth reformulation outside the scope of this file.
-/

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Ring.WithTop
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

namespace PolyClone.ZeroSumFreeSemiring

/-! ## Term language (generic over a carrier `S`) -/

/-- A term over a single binary operator with `S`-valued constants. -/
inductive Term (S : Type*) (α : Type*) where
  /-- A variable. -/
  | var : α → Term S α
  /-- A constant of type `S`. -/
  | const : S → Term S α
  /-- An application of the binary operator. -/
  | op : Term S α → Term S α → Term S α

/-- Evaluate a term, given a binary operator and a variable assignment. -/
def Term.eval {S : Type*} {α : Type*} (op : S → S → S) (v : α → S) :
    Term S α → S
  | .var a => v a
  | .const n => n
  | .op s t => op (s.eval op v) (t.eval op v)

/-- Size of a term (number of operator applications). Used for strong
    induction in the master theorem. -/
def Term.size {S : Type*} {α : Type*} : Term S α → ℕ
  | .var _ => 0
  | .const _ => 0
  | .op s u => s.size + u.size + 1

/-- A binary function `f : S → S → S` is *reached* by `op` if there is
    a term over `op` (with `S`-constants) whose evaluation matches `f`
    everywhere. -/
def Reaches {S : Type*} (op : S → S → S) (f : S → S → S) : Prop :=
  ∃ t : Term S (Fin 2), ∀ a b : S, t.eval op ![a, b] = f a b

/-! ## Target functions: addition and multiplication -/

/-- Addition as a function `S → S → S`. -/
def addFn (S : Type*) [Add S] : S → S → S := (· + ·)

/-- Multiplication as a function `S → S → S`. -/
def mulFn (S : Type*) [Mul S] : S → S → S := (· * ·)

/-! ## Easy half 1: affine operators don't reach `·`

A binary operator `⊙ : S × S → S` is *S-affine* if it has the form
`⊙(x, y) = α·x + β·y + γ` for some `α, β, γ ∈ S`. Over a zero-sum-free
semiring, ℕ-style "extract corners and use zero-sum-free" works.
-/

/-- A binary operator on `S` is *S-affine* if it equals `α·x + β·y + γ`
    for some `α, β, γ ∈ S`. -/
def IsAffine {S : Type*} [CommSemiring S] (op : S → S → S) : Prop :=
  ∃ α β γ : S, ∀ x y : S, op x y = α * x + β * y + γ

/-- Every term over an `S`-affine operator evaluates to an `S`-affine
    function of its inputs. -/
theorem affine_term_is_affine {S : Type*} [CommSemiring S]
    {op : S → S → S} (h_aff : IsAffine op) (t : Term S (Fin 2)) :
    ∃ A B C : S, ∀ a b : S, t.eval op ![a, b] = A * a + B * b + C := by
  obtain ⟨α, β, γ, hop⟩ := h_aff
  induction t with
  | var i =>
    fin_cases i
    · exact ⟨1, 0, 0, by intro a b; simp [Term.eval]⟩
    · exact ⟨0, 1, 0, by intro a b; simp [Term.eval]⟩
  | const n =>
    exact ⟨0, 0, n, by intro a b; simp [Term.eval]⟩
  | op s t ihs iht =>
    obtain ⟨As, Bs, Cs, hs⟩ := ihs
    obtain ⟨At, Bt, Ct, ht⟩ := iht
    refine ⟨α * As + β * At, α * Bs + β * Bt, α * Cs + β * Ct + γ, ?_⟩
    intro a b
    simp only [Term.eval, hs a b, ht a b, hop]
    ring

/-- **Theorem.** No `S`-affine operator reaches multiplication, where `S`
    is a zero-sum-free commutative semiring with `0 ≠ 1`.

    The zero-sum-free hypothesis is essential: over `ℤ`, the `α + γ = 0`
    conclusion does not force `α = 0`. -/
theorem affine_does_not_reach_mul
    {S : Type*} [CommSemiring S] [PartialOrder S] [CanonicallyOrderedAdd S]
    [Nontrivial S]
    {op : S → S → S} (h : IsAffine op) :
    ¬ Reaches op (mulFn S) := by
  rintro ⟨t, h_t⟩
  obtain ⟨A, B, C, h_form⟩ := affine_term_is_affine h t
  have h00 := h_t 0 0
  have h10 := h_t 1 0
  have h01 := h_t 0 1
  have h11 := h_t 1 1
  rw [h_form] at h00 h10 h01 h11
  simp only [mulFn, mul_zero, zero_mul, mul_one, one_mul,
             zero_add, add_zero] at h00 h10 h01 h11
  -- h00 : C = 0, h10 : A + C = 0, h01 : B + C = 0, h11 : A + B + C = 1
  obtain ⟨hA, _⟩ := add_eq_zero.mp h10
  obtain ⟨hB, _⟩ := add_eq_zero.mp h01
  rw [hA, hB, h00, zero_add, add_zero] at h11
  -- h11 : (0 : S) = 1
  exact absurd h11 zero_ne_one

/-! ## Easy half 2: Cross-preserving operators don't reach `+`

The Cross relation `f(0,0) · f(1,1) = f(1,0) · f(0,1)` is preserved by
`·` and by constants/projections. It fails for `+` (because `0 ≠ 1`
combined with the structure of the carrier). The proof of the closure
result is purely algebraic — it transports unchanged from `ℕ` to any
commutative semiring.
-/

/-- The *cross relation* on a binary function `f : S → S → S`. -/
def Cross {S : Type*} [CommSemiring S] (f : S → S → S) : Prop :=
  f 0 0 * f 1 1 = f 1 0 * f 0 1

theorem Cross.const {S : Type*} [CommSemiring S] (c : S) :
    Cross (fun _ _ : S => c) := by
  unfold Cross; ring

theorem Cross.proj_left {S : Type*} [CommSemiring S] :
    Cross (fun a _ : S => a) := by
  unfold Cross; ring

theorem Cross.proj_right {S : Type*} [CommSemiring S] :
    Cross (fun _ b : S => b) := by
  unfold Cross; ring

/-- If `op` preserves the Cross relation, every term over `op` satisfies it. -/
theorem term_cross_invariant {S : Type*} [CommSemiring S]
    {op : S → S → S}
    (hop : ∀ f g : S → S → S, Cross f → Cross g →
           Cross (fun a b => op (f a b) (g a b)))
    (t : Term S (Fin 2)) :
    Cross (fun a b => t.eval op ![a, b]) := by
  induction t with
  | var i =>
    fin_cases i
    · change Cross (fun a _ : S => a); exact Cross.proj_left
    · change Cross (fun _ b : S => b); exact Cross.proj_right
  | const n =>
    change Cross (fun _ _ : S => n); exact Cross.const n
  | op s t ihs iht =>
    change Cross (fun a b => op (Term.eval op ![a, b] s) (Term.eval op ![a, b] t))
    exact hop _ _ ihs iht

/-- Addition violates Cross on any commutative semiring with `0 ≠ 1`:
    `addFn(0,0) · addFn(1,1) = 0 · (1+1) = 0`, while
    `addFn(1,0) · addFn(0,1) = 1 · 1 = 1`, and `0 ≠ 1`. -/
theorem addFn_not_cross
    {S : Type*} [CommSemiring S] [Nontrivial S] :
    ¬ Cross (addFn S) := by
  intro h
  unfold Cross addFn at h
  -- h : (0 + 0 : S) * (1 + 1) = (1 + 0) * (0 + 1)
  simp at h

/-- **Theorem.** Any operator preserving Cross does not reach addition. -/
theorem cross_preserving_does_not_reach_add
    {S : Type*} [CommSemiring S] [Nontrivial S]
    {op : S → S → S}
    (hop : ∀ f g : S → S → S, Cross f → Cross g →
           Cross (fun a b => op (f a b) (g a b))) :
    ¬ Reaches op (addFn S) := by
  rintro ⟨t, h_t⟩
  apply addFn_not_cross (S := S)
  have h_eq : (fun a b => Term.eval op ![a, b] t) = addFn S := by
    funext a b; exact h_t a b
  have h_cross := term_cross_invariant hop t
  rwa [h_eq] at h_cross

/-- Multiplication preserves Cross — purely algebraic identity. -/
theorem mulFn_preserves_cross {S : Type*} [CommSemiring S] :
    ∀ f g : S → S → S, Cross f → Cross g →
    Cross (fun a b => mulFn S (f a b) (g a b)) := by
  intro f g hf hg
  show f 0 0 * g 0 0 * (f 1 1 * g 1 1) = f 1 0 * g 1 0 * (f 0 1 * g 0 1)
  unfold Cross at hf hg
  calc f 0 0 * g 0 0 * (f 1 1 * g 1 1)
      = (f 0 0 * f 1 1) * (g 0 0 * g 1 1) := by ring
    _ = (f 1 0 * f 0 1) * (g 1 0 * g 0 1) := by rw [hf, hg]
    _ = f 1 0 * g 1 0 * (f 0 1 * g 0 1) := by ring

/-- **Corollary.** Multiplication does not reach addition. -/
theorem mul_does_not_reach_add
    {S : Type*} [CommSemiring S] [Nontrivial S] :
    ¬ Reaches (mulFn S) (addFn S) :=
  cross_preserving_does_not_reach_add mulFn_preserves_cross

/-! ## Polynomial framework (generic)

A binary operator on `S` is *polynomial* if it equals the evaluation of
some `MvPolynomial (Fin 2) S`. This is the natural class for which the
master theorem could be stated. We define it here but defer the master
theorem to `Naturals.lean` (where it is proved for `ℕ`).
-/

/-- A binary operator on `S` is *polynomial* if it equals the evaluation
    of some `MvPolynomial (Fin 2) S`. -/
def IsPolynomial {S : Type*} [CommSemiring S] (op : S → S → S) : Prop :=
  ∃ p : MvPolynomial (Fin 2) S, ∀ a b : S, op a b = MvPolynomial.aeval ![a, b] p

/-! ## Hard-half infrastructure

This file ports the hard-half *infrastructure* of `Naturals.lean`
(Pieces 1–6) to the abstract setting. The master theorem itself, using
this infrastructure plus an Archimedean unboundedness hypothesis, is
proved in `NonNegRationals.lean`.

The typeclass `[CommSemiring S] [LinearOrder S] [IsOrderedRing S]
[CanonicallyOrderedAdd S] [Nontrivial S] [NoZeroDivisors S]
[IsLeftCancelAdd S]` captures the infrastructure here. Members include
`ℕ`, `ℚ≥0`, `ℝ≥0`. The class **excludes** `WithTop ℕ` (= ℕ∞) because
left-cancellation `a + ∞ = b + ∞ ⟹ a = b` fails there.

Pieces are kept in the same order as in
`Naturals.lean` to make cross-reference easy. -/

section HardHalf

variable {S : Type*} [CommSemiring S] [LinearOrder S]
  [IsOrderedRing S] [CanonicallyOrderedAdd S]
  [Nontrivial S] [NoZeroDivisors S] [IsLeftCancelAdd S]

/-! ### Piece 1: Sum-vanishing utility -/

/-- For non-negative terms, `∑ f i = 0` iff every `f i = 0`. Holds in any
    `CanonicallyOrderedAdd` carrier: if some term is non-zero (hence
    positive in the canonical order), the sum is at least that term,
    hence non-zero. -/
lemma sum_eq_zero_iff_zsf {ι : Type*} (s : Finset ι)
    (f : ι → S) : ∑ i ∈ s, f i = 0 ↔ ∀ i ∈ s, f i = 0 := by
  classical
  refine ⟨fun h i hi => ?_, fun h => Finset.sum_eq_zero h⟩
  by_contra h_ne
  have h_pos : 0 < f i := lt_of_le_of_ne zero_le (Ne.symm h_ne)
  have h_sum_pos : 0 < ∑ j ∈ s, f j :=
    lt_of_lt_of_le h_pos (Finset.single_le_sum (f := f) (fun _ _ => zero_le) hi)
  exact (lt_irrefl 0) (h ▸ h_sum_pos)

/-! ### Piece 2: Monomial-sum form of `aeval ![c, x] p` -/

/-- `aeval ![c, x] p` written as an explicit sum over `p`'s monomial support.
    Purely algebraic — `CommSemiring` is enough. -/
lemma aeval_pair_eq_monomial_sum (p : MvPolynomial (Fin 2) S) (c x : S) :
    MvPolynomial.aeval (![c, x] : Fin 2 → S) p =
    ∑ d ∈ p.support, p.coeff d * c^(d 0) * x^(d 1) := by
  classical
  rw [show MvPolynomial.aeval (![c, x] : Fin 2 → S) p =
        ∑ d ∈ p.support, p.coeff d * ∏ i ∈ d.support, (![c, x] : Fin 2 → S) i ^ d i from by
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
    simp [RingHom.id_apply]]
  apply Finset.sum_congr rfl
  intro d _
  have h_prod : ∏ i ∈ d.support, (![c, x] : Fin 2 → S) i ^ d i = c^(d 0) * x^(d 1) := by
    calc ∏ i ∈ d.support, (![c, x] : Fin 2 → S) i ^ d i
        = ∏ i ∈ (Finset.univ : Finset (Fin 2)), (![c, x] : Fin 2 → S) i ^ d i := by
          apply Finset.prod_subset d.support.subset_univ
          intro i _ hi
          have : d i = 0 := by
            by_contra hne; exact hi (Finsupp.mem_support_iff.mpr hne)
          rw [this, pow_zero]
      _ = (![c, x] : Fin 2 → S) 0 ^ d 0 * (![c, x] : Fin 2 → S) 1 ^ d 1 :=
            Fin.prod_univ_two _
      _ = c ^ d 0 * x ^ d 1 := by simp
  rw [h_prod, ← mul_assoc]

/-! ### Piece 3: Vanishing along a line forces vanishing everywhere -/

/-- If `aeval ![c, γ] p = 0` for `γ ≥ 1`, then `aeval ![c, M] p = 0` for every `M`.
    Uses zero-sum-free (via `sum_eq_zero_iff_zsf`) plus that `γ^k ≠ 0` for `γ ≥ 1`. -/
lemma aeval_zero_at_pos_imp_zero_everywhere
    (p : MvPolynomial (Fin 2) S) (c γ : S) (hγ : 1 ≤ γ)
    (h : MvPolynomial.aeval (![c, γ] : Fin 2 → S) p = 0) :
    ∀ M : S, MvPolynomial.aeval (![c, M] : Fin 2 → S) p = 0 := by
  classical
  intro M
  rw [aeval_pair_eq_monomial_sum p c γ] at h
  rw [aeval_pair_eq_monomial_sum p c M]
  have h_each : ∀ d ∈ p.support, p.coeff d * c^(d 0) * γ^(d 1) = 0 :=
    (sum_eq_zero_iff_zsf _ _).mp h
  apply Finset.sum_eq_zero
  intro d hd
  have h_this := h_each d hd
  have hγ_pos : 0 < γ := lt_of_lt_of_le zero_lt_one hγ
  have hγ_ne : γ ≠ 0 := ne_of_gt hγ_pos
  have hγ_pow_ne : γ^(d 1) ≠ 0 := pow_ne_zero _ hγ_ne
  have h_cancel : p.coeff d * c^(d 0) = 0 := by
    rcases mul_eq_zero.mp h_this with h1 | h2
    · exact h1
    · exact absurd h2 hγ_pow_ne
  rw [h_cancel, zero_mul]

/-! ### Piece 4: Monotonicity of `aeval ![c, ·] p` -/

/-- `aeval ![c, M] p` is monotone in `M` over a zero-sum-free linearly-
    ordered semiring with non-negative coefficients. -/
lemma aeval_pair_mono (p : MvPolynomial (Fin 2) S) (c : S) {M N : S}
    (h : M ≤ N) :
    MvPolynomial.aeval (![c, M] : Fin 2 → S) p ≤
    MvPolynomial.aeval (![c, N] : Fin 2 → S) p := by
  classical
  rw [aeval_pair_eq_monomial_sum p c M, aeval_pair_eq_monomial_sum p c N]
  apply Finset.sum_le_sum
  intro d _
  apply mul_le_mul_of_nonneg_left _ zero_le
  exact pow_le_pow_left₀ zero_le h _

/-! ### Piece 5: Partition by X₁-dependence -/

/-- Split `aeval ![c, x] p` into the constant-in-`x` part (`d 1 = 0`)
    and the rest (`d 1 ≥ 1`). -/
lemma aeval_pair_split_by_X1 (p : MvPolynomial (Fin 2) S) (c x : S) :
    MvPolynomial.aeval (![c, x] : Fin 2 → S) p =
    (∑ d ∈ p.support.filter (fun d => d 1 = 0), p.coeff d * c^(d 0)) +
    (∑ d ∈ p.support.filter (fun d => 1 ≤ d 1), p.coeff d * c^(d 0) * x^(d 1)) := by
  classical
  rw [aeval_pair_eq_monomial_sum p c x]
  have h_part : p.support =
      p.support.filter (fun d => d 1 = 0) ∪ p.support.filter (fun d => 1 ≤ d 1) := by
    ext d
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hd
      rcases Nat.eq_zero_or_pos (d 1) with h0 | h1
      · left; exact ⟨hd, h0⟩
      · right; exact ⟨hd, h1⟩
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  have h_disj : Disjoint (p.support.filter (fun d => d 1 = 0))
                         (p.support.filter (fun d => 1 ≤ d 1)) := by
    rw [Finset.disjoint_filter]
    intros d _ h0 h1; omega
  conv_lhs => rw [h_part]
  rw [Finset.sum_union h_disj]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mem_filter] at hd
  rw [hd.2, pow_zero, mul_one]

/-! ### Piece 6 (part 1): R-constant lemma -/

/-- If `R(0) = R(1)` where `R(M) := aeval ![c, M] p`, then `R(M) = R(0)`
    for all `M`. Uses left-cancellation to extract `S1coeffs = 0`. -/
lemma aeval_pair_const_of_eq_at_one
    {p : MvPolynomial (Fin 2) S} {c : S}
    (h_eq : MvPolynomial.aeval (![c, 0] : Fin 2 → S) p =
            MvPolynomial.aeval (![c, 1] : Fin 2 → S) p) :
    ∀ M, MvPolynomial.aeval (![c, M] : Fin 2 → S) p =
         MvPolynomial.aeval (![c, 0] : Fin 2 → S) p := by
  classical
  intro M
  rw [aeval_pair_split_by_X1 p c M, aeval_pair_split_by_X1 p c 0,
      aeval_pair_split_by_X1 p c 1] at *
  have h_S1_at_0 :
      (∑ d ∈ p.support.filter (fun d => 1 ≤ d 1), p.coeff d * c^(d 0) * (0 : S)^(d 1)) = 0 := by
    apply Finset.sum_eq_zero
    intro d hd
    rw [Finset.mem_filter] at hd
    rw [zero_pow (Nat.pos_iff_ne_zero.mp hd.2), mul_zero]
  have h_S1_at_1 :
      (∑ d ∈ p.support.filter (fun d => 1 ≤ d 1), p.coeff d * c^(d 0) * (1 : S)^(d 1)) =
      (∑ d ∈ p.support.filter (fun d => 1 ≤ d 1), p.coeff d * c^(d 0)) := by
    apply Finset.sum_congr rfl
    intro d _; rw [one_pow, mul_one]
  rw [h_S1_at_0, add_zero] at h_eq
  rw [h_S1_at_1] at h_eq
  have h_S1_zero : (∑ d ∈ p.support.filter (fun d => 1 ≤ d 1), p.coeff d * c^(d 0)) = 0 := by
    have h_eq' : (∑ d ∈ p.support.filter (fun d => d 1 = 0), p.coeff d * c^(d 0)) + 0 =
                 (∑ d ∈ p.support.filter (fun d => d 1 = 0), p.coeff d * c^(d 0)) +
                 (∑ d ∈ p.support.filter (fun d => 1 ≤ d 1), p.coeff d * c^(d 0)) := by
      rw [add_zero]; exact h_eq
    exact (add_left_cancel h_eq').symm
  have h_each : ∀ d ∈ p.support.filter (fun d => 1 ≤ d 1), p.coeff d * c^(d 0) = 0 :=
    (sum_eq_zero_iff_zsf _ _).mp h_S1_zero
  have h_S1_at_M :
      (∑ d ∈ p.support.filter (fun d => 1 ≤ d 1), p.coeff d * c^(d 0) * M^(d 1)) = 0 := by
    apply Finset.sum_eq_zero
    intro d hd
    rw [show p.coeff d * c^(d 0) * M^(d 1) = (p.coeff d * c^(d 0)) * M^(d 1) from rfl,
        h_each d hd, zero_mul]
  rw [h_S1_at_M, add_zero, h_S1_at_0, add_zero]

end HardHalf

/-! ## Beyond ℕ-discreteness

The ℕ proof in `Naturals.lean` uses `0 < n ↔ 1 ≤ n` (ℕ-discreteness) in
several places — notably in the growth-bound step `M ≤ R(M)` for the
R-dichotomy, and in the coefficient bound `q.coeff d ≥ 1` from
`q.coeff d ≠ 0`. On non-discrete carriers like `ℚ≥0` or `ℝ≥0`, these
specific bounds fail (`S1coeffs` and `q.coeff d` can be `1/2`).

The master theorem is nonetheless recovered on the broader Archimedean
class by **replacing the discrete bounds with asymptotic ones** (e.g.,
`c · n^d ≤ q(n, n)` for some `c > 0`) and using a **strengthened
inductive hypothesis** (no term realizes any positive scalar multiple
of `X + Y`, not just `X + Y` itself). Both ingredients are developed
in `NonNegRationals.lean`. -/

/-! ## Master theorem (proved in `NonNegRationals.lean`)

The master theorem — no polynomial binary operator generates both `+` and
`·` in its clone — is **fully proved** for any carrier in the typeclass

  `[CommSemiring S] [LinearOrder S] [IsOrderedRing S]
   [CanonicallyOrderedAdd S] [Nontrivial S] [NoZeroDivisors S]
   [IsLeftCancelAdd S] [Archimedean S] [MulPosReflectLE S]
   [IsLeftCancelMulZero S] [PosMulStrictMono S]`

in `PolyClone.NonNegRationals.polynomial_does_not_reach_both`.
Members of this class include `ℕ`, `NNRat`, `NNReal`. The proof uses
asymptotic polynomial growth + a strengthened inductive hypothesis on
positive scalar multiples of `X + Y`.

Whether the theorem holds **without `Archimedean`** is open (the present
proof strategy genuinely needs Archimedean unboundedness). -/

/-! ## Instance verification

Confirm that the generic typeclass requirements are satisfied by the
intended carrier types. -/

/-- The natural numbers satisfy all hypotheses. -/
example : CommSemiring ℕ := inferInstance
example : PartialOrder ℕ := inferInstance
example : CanonicallyOrderedAdd ℕ := inferInstance
example : Nontrivial ℕ := inferInstance
example : NoZeroDivisors ℕ := inferInstance

/-- Extended naturals `ℕ∞ = WithTop ℕ` satisfy all hypotheses. -/
example : CommSemiring (WithTop ℕ) := inferInstance
example : PartialOrder (WithTop ℕ) := inferInstance
example : CanonicallyOrderedAdd (WithTop ℕ) := inferInstance
example : Nontrivial (WithTop ℕ) := inferInstance

/-! ## Easy-half corollaries instantiated on ℕ

These are the easy halves of the master theorem, derived from the
generic versions above by instantiating `S := ℕ`. They match the
results in `Naturals.lean` but are proved from the abstract framework. -/

/-- Affine doesn't reach mul on ℕ (corollary of generic version). -/
example {op : ℕ → ℕ → ℕ} (h : IsAffine op) :
    ¬ Reaches op (mulFn ℕ) :=
  affine_does_not_reach_mul h

/-- Mul doesn't reach add on ℕ (corollary of generic version). -/
example : ¬ Reaches (mulFn ℕ) (addFn ℕ) :=
  mul_does_not_reach_add

/-- Affine doesn't reach mul on `ℕ∞` — same theorem instantiated on a
    non-ℕ zero-sum-free semiring. Demonstrates real generality. -/
example {op : WithTop ℕ → WithTop ℕ → WithTop ℕ} (h : IsAffine op) :
    ¬ Reaches op (mulFn (WithTop ℕ)) :=
  affine_does_not_reach_mul h

/-- Mul doesn't reach add on `ℕ∞`. -/
example : ¬ Reaches (mulFn (WithTop ℕ)) (addFn (WithTop ℕ)) :=
  mul_does_not_reach_add

end PolyClone.ZeroSumFreeSemiring
