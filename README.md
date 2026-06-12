# PolyClone

For a commutative ring `R` and `p ∈ R[x,y]`, let `Clo p` be the smallest
set of **formal** bivariate polynomials containing the variables `x, y`
and every constant `c ∈ R`, closed under `(f, g) ↦ p(f, g)`; say `p`
*generates* `R[x,y]` if `Clo p = R[x,y]`. (Declaration names in the
formal development use `complete` for this generation property.)

**Precision, for universal algebraists.** In clone-theoretic terms:
the binary terms in the language of commutative rings with constant
symbols form the binary part of an abstract clone, canonically
identified with `R[x,y]` under substitution, and the question is
whether the single term `p` generates it. This abstract object is
represented faithfully by operations on `R` when `R` is an infinite
integral domain, and is finer than its image otherwise; it should not
be confused with the clone of polynomial *operations* of `R` in the
universal-algebra sense, **nor with the full clone of all finitary
operations on the set `R`**. The distinction between formal
polynomials and the functions they induce matters over finite fields:
`1 + xy` induces NAND on `F₂`, and every Boolean function is a
composition of NAND; nevertheless `x + y ∉ Clo(1+xy)` by the F₂
theorem, since `D(1+xy) = 1 ≠ 0`. The F₂ theorem neither follows from
nor contradicts classical functional completeness theory (Post; Webb;
Rosenberg). Conversely, for odd prime powers `q`, generation of
`F_q[x,y]` by `x² − y` plus Lagrange interpolation implies that
`⟨F_q; x²−y⟩` *with constants* is functionally (polynomially)
complete in the classical sense. Primality of `⟨F_q; x²−y⟩`
*without* constants, and Mal'cev-condition analyses of `⟨R, p⟩`, are
NOT addressed here. See `BLUEPRINT.md` for the full statement-by-
statement correspondence and `paper/` for the draft manuscript with
definitions, proof outlines, and (in-progress) literature placement.

**Central theorem.** There is a single polynomial generating all of
`R[x,y]` under composition (with variables and constants) if and only
if `2` is a unit of `R`. When `2` is invertible, `x² − y` is a
generator; over any field of characteristic `2` (and hence over `ℤ` and
over any ring with a characteristic-`2` residue field), every `p`
misses `x+y` or `x·y`. The negative half is proved by an infinite
descent on a would-be counterexample's "Frobenius depth" — how many
times it factors through the squaring map.

## Results

| Statement | Lean |
|---|---|
| **the dichotomy**: single generator over `R` ⟺ `2 ∈ R×` | `complete_iff_two_isUnit` (`Perfect/Dichotomy.lean`) |
| no generator `p` over `ℤ` (degree-free disjunction) | `int_master`, `masterConjecture_int` (`FrobeniusDescent/IntReduction.lean`) |
| `∀ q ∈ F₂[x,y]`: `x+y ∉ Clo q` or `xy ∉ Clo q` | `F2_master_conjecture` (`FrobeniusDescent/Main.lean`) |
| same over every perfect char-2 field (Frobenius twist) | `perfect_char2_master` (`Perfect/Main.lean`) |
| same over every char-2 field (perfection embedding) | `char2_field_master` (`Perfect/Dichotomy.lean`) |
| `x² − y` generates when `2` is invertible (`ℚ`, `F₃`, …) | `qOp_complete` (`FrobeniusDescent/CharTwoDichotomy.lean`) |
| `Dq = 0 ⟹ xy ∉ Clo q` (derivative cocycle) | `XY_not_in_Clo` (`DXDYCocycle.lean`) |
| diagonal-rigidity reduction | `master` (`Tameness.lean`) |
| the Frobenius descent | `no_nonconstant_witness` (`FrobeniusDescent/Descent.lean`) |
| curve constraint ⟹ level algebraic (kill lemma) | `c_algebraic_of_curve_constraint` (`FrobeniusDescent/KillLemma.lean`) |
| common zero of coprime pair is algebraic | `algebraic_point` (`FrobeniusDescent/AlgebraicPoint.lean`) |
| `h_x, h_y` coprime after the peel (keystone) | `hX_hY_relPrime` (`FrobeniusDescent/Perfectness.lean`) |

**Semiring companion** (`Naturals.lean`, `ZeroSumFreeSemiring.lean`):
over the semiring `ℕ` — where subtraction is unavailable and the ring
dichotomy does not apply — the master theorem holds at the level of
*functions*: no polynomial binary operation on `ℕ` reaches both `+` and
`×` by composition (`polynomial_does_not_reach_both`). The easy halves
generalize to every zero-sum-free (canonically ordered) commutative
semiring (`ℕ∞`, `ℚ≥0`, `ℝ≥0`, `ℕ[X]`, …); the hard half is ℕ-specific
(discreteness). Since `ℕ` is an infinite domain, the function-level
statement implies the formal one.

`FrobeniusDescent/StatementAudit.lean` derives independently known
facts from the main theorems (e.g. `x+y ∉ Clo(xy)`, and the historical
test case `x+y ∉ Clo(y³+xy)`) as a guard against statement drift.

## Verification

The development contains **no `sorry`, no custom axioms, no
`native_decide`**. Every theorem above reports

    #print axioms ... = [propext, Classical.choice, Quot.sound]

(Lean's standard foundational axioms).

### Independent judge ([leanprover/comparator](https://github.com/leanprover/comparator))

The four headline theorems are verified end-to-end by an adversarial
judge in CI (workflow [`Comparator judge`](.github/workflows/comparator.yml)):
the statements live in a standalone, ~90-line challenge module
([`comparator/Challenge.lean`](comparator/Challenge.lean) — it does NOT
import this library), and the judge checks that the library proves those
exact statements from only the whitelisted axioms, replaying every proof
through **two independent kernels**. From the CI log:

```
Exporting #[..., PolyClone.FrobeniusDescent.F2_master_conjecture,
PolyClone.FrobeniusDescent.int_master, PolyClone.FrobeniusDescent.qOp_complete,
PolyClone.Perfect.complete_iff_two_isUnit, propext, Classical.choice,
Quot.sound, ...] from PolyClone
Running nanoda kernel on solution
Nanoda kernel accepts the solution
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
```

To trust the headline results you need only read `Challenge.lean` (do
the statements say what the paper claims?) and the judge's verdict —
not this repository's proofs or build.

## Building

Requires the Lean toolchain pinned in `lean-toolchain`.

    lake exe cache get   # fetch Mathlib binaries
    lake build
