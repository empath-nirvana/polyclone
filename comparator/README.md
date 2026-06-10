# Independent verification via leanprover/comparator

`Challenge.lean` restates PolyClone's four headline theorems with `sorry`
bodies, replicating the definitional trust base verbatim (it does NOT
import PolyClone). `config.json` names the theorems and definitions to be
compared and whitelists Lean's three standard axioms.

To judge: install [leanprover/comparator](https://github.com/leanprover/comparator)
(requires `landrun` — Linux only — and `lean4export`; `nanoda` for the
external kernel replay) and run it on `config.json` with this repository
as the solution. A pass certifies, without trusting our build, that the
solution proves exactly these statements from exactly these axioms.

Status: EXECUTED AND PASSING in CI (workflow "Comparator judge"):
both the nanoda kernel and the Lean kernel accept the solution.
Note: `Clo` is an inductive, so it is not listed in `definition_names`
(comparator's hole mechanism accepts only `def`s); it appears in every
judged theorem statement, so the dependency crawl compares it fully
structurally between Challenge and Solution — strictly stronger.
