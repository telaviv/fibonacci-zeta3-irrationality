# What you have to trust

## Axioms

`lake env lean Axioms.lean` prints, for the main theorem and each of its ingredients,

```
'FibZeta.irrational_zetaF3' depends on axioms: [propext, Classical.choice, Quot.sound]
```

(full output: `scripts/axioms.txt`). These are Lean's three standard axioms, the ones Mathlib uses. The project has no
`sorry`, no `axiom` declaration, no `native_decide` and no `implemented_by`, so nothing relies on the compiler.

## The statement

The kernel checks the proof; it cannot check that the statement means what we claim. For the theorem
`FibZeta.irrational_zetaF3 : Irrational FibZeta.zetaF3` read one definition (`FibZeta/Defs.lean`):

```lean
noncomputable def zetaF3 : ℝ := ∑' n : ℕ, 1 / ((Nat.fib (n + 1) : ℕ) : ℝ) ^ 3
```

`Nat.fib 1 = Nat.fib 2 = 1`, so this is `∑_{n ≥ 1} 1/F_n³`. A divergent `tsum` has the junk value `0`, which is
rational, so the theorem cannot be true for a degenerate reason; `FibZeta.hasSum_zetaF3` also proves that the series
converges to `zetaF3`.

Nothing else needs to be read to trust the theorem. To check that the formal proof follows the paper, read
`FibZeta/Defs.lean` and `FibZeta/Statements.lean`; an independent comparison of these with the paper is
`FIDELITY_REFEREE.md` (verdict PASS WITH FIXES, all fixes are documentation and were applied).

## Builds

* Full build after deleting all project build products (`.lake/build/lib/lean/FibZeta*`, `.lake/build/ir/FibZeta*`):
  `scripts/clean_build.log` (2026-11-13).
* Mathlib itself is not re-checked; it is taken from the official cache for v4.35.0.
