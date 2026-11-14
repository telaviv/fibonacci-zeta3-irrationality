# The sum of the reciprocal cubes of the Fibonacci numbers is irrational

A Lean 4 + Mathlib proof that

$$\zeta_F(3)=\sum_{n\ge1}\frac1{F_n^3}\notin\mathbb Q .$$

```lean
theorem FibZeta.irrational_zetaF3 : Irrational FibZeta.zetaF3
-- zetaF3 = ∑' n : ℕ, 1 / ((Nat.fib (n + 1) : ℕ) : ℝ) ^ 3
```

No `sorry`, no `native_decide`, no added axioms: `lake env lean Axioms.lean` prints
`[propext, Classical.choice, Quot.sound]` for the theorem and each of its ingredients (`scripts/axioms.txt`).

The written proof is the paper in `paper/` (`paper/main.tex`; build with `sh build.sh` from `paper/`). Its §8 maps
every step to a Lean declaration; `python paper/check_lean_names.py` checks that every Lean name it cites exists.

## Build

```sh
lake exe cache get      # Mathlib cache (Lean 4.35.0, Mathlib v4.35.0)
LEAN_NUM_THREADS=4 lake build
lake env lean Axioms.lean
```

## Layout

| Path | Content |
|---|---|
| `FibZeta/Defs.lean` | All definitions: the construction over a field with parameter τ, the real constants, the cyclotomic exponents |
| `FibZeta/Statements.lean` | The ingredients as propositions (`DecayBound`, `ConjBound`, `Integrality`, `CostBound`, `Nonvanishing`, `EntryIdentity`) |
| `FibZeta/Main.lean` | The assembly `irrational_zetaF3_of` (norm argument via τ² + τ − 1) |
| `FibZeta/Final.lean` | `irrational_zetaF3`, `hasSum_zetaF3` |
| `FibZeta/Roots.lean` | Root types depend only on the order of the root of unity |
| `FibZeta/Analytic/` | Real functional, moments, entry identity, real decay (paper Lemma 2.2, Prop 3.1) |
| `FibZeta/Denom/` | Integrality ring, local cyclotomic bounds, descent, specialisation (paper Lemma 4.1–Prop 4.4) |
| `FibZeta/Cost/` | Size of the clearing factor (paper Lemma 4.5, Prop 4.6) |
| `FibZeta/Conj/` | Smallness at the Galois conjugate (paper Prop 5.1) |
| `FibZeta/NonVan/` | Nonvanishing by rational interpolation (paper Prop 6.1) |

Each folder has a `README.md` mapping its theorems to the proof.

## Credit and licence

Apache License 2.0 (`LICENSE`). Parts are adapted from the Lean formalisation of the irrationality of ζ_{1/p}(3) in
[uplift-universal-inc/qzeta_3-irrationality](https://github.com/uplift-universal-inc/qzeta_3-irrationality)
(directory `lean/`, Apache-2.0); adapted files say so in their header, and `NOTICE` records it.
