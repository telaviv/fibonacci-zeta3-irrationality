# FibZeta/Analytic — `EntryIdentity` and `DecayBound`

Entry point: `FibZeta/Analytic/All.lean` (imports everything below).

| Theorem | File | PROOF.md step |
|---|---|---|
| `FibZeta.Analytic.entryIdentity : EntryIdentity` | `Entry.lean` | §1 Lemma 1 + partial fractions ("By Lemma 1, Δ_K(Ξ) = det[L(s^{i+j}/D_K)]") |
| `FibZeta.Analytic.decayBound : DecayBound` (with `C = 4096`) | `Decay.lean` | §2 Proposition 2 |

Files, in import order:

* `Functional.lean` — `θ(θ+1)` calculus (`thetaOp_add`, `_const_mul`, `_sum`, `_congr`), the summed functional as
  `HasSum (Lterm h)`, Lemma 1(i) `hasL_pow` (`L(s^k) = ν_k`), Lemma 1(ii) `hasL_simplePole`
  (`L(1/(1 − w^a s)) = 2ρ^{−a}(Ξ − S_a)`), summability of `ψ_N`.
* `Entry.lean` — partial fractions for `s^k/F_K` (`partial_fraction`, via `Lagrange.eval_interpolate_not_at_node`),
  `D_K = (−1)^K w^{A_K} F_K` (`DK_eq`), `hasL_fraction_DK`, `entryIdentity`. The hypotheses `1 ≤ K`, `k ≤ 2K` of
  `EntryIdentity` are not needed (the identity holds for all `K, k`).
* `Gram.lean` — linearity of `P ↦ L(P/D_K)` (`numeratorFunctional`), `gramR`, `Delta_eval_eq_det : Δ_K(Ξ) = det gramR`.
* `Basis.lean` — triple-root basis `B_j(s) = ∏_{u≤j}(s − q^{⌈u/3⌉})`, unitriangular change of basis
  (`det_tripleRootGram`), `abs_det_le_of_scaled_entries` (Mathlib's `Matrix.det_le`, the `K!` form of Hadamard).
* `Weight.lean` — Euler operator `θ`, `thetaOp_eq_theta : θ(θ+1) = θ² + θ`, bounds `|W| ≤ 2`, `|θW| ≤ (8/3)|x|`,
  `|θ²W| ≤ (16/3)|x|` for `W = 1/D_K` on `|x| ≤ |w| = t² ≤ 1/2` (signed `x`).
* `Jets.lean` — jet bounds of `B_j` at surviving nodes (`|x − ϱ| ≤ 2|ϱ|`, factor `2^j`), vanishing at earlier nodes.
* `Decay.lean` — pointwise entry bound `(32/3)(i+j+1)² 2^{i+j} |w|^{a_i+a_j} |w|^{m−R}`, geometric tail sum
  (`|L(B_iB_j/D_K)| ≤ (64/3)(i+j+1)² 2^{i+j} |w|^{a_i+a_j}`), `gram_det_bound`, `prefactor_le`
  (`K!·((64/3)(2K)²4^K)^K ≤ 4096^{K²}`), `decayBound`.

Adapted from the uplift Lean (`QZeta3/Purity`, `Functional`, `DividedDifferences`, `GramIdentity`, `AnalyticWeight`,
`AnalyticDeterminant`, `AnalyticEntry`, `GeometricTail`, `GramBasis`; Apache-2.0, F. Solomon Admasu); each file's
header says what changed. Numerical check of the entry bound: `scripts/analytic/entry_bound_check.py`
(max ratio entry/bound ≈ 0.016 for K ≤ 5).

Axioms (both theorems): `propext, Classical.choice, Quot.sound`.
