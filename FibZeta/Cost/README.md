# FibZeta/Cost — Proposition 3.6 (`CostBound`)

`FibZeta.Cost.costBound : FibZeta.CostBound`, with C = 7 000 000. Axioms: `propext, Classical.choice, Quot.sound`.

This route is weaker than PROOF §3.3 but elementary. It gives the cubic constant 4393/3675 = 1.19537… ≤ 121/100. The
PROOF's 1.1308 needs Σφ(n) ~ 3n²/π², which is not used here.

| File | Contents | PROOF step |
|---|---|---|
| `Cyclo.lean` | `log_norm_cyc_le`: log\|Φ_d(t)\| + log\|Φ_d(−φ)\| ≤ φ(d) log φ + 12 (Möbius inversion of Σ_{a\|n} log\|Φ_a(x)\| = log\|xⁿ − 1\|) | Lemma 3.5 |
| `Cluster.lean` | `cW_bound`: 4c(m)+16 ≤ 16m+(m−5)₊²; `cW'_le`: c′ ≤ c+4; cluster sizes 1 ≤ m_r ≤ K/e+1 with Σ m_r = K; `Wc_bound`: 4·Wc + 16e ≤ 16K + e(K/e−4)₊² + 16 | Prop 3.6, W part |
| `RootCount.lean` | `sum_totient_eW_le`: Σ_{e(d)=e} φ(d) ≤ 2φ(e); `sum_totient_alpha_le`: Σ_{α_j(ζ_d)=1} φ(d) ≤ 2j+1; `card_eW_fiber_le`: ≤ 8 orders d per e; regrouping of Σ_d by e(d); n_α(K,d) ≤ Σ_j [α_j](K−1−j) | §3.1 root types |
| `Sieve.lean` | φ(e) ≤ e·w(e), w = Π_{p∈{2,3,5,7}, p\|e}(1−1/p), expanded over the 16 divisors of 210; closed-form sums over multiples of q; `T1_le`: Σ w(e)e(K−e) ≤ μK³/6 + O(K²), `T2_le`: Σ w(e)(K−4e)₊² ≤ μK³/12 + O(K²), μ = 768/1225 | Prop 3.6 (totient averages) |
| `CostBound.lean` | `log_norm_CK_eq` (log\|C_K(t)C_K(−φ)\| = Σ n_d(…)); `sum_totient_nExp_le`: Σ n_d φ(d) ≤ 1.21K³ + 6610008K²; `sum_nExp_le`: Σ n_d ≤ 70K²(1+log K); `costBound` | Prop 3.6 |

Constant: W part ≤ 8·T1 + T2/2 + O(K²) → μ(4/3 + 1/24)K³ = 0.86204K³; α part ≤ Σ_j (K−1−j)(2j+1) ≤ K³/3.
All inequalities were tested in exact arithmetic first: `scripts/cost/check_cost.py`, `scripts/cost/sym_check.py`.
