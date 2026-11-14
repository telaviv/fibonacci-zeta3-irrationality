# FibZeta/Conj — Proposition 4 (conjugate smallness)

Main theorem: `FibZeta.Conj.conjBound : ConjBound` (`ConjBound.lean`), axioms `propext, Classical.choice, Quot.sound`.
Self-contained (Mathlib `Lagrange` API only; nothing copied from the uplift repo).

| File | Content | PROOF.md §4 step |
|---|---|---|
| `DivDiff.lean` | `E r K m = Σ_a r_a^m / F'(r_a)` (= h_{m−K+1}(r)); `E_base` (= [m = K−1] for m < K, Lagrange), `E_succ` (recursion in K), `E_bound` (\|E\| ≤ (1−ρ)^{−K} if \|r_a\| ≤ ρ < 1), `coeff_divByMonic` (coefficients of `X^k /ₘ F` are `E r K (k−1−j)`) | "Σ_a r_a^m/F′(r_a) = h_{m−K+1}(r)", "\|h_m(r)\| ≤ C₀ t^{2m}" (we use the cruder (1−t²)^{−K}), partial fractions |
| `Conjugate.lean` | τ = −φ: `node_neg_gold` (nodes r_a = (−t²)^a), `F_neg_gold`, `res_neg_gold`, `psi_neg_gold` (ψ_N(−φ) = −ψ_N(t)), `summable_psi_tR`, `S_add_Xi` (S_a(−φ)+Ξ = Σ_{N>a} ψ_N(t)), `two_gold_psi` (the Γ(r_a) summands), `inv_one_sub_cube`, `abs_nu_neg_gold` (\|ν_j(−φ)\| ≤ j(j+1)φ²) | the σ-data list and Γ(r_a) |
| `Entry.lean` | `T K k = mConst − Ξ·mLin` at −φ; `T_eq` (polynomial part + pole part), `abs_Lpoly_le`, `partB_eq` (pole part = Σ_M Σ_j c_{M,j} E rr K (k+j+1), after swapping the finite a-sum with both series), `abs_partB_le` | "T_k(−Ξ) = Σ h·σν + Σ γ_n h", bound \|T_k\| ≤ B_K |
| `ConjBound.lean` | `abs_T_le_pow` (\|T_k\| ≤ Dc^K for k < 2K), `eval_Delta`, `abs_nrm_neg_gold` (\|nrm\| = t^{K(K+1)}), `conjBound` (permutation bound `Matrix.det_le`, K! ≤ 2^{K²}) | Hadamard step, \|w\|^{A_K K} = φ^{−K²(K+1)} |

Numerical check of every identity used: `scripts/conj/check_conj.py` (mpmath, 200 digits).
