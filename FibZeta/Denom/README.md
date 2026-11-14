# FibZeta/Denom — Proposition 3.4 (`Integrality`)

Main theorem: `FibZeta.Denom.integrality : FibZeta.Integrality` (file `Integrality.lean`).
`#print axioms`: `propext, Classical.choice, Quot.sound`.

| File | Content | PROOF.md |
|---|---|---|
| `Localization.lean` | `LocalizationData R τ K` (inverses of `τ`, `1 − w^n` (n ≤ K), `1 − α_k` (1 ≤ k ≤ K−2)); `Delta_coeff_mem` | Lemma 3.1 |
| `Specialization.lean` | `Maps`, `maps_Delta`, `specialize_Delta_coeff`, `map_Delta` (Delta commutes with field homs) | §1 "Formal parameter" |
| `Local.lean` | local ring `regularAt ω ⊂ RatFunc 𝕜`, `uniformizer ω = X − ω`, `localEval` | §3.1 "Local setting" |
| `Descent.lean` | integer monic fractions, Gauss descent, pole descent; `integrality_of_local_bounds : LocalBounds ℂ → Integrality` (specialization at real τ ≠ 0, non-root of unity) | Prop 3.4 |
| `Gram.lean` | `momentPolynomial = L_X(f/F)`, `properPart`, Gram congruence `det_normalizedGram` | Prop 3.2 (change of basis) |
| `LocalDet.lean` | weighted determinants, rank correction `C_pow_mul_det_add_inv_mem_subring` | Prop 3.2 (scaling; α bullet) |
| `Framework.lean` | `π ν_l` regular (fact (c)), `poly_part_split` (rank ≤ K−1−k₀), `local_bound_of_basis` (common core) | Prop 3.2 / Lemma 3.3 |
| `Nodes.lean` | node collisions are simple zeros, `π³ S_a` regular, `F'(x_a)` cleared by `π^{collisions}`, `proper_term_coeff_mem` | §3.1 facts (a),(b),(d); Lemma 3.2a(ii),(iii) |
| `Monomial.lean` | `local_bound_monomial` (no clustering, e > K) | Lemma 3.3 |
| `Clusters.lean` | classes `{s_r + l e}`, `m_r`, `clusterSize = clMult`, weights `wRow = ⌈w_j⌉`, `wCol = ⌊w_j⌋`, inequalities, `sum_weights = c(m)/c′(m)` | Prop 3.2 (iv), weights |
| `ClusterBasis.lean` | CRT linear independence of `(F/F_r)(s − ω_r)^j` | Prop 3.2 (Newton basis is a basis) |
| `Newton.lean` | Newton cluster basis `N_{r,j}`, reduction, unit change-of-basis determinant | Prop 3.2 (Newton basis) |
| `NewtonLocal.lean` | `newton_term_mem` (Lemma 3.2a), `local_bound_cluster` | Prop 3.2 |
| `Integrality.lean` | choice of `k₀`, `nW = ∑ costs`, `localBounds`, `integrality` | Prop 3.4 |

Design: one local theorem (`local_bound_of_basis`) handles all root types. The α-part is the rank
correction with `k₀ = k_min(d)` (or `K − 1` if there is no α-root `≤ K − 2`), so `K − 1 − k₀ = nAlpha`.
W-roots (`e ≤ K`) use the Newton basis vanishing at the nodes `l = 1..j` of the class (so for
`r ≠ 0`, `j = m − 1` only the regular node `x_r` survives); `e > K` uses monomials.

Adapted (with header attribution) from the uplift Lean (`qzeta_3-irrationality`, Apache-2.0):
GenericMoments, GenericSpecialization, CyclotomicLocal, LocalEvaluation, IntegerFractions,
LocalPoleDescent, DenominatorDescent, GenericEvaluation, GenericGram, LocalDeterminants,
LocalGramBounds, PolynomialMomentRank, MovingClusterBasis, LocalClusterTransport, ClusterBasis.
