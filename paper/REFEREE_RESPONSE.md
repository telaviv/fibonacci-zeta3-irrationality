# Response to the referee report (`REFEREE.md`, verdict: minor revision), 2026-11-13

All points are addressed in `main.tex`. Point numbers refer to `REFEREE.md`.

| # | Action |
|---|---|
| 1 [error] | Prop 4.2 "Weights": the split is now by entry type, (A) entries with a singular node and (B) r < e with max(j,k) = m−1, as in the Lean proof (`weights_singular`, `weights_regular`). For r = e the weight κ_{m−1} = max(0,(4−m)/2) is noted. |
| 2 | Prop 4.6: summand f_K, the periodic-weight lemma with error 2P(M+V) and its proof, and the bound Σ_d b_{K,d} = O(K² log K) are written out. |
| 3 | Prop 5.1: L^σ_X defined; the renormalisation 1/(1−w^{−a}s) = −r_a/(s−r_a) and the evaluation at X = −Ξ are written; γ_n given explicitly. |
| 4 | §7: C_K(t) ≠ 0 stated with its reason. |
| 5 | Prop 4.2 rank correction: A^pol and B defined, regularity of both, why A is integral, rank of B′ = rank of B, rank ≤ max(0, K−1−k_min) with the dimension count. |
| 6 | Local facts (a)–(d) now carry one-line proofs; Lemma 4.3 says why Res_a, λ_a, S_a are regular. |
| 7 | Prop 6.1: T_n, E_n defined before use; the termwise application of L justified by uniform convergence with two derivatives. |
| 8 | Remark 4.7 labelled a sketch, not used; the finite-K paragraph of §7 is now a remark, labelled not used, says which three terms are summed, and says the scripts are available from the author. |
| 9 | The ℓ-adic sentence of Remark 5.2 is deleted; the heuristic is kept. |
| 10 | KRZ (ζ_q(3..11)) and Jouhet–Mosaki (ζ_q(3..9)) attributed correctly; Fischler–Zudilin added. |
| 11 | "remains open in the refereed literature"; [UPL] described as an unrefereed, AI-assisted draft, version 0.3.0-two-proofs, 2026-10-12, commit d12d56f; sentence that the paper does not depend logically on [UPL]. |
| 12 | New item [QZ3] (F. Solomon Admasu, QZeta3 v0.1.0, 2026-10-11, Apache-2.0), cited in Provenance. |
| 13 | [Fau] labelled unrefereed; Zudilin 2017 (Constr. Approx.) and Krattenthaler 2021 (arXiv:2103.03969) added. |
| 14 | "the survey [Wal10] and the introduction of [MS24]". |
| 15 | ESS08 pages 429–446 restored (checked against the bibliography of RIMS Kôkyûroku 1665, no. 16). André-Jeannin's proof described as Padé approximation of a Lambert series. Prévost (1998) and Matala-aho–Prévost (2006) not added: their exact titles could not be verified locally. DOIs not added. |
| 16 | Abstract hedged ("To our knowledge"). |
| 17 | (a) §8 points to the numbering translation in the header of `Statements.lean`; (b) "upper half of Lemma 4.5" in the text; (c) `EntryIdentity` is used only by `DecayBound`. |
| 18 | "an internal comparison … with an earlier draft of this section". |
| 19 | A "Use of AI tools" paragraph is added (for the owner to adapt to the journal's policy). |
| 20 | Euler's function is now φ_E(d) (macro `\eu`), announced in §2. |
| 21 | Sieve density β₇ = 768/1225; μ is the Möbius function only. |
| 22 | Renamed: weights κ_j, cluster points y_r, sieve weight η(e), uniformiser ϖ, test function g, Remark 4.7 function ℓ, order q (Prop 6.1), conjugate product F^σ, Cauchy transform 𝒞, triple-root basis V_j, conjugate constant M_K, residue coefficients Res_a, regular part A^pol, ζ_F(3) = u/v, roots β (§3), H_{n,Q}, c_0, ι_K, c_1, Y_k, 𝓔₁. Kept: B/B′ (only in Prop 4.2), T_{n,Q}, E_n. |
| 23 | Notation paragraph split into definitions and consequences; w(ζ), α_k(ζ) defined. |
| 24 | Prop 4.2 writes m = m_r and Δ_{K,τ}; the Gauss valuation (minimum over coefficients) is defined in the local setting. |
| 25 | Σ|γ_n| ≤ φ² derived (Σ n(n+1)t^{2n+1} = 2, 1/(1−t³) = φ²/2); M_K uses φ². |
| 26 | §1 table: column "size (per K³ log φ)", c_* = 1.1954…. |
| 27 | Short title for the running head; long displays split; tables in `\small`. 0 overfull boxes. |
| 28 | `\texorpdfstring` in the two section titles. |
| 29 | Pr\'evost typed consistently; c_* = 4393/3675 in Prop 4.6; the d = 2 exception explained; T_n defined. |
