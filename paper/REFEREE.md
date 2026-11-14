# Referee report: "The sum of the reciprocal cubes of the Fibonacci numbers is irrational"

Manuscript: `paper/main.tex` (build of 2026-11-13). Lean development: `lean_fibzeta` at commit `1040a28`.
Referee date: 2026-11-13.

## Verdict: minor revision

## Summary

The paper proves that ζ_F(3) = Σ 1/F_n³ is irrational. It adapts a moving-denominator Hankel-determinant construction
for the Lambert value Σ n²/(pⁿ−1) (the unrefereed work [UPL]) to the quadratic unit t = φ⁻¹. Determinants Δ_K(X) of a
second-Euler-derivative functional L are taken against D_K(s) = ∏(1 − wᵃs), w = −t². The proof combines four
estimates:

* real decay −(2/9)K³ log φ;
* smallness −K³ log φ of the conjugate determinant at σΞ = −Ξ, which replaces the p-adic content gain of the integer
  case;
* cyclotomic denominators of total size ≤ c_* K³ log φ, with c_* = 11μ₇/8 + 1/3 ≈ 1.1954 < 11/9;
* nonvanishing of Δ_K(Ξ) for infinitely many K, by rational interpolation.

The idea that the archimedean conjugate place does the work of the coefficient content is neat. The paper states it
clearly.

**Correctness.** I re-derived every step by hand and found no mathematical error that affects the result. One sentence
in the proof of Proposition 4.2 is false as literally written (point 1); the inequality that is actually needed holds.
I also checked the main claims independently by computer (scripts in `paper/referee_scratch/`):

* Lemma 2.2 / entry identity: the formal Hankel entries match a direct evaluation of the node-sum functional L (K = 2, 3).
* The closed form for 2Σa_j (K ≤ 12).
* The k_min table: brute force, d < 400.
* c(m) and c′(m): the closed forms, c ≤ (m+3)²/4, 0 ≤ c′ − c ≤ 3, and 0 ≤ δ(m) ≤ max(0, m−5)²/4 (m < 200).
* Constants: μ₇ = 768/1225, c_* = 4393/3675 = 1.195374, c_* − 11/9 = −0.026848, E₁ = 2.11360, C₀ = 2.0770907.
  I = 0.683122 lies in the stated interval, and the sharp constant is 1.130788 ≤ 1.130790.
* Σ_d b_{K,d}φ(d)/K³ = 1.1914 at K = 20 and 1.1580 at K = 40, matching Remark 4.7.
* **Exact Φ_d-multiplicities** in the denominator of Δ_{K,τ}(X) ∈ ℚ(τ)[X] against b_{K,d}, for K = 2..6, with my own
  sympy code: no violation, no cyclotomic factor outside 𝒟_K, and the bound is attained for most d.
* log_φ|σΔ_K(−Ξ)| = −19.5, −36.4, −78.4, −148.5 for K = 2..5, inside the Proposition 5.1 bound.

**Formal proof.** I ran `lake env lean Axioms.lean`. Every listed declaration, including `FibZeta.irrational_zetaF3`,
depends only on `[propext, Classical.choice, Quot.sound]`. `grep` finds no `sorry`, `admit`, `axiom`,
`native_decide` or `implemented_by` in `FibZeta/`. `check_lean_names.py` reports 0 problems. The statement
(`zetaF3 = ∑' n, 1/(Nat.fib (n+1))³`) is the right one, and the junk-value remark is correct. Section 8 describes the
code accurately (points 17–19 are small corrections). So the theorem is not in doubt.

**What a journal reader cannot yet check from the paper alone.** A few steps are compressed to one sentence:

* the periodic-weight summation in Proposition 4.6;
* the conjugate pole moment in Proposition 5.1;
* C_K(t) ≠ 0 in Section 7.

Each is easy, and each is covered by the Lean proof. Remarks 4.7 and 5.2 and the finite-K paragraph of Section 7 make
numerical or heuristic claims without a source or a label.

**Citations.** The bibliography needs work. The KRZ/Jouhet–Mosaki attribution is wrong. [MS24] is called a survey but
is not one. One entry is incomplete. The description of [UPL] omits that it is AI-assisted, and the wording
overstates its status. The Lean code adapted from [UPL] has a named author who is not cited.

**Exposition.** The notation needs one cleaning pass: φ is both the golden ratio and Euler's function; μ is used three
ways; w, ω, π, h, F, B, A, a, b are each used twice. There are also several overfull lines and an overfull running
head.

Two earlier internal referee reports on the underlying proof sketch (`handoff/fibzeta/REFEREE_1.md`, `REFEREE_2.md`)
reached "correct" on every step. I read them only after forming the view above, and I agree. Their fixes (⌈·⌉/⌊·⌋
scaling, "pole of order ≤ 3", the label on the "bound2" numerics) have been absorbed into the paper.

---

## Numbered points

### Correctness and completeness

1. **[error] Proof of Prop 4.2, paragraph "Weights" (main.tex ll. 266–269): the case labels are wrong.** The paragraph
   defines w_j in two cases: r < e and r = e. It then says "In the first case w_j + w_k ≥ m+2−j−k" and "In the second
   case w_j + w_k ≥ 0 ≥ m−1−j−k". Read literally, the first claim is about r < e, and it is false there. Take
   (j, k) = (0, m−1) with m = 2: then w₀ + w₁ = 2 < 3 = m+2−j−k. With m = 3: w₀ + w₂ = 5/2 < 3. The parenthetical
   argument "if w_k = 0 then k ≥ (m+2)/2" also fails for k = m−1 when m ≤ 3, because there w_{m−1} = 0 was imposed by
   hand. What the proof needs is a split by *entry type* from (iv), not by cluster type:
   (a) for every pair (j, k) whose entry has a singular node (all pairs when r = e; pairs with max(j, k) ≤ m−2 when
   r < e), w_j + w_k ≥ m+2−j−k;
   (b) for r < e and max(j, k) = m−1, w_j + w_k ≥ 0 ≥ m−1−j−k.
   Both hold, and the Lean proof (`weights_singular`, `weights_regular` in `Denom/NewtonLocal.lean`) is organised
   exactly this way. *Fix:* replace "In the first case … In the second case" by (a)/(b) above. In (a) for r = e, note
   that w_{m−1} = max(0, (4−m)/2), so the same three-line argument applies.

2. **[gap] Prop 4.6, W part: "Summing a smooth function against a periodic weight costs O(K²) over its integral against
   the mean" (ll. 331–333).** This is the only analytic input of the cost bound. Neither the summand nor the claim is
   written out. *Fix:* state the summand f_K(y) = 8y(K−y) + ½ max(0, K−4y)² + 6y, which is piecewise C¹ with
   ‖f_K‖_∞ and the total variation of f_K both O(K²). State the elementary lemma: for ω of period P and mean μ,
   |Σ_{1≤e≤K} ω(e) f(e) − μ∫₀^K f| ≤ P(‖f‖_∞ + V₀^K(f)). Also give one line for Σ_d b_{K,d} = O(K² log K), namely
   Σ_{e≤K} K²/e plus at most 4K values of d with an α part ≤ K. (The Lean proof covers this: `Cost/Sieve.lean`,
   `Cost/CostBound.lean`.)

3. **[gap] Prop 5.1, the conjugate pole moment (ll. 369–373).** The text jumps to "σL(1/(s−r_a)) = 2tᵃr_a⁻¹Σ_{N>a}ψ_N".
   Here "σL" is not defined: only σL_X was. The step also needs the renormalisation
   1/(1 − w^{−a}s) = −wᵃ/(s − r_a), so that σL_X(1/(s−r_a)) = −w^{−a}·2tᵃ(X + S_a). Only at X = −Ξ does this become
   2tᵃr_a⁻¹(Ξ − S_a). *Fix:* write this line, and write σL_{−Ξ} (or σL_X at X = −Ξ) throughout. Also state the
   expansion behind |γ_n|: γ_n = n(n+1)Σ_M t^{3M}w^{M(n−1)}. (Covered in Lean: `Conj/Entry.lean`.)

4. **[gap] Section 7: y_K ≠ 0 needs C_K(t) ≠ 0 (l. 420).** This holds because t is not a root of unity, so
   Φ_d(t) ≠ 0. Add the clause. (Lean: `aeval_CKpoly_ne_zero` in `Main.lean`.)

5. **[gap] Prop 4.2, rank correction (ll. 276–282): say why A is integral.** "The scaled matrix is A + π⁻¹B′ with A
   integral" should say what A collects: the scaled proper parts, which are integral by the weight inequalities of
   point 1, and the scaled regular parts A_P, which stay integral because all scaling exponents are ≥ 0. It should
   also say that B′ has regular entries (u_k(0) times Laurent polynomials in τ) and the same rank as B, since diagonal
   scaling is invertible over the fraction field. The rank bound should be stated as rank B ≤ max(0, K−1−k_min),
   because B vanishes on the (k_min+1)-dimensional space of f with deg f ≤ k_min. This was point 2 of REFEREE_1 and
   F3 of REFEREE_2; the paper's text is still one clause.

6. **[gap] Local facts (a)–(d) and Lemma 4.3 (ll. 224–228, 288–290) are stated without proof.** Each is one line:
   1 − (−τ²)ⁿ and 1 ∓ τ^{2k+1} are separable, so all their zeros are simple; x_a − x_b = x_a(1 − w^{a−b}); and when
   e > K, no difference |b−a| < K is divisible by e. Add these lines. For Lemma 4.3 say explicitly that the A_a, λ_a
   and S_a (a ≤ K < e) are regular at ζ, so only the ν_k carry poles.

7. **[gap] Prop 6.1: interchange of L with the expansion of (z−s)⁻¹ at ∞ (l. 405).** Add that Σ_j s^j z^{−j−1}
   converges with its first two s-derivatives uniformly on |s| ≤ t² for |z| > t² + ε. Also define T_n := T_{n,Q_n}
   and E_n before using them. The rest of the proof is complete and correct; I checked the degree count for V and
   the final zero count.

8. **[gap/label] Remark 4.7 and the second paragraph of Section 7 (ll. 345–351, 429–433).** These contain claims that
   are not proved in the paper:
   * the sharp constant 1.130790 and the margin 0.0914 (proof sketch only);
   * "−0.1359K³ log φ at K = 8, −0.1160 at K = 26";
   * "about 1.118K³ log φ at K = 26";
   * the exact-arithmetic checks for K ≤ 16 and K ≤ 13.

   None is used in the proof. *Fix:* add "(not used in the proof)" to the remark and call its argument a sketch.
   Say which "three exponents" are summed at finite K: log|N C_K| + log|Δ_K(Ξ)| + log|σΔ_K(−Ξ)|, without the
   2K log(25b) term. Point to the scripts and data that produced the numbers (repository path, or a supplementary
   file). For what it is worth, I reproduced Σ_d b_{K,d}φ(d)/K³ = 1.19 (K = 20) and 1.16 (K = 40), the bound on I,
   and the exact local bounds for K ≤ 6.

9. **[gap/label] Remark 5.2 (ll. 383–387).** "The exact ℓ-adic analogue shows that the coefficient content alone gives
   only about 5/6 K³" cannot be checked as written. ℓ is undefined, it is unclear what "exact ℓ-adic analogue" means,
   and no computation is cited. *Fix:* explain this or delete it. The first sentence of the remark is a useful
   heuristic and can stay.

### Introduction, novelty, citations

10. **[citation] KRZ06 / JM10 attribution (ll. 77–78).** Krattenthaler–Rivoal–Zudilin prove that one of
    ζ_q(3), …, ζ_q(11) is irrational (their Théorème 4). Jouhet–Mosaki improve this to one of ζ_q(3), ζ_q(5), ζ_q(7),
    ζ_q(9) (their Théorème 1.3). Both results are for 1/q ∈ ℤ∖{±1}. *Fix:* "KRZ proved that one of
    ζ_q(3), …, ζ_q(11) is irrational, and Jouhet and Mosaki reduced this to ζ_q(3), …, ζ_q(9)". Fischler–Zudilin
    (2010) could also be cited here.

11. **[citation] Status of [UPL] (ll. 76–81, 541–543).** The text says the irrationality of ζ_{1/p}(3) "was open until
    very recently" and that a proof "was posted … under the pen name uplift-universal-inc; it has not been externally
    reviewed". Two problems.
    (a) The first phrase asserts that the problem is settled. In the refereed literature it is still open. Write
        instead: "remains open in the refereed literature; in October 2026 a proof was claimed …".
    (b) The repository's own attribution file (`docs/ATTRIBUTION.md`) discloses "substantial AI-assisted
        construction, arithmetic experimentation, drafting, and review". The paper must say this: "an unrefereed,
        AI-assisted research draft with a Lean formalisation, posted on GitHub under a pen name".

    The bibliography entry should give the release version and date (`0.3.0-two-proofs`, 2026-10-12, per
    `CITATION.cff`), or a commit hash, rather than "October 2026". Add one sentence saying that the present paper
    does not depend logically on [UPL]: every step is proved here, and the Lean proof is self-contained. That is true,
    and it matters to a journal.

12. **[citation] Authorship of the adapted Lean code (Section 8, "Provenance", ll. 504–507).** The `lean/` directory of
    [UPL] carries its own `CITATION.cff`: "QZeta3: Lean 4 formalisation …", author Fikreab Solomon Admasu, v0.1.0,
    2026-10-11, Apache-2.0. The repository `NOTICE` already credits this; the paper does not. *Fix:* add a separate
    bibliography item for the QZeta3 Lean package with that author and version, and cite it in "Provenance".

13. **[citation] [Fau] (l. 524).** This is an unrefereed Zenodo preprint claiming a major result (ζ(5) ∉ ℚ). It is
    cited for the moving-denominator idea, which is fine. Describe it as "unrefereed preprint" in the text or the
    bibliography, as for [UPL]. For the Hankel-determinant lineage, also cite Zudilin, "A determinantal approach to
    irrationality", Constr. Approx. 45 (2017) 301–310, and Krattenthaler's determinant identity behind Uvarov's
    formula (arXiv:2103.03969). These are closer to the method than [Zud16]. [UPL]'s own bibliography cites both.

14. **[citation] "see the surveys [Wal10, MS24]" (l. 65).** [Wal10] (RIMS Kôkyûroku 1710, 2010, 166–179) is a survey
    and does discuss ζ_F (§3); this entry is correct. [MS24] (Integers 24 (2024) #A85) is a research paper on the
    analytic continuation of the ℓ-generalised Fibonacci zeta function. Only its introduction summarises the
    arithmetic results. *Fix:* "see the survey [Wal10] and the introduction of [MS24]".

15. **[citation] Incomplete or missing entries.**
    * [ESS08] (Ramanujan J. 17 (2008)) has no page numbers. My recollection is 429–446; please verify.
    * The weight-one literature closest to the method is not cited: André-Jeannin's ζ_F(1) is a Padé/Lambert-series
      proof, and so are Prévost's proofs for Σ 1/L_n (J. Number Theory 73 (1998)) and the irrationality measures of
      Matala-aho–Prévost (Ramanujan J. 11 (2006)). A sentence citing them would place the paper better.
    * DOIs would help throughout.

16. **[citation] Novelty claim in the abstract (ll. 44–45).** "Previously the only odd value … known to be irrational
    was ζ_F(1)" is unhedged in the abstract but hedged in the introduction ("as far as we know"). The literature is
    moving fast. *Fix:* hedge the abstract too ("To our knowledge, …"). I also checked the claim at ll. 82–85 that
    the Lambert expansion gives 1, odd parts of ζ_q(3) and ζ_q(1) at q = φ⁻², and weight-1 and weight-3 forms at
    q = φ⁻¹, φ⁻². It is correct: Ξ = (1/8)[Σ_{m≡3(4)}(m²−1)tᵐ/(1−tᵐ) − Σ_{m≡1(4)}(m²−1)tᵐ/(1+tᵐ)].

### Section 8 versus the Lean code

17. **[exposition] Section 8 is accurate. I verified:**
    * the versions (Lean v4.35.0, Mathlib `v4.35.0` in `lake-manifest.json`) and the size (8495 lines in `FibZeta/`);
    * the statement and the axioms, re-run;
    * every declaration name in the table;
    * `DecayBound` with C = 4096 (`Analytic/Decay.lean`);
    * `ConjBound` with h_m bounded by (1−t²)^{−K} = φ^K (`Conj/DivDiff.lean`, `E_bound`);
    * `CostBound` with 121/100, the proved 4393/3675 and the constant 12 in place of 2E₁ (`Cost/Cyclo.lean`, upper
      half only);
    * `Integrality` for real τ ≠ 0 with τ^m ≠ 1, with one integer polynomial per (K, i) (`Statements.lean`);
    * the local bounds in the local rings of ℂ(τ) (`Denom/NewtonLocal.lean`, `Denom/Monomial.lean`,
      `Denom/Integrality.lean`);
    * nonvanishing via the Cauchy transform, without `EntryIdentity` (`NonVan/Nonvanishing.lean`);
    * 𝓕(x_a) = 2tᵃ(Ξ − S_a), checked by hand.

    Small corrections:
    (a) The Lean docstrings (`Defs.lean`, the `Denom/` and `Cost/` headers, `Statements.lean` docstrings
        "Proposition 2", "Proposition 3.6", …) use the numbering of the source notes PROOF.md, not the paper's.
        `FIDELITY_REFEREE.md` F4 asked for a translation table in §8. Add one sentence and the table, or point to the
        header of `Statements.lean`, which has it.
    (b) Lemma 4.5 is formalised only in the direction used (upper bound). Say "the upper half of Lemma 4.5".
    (c) "Lemma 2.2, entries ↦ `EntryIdentity`": add that `EntryIdentity` is used only by `DecayBound`, not by the
        assembly.

18. **[exposition] "an independent comparison … (`FIDELITY_REFEREE.md`)" (l. 452).** That report was written against
    commit `ae200bb` and an earlier draft of §8; its line references to main.tex are stale. Give the commit it refers
    to, and say "internal" rather than "independent" unless the reviewer was independent of the project.

19. **[exposition] Disclosure of AI assistance.** Section 8 discloses the AI-assisted origin of [UPL] (once point 11 is
    fixed) but says nothing about how the present proof and formalisation were produced. Most journals now require a
    statement on the use of AI tools in research, writing and code. Add one, per the target journal's policy.

### Notation and exposition

20. **[exposition] φ is both the golden ratio and Euler's function.** Euler's function appears at
    ll. 119, 219, 308–313, 322, 330, 339, 346, 349. The worst case is Lemma 4.5, "φ(d) log φ". Use a different symbol
    for the totient (e.g. φ_E(d), or J(d), or write "Euler's function ϕ" in a different glyph) and announce it in §2.

21. **[exposition] μ has three meanings.** It is undefined in the intro (l. 118: "c_* = 11/8 μ + 1/3"; should be μ₇),
    it is the Möbius function in the proof of Lemma 4.5, and it is the sieve density μ₇. Write μ₇ in the intro and
    keep μ for Möbius only. Give μ₇ in lowest terms, 768/1225 (2304/3675 is unreduced; the Lean proof uses 768/1225).

22. **[exposition] Other symbol clashes; rename one member of each pair.**
    * w = −t² vs the weights w_j (Prop 4.2). Suggest κ_j for the weights.
    * ω_r (cluster points, Prop 4.2) vs ω(e) (sieve weight, Prop 4.6).
    * π (uniformiser τ − ζ) vs π in 3/π² (Remark 4.7). Suggest ϖ.
    * h (test function, Def 2.1), h_m (complete homogeneous symmetric polynomials), h (order of E at ∞, Prop 6.1).
    * F (node products, §4 and §8), F (a different product over r_a, §5), F_n (Fibonacci), F_r (cluster factor),
      𝓕 (Cauchy transform).
    * B_j (basis, §3), B (bilinear form) and B′ (Prop 4.2), B_K (constant, §5).
    * A_a(P), A_K, the matrix A and A_P.
    * a and b as node indices vs ζ_F(3) = a/b (§7).
    * ρ vs ϱ (§3).
    * R_j, R (§3) vs R_{n,Q} (§6).
    * c(m), c_{K mod 3}, c in E = cz^{−h}.
    * C (absolute constant) vs C_K.
    * T_k (§5) vs T_{n,Q} (§6).
    * E₁ vs E_n, E.

23. **[exposition] §2, l. 131: definitions appear inside a "Thus" sentence.** "Thus ρ² = −w, …, A_K = K(K+1)/2 and
    θ = s d/ds" mixes consequences with new definitions. Split them. Also define "w(ζ)" (the value of w at τ = ζ)
    before Lemma 4.1 uses it.

24. **[exposition] Prop 4.2 uses unsubscripted Δ and m.** Write Δ_{K,τ} and m = m_r. Define v(Δ_{K,τ}) as the minimum
    over coefficients (Gauss valuation) in the statement, not only in "Local setting".

25. **[exposition] Prop 5.1, l. 379: the constant "4" is reached indirectly.** "Σ_n 2n(n+1)t^{2n+1} = 4" is true, but
    the bound needed is Σ|γ_n| ≤ 2/(1−t³) = φ² < 4. That uses Σ n(n+1)t^{2n+1} = 2 and 1/(1−t³) = φ²/2 < 2. Say so.

26. **[exposition] Table in §1 (ll. 94–101).** The column of exponents should be headed "(per K³ log φ)". The row
    "denominators … ≤ c_* < 11/9" could add "(c_* = 1.1954)".

27. **[typo/layout] Overfull boxes** (from `build/main.log`):
    * display at l. 130 (48 pt);
    * the α-part display at l. 341 (71 pt);
    * the assembly display at l. 426 (104 pt);
    * the §8 table, ll. 474–487 (50 pt);
    * l. 335 (1.3 pt);
    * a 20 pt overfull box on every page "while \output is active". This is the running head: the full title is
      too long. Give amsart a short title, e.g. `\title[Reciprocal cubes of Fibonacci numbers]{…}`.

    Break the long displays with `multline` or `split`. The §8 table can use `\small` or `tabularx`.

28. **[typo/layout] hyperref warnings** "Token not allowed in a PDF string". These come from math in section titles
    ("The size of $C_K(t)$", "Proof of Theorem~\ref{…}"). Use `\texorpdfstring`.

29. **[typo] Small items.**
    * l. 81: "Prévost" is typed as UTF-8 é. Elsewhere the source uses `\'e`; be consistent.
    * l. 316: "c_* = … = 1.19537…": add "= 4393/3675" to match §8.
    * l. 221: "(d−2)/4 (d ≡ 2 mod 8, d ≥ 10), …, k_min(2) = 2": fine, but say that the case d = 2 is the exception
      because (d−2)/4 = 0.
    * l. 403: "T_n" is used before it is defined as T_{n,Q_n}.

---

## Referee's checks (reproducible)

All in `paper/referee_scratch/`:

| script | what it checks | result |
|---|---|---|
| `checks.py` | E₁, C₀, μ₇, c_*, 2Σa_j formula (K ≤ 12), c/c′/δ bounds (m < 200), I and the sharp constant | all as stated; I = 0.683122, constant 1.130788 |
| `bsum.py` | k_min table vs brute force (d < 400); Σ_d b_{K,d}φ(d)/K³ | table correct; 1.2949 (8), 1.1914 (20), 1.1751 (26), 1.1580 (40), 1.1448 (80) |
| `exact.py 6` | exact Φ_d-multiplicities in the denominator of Δ_{K,τ}(X) vs b_{K,d}, K = 2..6 | no violations; bound attained for most d |
| `numchk.py` | Ξ·5√5 = ζ_F(3); direct node-sum Hankel determinant = formal Δ_K(Ξ) (K = 2, 3); real and conjugate sizes, K = 2..5 | agree to 60 digits; conjugate inside the Prop 5.1 bound |
| `lake env lean Axioms.lean` | axioms of the main theorem and all ingredients | `[propext, Classical.choice, Quot.sound]` throughout |
