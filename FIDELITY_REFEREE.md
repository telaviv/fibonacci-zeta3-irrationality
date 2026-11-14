# Fidelity referee report: lean_fibzeta (main @ ae200bb), 2026-11-13

Scope: whether the Lean *statements* (`FibZeta/Defs.lean`, `FibZeta/Statements.lean`, the assembly in
`FibZeta/Main.lean`, `FibZeta/Final.lean`, `FibZeta/Roots.lean`, and the headline theorems of `Analytic/`, `Conj/`,
`Cost/`, `NonVan/`, plus the `Integrality` target of `w-denom`) mean what `paper/main.tex` says. Proofs were not
checked (the kernel checks them). I did not re-run `lake build` or `#print axioms`. `grep` finds no `sorry`, `admit`,
`axiom` or `native_decide` on main.

## Verdict: PASS WITH FIXES

The Lean statements are faithful. `zetaF3` is Σ_{n≥1} 1/F_n³, and the generic construction is the paper's Δ_{K,τ}
(I checked it entry by entry). Every frozen Prop is the paper's proposition or a correct weaker or equivalent form,
and the assembly uses each one in that form. I found no vacuity or junk-value loophole. The fixes needed are in the
documentation: the paper's §8 ("Formal verification") describes the finished state (`FibZeta.irrational_zetaF3`, no
`sorry`, "every step formalised"), but main only has the conditional
`irrational_zetaF3_of_integrality (hI : Integrality)`. Two table entries also name the wrong declarations.

**No blocking findings against the Lean statements.** One release gate (F1) must be cleared before the paper's §8 is
true as written. It clears itself once `w-denom` lands and the one-line final theorem is added.

---

## A. Checks that passed (with reasons)

**A1. `zetaF3`** (`Defs.lean:99`): `∑' n : ℕ, 1 / ((Nat.fib (n + 1) : ℕ) : ℝ) ^ 3`. Mathlib has `fib 0 = 0` and
`fib 1 = fib 2 = 1`, so the terms are 1/F_1³, 1/F_2³, …, which is exactly Σ_{n≥1} F_n^{-3}. Shifting the index avoids
the junk `1/0 = 0` at F_0 (that term would only add 0 anyway).

*Summability and junk values.* An unsummable real `tsum` is `0` by definition, and 0 is rational. So
`Irrational zetaF3` implies that the series is summable and that `zetaF3` is its true sum. The headline statement is
therefore meaningful without a separate summability lemma, and it cannot be satisfied by a junk value. (Summability
is also proved: `summable_psi_tR` in `Conj/Conjugate.lean` and the ψ-summability in `Analytic/Functional.lean`,
together with `one_div_fib_cube`.) The series has nonnegative terms, so unconditional summation is the usual sum.

**A2. Trust surface.** `irrational_zetaF3_of_integrality` has exactly one hypothesis, `Integrality`, and every other
ingredient is discharged by a theorem with the frozen type: `Analytic.decayBound : DecayBound`,
`Conj.conjBound : ConjBound`, `Cost.costBound : CostBound`, `NonVan.nonvanishing : Nonvanishing`. No sub-namespace
redefines `DecayBound`, `Delta`, `CKpoly`, etc., so the names resolve to the frozen `FibZeta.*` declarations; I listed
every `def` in the tree to confirm this. So:
* For the final unconditional theorem (after Denom), the reader only has to trust `zetaF3`, Mathlib's `Nat.fib`,
  `tsum` and `Irrational`. The construction in `Defs.lean` and the Props in `Statements.lean` are proof-internal. A
  wrong definition there could make the proof impossible, but it could not make a false theorem true.
* For the current conditional theorem, `Integrality` is load-bearing: if it were false, the theorem would be vacuous.
  A6 argues that it is true as stated and is not trivially satisfiable.

**A3. The generic construction vs §2.** With `-τ ^ 2` parsed as `-(τ²)`:
* `alpha τ k = (−τ)(−τ²)^k = ρ w^k`; `nu = k(k+1)α_k/(1−α_k)` (Lemma 2.2(i)); `psi`, `S` as in §2. All match.
* `node τ a = w^{−a} = x_a`, and `F = ∏_{a=1}^K (s − x_a)` is monic. `D_K = ∏(1 − w^a s) = ∏(−w^a)(s − x_a) =
  (−1)^K w^{A_K} F`, so `1/D_K = (−1)^K w^{−A_K}/F = nrm/F`. `AK = K(K+1)/2` (exact in ℕ). Match.
* Partial fractions: `s^k = (s^k /ₘ F)·F + r` and `r(x_a) = x_a^k`, so
  `s^k/F = (s^k /ₘ F) + Σ_a x_a^k/(F'(x_a)(s − x_a))`; this is `res`. It holds for every k, not only for
  deg < 2K − 1.
* Pole moment: `1/(s − x_a) = −w^a/(1 − w^a s)`, so by Lemma 2.2(ii)
  `L_X(1/(s − x_a)) = −w^a·2ρ^{−a}(X − S_a) = −2τ^a(X − S_a)` (since w/ρ = τ). This gives
  `mConst = Lpoly(quot) + 2Σ res_a τ^a S_a` and `mLin = −2Σ res_a τ^a`, as defined.
* `Delta τ K = det(X·[nrm·mLin(i+j)] + [nrm·mConst(i+j)])` over `0 ≤ i,j < K`, which is
  `det[L_X(s^{i+j}/D_K)]`. Match.
* At τ = t and τ = −φ no denominator vanishes: |α_k(t)| < 1 and |α_k(−φ)| > 1; 1 − w^N ≠ 0; the nodes are distinct
  since |w| ≠ 1; τ ≠ 0. So `Delta tR K` and `Delta (−φ) K` are the honest Δ_K and σΔ_K, with no `x/0 = 0`
  contamination. The proved `EntryIdentity` (entries = `Lfun(s^k/D_K)` for k ≤ 2K, in fact for all k per the Analytic
  README) and `Delta_eval_eq_det` independently confirm `Delta tR K` at `XiR` against the real functional.
* `tR = φ⁻¹`. `XiR = ∑' N, psi tR (N+1) = Σ_{N≥1} ψ_N(t)`, and `zetaF3_eq` shows `zetaF3 = 5√5·XiR`. Match.
* `thetaOp h = s²h'' + 2sh' = θ(θ+1)h`. `Lfun h = Σ_{n≥0} (−t)^{n+1}[θ(θ+1)h]((−t²)^{n+1})`, which is the paper's
  Σ_{n≥1} ρ^n[θ(θ+1)h](w^n). `deriv` is applied only at the points w^n ∈ [−t², t²], where `s ↦ s^k/D_K(s)` is real
  analytic (its poles satisfy |x_a| ≥ φ²). The junk `deriv = 0` therefore never occurs in `EntryIdentity`. Also,
  `Lfun` is not used by `Main`.
* `DK`, `aj` (`(u+2)/3 = ⌈u/3⌉` in ℕ) and `bK = 2Σ_{j<K} a_j` match. Spot checks: bK 1 = 0 and bK 2 = 2, both equal to
  (K³+3K²−c_{K mod 3})/9.

**A4. Frozen Props vs the paper.**

| Prop | Paper | Relation |
|---|---|---|
| `DecayBound`: ∃C>0, ∀K≥1, \|Δ_K(Ξ)\| ≤ C^{K²} t^{2b_K} | Prop 3.1: log\|Δ_K(Ξ)\| ≤ −(2/9)(K³+3K²−4) log φ + O(K²) | Equivalent, slightly sharper: it uses the exact b_K instead of the worst case c = 4. The paper's prefactor (C(2K)²4^{2K}√K)^K is e^{O(K²)}. Since t^{2b_K} = \|w\|^{b_K} = φ^{−2b_K}, the exponents agree. |
| `ConjBound`: \|Δ_{−φ}(−Ξ)\| ≤ C^{K²} t^{K²(K+1)} | Prop 5.1: −K²(K+1) log φ + K log(√K B_K), B_K = O(K²) | Weaker (drops the explicit B_K); sufficient. |
| `CostBound`: log\|C_K(t)C_K(−φ)\| ≤ (121/100)K³ log φ + CK²(1+log K)² | Prop 4.6: log\|N C_K(t)\| ≤ c_*K³ log φ + O(K² log K), c_* = 1.19537… | Weaker; N(C_K(t)) = C_K(t)C_K(−φ) since C_K ∈ ℤ[τ]. The margin 11/9 − 121/100 = 11/900 is exactly the constant in `Main.hkey`. |
| `Nonvanishing`: ∀N ∃K≥N, Δ_K(Ξ) ≠ 0 | Prop 6.1 | Equivalent. |
| `EntryIdentity` (k ≤ 2K) | "By Lemma 2.2, Δ_K(Ξ) = det[L(s^{i+j}/D_K)]" | Covers i + j ≤ 2K − 2; true for all k. Not used by `Main`. |
| `Integrality` | Prop 4.4 | Weaker (specialisation); sufficient (A6). |

Ranges: the paper fixes K ≥ 2 with absolute O-constants; Lean quantifies over K ≥ 1, which is harmless and has been
proved.

**A5. Cyclotomic exponents vs §4** (`Defs.lean:125–162`).
* `cW m = Σ_{j<m−1}(m+2−2j)` with truncated ℕ subtraction, i.e. `Σ_{j=0}^{m−2} max(0, m+2−2j) = c(m)`. Likewise
  `cW' m = Σ_{j<m}(…) = c'(m)`. Spot checks: c(1) = 0, c(2) = 4, c'(1) = 3, matching the paper's list.
* `clusterSize K e r = #{a ∈ [1,K] : a ≡ r (mod e)}`; for r = e this is the class a ≡ 0. That is I_r.
* `eW d = orderOf(−ζ_d²)` and `IsAlphaRoot d k ⟺ (−ζ_d)(−ζ_d²)^k = 1` give e(d) and α_k(ζ) = 1 at
  ζ_d = exp(2πi/d). `Roots.lean` proves that both are the same at every primitive d-th root, as the paper's
  parenthetical claims (that is what the Galois descent in Prop 4.4 needs).
* `nAlpha K d = K − 1 − (least k ≥ 1 with α_k = 1)` if that least k is ≤ K − 2, else 0. This equals
  max(0, K − 1 − k_min(d)) in all cases: if k_min ≥ K − 1 the max is 0. `K − 2` truncates correctly for K ≤ 2.
* `nW K d` is `Σ_{r=1}^{e−1} c(m_r) + c'(m_e)` when e ≤ K, else 0. (The guard `1 ≤ eW d` always holds for d ≥ 1.)
* `nExp = nW + nAlpha` reproduces b_{K,d} case by case: e ≤ K gives Prop 4.2 with the ε-term (ε = 1 iff some
  α_k = 1 with k ≤ K − 2, and otherwise the term is 0 anyway); e > K with an α-root gives Lemma 4.3; d ∉ 𝒟_K gives 0.
* `CKpoly K = ∏_{d=1}^{4K} Φ_d^{nExp K d}`. Restricting to d ≤ 4K is justified by the paper (§4, after Prop 4.4):
  type W gives ζ^{4e} = 1, and type α gives ζ^{4k+2} = 1. Restricting the product only *weakens* the clearing factor,
  so it can make `Integrality` harder, never easier.
* The definitions are also checked from both sides: `CostBound` (proved) caps `nExp` from above, and `Integrality`
  needs it to be large enough. A mis-definition would show up as an unprovable `Integrality`, not as unsoundness.

**A6. `Integrality`** (`Statements.lean:201`): `∀ K i, ∃ n A, ∀ τ : ℝ, τ ≠ 0 → (∀ m > 0, τ^m ≠ 1) →
C_K(τ)·[X^i]Δ_{K,τ} = A(τ)/τ^n`.
* *Faithful.* Prop 4.4 says C_K(τ)Δ_{K,τ}(X) ∈ ℤ[τ^{±1}][X] in ℚ(τ). The denominators of the construction are
  1 − α_k = 1 ∓ τ^{2k+1}, 1 − w^N, x_a − x_b (proportional to 1 − w^{a−b}), and powers of w. At a real τ ≠ 0 that is
  not a root of unity, none of them vanishes (their real zeros are ±1 and 0). So evaluating the rational-function
  `Delta (RatFunc.X) K` at τ commutes with every field operation and with `/ₘ F` (F is monic). The Lean statement is
  therefore exactly the specialisation of Prop 4.4 to such τ. It is weaker than Prop 4.4 but implied by it.
  `w-denom` takes this route (`Specialization.lean`, then
  `integrality_of_local_bounds : LocalBounds ℂ → Integrality`).
* *Sufficient.* `n` and `A` are chosen before `∀ τ`, so the same Laurent polynomial serves both τ = t and τ = −φ.
  This is exactly what the norm argument (`Main.hY`, `norm_ne_zero`) needs. With the quantifiers in the other order
  the statement would be useless; they are in the right order.
* *Not trivially satisfiable.* For fixed K and i, one Laurent polynomial has to agree with C_K·coeff at uncountably
  many τ, which is a genuine identity of rational functions. The hypotheses on τ are satisfiable (by t and −φ).
  `τ ≠ 0` is needed separately (τ = 0 passes the root-of-unity test), and it is included.

**A7. Assembly** (`Main.lean`, matching paper §7). Suppose `zetaF3 = a/b` with b = `q.den > 0`. Put
u(τ) = a(1+2τ)/(25b). Then u(t) = Ξ, since √5 = 1 + 2t, and u(−φ) = −Ξ, since 1 + 2(−φ) = −√5. `Integrality` gives
τ^N·C_K(τ)(25b)^K Δ_{K,τ}(u(τ)) = Q(τ) with one Q ∈ ℤ[X] for both τ. The product Q(t)Q(−φ) is an integer, nonzero
when Q(t) ≠ 0 (`norm_ne_zero`, via reduction mod τ² + τ − 1 and the irrationality of √5). Q(t) is nonzero because
C_K(t) ≠ 0 (`aeval_CKpoly_ne_zero`) and Δ_K(Ξ) ≠ 0 (`Nonvanishing`); and |t·(−φ)| = 1. Taking logs and inserting the
three bounds gives (11/900)K³ log φ ≤ O(K²(1 + log K)²), which is a contradiction for large K. This is the paper's
argument. Instead of using σ as a field automorphism, it uses the same polynomial identity at both roots, which is
legitimate and arguably cleaner. Junk-value checks: `Real.log` is applied only to quantities shown to be positive
(P > 0 is derived from `hbig`); `Real.log K` is used with K ≥ 1.

**A8. Degeneracy cross-checks.** `Delta tR K` cannot be a degenerate 0, because `Nonvanishing` is proved. A degenerate
`Delta (−φ) K` would make `ConjBound` easy, but it would then contradict `norm_ne_zero` together with `Integrality`, so
it cannot coexist with a proof of `Integrality`. Once all five ingredients are proved, no junk convention can make the
conclusion vacuous.

---

## B. Findings

**F1. [blocking for release; not a Lean-statement defect] Paper §8 and §1 describe a theorem that does not exist yet.**
`paper/main.tex:116, 441–445` states `theorem FibZeta.irrational_zetaF3 : Irrational FibZeta.zetaF3`, "no `sorry`",
and "the whole argument / every step is formalised". The abstract (line 50) says the same. Main currently has only
`FibZeta.irrational_zetaF3_of_integrality (hI : Integrality)` (`Final.lean:237`), and `FibZeta.Denom.integrality`
(table, line 472) does not exist. On `w-denom` the current endpoint is
`integrality_of_local_bounds (hb : LocalBounds ℂ) : Integrality`.
*Fix:* when Denom lands, add to `Final.lean` (and import `FibZeta.Denom.*`):
`theorem irrational_zetaF3 : Irrational zetaF3 := irrational_zetaF3_of_integrality Denom.integrality`. Run
`#print axioms FibZeta.irrational_zetaF3` and `paper/check_lean_names.py`, and make sure the Denom theorem is named
exactly `FibZeta.Denom.integrality : Integrality` (or update the table). Until then, the paper must say that the
formalisation is conditional on `Integrality`.

**F2. [documentation] Table row for nonvanishing names the wrong declaration** (`main.tex:475`). The row cites
`FibZeta.NonVan.nonvanishing_of_entry`. That theorem ignores its `EntryIdentity` hypothesis, and `Final.lean` uses the
unconditional `FibZeta.NonVan.nonvanishing`.
*Fix:* cite `FibZeta.NonVan.nonvanishing`. Optionally add a sentence: nonvanishing is proved directly for the formal
Hankel matrix (through the Cauchy transform at the nodes) and does not use `Lfun`.

**F3. [documentation] `Statements.lean` header misdescribes how `EntryIdentity` is used and what the final theorem is
called.** `Statements.lean:18–19` says `EntryIdentity` is "Used by the proofs of `DecayBound` and `Nonvanishing`". It
is used only by `DecayBound` (via `hasL_fraction_DK` in `Analytic/Gram.lean`). The header also says "the five
ingredients" but lists six, and it refers to `FibZeta.irrational_zetaF3` "in `FibZeta.lean`'s final file", which does
not exist yet (see F1).
*Fix:* edit the docstring only; this leaves every statement unchanged, so the freeze rule allows it if the owner
agrees. Otherwise record the correction in a README.

**F4. [documentation] Proposition numbering differs between the Lean docstrings and the paper.** The Lean docstrings
use PROOF.md numbering, while the paper uses section-relative numbering:

| Lean docstring (PROOF.md) | Paper |
|---|---|
| Lemma 1 | Lemma 2.2 |
| Prop 2 | Prop 3.1 |
| Lemma 3.1, Prop 3.2, Lemma 3.3, Prop 3.4 | Lemma 4.1, Prop 4.2, Lemma 4.3, Prop 4.4 |
| Lemma 3.5, Prop 3.6 | Lemma 4.5, Prop 4.6 |
| Prop 4 | Prop 5.1 |
| Prop 5 | Prop 6.1 |
| PROOF §6 (assembly) | paper §7 |

The paper (line 491) tells the reader to check `Defs.lean` and `Statements.lean` against the paper, so this mismatch
will confuse exactly that reader. The referee brief itself also says "§7 Formal verification", but the paper's
formal-verification section is §8.
*Fix:* add this table to paper §8 ("Lean docstrings follow the numbering of the source notes: …") or to a top-level
README.

**F5. [documentation] The paper overstates what has to be trusted** (`main.tex:490–491`). "The reader has to check
that the statements in `Defs.lean` and `Statements.lean` mean what is claimed here" is true for the claim that the
formalisation follows the paper. For the headline theorem it is more than needed: once
`FibZeta.irrational_zetaF3 : Irrational zetaF3` is proved, only `zetaF3` (and Mathlib's `Nat.fib`, `tsum`,
`Irrational`) needs checking (A2). It is also worth stating that a junk `tsum` value cannot make the theorem vacuous,
since 0 is rational (A1).
*Fix:* write two sentences, one about the theorem's trust base and one about fidelity to the paper's argument.

**F6. [cosmetic] "Slightly weaker" in §8 is not accurate for `DecayBound`** (`main.tex:480–482`). `DecayBound` is
equivalent to Prop 3.1, in fact slightly sharper since it uses the exact b_K. `ConjBound` and `CostBound` are weaker,
and `Integrality` is the specialisation of Prop 4.4.
*Fix:* "The formal statements are equivalent to or slightly weaker than the propositions."

**F7. [cosmetic] Table row for Integrality.** `Integrality` also relies on Lemma 4.1 (the integrality ring) and
Lemma 4.3 (pure α-roots). The row reads "Propositions 4.2–4.4", which by range includes Lemma 4.3 but not Lemma 4.1.
*Fix:* "Lemma 4.1 – Proposition 4.4".

**F8. [cosmetic, optional] A sanity lemma for readers.** Add `theorem zetaF3_hasSum : HasSum (fun n => 1 /
(Nat.fib (n+1) : ℝ)^3) zetaF3` to `Final.lean`; it is a few lines from `summable_psi_tR` and `one_div_fib_cube`. This
is not needed for meaning (A1), but it makes the definition self-evidently the convergent series.

**F9. [cosmetic] Unreachable guard in `nW`.** The condition `1 ≤ eW d` in `nW` is always true for d ≥ 1. It is harmless,
and `Defs.lean` is frozen, so leave it.

---

## Items asked about, short answers

1. `zetaF3` is correct (index shift and `Nat.fib` conventions). A separate summability proof is not needed for
   meaning, because an unsummable tsum would be the rational junk 0 (A1).
2. The construction matches Δ_K: moments, poles, residues, the normalisation nrm = (−1)^K w^{−A_K}, and the Hankel
   matrix. It matches at τ = t and at τ = −φ. `tR`, `XiR` and `Lfun` (with `deriv`, used only at points where h is
   smooth) are correct (A3).
3. All six Props have the right constants, quantifiers, ranges and exponents (A4).
4. `Integrality` is faithful (it is the specialisation of Prop 4.4) and sufficient, with the same A and n for both
   τ (A6).
5. `nExp`, `nW`, `nAlpha`, `eW`, `IsAlphaRoot` and `CKpoly` match Props 4.2 and 4.4 and Lemma 4.3 (PROOF 3.2–3.4 and
   3.3) (A5).
6. No vacuity: denominators are nonzero at t and −φ, `Real.log` is applied only to positive quantities, `deriv` is
   applied only at smooth points, and `Nonvanishing` excludes a degenerate Δ (A3, A7, A8).
7. Paper §8 needs F1 (release gate) and F2, F4–F7 (documentation and cosmetic).
