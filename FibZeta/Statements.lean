import FibZeta.Defs

/-!
# The five ingredients, as frozen statements

Each `Prop` below is one proposition of `handoff/fibzeta/PROOF.md`.  `FibZeta.Main` proves the
theorem from them (`irrational_zetaF3_of`); each is proved in its own module, and
`FibZeta.irrational_zetaF3` (in `FibZeta.lean`'s final file) combines them.

* `DecayBound` — Proposition 2: `|Δ_K(Ξ)| ≤ C^{K²} t^{2 b_K}` (`t^{2b_K} = |w|^{b_K}`).
* `ConjBound` — Proposition 4: `|σΔ_K(−Ξ)| ≤ C^{K²} t^{K²(K+1)}`, where `σΔ_K` is the construction
  at `τ = −φ`.
* `Integrality` — Proposition 3.4: `C_K(τ) Δ_{K,τ}` has coefficients in `ℤ[τ, τ⁻¹]`, uniformly in
  every real `τ ≠ 0` that is not a root of unity.
* `CostBound` — Proposition 3.6 (in a weaker, formally convenient form; the cubic constant
  `121/100 < 11/9` replaces `1.1308`).
* `Nonvanishing` — Proposition 5: `Δ_K(Ξ) ≠ 0` for infinitely many `K`.
* `EntryIdentity` — Lemma 1 + partial fractions: the entries of the formal Hankel matrix at
  `τ = t`, `X = Ξ` are the values `L(s^k/D_K)` of the real functional.  (Used by the proofs of
  `DecayBound` and `Nonvanishing`, not by `Main`.)
-/

open Polynomial Finset

namespace FibZeta

/-- Proposition 2 (real decay). -/
def DecayBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ K : ℕ, 1 ≤ K → |(Delta tR K).eval XiR| ≤ C ^ (K ^ 2) * tR ^ (2 * bK K)

/-- Proposition 4 (conjugate smallness). -/
def ConjBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ K : ℕ, 1 ≤ K →
    |(Delta (-Real.goldenRatio) K).eval (-XiR)| ≤ C ^ (K ^ 2) * tR ^ (K ^ 2 * (K + 1))

/-- Proposition 3.4 (global denominator), at every real non-root of unity. -/
def Integrality : Prop :=
  ∀ K i : ℕ, ∃ (n : ℕ) (A : ℤ[X]), ∀ τ : ℝ, τ ≠ 0 → (∀ m : ℕ, 0 < m → τ ^ m ≠ 1) →
    aeval τ (CKpoly K) * (Delta τ K).coeff i = aeval τ A / τ ^ n

/-- Proposition 3.6 (size of `N(C_K(t))`), with cubic constant `121/100`. -/
def CostBound : Prop :=
  ∃ C : ℝ, ∀ K : ℕ, 1 ≤ K →
    Real.log |aeval tR (CKpoly K) * aeval (-Real.goldenRatio) (CKpoly K)| ≤
      (121 / 100 : ℝ) * (K : ℝ) ^ 3 * Real.log Real.goldenRatio +
        C * (K : ℝ) ^ 2 * (1 + Real.log K) ^ 2

/-- Proposition 5 (nonvanishing). -/
def Nonvanishing : Prop := ∀ N : ℕ, ∃ K, N ≤ K ∧ (Delta tR K).eval XiR ≠ 0

/-- Lemma 1 with partial fractions: `L_X(s^k/D_K)` at `τ = t`, `X = Ξ` is `L(s^k/D_K)`. -/
def EntryIdentity : Prop :=
  ∀ K k : ℕ, 1 ≤ K → k ≤ 2 * K →
    nrm tR K * (mConst tR K k + XiR * mLin tR K k) = Lfun (fun s => s ^ k / DK K s)

end FibZeta
