import Mathlib

/-!
# Definitions for the irrationality of `ζ_F(3) = ∑ 1/F_n³`

Notation follows the written proof (`handoff/fibzeta/PROOF.md`, §0–§1, §3).

The algebraic construction is written over an arbitrary field `𝕜` and a parameter `τ : 𝕜`
("formal parameter" of PROOF §1).  It is specialised

* at `τ = t = φ⁻¹ ∈ ℝ` (the real determinant),
* at `τ = −φ ∈ ℝ` (the Galois conjugate, PROOF §4),
* at `τ = RatFunc.X` (the formal parameter, used for the denominators, PROOF §3).

With `w = −τ²`, `ρ = −τ`:

* `alpha τ k = ρ w^k`, `nu τ k = k(k+1) α_k/(1 − α_k)` (moments `L(s^k)`, Lemma 1(i));
* `psi τ N = τ^{3N}/(1 − w^N)³`, `S τ a = ∑_{N ≤ a} ψ_N`;
* `node τ a = w^{−a}` (the poles `x_a` of `1/D_K`), `F τ K = ∏_{a=1}^K (s − x_a)` (monic),
  `D_K(s) = ∏ (1 − w^a s) = (−1)^K w^{A_K} F(s)`;
* `L_X(1/(s − x_a)) = −2 τ^a (X − S_a)` (from Lemma 1(ii): `L(1/(1 − w^a s)) = 2ρ^{−a}(Ξ − S_a)`
  and `w/ρ = τ`);
* `L_X(s^k/F) = mConst + X · mLin` (polynomial quotient plus partial fractions);
* `Delta τ K = det [L_X(s^{i+j}/D_K)]_{0 ≤ i,j < K} ∈ 𝕜[X]`.

The definitions were checked numerically against the Gram determinant of the real functional
(`scripts/defs_check.py`).
-/

open Polynomial Finset

namespace FibZeta

/-! ### The generic construction -/

section Generic

variable {𝕜 : Type*} [Field 𝕜]

/-- `α_k = ρ w^k = (−τ)(−τ²)^k`. -/
def alpha (τ : 𝕜) (k : ℕ) : 𝕜 := (-τ) * (-τ ^ 2) ^ k

/-- The polynomial moments `ν_k = L(s^k) = k(k+1) α_k/(1 − α_k)` (Lemma 1(i)); `ν_0 = 0`. -/
def nu (τ : 𝕜) (k : ℕ) : 𝕜 := ((k : 𝕜) * ((k : 𝕜) + 1)) * alpha τ k / (1 - alpha τ k)

/-- `ψ_N = τ^{3N}/(1 − w^N)³`; at `τ = φ⁻¹` this is `F_N^{−3}/(5√5)`. -/
def psi (τ : 𝕜) (N : ℕ) : 𝕜 := τ ^ (3 * N) / (1 - (-τ ^ 2) ^ N) ^ 3

/-- The partial sums `S_a = ∑_{N=1}^a ψ_N`. -/
def S (τ : 𝕜) (a : ℕ) : 𝕜 := ∑ N ∈ Icc 1 a, psi τ N

/-- The pole `x_a = w^{−a}` of `1/D_K`. -/
def node (τ : 𝕜) (a : ℕ) : 𝕜 := ((-τ ^ 2) ^ a)⁻¹

/-- `F_K(s) = ∏_{a=1}^K (s − x_a)` (monic); `D_K = (−1)^K w^{A_K} F_K`. -/
noncomputable def F (τ : 𝕜) (K : ℕ) : 𝕜[X] := ∏ a ∈ Icc 1 K, (X - C (node τ a))

/-- The functional on polynomials: `L(∑ c_j s^j) = ∑ c_j ν_j`. -/
noncomputable def Lpoly (τ : 𝕜) (f : 𝕜[X]) : 𝕜 := ∑ j ∈ f.support, f.coeff j * nu τ j

/-- The residue coefficient `x_a^k / F_K'(x_a)` of `s^k/F_K` at `x_a`. -/
noncomputable def res (τ : 𝕜) (K k a : ℕ) : 𝕜 :=
  node τ a ^ k / (derivative (F τ K)).eval (node τ a)

/-- Constant term (in `X`) of `L_X(s^k/F_K)`: the polynomial moments of the quotient
`s^k /ₘ F_K` plus `∑_a res_a · 2τ^a S_a` (from `L_X(1/(s − x_a)) = −2τ^a (X − S_a)`). -/
noncomputable def mConst (τ : 𝕜) (K k : ℕ) : 𝕜 :=
  Lpoly τ (X ^ k /ₘ F τ K) + 2 * ∑ a ∈ Icc 1 K, res τ K k a * τ ^ a * S τ a

/-- Coefficient of `X` in `L_X(s^k/F_K)`: `−2 ∑_a res_a τ^a`. -/
noncomputable def mLin (τ : 𝕜) (K k : ℕ) : 𝕜 := -(2 * ∑ a ∈ Icc 1 K, res τ K k a * τ ^ a)

/-- `A_K = K(K+1)/2` (exact in `ℕ`). -/
def AK (K : ℕ) : ℕ := K * (K + 1) / 2

/-- The normalisation `1/D_K = nrm · 1/F_K`, `nrm = (−1)^K w^{−A_K}`. -/
def nrm (τ : 𝕜) (K : ℕ) : 𝕜 := (-1) ^ K * ((-τ ^ 2) ^ AK K)⁻¹

/-- The `X`-coefficient matrix of `[L_X(s^{i+j}/D_K)]`. -/
noncomputable def hankelLin (τ : 𝕜) (K : ℕ) : Matrix (Fin K) (Fin K) 𝕜 :=
  Matrix.of fun i j => nrm τ K * mLin τ K (i.val + j.val)

/-- The constant-coefficient matrix of `[L_X(s^{i+j}/D_K)]`. -/
noncomputable def hankelConst (τ : 𝕜) (K : ℕ) : Matrix (Fin K) (Fin K) 𝕜 :=
  Matrix.of fun i j => nrm τ K * mConst τ K (i.val + j.val)

/-- `Δ_K(X) = det [L_X(s^{i+j}/D_K)]_{0 ≤ i,j < K} ∈ 𝕜[X]`. -/
noncomputable def Delta (τ : 𝕜) (K : ℕ) : 𝕜[X] :=
  Matrix.det ((X : 𝕜[X]) • (hankelLin τ K).map C + (hankelConst τ K).map C)

end Generic

/-! ### The real numbers -/

/-- `t = φ⁻¹ = (√5 − 1)/2`. -/
noncomputable def tR : ℝ := Real.goldenRatio⁻¹

/-- The target `ζ_F(3) = ∑_{n ≥ 1} 1/F_n³` (index shifted so that `F_0 = 0` never appears). -/
noncomputable def zetaF3 : ℝ := ∑' n : ℕ, 1 / ((Nat.fib (n + 1) : ℕ) : ℝ) ^ 3

/-- `Ξ = ∑_{N ≥ 1} ψ_N(t) = ζ_F(3)/(5√5)`. -/
noncomputable def XiR : ℝ := ∑' N : ℕ, psi tR (N + 1)

/-- `θ(θ+1)h = s² h'' + 2 s h'` (`θ = s d/ds`). -/
noncomputable def thetaOp (h : ℝ → ℝ) (s : ℝ) : ℝ :=
  s ^ 2 * deriv (deriv h) s + 2 * s * deriv h s

/-- The real functional `L(h) = ∑_{n ≥ 1} ρⁿ [θ(θ+1)h](wⁿ)`, `ρ = −t`, `w = −t²` (PROOF §1). -/
noncomputable def Lfun (h : ℝ → ℝ) : ℝ :=
  ∑' n : ℕ, (-tR) ^ (n + 1) * thetaOp h ((-tR ^ 2) ^ (n + 1))

/-- `D_K(s) = ∏_{a=1}^K (1 − w^a s)` at `τ = t`. -/
noncomputable def DK (K : ℕ) (s : ℝ) : ℝ := ∏ a ∈ Icc 1 K, (1 - (-tR ^ 2) ^ a * s)

/-! ### Quantities of the real decay bound (Proposition 2) -/

/-- `a_j = ∑_{u=1}^{j} ⌈u/3⌉`; for natural numbers `⌈u/3⌉ = (u + 2)/3`. -/
def aj (j : ℕ) : ℕ := ∑ u ∈ Icc 1 j, (u + 2) / 3

/-- `b_K = 2 ∑_{j<K} a_j = (K³ + 3K² − c_{K mod 3})/9`; `|Δ_K(Ξ)| ≲ |w|^{b_K} = t^{2 b_K}`. -/
def bK (K : ℕ) : ℕ := 2 * ∑ j ∈ range K, aj j

/-! ### The cyclotomic exponents (Propositions 3.2, 3.4, Lemma 3.3) -/

/-- The cluster cost `c(m) = 2 ∑_{j=0}^{m−2} max(0, (m+2)/2 − j)` (clusters with a regular first
node). -/
def cW (m : ℕ) : ℕ := ∑ j ∈ range (m - 1), (m + 2 - 2 * j)

/-- The cluster cost `c′(m) = 2 ∑_{j=0}^{m−1} max(0, (m+2)/2 − j)` (the cluster `r = e`). -/
def cW' (m : ℕ) : ℕ := ∑ j ∈ range m, (m + 2 - 2 * j)

/-- The size `m_r = #{a ∈ [1, K] : a ≡ r (mod e)}` of the cluster `I_r`. -/
def clusterSize (K e r : ℕ) : ℕ := ((Icc 1 K).filter (fun a => a % e = r % e)).card

/-- The chosen primitive `d`-th root of unity `exp(2πi/d)`. -/
noncomputable def zetaC (d : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / d)

/-- `e(d)`: the order of `w(ζ) = −ζ²` for a primitive `d`-th root `ζ` (type (W)). -/
noncomputable def eW (d : ℕ) : ℕ := orderOf (-(zetaC d) ^ 2)

/-- Type (α): `α_k(ζ) = 1` for the primitive `d`-th root `ζ = zetaC d`. -/
def IsAlphaRoot (d k : ℕ) : Prop := (-zetaC d) * (-(zetaC d) ^ 2) ^ k = 1

open Classical in
/-- The α-part of the local exponent: `max(0, K − 1 − k_min(d))` if some `1 ≤ k ≤ K − 2` has
`α_k(ζ) = 1` (Lemma 3.3 and the `ε` term of Proposition 3.2), else `0`. -/
noncomputable def nAlpha (K d : ℕ) : ℕ :=
  if h : ∃ k, 1 ≤ k ∧ k ≤ K - 2 ∧ IsAlphaRoot d k then K - 1 - Nat.find h else 0

open Classical in
/-- The W-part of the local exponent (Proposition 3.2): if `e = e(d) ≤ K`,
`∑_{r=1}^{e−1} c(m_r) + c′(m_e)`, else `0`. -/
noncomputable def nW (K d : ℕ) : ℕ :=
  if 1 ≤ eW d ∧ eW d ≤ K then
    (∑ r ∈ Icc 1 (eW d - 1), cW (clusterSize K (eW d) r)) + cW' (clusterSize K (eW d) (eW d))
  else 0

/-- The local exponent `b_{K,d}` (Proposition 3.4). -/
noncomputable def nExp (K d : ℕ) : ℕ := nW K d + nAlpha K d

/-- The clearing polynomial `C_K(τ) = ∏_{d=1}^{4K} Φ_d(τ)^{b_{K,d}} ∈ ℤ[τ]` (Proposition 3.4). -/
noncomputable def CKpoly (K : ℕ) : ℤ[X] := ∏ d ∈ Icc 1 (4 * K), cyclotomic d ℤ ^ nExp K d

end FibZeta
