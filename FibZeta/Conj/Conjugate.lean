import FibZeta.Main
import FibZeta.Conj.DivDiff

/-!
# The construction at `τ = −φ` (PROOF §4)

At `τ = −φ`: `w = −φ² = (−t²)⁻¹`, so the nodes are `node a = (−t²)^a =: rr a` (`|rr a| = t^{2a}`);
`ψ_N(−φ) = −ψ_N(t)`, hence `S_a(−φ) + Ξ = ∑_{N > a} ψ_N(t)`; and
`2(−φ)^a ψ_{a+M+1}(t) = 2 r_a t^{3(M+1)} (1 − r_a w^{M+1})^{−3}` (the function `Γ(r_a)` of PROOF §4,
summand by summand).  Also `|ν_j(−φ)| ≤ j(j+1) φ²`.
-/

open Polynomial Finset

namespace FibZeta.Conj

/-- The conjugate nodes `r_a = (−t²)^a`. -/
noncomputable def rr (a : ℕ) : ℝ := (-tR ^ 2) ^ a

theorem tR_sq_pos : 0 < tR ^ 2 := by have := tR_pos; positivity

theorem tR_sq_lt_one : tR ^ 2 < 1 := by
  have := tR_pos; have := tR_lt_one; nlinarith

theorem abs_rr (a : ℕ) : |rr a| = (tR ^ 2) ^ a := by
  rw [rr, abs_pow, abs_neg, abs_of_pos tR_sq_pos]

theorem abs_rr_le {a : ℕ} (ha : 1 ≤ a) : |rr a| ≤ tR ^ 2 := by
  rw [abs_rr]; exact pow_le_of_le_one tR_sq_pos.le tR_sq_lt_one.le (by omega)

theorem abs_rr_le_one (a : ℕ) : |rr a| ≤ 1 := by
  rw [abs_rr]; exact pow_le_one₀ tR_sq_pos.le tR_sq_lt_one.le

theorem rr_injective : Function.Injective rr := by
  intro a b h
  have : (tR ^ 2) ^ a = (tR ^ 2) ^ b := by rw [← abs_rr, ← abs_rr, h]
  exact pow_right_injective₀ tR_sq_pos tR_sq_lt_one.ne this

theorem node_neg_gold (a : ℕ) : node (-Real.goldenRatio) a = rr a := by
  have h : (-(-Real.goldenRatio) ^ 2)⁻¹ = -tR ^ 2 := by
    unfold tR; rw [neg_sq, inv_neg, inv_pow]
  rw [node, rr, ← h, inv_pow]

theorem F_neg_gold (K : ℕ) : F (-Real.goldenRatio) K = Lagrange.nodal (Icc 1 K) rr := by
  rw [F, Lagrange.nodal_eq]
  exact prod_congr rfl fun a _ => by rw [node_neg_gold]

theorem res_neg_gold {K k a : ℕ} (ha : a ∈ Icc 1 K) :
    res (-Real.goldenRatio) K k a = rr a ^ k * Lagrange.nodalWeight (Icc 1 K) rr a := by
  rw [res, node_neg_gold, F_neg_gold, Lagrange.nodalWeight_eq_eval_derivative_nodal ha,
    div_eq_mul_inv]

/-! ### `ψ_N` at `−φ` and the tail `S_a(−φ) + Ξ` -/

theorem psi_neg_gold (N : ℕ) : psi (-Real.goldenRatio) N = -psi tR N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [psi]
  have hg : Real.goldenRatio = tR⁻¹ := by unfold tR; rw [inv_inv]
  have ht := tR_pos
  set T := tR ^ N with hT
  have hT0 : 0 < T := by positivity
  have hT1 : T < 1 := pow_lt_one₀ ht.le tR_lt_one hN.ne'
  have e1 : (-tR⁻¹) ^ (3 * N) = ((-1) ^ N * T⁻¹) ^ 3 := by
    rw [mul_comm 3 N, pow_mul, neg_pow, inv_pow]
  have e2 : (-(-tR⁻¹) ^ 2) ^ N = (-1) ^ N * (T⁻¹) ^ 2 := by
    rw [neg_sq, neg_pow, ← pow_mul, mul_comm 2 N, pow_mul, inv_pow]
  have e3 : tR ^ (3 * N) = T ^ 3 := by rw [mul_comm 3 N, pow_mul]
  have e4 : (-tR ^ 2) ^ N = (-1) ^ N * T ^ 2 := by
    rw [neg_pow, ← pow_mul, mul_comm 2 N, pow_mul]
  rw [psi, psi, hg, e1, e2, e3, e4]
  have hA : T ^ 2 - 1 ≠ 0 := by nlinarith
  have hB : 1 - T ^ 2 ≠ 0 := by nlinarith
  have hC : T ^ 2 + 1 ≠ 0 := by nlinarith
  rcases neg_one_pow_eq_or ℝ N with h | h <;> rw [h]
  · have : 1 - 1 * (T⁻¹) ^ 2 = (T ^ 2 - 1) / T ^ 2 := by field_simp
    rw [this]; field_simp; ring
  · have : 1 - -1 * (T⁻¹) ^ 2 = (T ^ 2 + 1) / T ^ 2 := by field_simp; ring
    rw [this]
    have : 1 - -1 * T ^ 2 = T ^ 2 + 1 := by ring
    rw [this]; field_simp

theorem abs_psi_tR_le (N : ℕ) : |psi tR N| ≤ (tR ^ 3) ^ N * ((1 - tR ^ 2)⁻¹) ^ 3 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simpa [psi] using pow_nonneg (by linarith [tR_sq_lt_one] : (0 : ℝ) ≤ 1 - tR ^ 2) 3
  have h1 : 1 - tR ^ 2 ≤ |1 - (-tR ^ 2) ^ N| := by
    have h2 : |(-tR ^ 2) ^ N| ≤ tR ^ 2 := by
      rw [abs_pow, abs_neg, abs_of_pos tR_sq_pos]
      exact pow_le_of_le_one tR_sq_pos.le tR_sq_lt_one.le hN.ne'
    have := abs_sub_abs_le_abs_sub 1 ((-tR ^ 2) ^ N)
    rw [abs_one] at this; linarith
  have h0 : 0 < 1 - tR ^ 2 := by linarith [tR_sq_lt_one]
  rw [psi, abs_div, abs_pow, abs_of_pos tR_pos, abs_pow, ← pow_mul, inv_pow, ← div_eq_mul_inv]
  exact div_le_div_of_nonneg_left (pow_pos tR_pos _).le (pow_pos h0 3) (pow_le_pow_left₀ h0.le h1 3)

theorem summable_psi_tR : Summable (fun N => psi tR N) := by
  have h3 : tR ^ 3 < 1 := pow_lt_one₀ tR_pos.le tR_lt_one (by norm_num)
  have hg : Summable (fun N : ℕ => (tR ^ 3) ^ N * ((1 - tR ^ 2)⁻¹) ^ 3) :=
    (summable_geometric_of_lt_one (pow_pos tR_pos 3).le h3).mul_right _
  exact Summable.of_norm_bounded hg fun N => by rw [Real.norm_eq_abs]; exact abs_psi_tR_le N

theorem sum_Icc_eq_sum_range (f : ℕ → ℝ) (a : ℕ) :
    ∑ N ∈ Icc 1 a, f N = ∑ i ∈ range a, f (i + 1) := by
  induction a with
  | zero => simp
  | succ a ih => rw [sum_Icc_succ_top (by omega), ih, sum_range_succ]

theorem S_add_Xi (a : ℕ) :
    S (-Real.goldenRatio) a + XiR = ∑' M : ℕ, psi tR (M + a + 1) := by
  have hs : Summable (fun N => psi tR (N + 1)) := (summable_nat_add_iff 1).mpr summable_psi_tR
  have h := hs.sum_add_tsum_nat_add a
  have hS : S (-Real.goldenRatio) a = -∑ i ∈ range a, psi tR (i + 1) := by
    rw [S]
    simp_rw [psi_neg_gold]
    rw [sum_neg_distrib, sum_Icc_eq_sum_range]
  rw [hS, XiR, ← h]
  ring

/-- `2(−φ)^a ψ_{M+a+1}(t) = 2 r_a t^{3(M+1)} / (1 − r_a w^{M+1})³`. -/
theorem two_gold_psi (a M : ℕ) :
    2 * (-Real.goldenRatio) ^ a * psi tR (M + a + 1) =
      2 * rr a * (tR ^ 3) ^ (M + 1) * (1 / (1 - rr a * (-tR ^ 2) ^ (M + 1)) ^ 3) := by
  have e1 : tR ^ (3 * (M + a + 1)) = (tR ^ 3) ^ a * (tR ^ 3) ^ (M + 1) := by
    rw [← pow_add, ← pow_mul]; ring_nf
  have e2 : (-tR ^ 2) ^ (M + a + 1) = rr a * (-tR ^ 2) ^ (M + 1) := by
    rw [rr, ← pow_add]; ring_nf
  have e3 : (-Real.goldenRatio) ^ a * (tR ^ 3) ^ a = rr a := by
    rw [← mul_pow, rr]
    congr 1
    linear_combination (-tR ^ 2) * tR_mul_gold
  rw [psi, e1, e2, ← e3]
  ring

/-- `1/(1 − x)³ = ∑_j C(j+2, 2) x^j`. -/
theorem inv_one_sub_cube {x : ℝ} (hx : |x| < 1) :
    1 / (1 - x) ^ 3 = ∑' j : ℕ, ((j + 2).choose 2 : ℝ) * x ^ j :=
  (tsum_choose_mul_geometric_of_norm_lt_one 2 (by rwa [Real.norm_eq_abs])).symm

theorem abs_rr_mul_q_lt (a M : ℕ) : |rr a * (-tR ^ 2) ^ (M + 1)| ≤ tR ^ 2 := by
  rw [abs_mul, abs_pow, abs_neg, abs_of_pos tR_sq_pos]
  calc |rr a| * (tR ^ 2) ^ (M + 1) ≤ 1 * tR ^ 2 := by
        gcongr
        · exact abs_rr_le_one a
        · exact pow_le_of_le_one tR_sq_pos.le tR_sq_lt_one.le (by omega)
    _ = tR ^ 2 := one_mul _

/-! ### The polynomial moments at `−φ` -/

theorem abs_nu_neg_gold (j : ℕ) :
    |nu (-Real.goldenRatio) j| ≤ ((j : ℝ) * ((j : ℝ) + 1)) * Real.goldenRatio ^ 2 := by
  set g := Real.goldenRatio with hgdef
  have hg1 : 1 < g := Real.one_lt_goldenRatio
  have hg0 : 0 < g := Real.goldenRatio_pos
  have hgsq : g ^ 2 = g + 1 := Real.goldenRatio_sq
  set α := alpha (-g) j with hαdef
  have hα : |α| = g * (g ^ 2) ^ j := by
    rw [hαdef, alpha, abs_mul, abs_pow, neg_neg, neg_sq, abs_neg, abs_of_pos hg0,
      abs_of_pos (by positivity : (0 : ℝ) < g ^ 2)]
  have hαg : g ≤ |α| := by
    rw [hα]; exact le_mul_of_one_le_right hg0.le (one_le_pow₀ (by nlinarith))
  have hd : |α| - 1 ≤ |1 - α| := by
    have := abs_sub_abs_le_abs_sub α 1
    rw [abs_one, abs_sub_comm] at this; linarith
  have hdpos : 0 < |1 - α| := by linarith
  have hjj : (0 : ℝ) ≤ (j : ℝ) * ((j : ℝ) + 1) := by positivity
  rw [nu, ← hαdef, mul_div_assoc, abs_mul, abs_div, abs_of_nonneg hjj]
  refine mul_le_mul_of_nonneg_left ?_ hjj
  rw [div_le_iff₀ hdpos]
  nlinarith

end FibZeta.Conj
