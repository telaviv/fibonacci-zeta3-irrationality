import FibZeta.Main

-- Adapted from uplift-universal-inc/qzeta_3-irrationality, lean/QZeta3/CauchyAtInfinity.lean,
-- lean/QZeta3/CauchyExterior.lean and lean/QZeta3/MomentDecay.lean (Apache-2.0, Lean formalisation by
-- F. Solomon Admasu). Changes: the Fibonacci Cauchy kernel `2ρⁿwⁿz/(z − wⁿ)³` (alternating weights and
-- poles), moments `ν_k` of `Defs.lean`, and the node values `𝓕(w^{−a}) = 2t^a(Ξ − S_a)`.

/-!
# The Cauchy transform `𝓕(z) = L(1/(z − s))` at infinity (PROOF §5)

`𝓕(z) = ∑_{n ≥ 1} ρⁿ · 2wⁿz/(z − wⁿ)³` with `ρ = −t`, `w = −t²`.

* `cauchyF_inv_eq` : `𝓕(1/u) = u ∑_k ν_k u^k` for `0 < |u| < 1`;
* `meromorphicAt_cauchyF_inv` : `u ↦ 𝓕(1/u)` is meromorphic (indeed analytic) at `0`;
* `analyticAt_cauchyF_of_one_lt_abs` : `𝓕` is analytic at every `|z| > 1`;
* `tendsto_cauchyF_monomial_sub` : `𝓕(z) z^k − ∑_{j<k} ν_j z^{k−1−j} → 0` as `z → +∞`;
* `cauchyF_node` : `𝓕(x_a) = 2 t^a (Ξ − S_a)` at `x_a = w^{−a}` (the pole moments of Lemma 1(ii)).
-/

open Filter Topology Finset
open scoped ENNReal NNReal

namespace FibZeta.NonVan

/-! ### Elementary facts about `t`, `ρ = −t`, `w = −t²` -/

theorem tsq_pos : 0 < tR ^ 2 := pow_pos tR_pos 2

theorem tsq_lt_one : tR ^ 2 < 1 := pow_lt_one₀ tR_pos.le tR_lt_one (by norm_num)

theorem norm_tsq_lt_one : ‖tR ^ 2‖ < 1 := by
  rw [Real.norm_eq_abs, abs_of_pos tsq_pos]; exact tsq_lt_one

theorem abs_w_pow (m : ℕ) : |(-tR ^ 2) ^ m| = (tR ^ 2) ^ m := by
  rw [abs_pow, abs_neg, abs_of_pos tsq_pos]

theorem abs_rho_pow (m : ℕ) : |(-tR) ^ m| = tR ^ m := by
  rw [abs_pow, abs_neg, abs_of_pos tR_pos]

theorem w_ne_zero : (-tR ^ 2 : ℝ) ≠ 0 := neg_ne_zero.mpr tsq_pos.ne'

theorem w_pow_ne_zero (m : ℕ) : (-tR ^ 2 : ℝ) ^ m ≠ 0 := pow_ne_zero _ w_ne_zero

theorem rho_mul_w_pow (m : ℕ) : (-tR) ^ m * (-tR ^ 2) ^ m = (tR ^ 3) ^ m := by
  rw [← mul_pow]; congr 1; ring

theorem tsq_pow_le_tsq {m : ℕ} (hm : 1 ≤ m) : (tR ^ 2) ^ m ≤ tR ^ 2 := by
  simpa using pow_le_pow_of_le_one tsq_pos.le tsq_lt_one.le hm

theorem tsq_pow_lt_one {m : ℕ} (hm : 1 ≤ m) : (tR ^ 2) ^ m < 1 :=
  lt_of_le_of_lt (tsq_pow_le_tsq hm) tsq_lt_one

/-! ### The moments `ν_k` -/

theorem abs_alpha (k : ℕ) : |alpha tR k| = tR * (tR ^ 2) ^ k := by
  unfold alpha; rw [abs_mul, abs_neg, abs_of_pos tR_pos, abs_w_pow]

theorem abs_alpha_le_t (k : ℕ) : |alpha tR k| ≤ tR := by
  rw [abs_alpha]
  exact mul_le_of_le_one_right tR_pos.le (pow_le_one₀ tsq_pos.le tsq_lt_one.le)

theorem abs_alpha_le_pow (k : ℕ) : |alpha tR k| ≤ (tR ^ 2) ^ k := by
  rw [abs_alpha]
  exact mul_le_of_le_one_left (by positivity) tR_lt_one.le

theorem norm_alpha_lt_one (k : ℕ) : ‖alpha tR k‖ < 1 := by
  rw [Real.norm_eq_abs]; exact lt_of_le_of_lt (abs_alpha_le_t k) tR_lt_one

theorem one_sub_t_le_abs (k : ℕ) : 1 - tR ≤ |1 - alpha tR k| := by
  have h1 := abs_alpha_le_t k
  have h2 := abs_sub_abs_le_abs_sub (1 : ℝ) (alpha tR k)
  rw [abs_one] at h2
  linarith

theorem one_sub_alpha_ne (k : ℕ) : 1 - alpha tR k ≠ 0 := by
  intro h
  have := one_sub_t_le_abs k
  rw [h, abs_zero] at this
  linarith [tR_lt_one]

theorem abs_nu_le (k : ℕ) : |nu tR k| ≤ 2 / (1 - tR) * ((k : ℝ) ^ 2 * (tR ^ 2) ^ k) := by
  have ht1 : 0 < 1 - tR := by linarith [tR_lt_one]
  have hk : ((k * (k + 1) : ℕ) : ℝ) ≤ ((2 * k ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast (by nlinarith : k * (k + 1) ≤ 2 * k ^ 2)
  push_cast at hk
  unfold nu
  rw [abs_div, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ) * ((k : ℝ) + 1))]
  rw [div_le_iff₀ (lt_of_lt_of_le ht1 (one_sub_t_le_abs k))]
  have h1 := abs_alpha_le_pow k
  have h2 := one_sub_t_le_abs k
  have h3 : (0 : ℝ) ≤ (tR ^ 2) ^ k := by positivity
  calc (k : ℝ) * ((k : ℝ) + 1) * |alpha tR k| ≤ (2 * (k : ℝ) ^ 2) * (tR ^ 2) ^ k :=
        mul_le_mul hk h1 (abs_nonneg _) (by positivity)
    _ = 2 / (1 - tR) * ((k : ℝ) ^ 2 * (tR ^ 2) ^ k) * (1 - tR) := by field_simp
    _ ≤ 2 / (1 - tR) * ((k : ℝ) ^ 2 * (tR ^ 2) ^ k) * |1 - alpha tR k| :=
        mul_le_mul_of_nonneg_left h2 (by positivity)

theorem summable_abs_nu : Summable (fun k : ℕ => |nu tR k|) :=
  Summable.of_nonneg_of_le (fun _ => abs_nonneg _) abs_nu_le
    ((summable_pow_mul_geometric_of_norm_lt_one 2 norm_tsq_lt_one).mul_left _)

theorem summable_nu_mul_pow {u : ℝ} (hu : ‖u‖ < 1) : Summable (fun k : ℕ => nu tR k * u ^ k) := by
  apply Summable.of_norm_bounded summable_abs_nu
  intro k
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  exact mul_le_of_le_one_right (abs_nonneg _)
    (pow_le_one₀ (abs_nonneg _) (by simpa [Real.norm_eq_abs] using hu.le))

/-- The shifted moment power series `∑_n ν_{n+k} u^n`. -/
noncomputable def momentSeries (k : ℕ) : FormalMultilinearSeries ℝ ℝ ℝ :=
  FormalMultilinearSeries.ofScalars ℝ (fun n => nu tR (n + k))

theorem momentSeries_radius_ge_one (k : ℕ) : (1 : ℝ≥0∞) ≤ (momentSeries k).radius := by
  apply (momentSeries k).le_radius_of_summable (r := 1)
  simpa [momentSeries, FormalMultilinearSeries.ofScalars_norm, Real.norm_eq_abs] using
    (summable_nat_add_iff k).mpr summable_abs_nu

theorem analyticAt_moment (k : ℕ) {u : ℝ} (hu : ‖u‖ < 1) :
    AnalyticAt ℝ (fun v : ℝ => ∑' n : ℕ, nu tR (n + k) * v ^ n) u := by
  have huR : u ∈ Metric.eball (0 : ℝ) (momentSeries k).radius := by
    apply mem_eball_zero_iff.mpr
    apply lt_of_lt_of_le _ (momentSeries_radius_ge_one k)
    exact ENNReal.coe_lt_coe.mpr hu
  have h := (momentSeries k).analyticOnNhd u huR
  convert h using 1
  ext v
  simpa [momentSeries, FormalMultilinearSeries.ofScalarsSum, smul_eq_mul] using
    (FormalMultilinearSeries.ofScalars_sum_eq (fun n => nu tR (n + k)) v).symm

/-! ### The Cauchy transform -/

/-- The `n`-th kernel `2ρ^{n+1}w^{n+1}z/(z − w^{n+1})³`. -/
noncomputable def kern (n : ℕ) (z : ℝ) : ℝ :=
  2 * (-tR) ^ (n + 1) * (-tR ^ 2) ^ (n + 1) * z / (z - (-tR ^ 2) ^ (n + 1)) ^ 3

/-- `𝓕(z) = L(1/(z − s)) = ∑_{n ≥ 1} ρⁿ · 2wⁿz/(z − wⁿ)³`. -/
noncomputable def cauchyF (z : ℝ) : ℝ := ∑' n : ℕ, kern n z

theorem hasSum_kk1_geometric {y : ℝ} (hy : ‖y‖ < 1) :
    HasSum (fun k : ℕ => (k : ℝ) * ((k : ℝ) + 1) * y ^ k) (2 * y / (1 - y) ^ 3) := by
  have h1 := hasSum_sq_mul_geometric_of_norm_lt_one hy
  have h2 := hasSum_coe_mul_geometric_of_norm_lt_one hy
  have hy1 : 1 - y ≠ 0 := by
    intro h
    have : y = 1 := by linarith
    rw [this, norm_one] at hy
    exact lt_irrefl _ hy
  convert h1.add h2 using 1
  · funext k; ring
  · field_simp; ring

/-- `𝓕(1/u) = u ∑_k ν_k u^k` for `0 < |u| < 1`. -/
theorem cauchyF_inv_eq {u : ℝ} (hu : ‖u‖ < 1) (hu0 : u ≠ 0) :
    cauchyF u⁻¹ = u * ∑' k : ℕ, nu tR k * u ^ k := by
  have hu' : |u| < 1 := by simpa [Real.norm_eq_abs] using hu
  let f : ℕ × ℕ → ℝ := fun nk =>
    (nk.2 : ℝ) * ((nk.2 : ℝ) + 1) * (alpha tR nk.2) ^ (nk.1 + 1) * u ^ (nk.2 + 1)
  have hf : Summable f := by
    have hg : Summable (fun n : ℕ => tR ^ (n + 1)) :=
      (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one tR_pos.le tR_lt_one)
    have hh : Summable (fun k : ℕ => (k : ℝ) * ((k : ℝ) + 1) * (tR ^ 2) ^ k) := by
      have := ((summable_pow_mul_geometric_of_norm_lt_one 2 norm_tsq_lt_one).add
        (summable_pow_mul_geometric_of_norm_lt_one 1 norm_tsq_lt_one))
      convert this using 1
      funext k; ring
    apply Summable.of_norm_bounded (hg.mul_of_nonneg hh (fun n => (pow_pos tR_pos _).le)
      (fun k => mul_nonneg (by positivity) (pow_nonneg tsq_pos.le _)))
    rintro ⟨n, k⟩
    simp only [f, Real.norm_eq_abs, abs_mul, abs_pow]
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ)),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1), abs_alpha]
    have hupow : |u| ^ (k + 1) ≤ 1 := pow_le_one₀ (abs_nonneg _) hu'.le
    have hpow : (tR * (tR ^ 2) ^ k) ^ (n + 1) ≤ tR ^ (n + 1) * (tR ^ 2) ^ k := by
      rw [mul_pow]
      apply mul_le_mul_of_nonneg_left _ (pow_pos tR_pos _).le
      rw [← pow_mul]
      exact pow_le_pow_of_le_one tsq_pos.le tsq_lt_one.le (by nlinarith)
    calc (k : ℝ) * ((k : ℝ) + 1) * (tR * (tR ^ 2) ^ k) ^ (n + 1) * |u| ^ (k + 1)
        ≤ (k : ℝ) * ((k : ℝ) + 1) * (tR ^ (n + 1) * (tR ^ 2) ^ k) * 1 := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hpow (by positivity)) hupow
            (by positivity)
            (mul_nonneg (by positivity) (mul_nonneg (pow_pos tR_pos _).le (pow_nonneg tsq_pos.le _)))
      _ = tR ^ (n + 1) * ((k : ℝ) * ((k : ℝ) + 1) * (tR ^ 2) ^ k) := by ring
  have hrow : ∀ n : ℕ, ∑' k : ℕ, f (n, k) = kern n u⁻¹ := by
    intro n
    let y : ℝ := (-tR ^ 2) ^ (n + 1) * u
    have hy : ‖y‖ < 1 := by
      rw [Real.norm_eq_abs, abs_mul, abs_w_pow]
      calc (tR ^ 2) ^ (n + 1) * |u| < 1 * 1 := by
            apply mul_lt_mul' (tsq_pow_lt_one (by omega)).le hu' (abs_nonneg _) one_pos
        _ = 1 := by ring
    have hs := (hasSum_kk1_geometric hy).mul_left ((-tR) ^ (n + 1) * u)
    have heq : (fun k : ℕ => (-tR) ^ (n + 1) * u * ((k : ℝ) * ((k : ℝ) + 1) * y ^ k)) =
        fun k => f (n, k) := by
      funext k
      simp only [f, alpha, y]
      rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm k (n + 1)]
      ring
    rw [heq] at hs
    rw [hs.tsum_eq]
    have hy1 : 1 - y ≠ 0 := by
      intro h
      have : y = 1 := by linarith
      rw [this, norm_one] at hy
      exact lt_irrefl _ hy
    have hz : u⁻¹ - (-tR ^ 2) ^ (n + 1) ≠ 0 := by
      intro h
      apply hy1
      have : (-tR ^ 2) ^ (n + 1) = u⁻¹ := (sub_eq_zero.mp h).symm
      simp only [y, this, inv_mul_cancel₀ hu0, sub_self]
    unfold kern
    have hyu : u⁻¹ - (-tR ^ 2) ^ (n + 1) = u⁻¹ * (1 - y) := by
      simp only [y]; field_simp
    rw [hyu, mul_pow, inv_pow]
    simp only [y]
    field_simp
  have hcol : ∀ k : ℕ, ∑' n : ℕ, f (n, k) = nu tR k * u ^ (k + 1) := by
    intro k
    have hs := hasSum_geometric_of_norm_lt_one (norm_alpha_lt_one k)
    have hs' : HasSum (fun n : ℕ => alpha tR k ^ (n + 1)) (alpha tR k / (1 - alpha tR k)) := by
      have := hs.mul_left (alpha tR k)
      convert this using 1
      · funext n; ring
      · field_simp [one_sub_alpha_ne k]
    have := hs'.mul_left ((k : ℝ) * ((k : ℝ) + 1)) |>.mul_right (u ^ (k + 1))
    rw [show (fun n : ℕ => f (n, k)) = fun n => (k : ℝ) * ((k : ℝ) + 1) * alpha tR k ^ (n + 1) *
      u ^ (k + 1) from rfl, this.tsum_eq]
    unfold nu
    ring
  calc cauchyF u⁻¹ = ∑' n : ℕ, ∑' k : ℕ, f (n, k) := by
        unfold cauchyF; exact tsum_congr (fun n => (hrow n).symm)
    _ = ∑' k : ℕ, ∑' n : ℕ, f (n, k) := (Summable.tsum_comm (f := fun n k => f (n, k)) hf).symm
    _ = ∑' k : ℕ, nu tR k * u ^ (k + 1) := tsum_congr hcol
    _ = u * ∑' k : ℕ, nu tR k * u ^ k := by
        rw [← tsum_mul_left]; congr 1; funext k; ring

theorem meromorphicAt_cauchyF_inv : MeromorphicAt (fun u : ℝ => cauchyF u⁻¹) 0 := by
  have h : AnalyticAt ℝ (fun u : ℝ => u * ∑' n : ℕ, nu tR (n + 0) * u ^ n) 0 :=
    analyticAt_id.mul (analyticAt_moment 0 (by simp))
  apply h.meromorphicAt.congr
  have hn : ∀ᶠ u : ℝ in 𝓝 (0 : ℝ), ‖u‖ < 1 :=
    continuous_norm.continuousAt.eventually_lt continuousAt_const (by norm_num)
  filter_upwards [hn.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with u hu hu0
  simpa using (cauchyF_inv_eq hu (by simpa using hu0)).symm

theorem analyticAt_cauchyF_of_one_lt_abs {z : ℝ} (hz : 1 < |z|) : AnalyticAt ℝ cauchyF z := by
  have hz0 : z ≠ 0 := by intro h; rw [h, abs_zero] at hz; linarith
  have hinv : ‖z⁻¹‖ < 1 := by
    rw [Real.norm_eq_abs, abs_inv]; exact inv_lt_one_of_one_lt₀ hz
  have hi : AnalyticAt ℝ (fun w : ℝ => w⁻¹) z := analyticAt_id.inv hz0
  have h := hi.mul ((analyticAt_moment 0 hinv).comp hi)
  apply h.congr
  have hn : ∀ᶠ w : ℝ in 𝓝 z, 1 < |w| :=
    continuousAt_const.eventually_lt continuous_abs.continuousAt hz
  filter_upwards [hn] with w hw
  have hw0 : w ≠ 0 := by intro h; rw [h, abs_zero] at hw; linarith
  have hwinv : ‖w⁻¹‖ < 1 := by
    rw [Real.norm_eq_abs, abs_inv]; exact inv_lt_one_of_one_lt₀ hw
  simpa using (cauchyF_inv_eq hwinv (inv_ne_zero hw0)).symm

/-! ### Polynomial part at infinity (from `MomentDecay.lean`) -/

/-- `∑_{j<k} ν_j z^{k−1−j}`, the polynomial part of `𝓕(z) z^k`. -/
noncomputable def momentPolynomial (k : ℕ) (z : ℝ) : ℝ :=
  ∑ j ∈ range k, nu tR j * z ^ (k - 1 - j)

theorem cauchyF_remainder {u : ℝ} (hu : ‖u‖ < 1) (hu0 : u ≠ 0) (k : ℕ) :
    cauchyF u⁻¹ * (u⁻¹) ^ k - momentPolynomial k u⁻¹ =
      u * ∑' n : ℕ, nu tR (n + k) * u ^ n := by
  have hsplit := (summable_nu_mul_pow hu).sum_add_tsum_nat_add k
  have htail : (∑' n : ℕ, nu tR (n + k) * u ^ (n + k)) =
      u ^ k * ∑' n : ℕ, nu tR (n + k) * u ^ n := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    rw [pow_add]
    ring
  rw [htail] at hsplit
  have hpoly : u ^ k * momentPolynomial k u⁻¹ =
      u * ∑ j ∈ range k, nu tR j * u ^ j := by
    unfold momentPolynomial
    rw [mul_sum, mul_sum]
    apply sum_congr rfl
    intro j hj
    have hjk : j < k := mem_range.mp hj
    have he : k = (k - 1 - j) + (j + 1) := by omega
    have hpow : u ^ k = u ^ (k - 1 - j) * u ^ (j + 1) := by rw [← pow_add, ← he]
    have hc : u ^ (k - 1 - j) * (u⁻¹) ^ (k - 1 - j) = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hu0, one_pow]
    calc u ^ k * (nu tR j * (u⁻¹) ^ (k - 1 - j)) =
        nu tR j * u ^ (j + 1) * (u ^ (k - 1 - j) * (u⁻¹) ^ (k - 1 - j)) := by rw [hpow]; ring
      _ = u * (nu tR j * u ^ j) := by rw [hc, pow_succ]; ring
  apply (mul_left_cancel₀ (pow_ne_zero k hu0))
  rw [mul_sub, hpoly, cauchyF_inv_eq hu hu0]
  have hinv : u ^ k * (u⁻¹) ^ k = 1 := by rw [← mul_pow, mul_inv_cancel₀ hu0, one_pow]
  calc u ^ k * ((u * ∑' n : ℕ, nu tR n * u ^ n) * (u⁻¹) ^ k) -
          u * ∑ j ∈ range k, nu tR j * u ^ j =
        u * (∑' n : ℕ, nu tR n * u ^ n) * (u ^ k * (u⁻¹) ^ k) -
          u * ∑ j ∈ range k, nu tR j * u ^ j := by ring
    _ = _ := by rw [hinv, ← hsplit]; ring

theorem tendsto_cauchyF_monomial_sub (k : ℕ) :
    Tendsto (fun z : ℝ => cauchyF z * z ^ k - momentPolynomial k z) atTop (𝓝 0) := by
  have htail := (analyticAt_moment k (by simp)).continuousAt.tendsto.comp
    (tendsto_inv_atTop_zero : Tendsto (fun z : ℝ => z⁻¹) atTop (𝓝 0))
  have hprod := (tendsto_inv_atTop_zero : Tendsto (fun z : ℝ => z⁻¹) atTop (𝓝 0)).mul htail
  simp only [zero_mul] at hprod
  apply hprod.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with z hz
  have hz0 : z ≠ 0 := by linarith
  have hzinv : ‖z⁻¹‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (by linarith))]
    exact inv_lt_one_of_one_lt₀ hz
  simpa using (cauchyF_remainder hzinv (inv_ne_zero hz0) k).symm

/-! ### Values at the interpolation nodes -/

theorem abs_psi_le (N : ℕ) (hN : 1 ≤ N) : |psi tR N| ≤ (tR ^ 3) ^ N / (1 - tR ^ 2) ^ 3 := by
  unfold psi
  have h1 : 0 < 1 - tR ^ 2 := by linarith [tsq_lt_one]
  have h2 : 1 - tR ^ 2 ≤ |1 - (-tR ^ 2) ^ N| := by
    have := abs_sub_abs_le_abs_sub (1 : ℝ) ((-tR ^ 2) ^ N)
    rw [abs_one, abs_w_pow] at this
    linarith [tsq_pow_le_tsq hN]
  rw [abs_div, abs_pow, abs_pow, abs_of_pos tR_pos, ← pow_mul]
  apply div_le_div₀ (pow_pos tR_pos _).le le_rfl (pow_pos h1 3)
  exact pow_le_pow_left₀ h1.le h2 3

theorem summable_psi_succ : Summable (fun N : ℕ => psi tR (N + 1)) := by
  have hg : Summable (fun N : ℕ => (tR ^ 3) ^ (N + 1) / (1 - tR ^ 2) ^ 3) := by
    apply Summable.div_const
    exact (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (pow_pos tR_pos 3).le
      (pow_lt_one₀ tR_pos.le tR_lt_one (by norm_num)))
  exact Summable.of_norm_bounded hg (fun N => by
    rw [Real.norm_eq_abs]; exact abs_psi_le (N + 1) (by omega))

theorem S_eq_sum_range (a : ℕ) : S tR a = ∑ i ∈ range a, psi tR (i + 1) := by
  induction a with
  | zero => simp [S]
  | succ a ih =>
      rw [sum_range_succ, ← ih, S, S, Finset.sum_Icc_succ_top (by omega)]

theorem kern_node (n a : ℕ) :
    kern n (node tR a) = 2 * tR ^ a * psi tR (n + a + 1) := by
  unfold kern node psi
  have hVW : (-tR ^ 2) ^ (n + a + 1) = (-tR ^ 2) ^ (n + 1) * (-tR ^ 2) ^ a := by
    rw [← pow_add]; congr 1; omega
  set W : ℝ := (-tR ^ 2) ^ a with hW
  set V : ℝ := (-tR ^ 2) ^ (n + 1) with hV
  have hW0 : W ≠ 0 := w_pow_ne_zero a
  have h1 : 1 - V * W ≠ 0 := by
    rw [← hVW]; intro h
    have h' : |(-tR ^ 2) ^ (n + a + 1)| = 1 := by rw [← sub_eq_zero.mp h, abs_one]
    rw [abs_w_pow] at h'
    linarith [tsq_pow_lt_one (show 1 ≤ n + a + 1 by omega)]
  have hden : W⁻¹ - V = W⁻¹ * (1 - V * W) := by field_simp
  rw [hden, hVW]
  have hrw : (-tR) ^ (n + 1) * V = (tR ^ 3) ^ (n + 1) := rho_mul_w_pow (n + 1)
  have hW2 : W ^ 2 = (tR ^ 4) ^ a := by
    rw [hW, ← pow_mul, mul_comm, pow_mul]; congr 1; ring
  have hpow : tR ^ (3 * (n + a + 1)) = (tR ^ 3) ^ (n + 1) * tR ^ (3 * a) := by
    rw [← pow_mul, ← pow_add]; congr 1; ring
  have h4 : (tR ^ 4) ^ a = tR ^ a * tR ^ (3 * a) := by
    rw [← pow_mul, ← pow_add]; congr 1; ring
  have key : (-tR) ^ (n + 1) * V * W ^ 2 = tR ^ a * tR ^ (3 * (n + a + 1)) := by
    rw [hrw, hW2, h4, hpow]; ring
  have hL : 2 * (-tR) ^ (n + 1) * V * W⁻¹ / (W⁻¹ * (1 - V * W)) ^ 3 =
      2 * ((-tR) ^ (n + 1) * V * W ^ 2) / (1 - V * W) ^ 3 := by
    field_simp
  rw [hL, key]
  ring

/-- `𝓕(x_a) = 2t^a(Ξ − S_a)` (Lemma 1(ii) in the form `L(1/(x_a − s))`). -/
theorem cauchyF_node (a : ℕ) : cauchyF (node tR a) = 2 * tR ^ a * (XiR - S tR a) := by
  have hsplit := summable_psi_succ.sum_add_tsum_nat_add a
  unfold cauchyF
  simp_rw [kern_node]
  rw [tsum_mul_left, S_eq_sum_range, XiR, ← hsplit]
  ring

end FibZeta.NonVan
