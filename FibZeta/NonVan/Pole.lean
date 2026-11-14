import FibZeta.NonVan.Cauchy

-- Adapted from uplift-universal-inc/qzeta_3-irrationality, lean/QZeta3/CauchyPole.lean,
-- lean/QZeta3/CauchyMeromorphic.lean and lean/QZeta3/CauchyNonrational.lean (Apache-2.0, Lean
-- formalisation by F. Solomon Admasu). Changes: Fibonacci kernel with alternating poles `w^{n+1}`;
-- summability for `|z| ≥ 1`; the rational-germ exclusion uses the positive poles `w^{2j+2}` only.

/-!
# Poles of the Cauchy transform; `𝓕` is not rational (PROOF §5)

* `cauchyF_split` : finite head plus rescaled tail `ρ^N w^{−N} 𝓕(z/w^N)`;
* `cauchyF_cubic_pole` : `(z − w^{m+1})³ 𝓕(z) → 2ρ^{m+1}w^{2(m+1)} ≠ 0`;
* `meromorphicOn_cauchyF_pos` : `𝓕` is meromorphic on `(0, ∞)`;
* `cauchyF_nonrational` : `𝓕 Q − P` is not eventually `0` at `+∞` unless `Q = 0`.
-/

open Filter Topology Finset Polynomial

namespace FibZeta.NonVan

theorem abs_kern_le (n : ℕ) {z : ℝ} (hz : 1 ≤ |z|) :
    |kern n z| ≤ 2 * (tR ^ 3) ^ (n + 1) / (1 - tR ^ 2) ^ 3 := by
  have h1 : 0 < 1 - tR ^ 2 := by linarith [tsq_lt_one]
  have hV : |(-tR ^ 2) ^ (n + 1)| ≤ tR ^ 2 := by
    rw [abs_w_pow]; exact tsq_pow_le_tsq (by omega)
  have hz0 : 0 < |z| := by linarith
  have hd : (1 - tR ^ 2) * |z| ≤ |z - (-tR ^ 2) ^ (n + 1)| := by
    have := abs_sub_abs_le_abs_sub z ((-tR ^ 2) ^ (n + 1))
    nlinarith [tsq_pos]
  have hd0 : 0 < (1 - tR ^ 2) * |z| := mul_pos h1 hz0
  unfold kern
  rw [abs_div, abs_mul, abs_mul, abs_mul, abs_two, abs_rho_pow, abs_w_pow,
    abs_pow (z - _) 3, mul_assoc 2, ← mul_pow, show tR * tR ^ 2 = tR ^ 3 by ring]
  rw [div_le_div_iff₀ (pow_pos (lt_of_lt_of_le hd0 hd) 3) (pow_pos h1 3)]
  have hA : 0 ≤ 2 * (tR ^ 3) ^ (n + 1) := mul_nonneg (by norm_num) (pow_pos (pow_pos tR_pos 3) _).le
  have hz3 : |z| * (1 - tR ^ 2) ^ 3 ≤ |z - (-tR ^ 2) ^ (n + 1)| ^ 3 := by
    have h3 := pow_le_pow_left₀ hd0.le hd 3
    have hz13 : |z| ≤ |z| ^ 3 := by
      calc |z| = |z| * 1 * 1 := by ring
        _ ≤ |z| * |z| * |z| := by gcongr
        _ = |z| ^ 3 := by ring
    calc |z| * (1 - tR ^ 2) ^ 3 ≤ |z| ^ 3 * (1 - tR ^ 2) ^ 3 :=
          mul_le_mul_of_nonneg_right hz13 (pow_pos h1 3).le
      _ = ((1 - tR ^ 2) * |z|) ^ 3 := by ring
      _ ≤ _ := h3
  calc 2 * (tR ^ 3) ^ (n + 1) * |z| * (1 - tR ^ 2) ^ 3
      = 2 * (tR ^ 3) ^ (n + 1) * (|z| * (1 - tR ^ 2) ^ 3) := by ring
    _ ≤ 2 * (tR ^ 3) ^ (n + 1) * |z - (-tR ^ 2) ^ (n + 1)| ^ 3 :=
        mul_le_mul_of_nonneg_left hz3 hA

theorem summable_kern {z : ℝ} (hz : 1 ≤ |z|) : Summable (fun n : ℕ => kern n z) := by
  have hg : Summable (fun n : ℕ => 2 * (tR ^ 3) ^ (n + 1) / (1 - tR ^ 2) ^ 3) := by
    apply Summable.div_const
    apply Summable.mul_left
    exact (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (pow_pos tR_pos 3).le
      (pow_lt_one₀ tR_pos.le tR_lt_one (by norm_num)))
  exact Summable.of_norm_bounded hg (fun n => by rw [Real.norm_eq_abs]; exact abs_kern_le n hz)

/-- Removing finitely many poles leaves a rescaled copy of the same transform. -/
theorem kern_shift (N n : ℕ) (z : ℝ) :
    kern (n + N) z = (-tR) ^ N * ((-tR ^ 2) ^ N)⁻¹ * kern n (z / (-tR ^ 2) ^ N) := by
  have hT : ((-tR ^ 2) ^ N : ℝ) ≠ 0 := w_pow_ne_zero N
  set T : ℝ := (-tR ^ 2) ^ N with hTdef
  have hpow : (-tR ^ 2) ^ (n + N + 1) = T * (-tR ^ 2) ^ (n + 1) := by
    rw [hTdef, ← pow_add]; congr 1; omega
  have hrho : (-tR) ^ (n + N + 1) = (-tR) ^ N * (-tR) ^ (n + 1) := by
    rw [← pow_add]; congr 1; omega
  unfold kern
  rw [hpow, hrho]
  have hminus : z - T * (-tR ^ 2) ^ (n + 1) = T * (z / T - (-tR ^ 2) ^ (n + 1)) := by
    field_simp
  rw [hminus, mul_pow]
  by_cases hza : z / T - (-tR ^ 2) ^ (n + 1) = 0
  · rw [hza]; simp
  field_simp

theorem cauchyF_tail_eq (N : ℕ) (z : ℝ) :
    (∑' n : ℕ, kern (n + N) z) =
      (-tR) ^ N * ((-tR ^ 2) ^ N)⁻¹ * cauchyF (z / (-tR ^ 2) ^ N) := by
  simp_rw [kern_shift N]
  rw [tsum_mul_left]
  rfl

/-- Exact finite head plus rescaled tail, assuming convergence of that tail. -/
theorem cauchyF_split (N : ℕ) (z : ℝ)
    (hs : Summable (fun n : ℕ => kern n (z / (-tR ^ 2) ^ N))) :
    cauchyF z = (∑ n ∈ range N, kern n z) +
      (-tR) ^ N * ((-tR ^ 2) ^ N)⁻¹ * cauchyF (z / (-tR ^ 2) ^ N) := by
  have htail : Summable (fun n : ℕ => kern (n + N) z) := by
    simp only [kern_shift N]
    exact hs.mul_left _
  have hall : Summable (fun n : ℕ => kern n z) :=
    (summable_nat_add_iff (f := fun n : ℕ => kern n z) N).mp htail
  have heq := hall.sum_add_tsum_nat_add N
  rw [cauchyF_tail_eq N z] at heq
  exact heq.symm

theorem w_pow_injective : Function.Injective (fun m : ℕ => (-tR ^ 2 : ℝ) ^ m) := by
  intro i j hij
  have h := congrArg abs hij
  simp only [abs_w_pow] at h
  exact pow_right_injective₀ tsq_pos (ne_of_lt tsq_lt_one) h

theorem continuousAt_kern {n : ℕ} {z : ℝ} (hz : z ≠ (-tR ^ 2) ^ (n + 1)) :
    ContinuousAt (kern n) z := by
  unfold kern
  exact (continuousAt_const.mul continuousAt_id).div
    ((continuousAt_id.sub continuousAt_const).pow 3) (pow_ne_zero 3 (sub_ne_zero.mpr hz))

/-- Every pole `w^{m+1}` is a genuine cubic pole, with nonzero leading coefficient. -/
theorem cauchyF_cubic_pole (m : ℕ) :
    Tendsto (fun z : ℝ => (z - (-tR ^ 2) ^ (m + 1)) ^ 3 * cauchyF z)
      (𝓝[≠] ((-tR ^ 2) ^ (m + 1)))
      (𝓝 (2 * (-tR) ^ (m + 1) * (-tR ^ 2) ^ (m + 1) * (-tR ^ 2) ^ (m + 1))) := by
  set r : ℝ := (-tR ^ 2) ^ (m + 1) with hr
  set T : ℝ := (-tR ^ 2) ^ (m + 2) with hT
  set c : ℝ := 2 * (-tR) ^ (m + 1) * r with hc
  let s := (range (m + 2)).erase m
  let R : ℝ → ℝ := fun z => (∑ n ∈ s, kern n z) + (-tR) ^ (m + 2) * T⁻¹ * cauchyF (z / T)
  have hT0 : T ≠ 0 := w_pow_ne_zero _
  have hscale : |r / T| = (tR ^ 2)⁻¹ := by
    rw [abs_div, hr, hT, abs_w_pow, abs_w_pow, pow_succ (tR ^ 2) (m + 1)]
    field_simp [(pow_pos tsq_pos (m + 1)).ne']
  have hgt : 1 < |r / T| := by
    rw [hscale]; exact one_lt_inv_iff₀.mpr ⟨tsq_pos, tsq_lt_one⟩
  have hhead : ContinuousAt (fun z => ∑ n ∈ s, kern n z) r := by
    apply tendsto_finsetSum
    intro n hn
    have hnm : n ≠ m := (mem_erase.mp hn).1
    apply continuousAt_kern
    intro heq
    exact hnm (by have := w_pow_injective heq; omega)
  have htail : ContinuousAt (fun z => (-tR) ^ (m + 2) * T⁻¹ * cauchyF (z / T)) r := by
    have hf : ContinuousAt cauchyF (r / T) :=
      (analyticAt_cauchyF_of_one_lt_abs hgt).continuousAt
    exact continuousAt_const.mul
      (hf.comp (f := fun z : ℝ => z / T) (x := r) (continuousAt_id.div_const T))
  have hR : ContinuousAt R r := hhead.add htail
  have hnear : ∀ᶠ z : ℝ in 𝓝 r, 1 < |z / T| :=
    continuousAt_const.eventually_lt
      ((continuous_abs.continuousAt).comp (f := fun z : ℝ => z / T) (continuousAt_id.div_const T))
      hgt
  have hsplit : ∀ᶠ z : ℝ in 𝓝 r, cauchyF z = kern m z + R z := by
    filter_upwards [hnear] with z hz
    rw [cauchyF_split (m + 2) z (summable_kern hz.le)]
    rw [← Finset.sum_erase_add (range (m + 2)) (fun n => kern n z) (a := m) (by simp)]
    dsimp [R, s, T]
    ring
  have hlim : Tendsto (fun z : ℝ => c * z + (z - r) ^ 3 * R z) (𝓝 r) (𝓝 (c * r)) := by
    have hcont : ContinuousAt (fun z : ℝ => c * z + (z - r) ^ 3 * R z) r :=
      (continuousAt_const.mul continuousAt_id).add
        (((continuousAt_id.sub continuousAt_const).pow 3).mul hR)
    convert hcont.tendsto using 1
    simp
  apply (hlim.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [hsplit.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hzr
  have hzr' : z - r ≠ 0 := sub_ne_zero.mpr hzr
  rw [hz]
  unfold kern
  rw [← hr]
  field_simp
  rw [hc]
  ring

/-- At every positive point, a finite rational head and a scaled analytic tail give a
meromorphic expression for the Cauchy transform. -/
theorem meromorphicOn_cauchyF_pos : MeromorphicOn cauchyF (Set.Ioi 0) := by
  intro z hz
  have hz0 : (0 : ℝ) < z := hz
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hz0 tsq_lt_one
  set T : ℝ := (-tR ^ 2) ^ N with hTdef
  have hT0 : T ≠ 0 := w_pow_ne_zero N
  have hTabs : |T| = (tR ^ 2) ^ N := abs_w_pow N
  have hTpos : 0 < |T| := abs_pos.mpr hT0
  have hzt : 1 < |z / T| := by
    rw [abs_div, abs_of_pos hz0, hTabs, one_lt_div (pow_pos tsq_pos N)]; exact hN
  have hhead : MeromorphicAt (fun y : ℝ => ∑ n ∈ Finset.range N, kern n y) z := by
    apply MeromorphicAt.fun_sum
    intro n _
    unfold kern
    exact ((MeromorphicAt.const _ z).mul (MeromorphicAt.id z)).div
      (((MeromorphicAt.id z).sub (MeromorphicAt.const _ z)).pow 3)
  have hscale : AnalyticAt ℝ (fun y : ℝ => y / T) z := analyticAt_id.div_const
  have htail : AnalyticAt ℝ (fun y : ℝ => (-tR) ^ N * T⁻¹ * cauchyF (y / T)) z :=
    analyticAt_const.mul ((analyticAt_cauchyF_of_one_lt_abs hzt).comp
      (f := fun y : ℝ => y / T) hscale)
  apply (hhead.add htail.meromorphicAt).congr
  have hn : ∀ᶠ y : ℝ in 𝓝 z, 1 < |y / T| :=
    continuousAt_const.eventually_lt
      ((continuous_abs.continuousAt).comp (f := fun y : ℝ => y / T) (continuousAt_id.div_const T))
      hzt
  filter_upwards [hn.filter_mono nhdsWithin_le_nhds] with y hy
  exact (cauchyF_split N y (summable_kern hy.le)).symm

/-- A meromorphic germ which vanishes at positive infinity vanishes near every positive point. -/
theorem meromorphicOn_Ioi_eventually_zero_of_atTop {f : ℝ → ℝ}
    (hf : MeromorphicOn f (Set.Ioi 0))
    (hzero : ∀ᶠ x : ℝ in atTop, f x = 0) {x : ℝ} (hx : 0 < x) :
    ∀ᶠ y : ℝ in 𝓝[≠] x, f y = 0 := by
  obtain ⟨A, hA⟩ := eventually_atTop.mp hzero
  let a := max A 0 + 1
  have ha : 0 < a := by dsimp [a]; linarith [le_max_right A 0]
  have hAa : A < a := by dsimp [a]; linarith [le_max_left A 0]
  have hlocal : ∀ᶠ y : ℝ in 𝓝[≠] a, f y = 0 := by
    have hn : ∀ᶠ y : ℝ in 𝓝 a, A < y := eventually_gt_nhds hAa
    filter_upwards [hn.filter_mono nhdsWithin_le_nhds] with y hy
    exact hA y (le_of_lt hy)
  apply meromorphicOrderAt_eq_top_iff.mp
  exact hf.meromorphicOrderAt_eq_top_of_isPreconnected isPreconnected_Ioi ha hx
    (meromorphicOrderAt_eq_top_iff.mpr hlocal)

theorem analyticAt_polynomial_eval (P : ℝ[X]) (x : ℝ) :
    AnalyticAt ℝ (fun y : ℝ => P.eval y) x := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      convert hP.add hQ using 1
      ext y
      simp
  | monomial n c =>
      convert (show AnalyticAt ℝ (fun _ : ℝ => c) x from analyticAt_const).mul
        (analyticAt_id.pow n) using 1
      ext y
      simp

/-- A nonzero cubic principal part forces every rational denominator to vanish
at its pole whenever the rational identity holds in the punctured germ. -/
theorem polynomial_root_of_cubic_pole {f : ℝ → ℝ} {a c : ℝ} (hc : c ≠ 0)
    (hpole : Tendsto (fun z : ℝ => (z - a) ^ 3 * f z) (𝓝[≠] a) (𝓝 c))
    (P Q : ℝ[X]) (heq : ∀ᶠ z : ℝ in 𝓝[≠] a, f z * Q.eval z - P.eval z = 0) :
    Q.eval a = 0 := by
  have hQ : Tendsto (fun z : ℝ => Q.eval z) (𝓝[≠] a) (𝓝 (Q.eval a)) :=
    (analyticAt_polynomial_eval Q a).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hP : Tendsto (fun z : ℝ => P.eval z) (𝓝[≠] a) (𝓝 (P.eval a)) :=
    (analyticAt_polynomial_eval P a).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hz : Tendsto (fun z : ℝ => (z - a) ^ 3) (𝓝[≠] a) (𝓝 0) := by
    convert ((tendsto_id.sub_const a).pow 3).mono_left nhdsWithin_le_nhds using 1 <;> simp
  have hlim : Tendsto (fun z : ℝ => (z - a) ^ 3 * (f z * Q.eval z - P.eval z))
      (𝓝[≠] a) (𝓝 (c * Q.eval a)) := by
    convert (hpole.mul hQ).sub (hz.mul hP) using 1
    · ext z
      ring
    · simp
  have hlim0 : Tendsto (fun z : ℝ => (z - a) ^ 3 * (f z * Q.eval z - P.eval z))
      (𝓝[≠] a) (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [heq] with z hz
    simp [hz]
  exact (mul_eq_zero.mp (tendsto_nhds_unique hlim hlim0)).resolve_left hc

/-- The positive poles `w^{2j+2} = t^{4j+4}`. -/
theorem w_pow_even_pos (j : ℕ) : 0 < (-tR ^ 2 : ℝ) ^ (2 * j + 2) := by
  rw [show 2 * j + 2 = 2 * (j + 1) by ring, pow_mul]
  exact pow_pos (by nlinarith [tsq_pos]) _

/-- `𝓕` has no rational germ at `+∞`. -/
theorem cauchyF_nonrational (P Q : ℝ[X]) (hQ : Q ≠ 0) :
    ¬ ∀ᶠ x : ℝ in atTop, cauchyF x * Q.eval x - P.eval x = 0 := by
  intro hzero
  apply hQ
  apply Q.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    (f := fun j : Fin (Q.natDegree + 1) => (-tR ^ 2 : ℝ) ^ (2 * j.val + 2))
  · intro i j hij
    have := w_pow_injective hij
    apply Fin.ext
    omega
  · intro j
    have herr : MeromorphicOn (fun x => cauchyF x * Q.eval x - P.eval x) (Set.Ioi 0) := by
      intro x hx
      exact ((meromorphicOn_cauchyF_pos x hx).mul (analyticAt_polynomial_eval Q x).meromorphicAt).sub
        (analyticAt_polynomial_eval P x).meromorphicAt
    have heq := meromorphicOn_Ioi_eventually_zero_of_atTop herr hzero (w_pow_even_pos j.val)
    have hc : (2 * (-tR) ^ (2 * j.val + 1 + 1) * (-tR ^ 2) ^ (2 * j.val + 1 + 1) *
        (-tR ^ 2) ^ (2 * j.val + 1 + 1) : ℝ) ≠ 0 := by
      have h1 : ((-tR) ^ (2 * j.val + 1 + 1) : ℝ) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr tR_pos.ne')
      have h2 := w_pow_ne_zero (2 * j.val + 1 + 1)
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero h1) h2) h2
    exact polynomial_root_of_cubic_pole hc (cauchyF_cubic_pole (2 * j.val + 1)) P Q heq
  · simp

end FibZeta.NonVan
