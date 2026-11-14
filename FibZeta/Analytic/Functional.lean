/-
Adapted from uplift-universal-inc/qzeta_3-irrationality, lean/QZeta3/Functional.lean and
lean/QZeta3/Purity.lean (Apache-2.0, Lean formalisation by F. Solomon Admasu). Changes: operator
θ² replaced by θ(θ+1) = s²∂² + 2s∂, positive lattice replaced by the alternating nodes (−t²)ⁿ with
weights (−t)ⁿ, moments rewritten for `FibZeta.nu` and `FibZeta.psi`.
-/
import FibZeta.Main

/-!
# The real functional: calculus of `θ(θ+1)` and the moments (PROOF §1, Lemma 1)

* `thetaOp_add`, `thetaOp_const_mul`, `thetaOp_sum`, `thetaOp_congr`: pointwise linearity of
  `θ(θ+1)` on functions `C²` at the point;
* `hasL_*`: the summed functional `∑ ρⁿ⁺¹ [θ(θ+1)h](wⁿ⁺¹)` is linear on `HasSum`s;
* `hasL_pow`: `L(s^k) = ν_k` (Lemma 1(i));
* `hasL_simplePole`: `L(1/(1 − w^a s)) = 2 ρ^{−a} (Ξ − S_a)` (Lemma 1(ii)).
-/

open Polynomial Finset Filter Topology

namespace FibZeta.Analytic

/-! ### Elementary facts about `t` -/

theorem tR_sq_pos : 0 < tR ^ 2 := pow_pos tR_pos 2

theorem tR_sq_lt_one : tR ^ 2 < 1 := pow_lt_one₀ tR_pos.le tR_lt_one (by norm_num)

theorem abs_w_pow (n : ℕ) : |(-tR ^ 2) ^ n| = tR ^ (2 * n) := by
  rw [abs_pow, abs_neg, abs_of_pos tR_sq_pos, pow_mul]

/-- The `n`-th node `wⁿ⁺¹ = (−t²)ⁿ⁺¹`. -/
noncomputable def pt (n : ℕ) : ℝ := (-tR ^ 2) ^ (n + 1)

theorem abs_pt_le (n : ℕ) : |pt n| ≤ tR ^ 2 := by
  rw [pt, abs_w_pow, pow_mul]
  calc (tR ^ 2) ^ (n + 1) ≤ (tR ^ 2) ^ 1 :=
        pow_le_pow_of_le_one tR_sq_pos.le tR_sq_lt_one.le (by omega)
    _ = tR ^ 2 := pow_one _

theorem abs_pt_lt_one (n : ℕ) : |pt n| < 1 := (abs_pt_le n).trans_lt tR_sq_lt_one

/-! ### The operator `θ(θ+1)` -/

theorem differentiableAt_deriv {f : ℝ → ℝ} {x : ℝ} (hf : ContDiffAt ℝ 2 f x) :
    DifferentiableAt ℝ (deriv f) x :=
  (hf.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)

theorem thetaOp_congr {f g : ℝ → ℝ} {x : ℝ} (h : f =ᶠ[𝓝 x] g) :
    thetaOp f x = thetaOp g x := by
  simp only [thetaOp, h.deriv.deriv_eq, h.deriv_eq]

theorem thetaOp_add {f g : ℝ → ℝ} {x : ℝ} (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    thetaOp (fun y => f y + g y) x = thetaOp f x + thetaOp g x := by
  have he : deriv (fun y => f y + g y) =ᶠ[𝓝 x] fun y => deriv f y + deriv g y := by
    filter_upwards [hf.eventually (by simp), hg.eventually (by simp)] with y hyf hyg
    exact deriv_fun_add (hyf.differentiableAt (by norm_num)) (hyg.differentiableAt (by norm_num))
  simp only [thetaOp, he.deriv_eq, he.eq_of_nhds]
  rw [deriv_fun_add (differentiableAt_deriv hf) (differentiableAt_deriv hg)]
  ring

theorem thetaOp_const_mul {f : ℝ → ℝ} {x : ℝ} (hf : ContDiffAt ℝ 2 f x) (c : ℝ) :
    thetaOp (fun y => c * f y) x = c * thetaOp f x := by
  have he : deriv (fun y => c * f y) =ᶠ[𝓝 x] fun y => c * deriv f y := by
    filter_upwards [hf.eventually (by simp)] with y hy
    exact deriv_const_mul c (hy.differentiableAt (by norm_num))
  simp only [thetaOp, he.deriv_eq, he.eq_of_nhds]
  rw [deriv_const_mul c (differentiableAt_deriv hf)]
  ring

theorem thetaOp_zero (x : ℝ) : thetaOp (fun _ => (0 : ℝ)) x = 0 := by
  simp [thetaOp]

theorem thetaOp_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ) {x : ℝ}
    (hf : ∀ i ∈ s, ContDiffAt ℝ 2 (f i) x) :
    thetaOp (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, thetaOp (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using thetaOp_zero x
  | @insert i s hi ih =>
    have hfi := hf i (mem_insert_self i s)
    have hfs : ∀ j ∈ s, ContDiffAt ℝ 2 (f j) x := fun j hj => hf j (mem_insert_of_mem hj)
    simp only [sum_insert hi]
    rw [thetaOp_add hfi (ContDiffAt.sum hfs), ih hfs]

/-! ### The summed functional -/

/-- The `n`-th term `ρⁿ⁺¹ [θ(θ+1)h](wⁿ⁺¹)` of `Lfun h`. -/
noncomputable def Lterm (h : ℝ → ℝ) (n : ℕ) : ℝ := (-tR) ^ (n + 1) * thetaOp h (pt n)

theorem Lfun_eq_tsum (h : ℝ → ℝ) : Lfun h = ∑' n, Lterm h n := rfl

/-- `h` is `C²` on the open unit interval, which contains every node. -/
def Good (h : ℝ → ℝ) : Prop := ∀ x : ℝ, |x| < 1 → ContDiffAt ℝ 2 h x

theorem hasL_congr {f g : ℝ → ℝ} {v : ℝ} (he : ∀ n, f =ᶠ[𝓝 (pt n)] g)
    (hs : HasSum (Lterm g) v) : HasSum (Lterm f) v := by
  apply hs.congr_fun
  intro n
  simp only [Lterm, thetaOp_congr (he n)]

theorem hasL_const_mul {f : ℝ → ℝ} {v : ℝ} (hf : Good f) (hs : HasSum (Lterm f) v) (c : ℝ) :
    HasSum (Lterm (fun y => c * f y)) (c * v) := by
  apply (hs.mul_left c).congr_fun
  intro n
  simp only [Lterm, thetaOp_const_mul (hf _ (abs_pt_lt_one n)) c]
  ring

theorem hasL_add {f g : ℝ → ℝ} {v u : ℝ} (hf : Good f) (hg : Good g)
    (hs : HasSum (Lterm f) v) (ht : HasSum (Lterm g) u) :
    HasSum (Lterm (fun y => f y + g y)) (v + u) := by
  apply (hs.add ht).congr_fun
  intro n
  simp only [Lterm, thetaOp_add (hf _ (abs_pt_lt_one n)) (hg _ (abs_pt_lt_one n))]
  ring

theorem hasL_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ) (v : ι → ℝ)
    (hf : ∀ i ∈ s, Good (f i)) (hs : ∀ i ∈ s, HasSum (Lterm (f i)) (v i)) :
    HasSum (Lterm (fun y => ∑ i ∈ s, f i y)) (∑ i ∈ s, v i) := by
  apply (hasSum_sum hs).congr_fun
  intro n
  simp only [Lterm, thetaOp_sum s f (fun i hi => hf i hi _ (abs_pt_lt_one n)), mul_sum]

theorem good_add {f g : ℝ → ℝ} (hf : Good f) (hg : Good g) : Good (fun y => f y + g y) :=
  fun x hx => (hf x hx).add (hg x hx)

theorem good_const_mul {f : ℝ → ℝ} (hf : Good f) (c : ℝ) : Good (fun y => c * f y) :=
  fun x hx => contDiffAt_const.mul (hf x hx)

theorem good_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ) (hf : ∀ i ∈ s, Good (f i)) :
    Good (fun y => ∑ i ∈ s, f i y) :=
  fun x hx => ContDiffAt.sum (fun i hi => hf i hi x hx)

/-! ### Monomials (Lemma 1(i)) -/

theorem thetaOp_pow (k : ℕ) (x : ℝ) :
    thetaOp (fun y => y ^ k) x = (k : ℝ) * (k + 1) * x ^ k := by
  have h1 : deriv (fun y : ℝ => y ^ k) = fun y => (k : ℝ) * y ^ (k - 1) := by
    funext y; exact deriv_pow_field k
  have h2 : deriv (fun y : ℝ => (k : ℝ) * y ^ (k - 1)) x =
      (k : ℝ) * (((k - 1 : ℕ) : ℝ) * x ^ (k - 1 - 1)) := by
    rw [deriv_const_mul _ (differentiableAt_pow _), deriv_pow_field]
  rw [thetaOp, h1, h2]
  rcases k with _ | _ | k
  · simp
  · norm_num
  · simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    ring

theorem good_pow (k : ℕ) : Good (fun y : ℝ => y ^ k) := fun _ _ => contDiffAt_id.pow k

theorem abs_alpha_lt_one (k : ℕ) : |alpha tR k| < 1 := by
  rw [alpha, abs_mul, abs_neg, abs_of_pos tR_pos, abs_w_pow]
  calc tR * tR ^ (2 * k) ≤ tR * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ tR_pos.le tR_lt_one.le) tR_pos.le
    _ < 1 := by rw [mul_one]; exact tR_lt_one

/-- `L(s^k) = ν_k`. -/
theorem hasL_pow (k : ℕ) : HasSum (Lterm (fun y => y ^ k)) (nu tR k) := by
  have hα := abs_alpha_lt_one k
  have hg := ((hasSum_geometric_of_abs_lt_one hα).mul_left
    ((k : ℝ) * (k + 1) * alpha tR k))
  have h1 : 1 - alpha tR k ≠ 0 := by
    have := (abs_lt.mp hα).2; linarith
  convert hg using 1
  · funext n
    simp only [Lterm, thetaOp_pow, pt, alpha]
    ring
  · rw [nu]; field_simp

/-- The polynomial part: `L(P) = Lpoly P`. -/
theorem hasL_poly (P : ℝ[X]) : HasSum (Lterm (fun y => P.eval y)) (Lpoly tR P) := by
  have he : (fun y => P.eval y) = fun y => ∑ j ∈ P.support, P.coeff j * y ^ j := by
    funext y; rw [eval_eq_sum, Polynomial.sum_def]
  rw [he, Lpoly]
  exact hasL_sum _ _ _ (fun j _ => good_const_mul (good_pow j) _)
    (fun j _ => hasL_const_mul (good_pow j) (hasL_pow j) _)

theorem good_poly (P : ℝ[X]) : Good (fun y => P.eval y) := by
  have he : (fun y => P.eval y) = fun y => ∑ j ∈ P.support, P.coeff j * y ^ j := by
    funext y; rw [eval_eq_sum, Polynomial.sum_def]
  rw [he]
  exact good_sum _ _ (fun j _ => good_const_mul (good_pow j) _)

/-! ### Simple poles (Lemma 1(ii)) -/

theorem thetaOp_inv_affine {c x : ℝ} (hx : 1 - c * x ≠ 0) :
    thetaOp (fun y => (1 - c * y)⁻¹) x = 2 * c * x / (1 - c * x) ^ 3 := by
  have hd : ∀ y, 1 - c * y ≠ 0 →
      HasDerivAt (fun y => (1 - c * y)⁻¹) (c / (1 - c * y) ^ 2) y := by
    intro y hy
    have h := (((hasDerivAt_id' y).const_mul c).const_sub (1 : ℝ)).fun_inv hy
    convert h using 1
    ring
  have hn : ∀ᶠ y in 𝓝 x, 1 - c * y ≠ 0 :=
    (continuous_const.sub (continuous_const.mul continuous_id)).continuousAt.eventually_ne hx
  have he : deriv (fun y => (1 - c * y)⁻¹) =ᶠ[𝓝 x] fun y => c / (1 - c * y) ^ 2 :=
    hn.mono fun y hy => (hd y hy).deriv
  have h2 : HasDerivAt (fun y => c / (1 - c * y) ^ 2) (2 * c ^ 2 / (1 - c * x) ^ 3) x := by
    have h := (hasDerivAt_const x c).fun_div
      ((((hasDerivAt_id' x).const_mul c).const_sub (1 : ℝ)).fun_pow 2)
      (pow_ne_zero 2 hx)
    convert h using 1
    field_simp
    ring
  rw [thetaOp, he.deriv_eq, h2.deriv, (hd x hx).deriv]
  field_simp
  ring

theorem one_sub_w_pow_ne_zero {N : ℕ} (hN : 0 < N) : 1 - (-tR ^ 2) ^ N ≠ 0 := by
  have h : |(-tR ^ 2) ^ N| < 1 := by
    rw [abs_w_pow, pow_mul]; exact pow_lt_one₀ tR_sq_pos.le tR_sq_lt_one (by omega)
  have := (abs_lt.mp h).2
  linarith

theorem abs_psi_le {N : ℕ} (hN : 0 < N) : |psi tR N| ≤ (tR ^ 3) ^ N / (1 - tR ^ 2) ^ 3 := by
  have hlow : 1 - tR ^ 2 ≤ |1 - (-tR ^ 2) ^ N| := by
    have h1 : |(-tR ^ 2) ^ N| ≤ tR ^ 2 := by
      rw [abs_w_pow, pow_mul]
      calc (tR ^ 2) ^ N ≤ (tR ^ 2) ^ 1 :=
            pow_le_pow_of_le_one tR_sq_pos.le tR_sq_lt_one.le (by omega)
        _ = tR ^ 2 := pow_one _
    have := abs_sub_abs_le_abs_sub 1 ((-tR ^ 2) ^ N)
    rw [abs_one] at this
    linarith
  have hpos : 0 < 1 - tR ^ 2 := by linarith [tR_sq_lt_one]
  rw [psi, abs_div, abs_pow, abs_pow, abs_of_pos tR_pos, ← pow_mul]
  exact div_le_div_of_nonneg_left (pow_nonneg tR_pos.le _) (pow_pos hpos 3)
    (pow_le_pow_left₀ hpos.le hlow 3)

theorem summable_psi : Summable (fun N : ℕ => psi tR (N + 1)) := by
  have hg : Summable (fun N : ℕ => (tR ^ 3) ^ (N + 1) / (1 - tR ^ 2) ^ 3) := by
    have h3 : tR ^ 3 < 1 := pow_lt_one₀ tR_pos.le tR_lt_one (by norm_num)
    have := (summable_geometric_of_lt_one (pow_nonneg tR_pos.le 3) h3).mul_left (tR ^ 3)
    refine (this.div_const ((1 - tR ^ 2) ^ 3)).congr fun N => ?_
    ring
  exact Summable.of_norm_bounded hg fun N => by
    rw [Real.norm_eq_abs]; exact abs_psi_le (by omega)

theorem hasSum_psi : HasSum (fun N : ℕ => psi tR (N + 1)) XiR := summable_psi.hasSum

theorem S_eq_sum_range (a : ℕ) : S tR a = ∑ i ∈ range a, psi tR (i + 1) := by
  induction a with
  | zero => simp [S]
  | succ a ih => rw [S, sum_Icc_succ_top (by omega), ← S, ih, sum_range_succ]

/-- `Ξ − S_a` is the tail of the series. -/
theorem hasSum_psi_tail (a : ℕ) :
    HasSum (fun n : ℕ => psi tR (n + 1 + a)) (XiR - S tR a) := by
  have hs : Summable (fun n : ℕ => psi tR (n + 1 + a)) := by
    have := (summable_nat_add_iff a).mpr summable_psi
    refine this.congr fun n => ?_
    congr 1; omega
  have h := summable_psi.sum_add_tsum_nat_add a
  have hS := S_eq_sum_range a
  convert hs.hasSum using 1
  rw [hS, XiR, ← h]
  have : (fun i : ℕ => psi tR (i + a + 1)) = fun n => psi tR (n + 1 + a) := by
    funext n; congr 1; omega
  rw [this]
  ring

theorem good_simplePole (c : ℝ) (hc : |c| ≤ 1) : Good (fun y => (1 - c * y)⁻¹) := by
  intro x hx
  have : |c * x| < 1 := by
    rw [abs_mul]
    calc |c| * |x| ≤ 1 * |x| := mul_le_mul_of_nonneg_right hc (abs_nonneg x)
      _ < 1 := by rw [one_mul]; exact hx
  have hne : 1 - c * x ≠ 0 := by have := (abs_lt.mp this).2; linarith
  exact (contDiffAt_const.sub (contDiffAt_const.mul contDiffAt_id)).inv hne

theorem abs_w_pow_le_one (a : ℕ) : |(-tR ^ 2) ^ a| ≤ 1 := by
  rw [abs_w_pow]; exact pow_le_one₀ tR_pos.le tR_lt_one.le

/-- `L(1/(1 − w^a s)) = 2 ρ^{−a} (Ξ − S_a)` (Lemma 1(ii)). -/
theorem hasL_simplePole (a : ℕ) :
    HasSum (Lterm (fun y => (1 - (-tR ^ 2) ^ a * y)⁻¹))
      (2 * ((-tR) ^ a)⁻¹ * (XiR - S tR a)) := by
  have ht0 : (-tR) ≠ 0 := neg_ne_zero.mpr tR_pos.ne'
  convert (hasSum_psi_tail a).mul_left (2 * ((-tR) ^ a)⁻¹) using 1
  funext n
  have hne : 1 - (-tR ^ 2) ^ a * pt n ≠ 0 := by
    rw [pt, ← pow_add]; exact one_sub_w_pow_ne_zero (by omega)
  simp only [Lterm]
  rw [thetaOp_inv_affine hne]
  simp only [psi, pt]
  have hne' : 1 - (-tR ^ 2) ^ (n + 1 + a) ≠ 0 := one_sub_w_pow_ne_zero (by omega)
  have hpow : (-tR ^ 2) ^ a * (-tR ^ 2) ^ (n + 1) = (-tR ^ 2) ^ (n + 1 + a) := by ring
  have h3 : (-tR) * (-tR ^ 2) = tR ^ 3 := by ring
  have hkey : tR ^ (3 * (n + 1 + a)) =
      (-tR) ^ (n + 1) * (-tR ^ 2) ^ (n + 1 + a) * (-tR) ^ a := by
    calc tR ^ (3 * (n + 1 + a)) = ((-tR) * (-tR ^ 2)) ^ (n + 1 + a) := by rw [h3, ← pow_mul]
      _ = _ := by rw [mul_pow, pow_add (-tR) (n + 1) a]; ring
  rw [mul_assoc (2 : ℝ), hpow, hkey]
  have ha : (-tR) ^ a ≠ 0 := pow_ne_zero _ ht0
  field_simp

end FibZeta.Analytic
