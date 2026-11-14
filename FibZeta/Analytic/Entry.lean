/-
Adapted from uplift-universal-inc/qzeta_3-irrationality, lean/QZeta3/DividedDifferences.lean and
lean/QZeta3/GramIdentity.lean (Apache-2.0, Lean formalisation by F. Solomon Admasu). Changes: real
nodes `x_a = w^{−a}` with `w = −t²` instead of `p^a`, partial fractions via
`Lagrange.eval_interpolate_not_at_node`, normalisation `D_K = (−1)^K w^{A_K} F_K`.
-/
import FibZeta.Analytic.Functional

/-!
# The entry identity (Lemma 1 + partial fractions, PROOF §1)

`entryIdentity : EntryIdentity`: at `τ = t`, `X = Ξ`, the formal entries
`nrm · (mConst + Ξ · mLin)` are the values `L(s^k/D_K)` of the real functional.
-/

open Polynomial Finset Filter Topology

namespace FibZeta.Analytic

theorem w_ne_zero : (-tR ^ 2 : ℝ) ≠ 0 := neg_ne_zero.mpr tR_sq_pos.ne'

theorem node_injOn (K : ℕ) : Set.InjOn (node tR) (Icc 1 K : Set ℕ) := by
  intro a _ b _ h
  simp only [node] at h
  have h1 := inv_injective h
  have h2 : (tR ^ 2) ^ a = (tR ^ 2) ^ b := by
    have := congrArg abs h1
    rwa [abs_pow, abs_pow, abs_neg, abs_of_pos tR_sq_pos] at this
  exact pow_right_injective₀ tR_sq_pos tR_sq_lt_one.ne h2

theorem one_lt_abs_node {a : ℕ} (ha : 1 ≤ a) : 1 < |node tR a| := by
  rw [node, abs_inv, abs_w_pow]
  exact one_lt_inv₀ (pow_pos tR_pos _) |>.mpr (pow_lt_one₀ tR_pos.le tR_lt_one (by omega))

theorem ne_node_of_abs_lt {x : ℝ} (hx : |x| < 1) (K : ℕ) : ∀ a ∈ Icc 1 K, x ≠ node tR a := by
  intro a ha h
  have := one_lt_abs_node (mem_Icc.mp ha).1
  rw [← h] at this
  linarith

theorem F_eq_nodal (K : ℕ) : F tR K = Lagrange.nodal (Icc 1 K) (node tR) := rfl

/-- Partial fractions for `x^k / F_K(x)`. -/
theorem partial_fraction (K k : ℕ) (x : ℝ) (hx : ∀ a ∈ Icc 1 K, x ≠ node tR a) :
    x ^ k / (F tR K).eval x =
      (X ^ k /ₘ F tR K).eval x + ∑ a ∈ Icc 1 K, res tR K k a / (x - node tR a) := by
  have hmon : (F tR K).Monic := Lagrange.nodal_monic
  have hdeg : (X ^ k %ₘ F tR K).degree < #(Icc 1 K) := by
    have := degree_modByMonic_lt (X ^ k) hmon
    rwa [F_eq_nodal, Lagrange.degree_nodal] at this
  have hint := Lagrange.eq_interpolate (node_injOn K) hdeg
  have hroot : ∀ a ∈ Icc 1 K, (X ^ k %ₘ F tR K).eval (node tR a) = node tR a ^ k := by
    intro a ha
    have hFa : (F tR K).eval (node tR a) = 0 := Lagrange.eval_nodal_at_node ha
    have h := congrArg (eval (node tR a)) (modByMonic_add_div (X ^ k) (F tR K))
    simp only [eval_add, eval_mul, eval_pow, eval_X, hFa, zero_mul, add_zero] at h
    exact h
  have hF : (F tR K).eval x ≠ 0 := Lagrange.eval_nodal_not_at_node hx
  have hr : (X ^ k %ₘ F tR K).eval x =
      (F tR K).eval x * ∑ a ∈ Icc 1 K, res tR K k a / (x - node tR a) := by
    conv_lhs => rw [hint]
    rw [Lagrange.eval_interpolate_not_at_node _ hx, ← F_eq_nodal]
    congr 1
    apply sum_congr rfl
    intro a ha
    rw [hroot a ha, Lagrange.nodalWeight_eq_eval_derivative_nodal ha, res, ← F_eq_nodal]
    ring
  have hmain := congrArg (eval x) (modByMonic_add_div (X ^ k) (F tR K))
  simp only [eval_add, eval_mul, eval_pow, eval_X] at hmain
  rw [← hmain, hr]
  field_simp
  ring

theorem AK_succ (K : ℕ) : AK (K + 1) = AK K + (K + 1) := by
  unfold AK
  have : (K + 1) * (K + 1 + 1) = K * (K + 1) + (K + 1) * 2 := by ring
  rw [this, Nat.add_mul_div_right _ _ two_pos]

theorem DK_eq (K : ℕ) (x : ℝ) :
    DK K x = ((-1) ^ K * (-tR ^ 2) ^ AK K) * (F tR K).eval x := by
  induction K with
  | zero => simp [DK, F, AK]
  | succ K ih =>
    have hF : F tR (K + 1) = F tR K * (X - C (node tR (K + 1))) := by
      rw [F, prod_Icc_succ_top (by omega)]; rfl
    have hD : DK (K + 1) x = DK K x * (1 - (-tR ^ 2) ^ (K + 1) * x) := by
      rw [DK, prod_Icc_succ_top (by omega)]; rfl
    have hw : (-tR ^ 2 : ℝ) ^ (K + 1) ≠ 0 := pow_ne_zero _ w_ne_zero
    rw [hD, ih, hF, AK_succ, eval_mul, eval_sub, eval_X, eval_C, node,
      pow_add (-tR ^ 2) (AK K) (K + 1), pow_succ (-1 : ℝ) K]
    generalize (-tR ^ 2 : ℝ) ^ (K + 1) = u at hw ⊢
    field_simp
    ring

theorem nrm_ne_zero (K : ℕ) : nrm tR K ≠ 0 := by
  rw [nrm]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (inv_ne_zero (pow_ne_zero _ w_ne_zero))

theorem fraction_DK (K k : ℕ) (x : ℝ) :
    x ^ k / DK K x = nrm tR K * (x ^ k / (F tR K).eval x) := by
  rw [DK_eq, nrm]
  have h1 : ((-1 : ℝ) ^ K) * (-1) ^ K = 1 := by rw [← mul_pow]; norm_num
  have hw : (-tR ^ 2 : ℝ) ^ AK K ≠ 0 := pow_ne_zero _ w_ne_zero
  have hs : ((-1 : ℝ) ^ K) ≠ 0 := pow_ne_zero _ (by norm_num)
  generalize (-tR ^ 2 : ℝ) ^ AK K = v at hw ⊢
  generalize ((-1 : ℝ) ^ K) = e at h1 hs ⊢
  rcases eq_or_ne ((F tR K).eval x) 0 with h | h
  · simp [h]
  · field_simp
    linear_combination (-x ^ k) * h1

/-- The pole pieces `res/(y − x_a) = (−res w^a) (1 − w^a y)⁻¹`. -/
theorem pole_eq (c : ℝ) (a : ℕ) (y : ℝ) (hy : y ≠ node tR a) :
    c / (y - node tR a) = (-c * (-tR ^ 2) ^ a) * (1 - (-tR ^ 2) ^ a * y)⁻¹ := by
  have hw : (-tR ^ 2 : ℝ) ^ a ≠ 0 := pow_ne_zero _ w_ne_zero
  have h1 : y - node tR a ≠ 0 := sub_ne_zero.mpr hy
  have h2 : 1 - (-tR ^ 2) ^ a * y ≠ 0 := by
    intro h; apply h1; rw [node]; field_simp; linear_combination -h
  rw [node] at h1 ⊢
  generalize (-tR ^ 2 : ℝ) ^ a = u at hw h1 h2 ⊢
  have h3 : y - u⁻¹ = -(u⁻¹) * (1 - u * y) := by field_simp; ring
  rw [h3, div_eq_mul_inv, mul_inv, inv_neg, inv_inv]
  ring

theorem w_pow_mul_inv (a : ℕ) : (-tR ^ 2) ^ a * ((-tR) ^ a)⁻¹ = tR ^ a := by
  have ht : ((-tR) ^ a) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr tR_pos.ne')
  have : (-tR ^ 2 : ℝ) ^ a = (-tR) ^ a * tR ^ a := by rw [← mul_pow]; ring
  rw [this]; field_simp

/-- The entries as convergent series. -/
theorem hasL_fraction_DK (K k : ℕ) :
    HasSum (Lterm (fun y => y ^ k / DK K y))
      (nrm tR K * (mConst tR K k + XiR * mLin tR K k)) := by
  set Q := X ^ k /ₘ F tR K
  let P : ℕ → ℝ → ℝ := fun a y =>
    (-(res tR K k a) * (-tR ^ 2) ^ a) * (1 - (-tR ^ 2) ^ a * y)⁻¹
  let g : ℝ → ℝ := fun y => nrm tR K * (Q.eval y + ∑ a ∈ Icc 1 K, P a y)
  have hgood : Good (fun y => Q.eval y + ∑ a ∈ Icc 1 K, P a y) :=
    good_add (good_poly Q) (good_sum _ _ fun a _ =>
      good_const_mul (good_simplePole _ (abs_w_pow_le_one a)) _)
  have hP : HasSum (Lterm (fun y => Q.eval y + ∑ a ∈ Icc 1 K, P a y))
      (Lpoly tR Q + ∑ a ∈ Icc 1 K,
        (-(res tR K k a) * (-tR ^ 2) ^ a) * (2 * ((-tR) ^ a)⁻¹ * (XiR - S tR a))) :=
    hasL_add (good_poly Q) (good_sum _ _ fun a _ =>
      good_const_mul (good_simplePole _ (abs_w_pow_le_one a)) _) (hasL_poly Q)
      (hasL_sum _ _ _ (fun a _ => good_const_mul (good_simplePole _ (abs_w_pow_le_one a)) _)
        (fun a _ => hasL_const_mul (good_simplePole _ (abs_w_pow_le_one a))
          (hasL_simplePole a) _))
  have hg := hasL_const_mul hgood hP (nrm tR K)
  have he : ∀ n, (fun y => y ^ k / DK K y) =ᶠ[𝓝 (pt n)] g := by
    intro n
    filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds (abs_pt_lt_one n)]
      with y hy
    have hy' := ne_node_of_abs_lt hy K
    simp only [g, P]
    rw [fraction_DK, partial_fraction K k y hy']
    congr 2
    apply sum_congr rfl
    intro a ha
    exact pole_eq _ a y (hy' a ha)
  convert hasL_congr he hg using 2
  have hterm : ∀ a ∈ Icc 1 K,
      (-(res tR K k a) * (-tR ^ 2) ^ a) * (2 * ((-tR) ^ a)⁻¹ * (XiR - S tR a)) =
        2 * (res tR K k a * tR ^ a * S tR a) + XiR * (-(2 * (res tR K k a * tR ^ a))) := by
    intro a _
    have h := w_pow_mul_inv a
    linear_combination (-(2 * res tR K k a * (XiR - S tR a))) * h
  rw [sum_congr rfl hterm, sum_add_distrib, ← mul_sum, ← mul_sum, mConst, mLin]
  simp only [sum_neg_distrib, ← mul_sum]
  ring

/-- **Entry identity** (Lemma 1 + partial fractions). -/
theorem entryIdentity : EntryIdentity := by
  intro K k _ _
  exact (hasL_fraction_DK K k).tsum_eq.symm

end FibZeta.Analytic
