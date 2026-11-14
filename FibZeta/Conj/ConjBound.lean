import FibZeta.Conj.Entry

/-!
# Proposition 4: conjugate smallness (`ConjBound`)

`σΔ_K(−Ξ) = det[nrm · T_{i+j}] = nrm^K det[T_{i+j}]` with `|nrm(−φ, K)| = t^{K(K+1)}`
(`abs_nrm_neg_gold`), so `|nrm|^K = t^{K²(K+1)}`.  Every entry satisfies
`|T_k| ≤ (1 − t²)^{−K} (k²(k+1)φ² + c_B) ≤ D^K` for `k < 2K` (`abs_T_le_pow`), and the
permutation bound `|det| ≤ K! (D^K)^K ≤ (2D)^{K²}` finishes the proof.
-/

open Polynomial Finset

namespace FibZeta.Conj

theorem abs_T_le {K : ℕ} (hK : 1 ≤ K) (k : ℕ) :
    |T K k| ≤ k * (BE K * ((k : ℝ) * ((k : ℝ) + 1) * Real.goldenRatio ^ 2)) + BE K * cB := by
  rw [T_eq, partB_eq]
  exact (abs_add_le _ _).trans (add_le_add (abs_Lpoly_le hK k) (abs_partB_le K k))

theorem cB_nonneg : 0 ≤ cB := by
  have h3 : tR ^ 3 < 1 := pow_lt_one₀ tR_pos.le tR_lt_one (by norm_num)
  have h2 : 0 < 1 - tR ^ 2 := by linarith [tR_sq_lt_one]
  unfold cB
  have : 0 < (1 - tR ^ 3)⁻¹ := inv_pos.mpr (by linarith)
  have : 0 < 1 / (1 - tR ^ 2) ^ 3 := by positivity
  have : 0 < tR ^ 3 := pow_pos tR_pos 3
  positivity

/-- The base of the entry bound `|T_k| ≤ D^K`. -/
noncomputable def Dc : ℝ := (1 - tR ^ 2)⁻¹ * 8 * max (8 * Real.goldenRatio ^ 2 + cB) 1

theorem Dc_pos : 0 < Dc := by
  have h2 : 0 < 1 - tR ^ 2 := by linarith [tR_sq_lt_one]
  unfold Dc
  have : 0 < max (8 * Real.goldenRatio ^ 2 + cB) 1 := lt_max_of_lt_right one_pos
  have : 0 < (1 - tR ^ 2)⁻¹ := inv_pos.mpr h2
  positivity

theorem abs_T_le_pow {K : ℕ} (hK : 1 ≤ K) {k : ℕ} (hk : k < 2 * K) : |T K k| ≤ Dc ^ K := by
  set c₀ := 8 * Real.goldenRatio ^ 2 + cB with hc₀
  set c₁ := max c₀ 1 with hc₁
  have hk1 : (k : ℝ) ≤ 2 * K := by exact_mod_cast hk.le
  have hk2 : (k : ℝ) + 1 ≤ 2 * K := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h8 : (k : ℝ) * ((k : ℝ) * ((k : ℝ) + 1)) ≤ 8 * (K : ℝ) ^ 3 := by
    have := mul_le_mul hk1 (mul_le_mul hk1 hk2 (by positivity) (by positivity))
      (by positivity) (by positivity)
    nlinarith
  have hK3 : (1 : ℝ) ≤ (K : ℝ) ^ 3 := one_le_pow₀ (by exact_mod_cast hK)
  have hcB := cB_nonneg
  have hK8 : (K : ℝ) ^ 3 ≤ 8 ^ K := by
    have : (K : ℝ) ≤ 2 ^ K := by exact_mod_cast Nat.lt_two_pow_self.le
    calc (K : ℝ) ^ 3 ≤ (2 ^ K) ^ 3 := pow_le_pow_left₀ (Nat.cast_nonneg _) this 3
      _ = 8 ^ K := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hc₀1 : c₀ ≤ c₁ ^ K := (le_max_left _ _).trans (le_self_pow₀ (le_max_right _ _) (by omega))
  have hc₀0 : 0 ≤ c₀ := by positivity
  calc |T K k|
      ≤ BE K * ((k : ℝ) * ((k : ℝ) * ((k : ℝ) + 1)) * Real.goldenRatio ^ 2 + cB) :=
        (abs_T_le hK k).trans_eq (by ring)
    _ ≤ BE K * ((K : ℝ) ^ 3 * c₀) := by
        refine mul_le_mul_of_nonneg_left ?_ (BE_nonneg K)
        rw [hc₀]
        nlinarith [mul_le_mul_of_nonneg_right h8 (sq_nonneg Real.goldenRatio),
          mul_le_mul_of_nonneg_right hK3 hcB]
    _ ≤ BE K * (8 ^ K * c₁ ^ K) := by
        refine mul_le_mul_of_nonneg_left ?_ (BE_nonneg K)
        exact mul_le_mul hK8 hc₀1 hc₀0 (by positivity)
    _ = Dc ^ K := by rw [Dc, BE, mul_pow, mul_pow]; ring

theorem eval_Delta (τ x : ℝ) (K : ℕ) :
    (Delta τ K).eval x = Matrix.det (Matrix.of fun i j : Fin K =>
      nrm τ K * (mConst τ K (i.val + j.val) + x * mLin τ K (i.val + j.val))) := by
  rw [Delta, ← coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp [hankelLin, hankelConst]
  ring

theorem abs_nrm_neg_gold (K : ℕ) : |nrm (-Real.goldenRatio) K| = tR ^ (K * (K + 1)) := by
  have h2 : 2 * AK K = K * (K + 1) := by
    unfold AK; exact Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self K)
  have hg0 : 0 < Real.goldenRatio := Real.goldenRatio_pos
  rw [nrm, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_inv, abs_pow, neg_sq,
    abs_neg, abs_of_pos (pow_pos hg0 2), ← h2, pow_mul, tR, inv_pow, inv_pow]

/-- **Proposition 4** (conjugate smallness). -/
theorem conjBound : ConjBound := by
  refine ⟨2 * Dc, by linarith [Dc_pos], fun K hK => ?_⟩
  rw [eval_Delta]
  have hmat : (Matrix.of fun i j : Fin K => nrm (-Real.goldenRatio) K *
      (mConst (-Real.goldenRatio) K (i.val + j.val) +
        (-XiR) * mLin (-Real.goldenRatio) K (i.val + j.val))) =
      nrm (-Real.goldenRatio) K • Matrix.of fun i j : Fin K => T K (i.val + j.val) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, T]
    ring
  rw [hmat, Matrix.det_smul, Fintype.card_fin, abs_mul, abs_pow, abs_nrm_neg_gold]
  have hdet := Matrix.det_le (abv := AbsoluteValue.abs)
    (A := Matrix.of fun i j : Fin K => T K (i.val + j.val)) (x := Dc ^ K)
    (fun i j => by
      simp only [AbsoluteValue.abs_apply, Matrix.of_apply]
      exact abs_T_le_pow hK (by omega))
  simp only [AbsoluteValue.abs_apply, Fintype.card_fin, nsmul_eq_mul] at hdet
  have hfac : (K.factorial : ℝ) ≤ (2 ^ K) ^ K := by
    exact_mod_cast (Nat.factorial_le_pow K).trans (Nat.pow_le_pow_left Nat.lt_two_pow_self.le K)
  have hD : 0 ≤ Dc ^ K := pow_nonneg Dc_pos.le K
  have ht : 0 ≤ (tR ^ (K * (K + 1))) ^ K := pow_nonneg (pow_nonneg tR_pos.le _) K
  calc (tR ^ (K * (K + 1))) ^ K * |Matrix.det (Matrix.of fun i j : Fin K => T K (i.val + j.val))|
      ≤ (tR ^ (K * (K + 1))) ^ K * ((2 ^ K) ^ K * (Dc ^ K) ^ K) := by
        refine mul_le_mul_of_nonneg_left (hdet.trans ?_) ht
        exact mul_le_mul_of_nonneg_right hfac (pow_nonneg hD K)
    _ = (2 * Dc) ^ (K ^ 2) * tR ^ (K ^ 2 * (K + 1)) := by
        rw [← pow_mul, ← pow_mul, ← pow_mul, ← mul_pow, show K * K = K ^ 2 by ring,
          show K * (K + 1) * K = K ^ 2 * (K + 1) by ring]
        ring

end FibZeta.Conj
