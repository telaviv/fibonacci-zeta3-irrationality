import FibZeta.Conj.Conjugate

/-!
# The entries `T_k = σL_X(s^k/F)` at `X = −Ξ` are bounded (PROOF §4)

`T K k = mConst(−φ, K, k) − Ξ · mLin(−φ, K, k)` splits as

* the polynomial part `Lpoly (X^k /ₘ F)`, whose coefficients are `E rr K (k − 1 − j)`
  (`coeff_divByMonic`), bounded by `(1 − t²)^{−K}` (`E_bound`), against `|ν_j(−φ)| ≤ j(j+1)φ²`;
* the pole part `2 ∑_a res_a (−φ)^a (S_a(−φ) + Ξ)`, which after expanding
  `2(−φ)^a (S_a(−φ) + Ξ) = ∑_M 2 r_a t^{3(M+1)} ∑_j C(j+2,2) (r_a w^{M+1})^j` and exchanging the
  finite sum over `a` with the two series becomes `∑_M ∑_j c_{M,j} E rr K (k + j + 1)`
  (`partB_eq`); each `E` is bounded, so the double series is bounded (`abs_partB_le`).
-/

open Polynomial Finset

namespace FibZeta.Conj

/-- `T_k = L_X(s^k/F)` at `τ = −φ`, `X = −Ξ`. -/
noncomputable def T (K k : ℕ) : ℝ :=
  mConst (-Real.goldenRatio) K k - XiR * mLin (-Real.goldenRatio) K k

/-- The bound `(1 − t²)^{−K}` on all `E rr K m`. -/
noncomputable def BE (K : ℕ) : ℝ := ((1 - tR ^ 2)⁻¹) ^ K

theorem BE_nonneg (K : ℕ) : 0 ≤ BE K := by
  unfold BE; exact pow_nonneg (inv_nonneg.mpr (by linarith [tR_sq_lt_one])) K

theorem abs_E_rr_le (K m : ℕ) : |E rr K m| ≤ BE K :=
  E_bound tR_sq_pos.le tR_sq_lt_one (fun _ ha => abs_rr_le ha) rr_injective.injOn K m

theorem T_eq (K k : ℕ) :
    T K k = Lpoly (-Real.goldenRatio) (X ^ k /ₘ F (-Real.goldenRatio) K) +
      2 * ∑ a ∈ Icc 1 K, res (-Real.goldenRatio) K k a * (-Real.goldenRatio) ^ a *
        (S (-Real.goldenRatio) a + XiR) := by
  rw [T, mConst, mLin]
  have : ∑ a ∈ Icc 1 K, res (-Real.goldenRatio) K k a * (-Real.goldenRatio) ^ a *
        (S (-Real.goldenRatio) a + XiR) =
      ∑ a ∈ Icc 1 K, res (-Real.goldenRatio) K k a * (-Real.goldenRatio) ^ a *
        S (-Real.goldenRatio) a +
      (∑ a ∈ Icc 1 K, res (-Real.goldenRatio) K k a * (-Real.goldenRatio) ^ a) * XiR := by
    rw [sum_mul, ← sum_add_distrib]
    exact sum_congr rfl fun a _ => by ring
  rw [this]; ring

/-! ### The polynomial part -/

theorem abs_Lpoly_le {K : ℕ} (hK : 1 ≤ K) (k : ℕ) :
    |Lpoly (-Real.goldenRatio) (X ^ k /ₘ F (-Real.goldenRatio) K)| ≤
      k * (BE K * ((k : ℝ) * ((k : ℝ) + 1) * Real.goldenRatio ^ 2)) := by
  rw [F_neg_gold]
  have hcoeff := coeff_divByMonic hK rr_injective.injOn k
  have hsupp : (X ^ k /ₘ Lagrange.nodal (Icc 1 K) rr).support ⊆ range k := by
    intro j hj
    rw [mem_support_iff, hcoeff] at hj
    rw [mem_range]
    by_contra h
    exact hj (by simp [h])
  rw [Lpoly]
  calc |∑ j ∈ (X ^ k /ₘ Lagrange.nodal (Icc 1 K) rr).support,
          (X ^ k /ₘ Lagrange.nodal (Icc 1 K) rr).coeff j * nu (-Real.goldenRatio) j|
      ≤ ∑ j ∈ (X ^ k /ₘ Lagrange.nodal (Icc 1 K) rr).support,
          |(X ^ k /ₘ Lagrange.nodal (Icc 1 K) rr).coeff j * nu (-Real.goldenRatio) j| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ range k,
          |(X ^ k /ₘ Lagrange.nodal (Icc 1 K) rr).coeff j * nu (-Real.goldenRatio) j| :=
        sum_le_sum_of_subset_of_nonneg hsupp (fun _ _ _ => abs_nonneg _)
    _ ≤ ∑ _j ∈ range k, BE K * ((k : ℝ) * ((k : ℝ) + 1) * Real.goldenRatio ^ 2) := by
        refine sum_le_sum fun j hj => ?_
        have hjk : (j : ℝ) ≤ k := by exact_mod_cast (mem_range.mp hj).le
        have hc : |(X ^ k /ₘ Lagrange.nodal (Icc 1 K) rr).coeff j| ≤ BE K := by
          rw [hcoeff]
          split_ifs
          · exact abs_E_rr_le _ _
          · rw [abs_zero]; exact BE_nonneg K
        have hn : |nu (-Real.goldenRatio) j| ≤
            (k : ℝ) * ((k : ℝ) + 1) * Real.goldenRatio ^ 2 := by
          refine (abs_nu_neg_gold j).trans ?_
          have : (j : ℝ) * ((j : ℝ) + 1) ≤ (k : ℝ) * ((k : ℝ) + 1) := by
            have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
            nlinarith
          exact mul_le_mul_of_nonneg_right this (by positivity)
        rw [abs_mul]
        exact mul_le_mul hc hn (abs_nonneg _) (BE_nonneg K)
    _ = k * (BE K * ((k : ℝ) * ((k : ℝ) + 1) * Real.goldenRatio ^ 2)) := by
        rw [sum_const, card_range, nsmul_eq_mul]

/-! ### The pole part -/

/-- `c_{M,j} = 2 t^{3(M+1)} C(j+2,2) w^{(M+1)j}`. -/
noncomputable def cc (M j : ℕ) : ℝ :=
  2 * (tR ^ 3) ^ (M + 1) * ((j + 2).choose 2 : ℝ) * ((-tR ^ 2) ^ (M + 1)) ^ j

theorem partB_eq (K k : ℕ) :
    2 * ∑ a ∈ Icc 1 K, res (-Real.goldenRatio) K k a * (-Real.goldenRatio) ^ a *
        (S (-Real.goldenRatio) a + XiR) =
      ∑' M : ℕ, ∑' j : ℕ, cc M j * E rr K (k + j + 1) := by
  -- the summand, indexed by node `a`, outer index `M`, inner index `j`
  set f : ℕ → ℕ → ℕ → ℝ := fun a M j =>
    res (-Real.goldenRatio) K k a * (cc M j * rr a ^ (j + 1)) with hf
  have hx : ∀ a M, ‖rr a * (-tR ^ 2) ^ (M + 1)‖ < 1 := fun a M => by
    rw [Real.norm_eq_abs]; exact (abs_rr_mul_q_lt a M).trans_lt tR_sq_lt_one
  have hterm : ∀ a M j, f a M j =
      res (-Real.goldenRatio) K k a * (2 * rr a * (tR ^ 3) ^ (M + 1)) *
        (((j + 2).choose 2 : ℝ) * (rr a * (-tR ^ 2) ^ (M + 1)) ^ j) := by
    intro a M j; simp only [hf, cc]; ring
  have hsumj : ∀ a M, Summable (f a M) := fun a M => by
    have := (summable_choose_mul_geometric_of_norm_lt_one 2 (hx a M)).mul_left
      (res (-Real.goldenRatio) K k a * (2 * rr a * (tR ^ 3) ^ (M + 1)))
    exact this.congr fun j => (hterm a M j).symm
  have hinner : ∀ a M, ∑' j, f a M j =
      res (-Real.goldenRatio) K k a * (2 * (-Real.goldenRatio) ^ a * psi tR (M + a + 1)) := by
    intro a M
    simp_rw [hterm]
    rw [tsum_mul_left, ← inv_one_sub_cube (by simpa [Real.norm_eq_abs] using hx a M),
      two_gold_psi]
    ring
  have hsumM : ∀ a, Summable (fun M => ∑' j, f a M j) := fun a => by
    simp_rw [hinner]
    have hs : Summable (fun M => psi tR (M + (a + 1))) :=
      (summable_nat_add_iff (a + 1)).mpr summable_psi_tR
    have := hs.mul_left (res (-Real.goldenRatio) K k a * (2 * (-Real.goldenRatio) ^ a))
    simpa only [add_assoc, mul_assoc] using this
  have hstep1 : ∀ a, 2 * (res (-Real.goldenRatio) K k a * (-Real.goldenRatio) ^ a *
      (S (-Real.goldenRatio) a + XiR)) = ∑' M, ∑' j, f a M j := by
    intro a
    simp_rw [hinner]
    rw [S_add_Xi, tsum_mul_left, tsum_mul_left]
    ring
  rw [mul_sum, sum_congr rfl fun a _ => hstep1 a,
    ← Summable.tsum_finsetSum fun a _ => hsumM a]
  refine tsum_congr fun M => ?_
  rw [← Summable.tsum_finsetSum fun a _ => hsumj a M]
  refine tsum_congr fun j => ?_
  rw [E, mul_sum]
  refine sum_congr rfl fun a ha => ?_
  simp only [hf]
  rw [res_neg_gold ha, show k + j + 1 = k + (j + 1) by ring, pow_add]
  ring

/-- The constant of the pole part: `2 t³/(1 − t³) · (1 − t²)^{−3}`. -/
noncomputable def cB : ℝ := 2 * tR ^ 3 * (1 - tR ^ 3)⁻¹ * (1 / (1 - tR ^ 2) ^ 3)

theorem abs_partB_le (K k : ℕ) :
    |∑' M : ℕ, ∑' j : ℕ, cc M j * E rr K (k + j + 1)| ≤ BE K * cB := by
  have ht3 : 0 ≤ tR ^ 3 := (pow_pos tR_pos 3).le
  have ht3' : tR ^ 3 < 1 := pow_lt_one₀ tR_pos.le tR_lt_one (by norm_num)
  have hq : ∀ M : ℕ, |(-tR ^ 2) ^ (M + 1)| ≤ tR ^ 2 := fun M => by
    rw [abs_pow, abs_neg, abs_of_pos tR_sq_pos]
    exact pow_le_of_le_one tR_sq_pos.le tR_sq_lt_one.le (by omega)
  have hgeo2 : HasSum (fun j : ℕ => ((j + 2).choose 2 : ℝ) * (tR ^ 2) ^ j)
      (1 / (1 - tR ^ 2) ^ (2 + 1)) :=
    hasSum_choose_mul_geometric_of_norm_lt_one 2
      (by rw [Real.norm_eq_abs, abs_of_pos tR_sq_pos]; exact tR_sq_lt_one)
  -- inner bound
  have hin : ∀ M : ℕ, ‖∑' j : ℕ, cc M j * E rr K (k + j + 1)‖ ≤
      2 * (tR ^ 3) ^ (M + 1) * BE K * (1 / (1 - tR ^ 2) ^ (2 + 1)) := by
    intro M
    refine tsum_of_norm_bounded (hgeo2.mul_left (2 * (tR ^ 3) ^ (M + 1) * BE K)) fun j => ?_
    have hA : 0 ≤ 2 * (tR ^ 3) ^ (M + 1) * ((j + 2).choose 2 : ℝ) :=
      mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ht3 _)) (Nat.cast_nonneg _)
    rw [Real.norm_eq_abs, cc, abs_mul, abs_mul, abs_pow, abs_of_nonneg hA]
    have h1 : |(-tR ^ 2) ^ (M + 1)| ^ j ≤ (tR ^ 2) ^ j :=
      pow_le_pow_left₀ (abs_nonneg _) (hq M) j
    have h2 := abs_E_rr_le K (k + j + 1)
    calc 2 * (tR ^ 3) ^ (M + 1) * ((j + 2).choose 2 : ℝ) * |(-tR ^ 2) ^ (M + 1)| ^ j *
          |E rr K (k + j + 1)|
        ≤ 2 * (tR ^ 3) ^ (M + 1) * ((j + 2).choose 2 : ℝ) * (tR ^ 2) ^ j * BE K :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 hA) h2 (abs_nonneg _)
            (mul_nonneg hA (pow_nonneg tR_sq_pos.le j))
      _ = 2 * (tR ^ 3) ^ (M + 1) * BE K * (((j + 2).choose 2 : ℝ) * (tR ^ 2) ^ j) := by ring
  have hgeo3 : HasSum (fun M : ℕ => (tR ^ 3) ^ M) (1 - tR ^ 3)⁻¹ :=
    hasSum_geometric_of_lt_one ht3 ht3'
  have hout := hgeo3.mul_left (2 * tR ^ 3 * BE K * (1 / (1 - tR ^ 2) ^ (2 + 1)))
  calc |∑' M : ℕ, ∑' j : ℕ, cc M j * E rr K (k + j + 1)|
      = ‖∑' M : ℕ, ∑' j : ℕ, cc M j * E rr K (k + j + 1)‖ := (Real.norm_eq_abs _).symm
    _ ≤ 2 * tR ^ 3 * BE K * (1 / (1 - tR ^ 2) ^ (2 + 1)) * (1 - tR ^ 3)⁻¹ :=
        tsum_of_norm_bounded hout fun M => (hin M).trans_eq (by ring)
    _ = BE K * cB := by rw [cB]; ring

end FibZeta.Conj
