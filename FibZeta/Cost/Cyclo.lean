/-
Adapted from uplift-universal-inc/qzeta_3-irrationality, lean/QZeta3/CyclotomicBounds.lean (Apache-2.0, Lean
formalisation by F. Solomon Admasu). Changes: the integer point `p` is replaced by the pair `t = φ⁻¹`, `−φ` (norm of
`Φ_d(t)` in `ℤ[φ]`), with the geometric error bound at ratio `t ≤ 2/3`.
-/
import FibZeta.Main

/-!
# Lemma 3.5: size of `N(Φ_d(t)) = Φ_d(t) Φ_d(−φ)`

`log |Φ_d(t)| + log |Φ_d(−φ)| ≤ φ(d) log φ + 12` for every `d ≥ 1`.

Proof: `∑_{a ∣ n} log|Φ_a(x)| = log|x^n − 1|`; at `x = t` and `x = −φ` the sum of the two minus `n log φ` is
`G(n) = log(1 − tⁿ) + log|1 − (−t)ⁿ|`, `|G(n)| ≤ 6 tⁿ`; Möbius inversion gives
`|F(d)| ≤ ∑_{a ∣ d} 6 tᵃ ≤ 6 t/(1 − t) ≤ 12`.
-/

open Polynomial Finset
open scoped ArithmeticFunction.Moebius

namespace FibZeta.Cost

theorem tR_le : tR ≤ 2 / 3 := by
  rw [tR_eq]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 5]

theorem gold_pos : 0 < Real.goldenRatio := Real.goldenRatio_pos

theorem log_gold_pos : 0 < Real.log Real.goldenRatio :=
  Real.log_pos Real.one_lt_goldenRatio

theorem abs_log_one_sub_le {v : ℝ} (hv : |v| ≤ 2 / 3) : |Real.log (|1 - v|)| ≤ 3 * |v| := by
  have hv1 : v ≤ 2 / 3 := le_trans (le_abs_self v) hv
  have h1 : 0 < 1 - v := by linarith
  rw [abs_of_pos h1]
  have habs := abs_nonneg v
  have hle := le_abs_self v
  have hge := neg_abs_le v
  refine abs_le.mpr ⟨?_, ?_⟩
  · have hlow := Real.one_sub_inv_le_log_of_pos h1
    have hinv : (1 - v)⁻¹ ≤ 1 + 3 * |v| := by
      rw [inv_eq_one_div, div_le_iff₀ h1]
      nlinarith [mul_le_mul_of_nonneg_left hv1 habs]
    linarith
  · have := Real.log_le_sub_one_of_pos h1
    linarith

theorem cyc_eval_ne_zero {x : ℝ} (hx : ∀ m : ℕ, 0 < m → x ^ m ≠ 1) {a : ℕ} (ha : 0 < a) :
    (cyclotomic a ℝ).eval x ≠ 0 := by
  intro h
  have : NeZero a := ⟨ha.ne'⟩
  have hroot : (cyclotomic a ℝ).IsRoot x := h
  rw [isRoot_cyclotomic_iff] at hroot
  exact hx a ha hroot.pow_eq_one

theorem sum_log_cyc {x : ℝ} (hx : ∀ m : ℕ, 0 < m → x ^ m ≠ 1) {n : ℕ} (hn : 0 < n) :
    ∑ a ∈ n.divisors, Real.log |(cyclotomic a ℝ).eval x| = Real.log |x ^ n - 1| := by
  rw [← Real.log_prod (fun a ha => abs_ne_zero.mpr
    (cyc_eval_ne_zero hx (Nat.pos_of_mem_divisors ha))), ← Finset.abs_prod, ← eval_prod,
    prod_cyclotomic_eq_X_pow_sub_one hn]
  simp

theorem tR_not_root : ∀ m : ℕ, 0 < m → tR ^ m ≠ 1 := by
  apply pow_ne_one_of_abs_ne_one
  rw [abs_of_pos tR_pos]; exact tR_lt_one.ne

theorem gold_not_root : ∀ m : ℕ, 0 < m → (-Real.goldenRatio) ^ m ≠ 1 := by
  apply pow_ne_one_of_abs_ne_one
  rw [abs_neg, abs_of_pos gold_pos]; exact Real.one_lt_goldenRatio.ne'

/-- The cyclotomic error `F(a) = log|Φ_a(t)| + log|Φ_a(−φ)| − φ(a) log φ`. -/
noncomputable def cycErr (a : ℕ) : ℝ :=
  Real.log |(cyclotomic a ℝ).eval tR| + Real.log |(cyclotomic a ℝ).eval (-Real.goldenRatio)| -
    (Nat.totient a : ℝ) * Real.log Real.goldenRatio

/-- `G(n) = log|1 − tⁿ| + log|1 − (−t)ⁿ|`. -/
noncomputable def cycG (n : ℕ) : ℝ := Real.log |1 - tR ^ n| + Real.log |1 - (-tR) ^ n|

theorem sum_cycErr {n : ℕ} (hn : 0 < n) : ∑ a ∈ n.divisors, cycErr a = cycG n := by
  unfold cycErr cycG
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, sum_log_cyc tR_not_root hn,
    sum_log_cyc gold_not_root hn]
  have hs : (∑ d ∈ n.divisors, (Nat.totient d : ℝ)) = n := by exact_mod_cast Nat.sum_totient n
  rw [hs]
  have h1 : |tR ^ n - 1| = |1 - tR ^ n| := abs_sub_comm _ _
  have h2 : (-Real.goldenRatio) ^ n - 1 = (-Real.goldenRatio) ^ n * (1 - (-tR) ^ n) := by
    have : (-Real.goldenRatio) ^ n * (-tR) ^ n = 1 := by
      rw [← mul_pow]; simp [mul_comm, tR_mul_gold]
    linear_combination this
  rw [h1, h2, abs_mul, Real.log_mul, abs_pow, abs_neg, abs_of_pos gold_pos, Real.log_pow]
  · ring
  · exact abs_ne_zero.mpr (pow_ne_zero _ (neg_ne_zero.mpr gold_pos.ne'))
  · refine abs_ne_zero.mpr (sub_ne_zero.mpr ?_)
    intro h
    have := congrArg abs h
    rw [abs_one, abs_pow, abs_neg, abs_of_pos tR_pos] at this
    exact tR_not_root n hn this.symm

theorem abs_cycG_le {n : ℕ} (hn : 0 < n) : |cycG n| ≤ 6 * tR ^ n := by
  have hp : 0 ≤ tR ^ n := pow_nonneg tR_pos.le n
  have hle : tR ^ n ≤ 2 / 3 :=
    le_trans (pow_le_of_le_one tR_pos.le tR_lt_one.le hn.ne') tR_le
  have a1 : |tR ^ n| = tR ^ n := abs_of_nonneg hp
  have a2 : |(-tR) ^ n| = tR ^ n := by rw [abs_pow, abs_neg, abs_of_pos tR_pos]
  have e1 := abs_log_one_sub_le (v := tR ^ n) (by rw [a1]; exact hle)
  have e2 := abs_log_one_sub_le (v := (-tR) ^ n) (by rw [a2]; exact hle)
  rw [a1] at e1; rw [a2] at e2
  unfold cycG
  calc _ ≤ |Real.log (|1 - tR ^ n|)| + |Real.log (|1 - (-tR) ^ n|)| := abs_add_le _ _
    _ ≤ _ := by linarith

theorem sum_tR_pow_le (d : ℕ) : ∑ a ∈ Icc 1 d, tR ^ a ≤ 2 := by
  have h := geom_sum_Ico_le_of_lt_one (m := 1) (n := d + 1) tR_pos.le tR_lt_one
  have hI : Icc 1 d = Ico 1 (d + 1) := by ext; simp
  rw [hI]
  refine h.trans ?_
  rw [pow_one, div_le_iff₀ (by linarith [tR_lt_one])]
  linarith [tR_le]

theorem abs_cycErr_le {d : ℕ} (hd : 0 < d) : |cycErr d| ≤ 12 := by
  have hm := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp
    (fun n hn => sum_cycErr hn)) d hd
  rw [← hm, Nat.sum_divisorsAntidiagonal' (fun a b => (μ a : ℝ) * cycG b)]
  calc |∑ a ∈ d.divisors, (μ (d / a) : ℝ) * cycG a|
      ≤ ∑ a ∈ d.divisors, |(μ (d / a) : ℝ) * cycG a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ d.divisors, 6 * tR ^ a := by
      apply Finset.sum_le_sum
      intro a ha
      rw [abs_mul]
      have hmu : |(μ (d / a) : ℝ)| ≤ 1 := by
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d / a))
      calc _ ≤ 1 * |cycG a| := mul_le_mul_of_nonneg_right hmu (abs_nonneg _)
        _ ≤ _ := by rw [one_mul]; exact abs_cycG_le (Nat.pos_of_mem_divisors ha)
    _ ≤ ∑ a ∈ Icc 1 d, 6 * tR ^ a := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro a ha
        exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors ha,
          Nat.le_of_dvd hd (Nat.dvd_of_mem_divisors ha)⟩
      · intro a _ _; have := tR_pos; positivity
    _ ≤ 12 := by rw [← Finset.mul_sum]; linarith [sum_tR_pow_le d]

/-- **Lemma 3.5** (upper half, constant 12). -/
theorem log_norm_cyc_le {d : ℕ} (hd : 0 < d) :
    Real.log |(cyclotomic d ℝ).eval tR| + Real.log |(cyclotomic d ℝ).eval (-Real.goldenRatio)| ≤
      (Nat.totient d : ℝ) * Real.log Real.goldenRatio + 12 := by
  have := (abs_le.mp (abs_cycErr_le hd)).2
  unfold cycErr at this
  linarith

end FibZeta.Cost
