import FibZeta.Statements

/-!
# Assembly (PROOF §6)

`irrational_zetaF3_of` derives `Irrational zetaF3` from the five frozen ingredients of
`FibZeta.Statements`.

Suppose `ζ_F(3) = a/b`.  Then `Ξ = ζ_F(3)/(5√5) = u(t)` and `−Ξ = u(−φ)` with
`u(τ) = a(1 + 2τ)/(25b)` (as `√5 = 1 + 2t = −(1 + 2(−φ))`).  By `Integrality`,
`Y(τ) = C_K(τ) (25b)^K Δ_{K,τ}(u(τ)) = Q(τ)/τ^N` for one integer polynomial `Q` and both
`τ = t`, `τ = −φ`.  Since `t` and `−φ` are the two roots of `τ² + τ − 1`, the product
`Q(t) Q(−φ)` is an integer, nonzero when `Q(t) ≠ 0` (`norm_ne_zero`).  So
`1 ≤ |Y(t) Y(−φ)|` whenever `Δ_K(Ξ) ≠ 0`, which happens for infinitely many `K`
(`Nonvanishing`), while `DecayBound`, `ConjBound` and `CostBound` make the right side
`≤ exp(−(11/9 − 121/100) K³ log φ + O(K² log² K))`.
-/

open Polynomial Finset Filter Topology

namespace FibZeta

/-! ### Facts about `t` and `φ` -/

theorem tR_eq : tR = (√5 - 1) / 2 := by
  unfold tR
  rw [Real.inv_goldenRatio, Real.goldenConj]
  ring

theorem sqrt5_eq : √5 = 1 + 2 * tR := by rw [tR_eq]; ring

theorem gold_eq : Real.goldenRatio = 1 + tR := by
  rw [tR_eq, Real.goldenRatio]; ring

theorem tR_pos : 0 < tR := by
  unfold tR; exact inv_pos.mpr Real.goldenRatio_pos

theorem tR_lt_one : tR < 1 := by
  unfold tR; exact inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio

theorem tR_mul_gold : tR * Real.goldenRatio = 1 := by
  unfold tR; exact inv_mul_cancel₀ Real.goldenRatio_pos.ne'

theorem tR_sq : tR ^ 2 + tR - 1 = 0 := by
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  rw [tR_eq]; nlinarith [h5]

theorem gold_sq : (-Real.goldenRatio) ^ 2 + (-Real.goldenRatio) - 1 = 0 := by
  have := Real.goldenRatio_sq
  linear_combination this

theorem neg_gold_add : 1 + 2 * (-Real.goldenRatio) = -√5 := by
  rw [Real.goldenRatio]; ring

theorem log_tR : Real.log tR = -Real.log Real.goldenRatio := by
  unfold tR; exact Real.log_inv _

/-- `1/F_n³ = 5√5 ψ_n(t)` (Binet). -/
theorem one_div_fib_cube (n : ℕ) :
    1 / ((Nat.fib n : ℕ) : ℝ) ^ 3 = 5 * √5 * psi tR n := by
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs : (0 : ℝ) < √5 := by positivity
  rw [Real.coe_fib_eq, psi]
  have hg : Real.goldenRatio = tR⁻¹ := by unfold tR; rw [inv_inv]
  have hc : Real.goldenConj = -tR := by
    unfold tR; rw [Real.inv_goldenRatio, neg_neg]
  rw [hg, hc]
  have ht := tR_pos
  have hmul : (-tR) ^ n = (-tR ^ 2) ^ n * (tR⁻¹) ^ n := by
    rw [← mul_pow]; congr 1; field_simp
  rw [hmul]
  have hfac : (tR⁻¹ ^ n - (-tR ^ 2) ^ n * tR⁻¹ ^ n) / √5 =
      tR⁻¹ ^ n * (1 - (-tR ^ 2) ^ n) / √5 := by ring
  rw [hfac]
  by_cases h1 : (1 - (-tR ^ 2) ^ n) = 0
  · rw [h1]; simp
  · have htn : tR ^ n ≠ 0 := pow_ne_zero _ ht.ne'
    have h3 : √5 ^ 3 = 5 * √5 := by rw [pow_succ, h5]
    rw [div_pow, mul_pow, h3]
    simp only [inv_pow]
    field_simp
    ring

/-- `ζ_F(3) = 5√5 Ξ`. -/
theorem zetaF3_eq : zetaF3 = 5 * √5 * XiR := by
  unfold zetaF3 XiR
  rw [← tsum_mul_left]
  congr 1
  funext n
  exact one_div_fib_cube (n + 1)

/-! ### Degree and nonvanishing of `C_K` -/

theorem natDegree_Delta_le {𝕜 : Type*} [Field 𝕜] (τ : 𝕜) (K : ℕ) :
    (Delta τ K).natDegree ≤ K := by
  unfold Delta
  simpa [Fintype.card_fin] using
    Polynomial.natDegree_det_X_add_C_le (hankelLin τ K) (hankelConst τ K)

theorem pow_ne_one_of_abs_ne_one {τ : ℝ} (h : |τ| ≠ 1) : ∀ m : ℕ, 0 < m → τ ^ m ≠ 1 := by
  intro m hm hτ
  apply h
  have : |τ| ^ m = 1 := by rw [← abs_pow, hτ, abs_one]
  exact (pow_eq_one_iff_of_nonneg (abs_nonneg τ) hm.ne').mp this

theorem aeval_CKpoly_ne_zero {τ : ℝ} (h : ∀ m : ℕ, 0 < m → τ ^ m ≠ 1) (K : ℕ) :
    aeval τ (CKpoly K) ≠ 0 := by
  unfold CKpoly
  rw [map_prod]
  refine Finset.prod_ne_zero_iff.mpr fun d hd => ?_
  rw [map_pow]
  refine pow_ne_zero _ ?_
  have hd0 : 0 < d := by have := (mem_Icc.mp hd).1; omega
  intro h0
  have : NeZero d := ⟨hd0.ne'⟩
  have hroot : (cyclotomic d ℝ).IsRoot τ := by
    rw [IsRoot, ← map_cyclotomic_int, eval_map]
    rw [aeval_def] at h0
    simpa using h0
  rw [isRoot_cyclotomic_iff] at hroot
  exact h d hd0 hroot.pow_eq_one

/-! ### The norm argument -/

/-- For `Q ∈ ℤ[X]`, `Q(t) Q(−φ)` is an integer, nonzero when `Q(t) ≠ 0`. -/
theorem norm_ne_zero (Q : ℤ[X]) :
    ∃ z : ℤ, aeval tR Q * aeval (-Real.goldenRatio) Q = z ∧
      (aeval tR Q ≠ 0 → z ≠ 0) := by
  set M : ℤ[X] := X ^ 2 + X - 1 with hM
  have hMm : M.Monic := by
    rw [hM]
    have : (X ^ 2 + X - 1 : ℤ[X]) = X ^ 2 + (X - C 1) := by simp; ring
    rw [this]
    exact monic_X_pow_add (by rw [degree_X_sub_C]; norm_num)
  have hMdeg : M.natDegree = 2 := by
    rw [hM]
    have : (X ^ 2 + X - 1 : ℤ[X]) = X ^ 2 + (X - C 1) := by simp; ring
    rw [this, natDegree_add_eq_left_of_natDegree_lt]
    · simp
    · rw [natDegree_X_sub_C]; simp
  set R := Q %ₘ M with hR
  have hdecomp : Q = M * (Q /ₘ M) + R := by
    have := modByMonic_add_div Q M
    rw [hR]; linear_combination -this
  have hRdeg : R.natDegree ≤ 1 := by
    have hM1 : M ≠ 1 := by
      intro h; rw [h] at hMdeg; simp at hMdeg
    have := natDegree_modByMonic_lt Q hMm hM1
    rw [hMdeg, ← hR] at this; omega
  have hRform : R = C (R.coeff 0) + C (R.coeff 1) * X := by
    conv_lhs => rw [eq_X_add_C_of_natDegree_le_one hRdeg]
    ring
  set a := R.coeff 0
  set b := R.coeff 1
  have hMt : aeval tR M = 0 := by
    rw [hM]; simp; linear_combination tR_sq
  have hMg : aeval (-Real.goldenRatio) M = 0 := by
    rw [hM]; simp only [map_sub, map_add, map_pow, aeval_X, map_one]
    linear_combination gold_sq
  have hQt : aeval tR Q = a + b * tR := by
    rw [hdecomp, map_add, map_mul, hMt, zero_mul, zero_add, hRform]; simp
  have hQg : aeval (-Real.goldenRatio) Q = a - b * Real.goldenRatio := by
    rw [hdecomp, map_add, map_mul, hMg, zero_mul, zero_add, hRform]; simp; ring
  refine ⟨a ^ 2 - a * b - b ^ 2, ?_, ?_⟩
  · rw [hQt, hQg, gold_eq]
    push_cast
    linear_combination (-(b : ℝ) ^ 2) * tR_sq
  · intro hne hz
    apply hne
    rw [hQt]
    -- `a² − ab − b² = 0` forces `b = 0` (irrationality of `√5`), hence `a = 0`.
    have hb : b = 0 := by
      by_contra hb
      have hirr : Irrational √5 := Nat.Prime.irrational_sqrt (by norm_num : Nat.Prime 5)
      apply hirr
      have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb
      have hsq : (((2 * a - b : ℤ) : ℝ) / b) ^ 2 = 5 := by
        have : ((2 * a - b) ^ 2 : ℤ) = 5 * b ^ 2 := by linear_combination 4 * hz
        have hR : (((2 * a - b) ^ 2 : ℤ) : ℝ) = ((5 * b ^ 2 : ℤ) : ℝ) := by rw [this]
        push_cast at hR ⊢
        field_simp
        linarith
      refine ⟨|((2 * a - b : ℤ) : ℚ) / b|, ?_⟩
      rw [Rat.cast_abs, Rat.cast_div, Rat.cast_intCast, Rat.cast_intCast,
        ← Real.sqrt_sq (abs_nonneg _), sq_abs, hsq]
    have ha : a = 0 := by
      rw [hb] at hz; simpa using hz
    rw [ha, hb]; simp

/-! ### The final estimate -/

theorem bK_lower (K : ℕ) : (2 : ℝ) / 9 * ((K : ℝ) ^ 3 - K) ≤ 2 * (bK K : ℝ) := by
  have haj : ∀ j : ℕ, j * (j + 1) ≤ 6 * aj j := by
    intro j
    induction j with
    | zero => simp [aj]
    | succ j ih =>
      have : aj (j + 1) = aj j + (j + 1 + 2) / 3 := by
        unfold aj; rw [Finset.sum_Icc_succ_top (by omega)]
      rw [this]
      have : 3 * ((j + 1 + 2) / 3) ≥ j + 1 := by omega
      nlinarith
  have hsum : ∀ K : ℕ, (K : ℝ) ^ 3 - K = 3 * ∑ j ∈ range K, ((j : ℝ) * (j + 1)) := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Finset.sum_range_succ, mul_add, ← ih]; push_cast; ring
  rw [hsum]
  unfold bK
  push_cast
  rw [show (2 : ℝ) / 9 * (3 * ∑ j ∈ range K, (j : ℝ) * (j + 1)) =
      ∑ j ∈ range K, 2 / 9 * (3 * ((j : ℝ) * (j + 1))) by rw [Finset.mul_sum, Finset.mul_sum]]
  refine le_trans (Finset.sum_le_sum (g := fun i => 2 * (2 * (aj i : ℝ))) ?_)
    (le_of_eq (by rw [Finset.mul_sum, Finset.mul_sum]))
  intro j _
  have := haj j
  have hR : ((j : ℝ) * (j + 1)) ≤ 6 * (aj j : ℝ) := by exact_mod_cast this
  nlinarith

/-- Eventually `C (1 + log K)² + M < ε K`. -/
theorem eventually_log_sq_lt (C M ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ K : ℕ in atTop, C * (1 + Real.log K) ^ 2 + M < ε * K := by
  have h1 : Tendsto (fun x : ℝ => Real.log x ^ 2 / (1 * x + 0)) atTop (𝓝 0) :=
    Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
  have h2 : Tendsto (fun x : ℝ => Real.log x ^ 1 / (1 * x + 0)) atTop (𝓝 0) :=
    Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have h3 : Tendsto (fun x : ℝ => (|C| + |M| + 1) * x⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.const_mul (|C| + |M| + 1)
  have hsum : Tendsto (fun x : ℝ => |C| * (Real.log x ^ 2 / (1 * x + 0)) +
      2 * |C| * (Real.log x ^ 1 / (1 * x + 0)) + (|C| + |M| + 1) * x⁻¹) atTop (𝓝 0) := by
    simpa using ((h1.const_mul |C|).add (h2.const_mul (2 * |C|))).add h3
  have hev := (hsum.eventually (gt_mem_nhds hε)).and
    ((eventually_ge_atTop (1 : ℝ)))
  have hevN := tendsto_natCast_atTop_atTop.eventually hev
  filter_upwards [hevN] with K ⟨hK, hK1⟩
  have hKpos : (0 : ℝ) < K := by linarith
  have hlog : 0 ≤ Real.log K := Real.log_nonneg hK1
  simp only [one_mul, add_zero, pow_one] at hK
  have key : |C| * (1 + Real.log K) ^ 2 + |M| <
      ε * K := by
    have := (mul_lt_mul_iff_of_pos_right hKpos).mpr hK
    have e : (|C| * (Real.log K ^ 2 / K) + 2 * |C| * (Real.log K / K) +
        (|C| + |M| + 1) * (K : ℝ)⁻¹) * K =
        |C| * (1 + Real.log K) ^ 2 + |M| + 1 := by
      field_simp; ring
    rw [e] at this; linarith
  have hC : C * (1 + Real.log K) ^ 2 ≤ |C| * (1 + Real.log K) ^ 2 :=
    mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
  linarith [le_abs_self M]

/-- **Main theorem, conditional form.** -/
theorem irrational_zetaF3_of (hD : DecayBound) (hC : ConjBound) (hI : Integrality)
    (hc : CostBound) (hN : Nonvanishing) : Irrational zetaF3 := by
  rintro ⟨q, hq⟩
  obtain ⟨C1, hC1, hD⟩ := hD
  obtain ⟨C2, hC2, hC⟩ := hC
  obtain ⟨C3, hc⟩ := hc
  set a : ℤ := q.num
  set b : ℕ := q.den
  have hb : (0 : ℝ) < b := by exact_mod_cast q.den_pos
  set φ := Real.goldenRatio
  have hφ1 : 1 < φ := Real.one_lt_goldenRatio
  have hlogφ : 0 < Real.log φ := Real.log_pos hφ1
  set u : ℝ → ℝ := fun τ => a * (1 + 2 * τ) / (25 * b) with hu
  have hq' : zetaF3 = a / b := by rw [← hq]; exact (Rat.cast_def q)
  have hs5 : (0 : ℝ) < √5 := by positivity
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hXi : XiR = u tR := by
    have h := zetaF3_eq
    rw [hq'] at h
    have h' : (a : ℝ) = 5 * √5 * XiR * b := by rw [div_eq_iff hb.ne'] at h; linarith
    rw [hu]; simp only
    rw [← sqrt5_eq, eq_div_iff (by positivity)]
    linear_combination (-√5) * h' - 5 * XiR * b * h5
  have hXi' : -XiR = u (-φ) := by
    rw [hXi, hu]; simp only
    rw [← sqrt5_eq, neg_gold_add]; ring
  -- the integer polynomial `Q_K`
  have hY : ∀ K : ℕ, ∃ (N : ℕ) (Q : ℤ[X]), ∀ τ : ℝ, τ ≠ 0 → (∀ m : ℕ, 0 < m → τ ^ m ≠ 1) →
      τ ^ N * (aeval τ (CKpoly K) * (25 * b) ^ K * (Delta τ K).eval (u τ)) = aeval τ Q := by
    intro K
    choose n A hA using hI K
    refine ⟨∑ i ∈ range (K + 1), n i, ∑ i ∈ range (K + 1),
      A i * X ^ (∑ j ∈ range (K + 1), n j - n i) * C ((25 * (b : ℤ)) ^ (K - i) * a ^ i) *
        (1 + 2 * X) ^ i, ?_⟩
    intro τ hτ hroot
    rw [eval_eq_sum_range' (Nat.lt_succ_of_le (natDegree_Delta_le τ K)), Finset.mul_sum,
      Finset.mul_sum, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hiK : i ≤ K := Nat.lt_succ_iff.mp (mem_range.mp hi)
    have hni : n i ≤ ∑ j ∈ range (K + 1), n j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le _) hi
    have hAi := hA i τ hτ hroot
    have hτn : τ ^ n i ≠ 0 := pow_ne_zero _ hτ
    simp only [map_mul, map_pow, aeval_X, aeval_C, map_add, map_one, eq_intCast, map_natCast,
      map_intCast, map_ofNat]
    have hpow : τ ^ (∑ j ∈ range (K + 1), n j) =
        τ ^ (∑ j ∈ range (K + 1), n j - n i) * τ ^ n i := by
      rw [← pow_add, Nat.sub_add_cancel hni]
    have hpowb : ((25 : ℝ) * b) ^ K = (25 * b) ^ (K - i) * (25 * b) ^ i := by
      rw [← pow_add, Nat.sub_add_cancel hiK]
    rw [hpow, hpowb]
    have hub : (u τ) ^ i * (25 * b) ^ i = (a * (1 + 2 * τ)) ^ i := by
      rw [← mul_pow]; congr 1; exact div_mul_cancel₀ _ (by positivity)
    calc τ ^ (∑ j ∈ range (K + 1), n j - n i) * τ ^ n i *
          (aeval τ (CKpoly K) * ((25 * b) ^ (K - i) * (25 * b) ^ i) *
            ((Delta τ K).coeff i * u τ ^ i))
        = τ ^ (∑ j ∈ range (K + 1), n j - n i) * (τ ^ n i *
            (aeval τ (CKpoly K) * (Delta τ K).coeff i)) * (25 * b) ^ (K - i) *
            ((u τ) ^ i * (25 * b) ^ i) := by ring
      _ = _ := by
        rw [hAi, hub, mul_div_cancel₀ _ hτn, mul_pow (a : ℝ)]
        push_cast
        ring
  -- nonvanishing points of `t` and `−φ`
  have ht0 : tR ≠ 0 := tR_pos.ne'
  have htr : ∀ m : ℕ, 0 < m → tR ^ m ≠ 1 := pow_ne_one_of_abs_ne_one (by
    rw [abs_of_pos tR_pos]; exact tR_lt_one.ne)
  have hg0 : -φ ≠ 0 := by linarith
  have hgr : ∀ m : ℕ, 0 < m → (-φ) ^ m ≠ 1 := pow_ne_one_of_abs_ne_one (by
    rw [abs_neg, abs_of_pos (by linarith)]; exact hφ1.ne')
  -- the key inequality for every `K` with `Δ_K(Ξ) ≠ 0`
  have hkey : ∀ K : ℕ, 1 ≤ K → (Delta tR K).eval XiR ≠ 0 →
      (11 / 900 : ℝ) * K ^ 3 * Real.log φ ≤
        C3 * K ^ 2 * (1 + Real.log K) ^ 2 +
          K ^ 2 * (2 * |Real.log (25 * b)| + |Real.log (C1 * C2)| + Real.log φ) := by
    intro K hK hne
    obtain ⟨N, Q, hQ⟩ := hY K
    have hQt := hQ tR ht0 htr
    have hQg := hQ (-φ) hg0 hgr
    rw [← hXi] at hQt
    rw [← hXi'] at hQg
    obtain ⟨z, hz, hz0⟩ := norm_ne_zero Q
    have hCt := aeval_CKpoly_ne_zero htr K
    have hQt0 : aeval tR Q ≠ 0 := by
      rw [← hQt]
      exact mul_ne_zero (pow_ne_zero _ ht0) (mul_ne_zero (mul_ne_zero hCt (by positivity)) hne)
    have hz1 : (1 : ℝ) ≤ |(z : ℝ)| := by
      have := hz0 hQt0
      exact_mod_cast Int.one_le_abs this
    -- `|Q(t) Q(−φ)| = |Y(t)| |Y(−φ)|` since `|t (−φ)| = 1`
    set Yt := aeval tR (CKpoly K) * (25 * b) ^ K * (Delta tR K).eval XiR
    set Yg := aeval (-φ) (CKpoly K) * (25 * b) ^ K * (Delta (-φ) K).eval (-XiR)
    have hprod : |(z : ℝ)| = |Yt| * |Yg| := by
      rw [← hz, ← hQt, ← hQg]
      have e : tR ^ N * Yt * ((-φ) ^ N * Yg) = (tR * (-φ)) ^ N * (Yt * Yg) := by rw [mul_pow]; ring
      rw [e, mul_neg, tR_mul_gold, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    have hDt := hD K hK
    have hDg := hC K hK
    have hcK := hc K hK
    set P := |aeval tR (CKpoly K) * aeval (-φ) (CKpoly K)|
    have hbig : (1 : ℝ) ≤ P * (25 * b) ^ (2 * K) * (C1 * C2) ^ (K ^ 2) *
        tR ^ (2 * bK K + K ^ 2 * (K + 1)) := by
      calc (1 : ℝ) ≤ |Yt| * |Yg| := by rw [← hprod]; exact hz1
        _ = P * (25 * b) ^ (2 * K) * (|(Delta tR K).eval XiR| *
              |(Delta (-φ) K).eval (-XiR)|) := by
            simp only [Yt, Yg, P, abs_mul, abs_pow]
            rw [abs_of_pos (by norm_num : (0 : ℝ) < 25), abs_of_pos hb]
            ring
        _ ≤ P * (25 * b) ^ (2 * K) * ((C1 ^ (K ^ 2) * tR ^ (2 * bK K)) *
              (C2 ^ (K ^ 2) * tR ^ (K ^ 2 * (K + 1)))) := by
            apply mul_le_mul_of_nonneg_left _ (mul_nonneg (abs_nonneg _) (by positivity))
            exact mul_le_mul hDt hDg (abs_nonneg _)
              (mul_nonneg (pow_nonneg hC1.le _) (pow_nonneg tR_pos.le _))
        _ = _ := by rw [mul_pow, pow_add]; ring
    have hPpos : 0 < P := by
      have hP0 : 0 ≤ P := abs_nonneg _
      rcases hP0.lt_or_eq with h | h
      · exact h
      · exfalso; rw [← h] at hbig; simp at hbig; linarith
    have hlog := Real.log_le_log one_pos hbig
    rw [Real.log_one, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_pow, log_tR] at hlog
    have hbK := bK_lower K
    have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK
    push_cast at hlog
    have hK2 : (K : ℝ) ≤ K ^ 2 := by nlinarith only [hKR]
    have e1a := mul_le_mul_of_nonneg_left (le_abs_self (Real.log (25 * b)))
      (by positivity : (0 : ℝ) ≤ 2 * K)
    have e1b := mul_le_mul_of_nonneg_right hK2 (abs_nonneg (Real.log (25 * b)))
    have e2 := mul_le_mul_of_nonneg_left (le_abs_self (Real.log (C1 * C2))) (sq_nonneg (K : ℝ))
    have hb' := mul_le_mul_of_nonneg_right hbK hlogφ.le
    have hk' : (K : ℝ) * Real.log φ ≤ K ^ 2 * Real.log φ := mul_le_mul_of_nonneg_right hK2 hlogφ.le
    have hk3 : (0 : ℝ) ≤ K ^ 2 * Real.log φ := by positivity
    linarith only [hcK, hlog, hb', e1a, e1b, e2, hk', hk3]
  -- contradiction for large `K`
  have hev := eventually_log_sq_lt C3
    (2 * |Real.log (25 * b)| + |Real.log (C1 * C2)| + Real.log φ) (11 / 900 * Real.log φ)
    (by positivity)
  obtain ⟨K0, hK0⟩ := eventually_atTop.mp hev
  obtain ⟨K, hK, hne⟩ := hN (K0 + 1)
  have hK1 : 1 ≤ K := by omega
  have h1 := hkey K hK1 hne
  have h2 := hK0 K (by omega)
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK1
  have hK2 : (0 : ℝ) < K ^ 2 := by positivity
  have : (11 / 900 : ℝ) * K ^ 3 * Real.log φ =
      K ^ 2 * (11 / 900 * Real.log φ * K) := by ring
  rw [this] at h1
  have h3 : C3 * K ^ 2 * (1 + Real.log K) ^ 2 +
      K ^ 2 * (2 * |Real.log (25 * b)| + |Real.log (C1 * C2)| + Real.log φ) =
      K ^ 2 * (C3 * (1 + Real.log K) ^ 2 +
        (2 * |Real.log (25 * b)| + |Real.log (C1 * C2)| + Real.log φ)) := by ring
  rw [h3] at h1
  have := (mul_le_mul_iff_of_pos_left hK2).mp h1
  linarith

end FibZeta
