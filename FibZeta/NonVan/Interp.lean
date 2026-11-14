import FibZeta.NonVan.Pole

-- Adapted from uplift-universal-inc/qzeta_3-irrationality, lean/QZeta3/CauchyInterpolation.lean and
-- lean/QZeta3/Nonvanishing.lean (Apache-2.0, Lean formalisation by F. Solomon Admasu). Changes: the
-- functional is the formal one of `Defs.lean` (`L_X` at `X = Ξ`, polynomial quotient plus residues)
-- instead of a real functional with derivatives; interpolation is a polynomial identity.

/-!
# Orthogonal polynomials interpolate the Cauchy transform (PROOF §5)

We work directly with the formal Hankel matrix of `Defs.lean` at `τ = t`, `X = Ξ`:

* `Ln n` : the linear functional `P ↦ L_Ξ(P/F_n) = Lpoly(P /ₘ F_n) + ∑_a P(x_a)/F_n'(x_a) · 2t^a(S_a − Ξ)`;
  `Ln n (s^k) = mConst + Ξ · mLin` (`Ln_X_pow`);
* `Delta_eval` : `Δ_n(Ξ) = nrm^n · det[Ln n (s^{i+j})]`;
* `cauchyPart_interpolates` : if `Ln n (s^j Q) = 0` for `j < n`, then `𝓕 Q − T` vanishes at
  every node `x_a = w^{−a}`, `1 ≤ a ≤ n`, where `T` is the polynomial part of `𝓕 Q` at infinity;
* `tendsto_cauchyPart_error` : `𝓕 Q − T → 0` at `+∞`.

The real functional `Lfun` is not needed: the only analytic input is `𝓕(x_a) = 2t^a(Ξ − S_a)`
(`cauchyF_node`), which is the formal pole moment `−L_Ξ(1/(s − x_a))`.
-/

open Polynomial Finset Filter Topology

namespace FibZeta.NonVan

/-! ### The functional on polynomials -/

/-- `Lpoly` at `τ = t` as a linear map. -/
noncomputable def LpolyLin : ℝ[X] →ₗ[ℝ] ℝ :=
  Polynomial.lsum (fun j => (nu tR j) • LinearMap.id)

theorem LpolyLin_apply (f : ℝ[X]) : LpolyLin f = Lpoly tR f := by
  simp only [LpolyLin, Polynomial.lsum_apply, LinearMap.smul_apply, LinearMap.id_apply,
    smul_eq_mul, Polynomial.sum_def, Lpoly]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

theorem Lpoly_X_pow (j : ℕ) : Lpoly tR (X ^ j : ℝ[X]) = nu tR j := by
  simp [Lpoly, Polynomial.support_X_pow]

theorem F_monic (n : ℕ) : (F tR n).Monic :=
  monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)

theorem F_natDegree (n : ℕ) : (F tR n).natDegree = n := by
  unfold F
  rw [natDegree_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)]
  simp

/-- The linear functional `L_Ξ(P/F_n)`. -/
noncomputable def Ln (n : ℕ) : ℝ[X] →ₗ[ℝ] ℝ :=
  LpolyLin ∘ₗ divByMonicHom (F tR n) +
    ∑ a ∈ Icc 1 n, (2 * tR ^ a * (S tR a - XiR) / (derivative (F tR n)).eval (node tR a)) •
      leval (node tR a)

theorem Ln_apply (n : ℕ) (P : ℝ[X]) :
    Ln n P = Lpoly tR (P /ₘ F tR n) + ∑ a ∈ Icc 1 n,
      2 * tR ^ a * (S tR a - XiR) / (derivative (F tR n)).eval (node tR a) *
        P.eval (node tR a) := by
  simp only [Ln, LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, leval_apply, smul_eq_mul,
    LpolyLin_apply]
  rfl

theorem Ln_X_pow (n k : ℕ) : Ln n (X ^ k) = mConst tR n k + XiR * mLin tR n k := by
  rw [Ln_apply, mConst, mLin, add_assoc]
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  simp only [res, eval_pow, eval_X]
  ring

theorem nrm_ne_zero (n : ℕ) : nrm tR n ≠ 0 := by
  unfold nrm
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (inv_ne_zero (w_pow_ne_zero _))

/-- `Δ_n(Ξ) = nrm^n · det[L_Ξ(s^{i+j}/F_n)]`. -/
theorem Delta_eval (n : ℕ) :
    (Delta tR n).eval XiR =
      nrm tR n ^ n * (Matrix.of fun i j : Fin n => Ln n (X ^ (i.val + j.val))).det := by
  unfold Delta
  rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
  have hM : (evalRingHom XiR).mapMatrix
      ((X : ℝ[X]) • (hankelLin tR n).map C + (hankelConst tR n).map C) =
      nrm tR n • Matrix.of fun i j : Fin n => Ln n (X ^ (i.val + j.val)) := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, coe_evalRingHom, eval_add, eval_mul, eval_X, eval_C, hankelLin, hankelConst,
      Matrix.of_apply, Ln_X_pow]
    ring
  rw [hM, Matrix.det_smul, Fintype.card_fin]

/-! ### Divided differences and the polynomial part at infinity -/

/-- Divided difference of a monomial, as a polynomial in the support variable. -/
noncomputable def monomialDivDiff (k : ℕ) (z : ℝ) : ℝ[X] :=
  ∑ j ∈ range k, C (z ^ (k - 1 - j)) * X ^ j

/-- Divided difference `(Q(z) − Q(s))/(z − s)`, as a polynomial in `s`. -/
noncomputable def realDivDiff (Q : ℝ[X]) (z : ℝ) : ℝ[X] :=
  ∑ k ∈ Q.support, Q.coeff k • monomialDivDiff k z

/-- The polynomial part of `𝓕 Q` at infinity: `∑_k Q_k ∑_{j<k} ν_j z^{k−1−j}`. -/
noncomputable def cauchyPart (Q : ℝ[X]) : ℝ[X] :=
  ∑ k ∈ Q.support, Q.coeff k • ∑ j ∈ range k, C (nu tR j) * X ^ (k - 1 - j)

theorem eval_monomialDivDiff (k : ℕ) (z x : ℝ) :
    (monomialDivDiff k z).eval x = ∑ j ∈ range k, z ^ (k - 1 - j) * x ^ j := by
  simp only [monomialDivDiff, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

theorem monomialDivDiff_identity (k : ℕ) (z x : ℝ) :
    (z - x) * (monomialDivDiff k z).eval x = z ^ k - x ^ k := by
  rw [eval_monomialDivDiff]
  have h := geom_sum₂_mul x z k
  simp_rw [mul_comm (x ^ _) (z ^ _)] at h
  nlinarith

theorem realDivDiff_identity (Q : ℝ[X]) (z x : ℝ) :
    (z - x) * (realDivDiff Q z).eval x = Q.eval z - Q.eval x := by
  simp only [realDivDiff, Polynomial.eval_finsetSum, Polynomial.eval_smul,
    smul_eq_mul, Finset.mul_sum]
  have hterm : ∀ k, (z - x) * (Q.coeff k * (monomialDivDiff k z).eval x) =
      Q.coeff k * (z ^ k - x ^ k) := by
    intro k
    rw [← mul_assoc, mul_comm (z - x) (Q.coeff k), mul_assoc, monomialDivDiff_identity]
  simp_rw [hterm, mul_sub]
  rw [Finset.sum_sub_distrib]
  simp only [Polynomial.eval_eq_sum, Polynomial.sum_def]

/-- As polynomials: `(s − z) · B = Q − Q(z)`. -/
theorem realDivDiff_mul (Q : ℝ[X]) (z : ℝ) :
    (X - C z) * realDivDiff Q z = Q - C (Q.eval z) := by
  apply Polynomial.funext
  intro x
  have h := realDivDiff_identity Q z x
  simp only [eval_mul, eval_sub, eval_X, eval_C]
  linarith

theorem cauchyPart_eval (Q : ℝ[X]) (z : ℝ) :
    (cauchyPart Q).eval z = Lpoly tR (realDivDiff Q z) := by
  rw [← LpolyLin_apply]
  simp only [cauchyPart, realDivDiff, monomialDivDiff, Polynomial.eval_finsetSum,
    Polynomial.eval_smul, smul_eq_mul, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [← Polynomial.smul_eq_C_mul, map_smul, LpolyLin_apply, Lpoly_X_pow, smul_eq_mul, mul_comm]

/-- `𝓕 Q − T → 0` at `+∞`. -/
theorem tendsto_cauchyPart_error (Q : ℝ[X]) :
    Tendsto (fun z => cauchyF z * Q.eval z - (cauchyPart Q).eval z) atTop (𝓝 0) := by
  have heq : ∀ z : ℝ,
      cauchyF z * Q.eval z - (cauchyPart Q).eval z =
      ∑ k ∈ Q.support, Q.coeff k * (cauchyF z * z ^ k - momentPolynomial k z) := by
    intro z
    simp only [cauchyPart, momentPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_smul,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
    congr 1
    rw [Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have h := tendsto_finsetSum Q.support (fun k _ =>
    (tendsto_cauchyF_monomial_sub k).const_mul (Q.coeff k))
  simpa only [heq, mul_zero, Finset.sum_const_zero] using h

/-! ### Interpolation at the nodes -/

/-- Orthogonality to monomials extends to every polynomial of lower degree. -/
theorem orthogonal_to_polynomial (L : ℝ[X] →ₗ[ℝ] ℝ) (Q H : ℝ[X]) {n : ℕ}
    (horth : ∀ j : Fin n, L (X ^ j.val * Q) = 0) (hH : H.natDegree < n) :
    L (H * Q) = 0 := by
  conv_lhs => rw [← Polynomial.sum_monomial_eq H]
  simp only [Polynomial.sum_def, Finset.sum_mul, map_sum]
  apply Finset.sum_eq_zero
  intro j hj
  have hjn : j < n := (Polynomial.le_natDegree_of_mem_supp j hj).trans_lt hH
  rw [← Polynomial.C_mul_X_pow_eq_monomial, ← Polynomial.smul_eq_C_mul,
    smul_mul_assoc, map_smul, horth ⟨j, hjn⟩, smul_zero]

theorem node_injective : Function.Injective (node tR) := by
  intro a b h
  unfold node at h
  exact w_pow_injective (inv_inj.mp h)

/-- The cofactor `H_a = ∏_{b ≠ a} (s − x_b)`. -/
noncomputable def cofactor (n a : ℕ) : ℝ[X] := ∏ b ∈ (Icc 1 n).erase a, (X - C (node tR b))

theorem F_eq_mul_cofactor {n a : ℕ} (ha : a ∈ Icc 1 n) :
    F tR n = (X - C (node tR a)) * cofactor n a := by
  unfold F cofactor
  exact (Finset.mul_prod_erase _ (fun b => X - C (node tR b)) ha).symm

theorem cofactor_monic (n a : ℕ) : (cofactor n a).Monic :=
  monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)

theorem cofactor_natDegree {n a : ℕ} (ha : a ∈ Icc 1 n) : (cofactor n a).natDegree = n - 1 := by
  unfold cofactor
  rw [natDegree_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)]
  simp [Finset.card_erase_of_mem ha]

theorem cofactor_eval_ne {n a : ℕ} {b : ℕ} (hb : b ∈ Icc 1 n) (hba : b ≠ a) :
    (cofactor n a).eval (node tR b) = 0 := by
  unfold cofactor
  rw [eval_prod]
  exact Finset.prod_eq_zero (mem_erase.mpr ⟨hba, hb⟩) (by simp)

theorem cofactor_eval_self (n a : ℕ) : (cofactor n a).eval (node tR a) ≠ 0 := by
  unfold cofactor
  rw [eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro b hb
  simp only [eval_sub, eval_X, eval_C]
  exact sub_ne_zero.mpr (fun h => (mem_erase.mp hb).1 (node_injective h).symm)

theorem derivative_F_eval {n a : ℕ} (ha : a ∈ Icc 1 n) :
    (derivative (F tR n)).eval (node tR a) = (cofactor n a).eval (node tR a) := by
  rw [F_eq_mul_cofactor ha, derivative_mul]
  simp

/-- The functional on `H_a Q`: polynomial part of the divided difference plus one residue. -/
theorem Ln_cofactor_mul {n a : ℕ} (ha : a ∈ Icc 1 n) (Q : ℝ[X]) :
    Ln n (cofactor n a * Q) = Lpoly tR (realDivDiff Q (node tR a)) +
      2 * tR ^ a * (S tR a - XiR) * Q.eval (node tR a) := by
  have hn := Finset.mem_Icc.mp ha
  have hHQ : cofactor n a * Q = C (Q.eval (node tR a)) * cofactor n a +
      F tR n * realDivDiff Q (node tR a) := by
    have h1 := realDivDiff_mul Q (node tR a)
    rw [F_eq_mul_cofactor ha]
    calc cofactor n a * Q = cofactor n a * ((X - C (node tR a)) * realDivDiff Q (node tR a) +
          C (Q.eval (node tR a))) := by rw [h1]; ring
      _ = _ := by ring
  have hdiv : (cofactor n a * Q) /ₘ F tR n = realDivDiff Q (node tR a) := by
    refine (div_modByMonic_unique _ (C (Q.eval (node tR a)) * cofactor n a) (F_monic n)
      ⟨hHQ.symm, ?_⟩).1
    calc degree (C (Q.eval (node tR a)) * cofactor n a) ≤ degree (cofactor n a) := by
          rw [← smul_eq_C_mul]; exact degree_smul_le _ _
      _ = (n - 1 : ℕ) := by rw [degree_eq_natDegree (cofactor_monic n a).ne_zero,
          cofactor_natDegree ha]
      _ < n := by exact_mod_cast (by omega : n - 1 < n)
      _ = degree (F tR n) := by rw [degree_eq_natDegree (F_monic n).ne_zero, F_natDegree]
  rw [Ln_apply, hdiv]
  congr 1
  rw [Finset.sum_eq_single a]
  · rw [eval_mul, derivative_F_eval ha]
    have := cofactor_eval_self n a
    field_simp
  · intro b hb hba
    rw [eval_mul, cofactor_eval_ne hb hba]
    ring
  · intro h; exact absurd ha h

/-- Orthogonality forces exact interpolation at each node of `F_n`. -/
theorem cauchyPart_interpolates {n : ℕ} (Q : ℝ[X])
    (horth : ∀ j : Fin n, Ln n (X ^ j.val * Q) = 0) {a : ℕ} (ha : a ∈ Icc 1 n) :
    cauchyF (node tR a) * Q.eval (node tR a) - (cauchyPart Q).eval (node tR a) = 0 := by
  have hdeg : (cofactor n a).natDegree < n := by
    rw [cofactor_natDegree ha]; have := Finset.mem_Icc.mp ha; omega
  have hzero := orthogonal_to_polynomial (Ln n) Q (cofactor n a) horth hdeg
  rw [Ln_cofactor_mul ha] at hzero
  rw [cauchyF_node, cauchyPart_eval]
  linear_combination (-1 : ℝ) * hzero

end FibZeta.NonVan
