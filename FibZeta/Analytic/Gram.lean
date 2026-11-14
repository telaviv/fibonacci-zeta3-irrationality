/-
Adapted from uplift-universal-inc/qzeta_3-irrationality, lean/QZeta3/GramIdentity.lean (Apache-2.0,
Lean formalisation by F. Solomon Admasu). Changes: the functional `FibZeta.Lfun` with alternating
nodes; the Gram identity is stated for `FibZeta.Delta tR K` evaluated at `XiR`.
-/
import FibZeta.Analytic.Entry

/-!
# The real Gram determinant

* `numeratorFunctional K : ℝ[X] →ₗ[ℝ] ℝ`, `P ↦ L(P/D_K)`;
* `gramR K = [L(s^{i+j}/D_K)]` and `Delta_eval_eq_det : Δ_K(Ξ) = det gramR` (PROOF §1, "By Lemma 1").
-/

open Polynomial Finset Filter Topology

namespace FibZeta.Analytic

theorem DK_ne_zero {y : ℝ} (hy : |y| < 1) (K : ℕ) : DK K y ≠ 0 := by
  rw [DK]
  apply prod_ne_zero_iff.mpr
  intro a _
  have : |(-tR ^ 2) ^ a * y| < 1 := by
    rw [abs_mul]
    calc |(-tR ^ 2) ^ a| * |y| ≤ 1 * |y| :=
          mul_le_mul_of_nonneg_right (abs_w_pow_le_one a) (abs_nonneg y)
      _ < 1 := by rw [one_mul]; exact hy
  have := (abs_lt.mp this).2
  linarith

theorem contDiffAt_DK (K : ℕ) (y : ℝ) : ContDiffAt ℝ 2 (DK K) y := by
  have : DK K = fun s => ∏ a ∈ Icc 1 K, (1 - (-tR ^ 2) ^ a * s) := rfl
  rw [this]
  exact contDiffAt_prod fun a _ => contDiffAt_const.sub (contDiffAt_const.mul contDiffAt_id)

theorem good_frac_DK (K j : ℕ) : Good (fun y => y ^ j / DK K y) := fun x hx =>
  (contDiffAt_id.pow j).div (contDiffAt_DK K x) (DK_ne_zero hx K)

theorem poly_div_DK_eq_sum (K : ℕ) (P : ℝ[X]) :
    (fun y : ℝ => P.eval y / DK K y) =
      (fun y => ∑ j ∈ P.support, P.coeff j * (y ^ j / DK K y)) := by
  funext y
  rw [eval_eq_sum, Polynomial.sum_def, Finset.sum_div]
  apply sum_congr rfl
  intro j _
  ring

theorem good_poly_div_DK (K : ℕ) (P : ℝ[X]) : Good (fun y => P.eval y / DK K y) := by
  rw [poly_div_DK_eq_sum]
  exact good_sum _ _ fun j _ => good_const_mul (good_frac_DK K j) _

theorem hasL_poly_div_DK (K : ℕ) (P : ℝ[X]) :
    HasSum (Lterm (fun y => P.eval y / DK K y))
      (∑ j ∈ P.support, P.coeff j * (nrm tR K * (mConst tR K j + XiR * mLin tR K j))) := by
  rw [poly_div_DK_eq_sum]
  exact hasL_sum _ _ _ (fun j _ => good_const_mul (good_frac_DK K j) _)
    (fun j _ => hasL_const_mul (good_frac_DK K j) (hasL_fraction_DK K j) _)

theorem summable_poly_div_DK (K : ℕ) (P : ℝ[X]) :
    Summable (Lterm (fun y => P.eval y / DK K y)) :=
  (hasL_poly_div_DK K P).summable

theorem Lfun_poly_div_DK_add (K : ℕ) (P Q : ℝ[X]) :
    Lfun (fun y => (P + Q).eval y / DK K y) =
      Lfun (fun y => P.eval y / DK K y) + Lfun (fun y => Q.eval y / DK K y) := by
  have hs := hasL_add (good_poly_div_DK K P) (good_poly_div_DK K Q)
    (summable_poly_div_DK K P).hasSum (summable_poly_div_DK K Q).hasSum
  have he : (fun y => (P + Q).eval y / DK K y) =
      (fun y => P.eval y / DK K y + Q.eval y / DK K y) := by
    funext y; rw [eval_add, add_div]
  rw [he]
  exact hs.tsum_eq

theorem Lfun_poly_div_DK_smul (K : ℕ) (P : ℝ[X]) (c : ℝ) :
    Lfun (fun y => (c • P).eval y / DK K y) = c * Lfun (fun y => P.eval y / DK K y) := by
  have hs := hasL_const_mul (good_poly_div_DK K P) (summable_poly_div_DK K P).hasSum c
  have he : (fun y => (c • P).eval y / DK K y) = (fun y => c * (P.eval y / DK K y)) := by
    funext y; rw [eval_smul, smul_eq_mul]; ring
  rw [he]
  exact hs.tsum_eq

/-- `P ↦ L(P/D_K)` as a linear map. -/
noncomputable def numeratorFunctional (K : ℕ) : ℝ[X] →ₗ[ℝ] ℝ where
  toFun P := Lfun (fun y => P.eval y / DK K y)
  map_add' := Lfun_poly_div_DK_add K
  map_smul' c P := by
    simpa only [smul_eq_mul, RingHom.id_apply] using Lfun_poly_div_DK_smul K P c

/-- The real Gram matrix `[L(s^{i+j}/D_K)]`. -/
noncomputable def gramR (K : ℕ) : Matrix (Fin K) (Fin K) ℝ :=
  Matrix.of fun i j => Lfun (fun y => y ^ (i.val + j.val) / DK K y)

/-- `Δ_K(Ξ)` is the real Gram determinant. -/
theorem Delta_eval_eq_det (K : ℕ) : (Delta tR K).eval XiR = (gramR K).det := by
  unfold Delta
  rw [← coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, map_add, map_mul, coe_evalRingHom, eval_X, eval_C, hankelLin, hankelConst,
    Matrix.of_apply, gramR]
  rw [show Lfun (fun y => y ^ (i.val + j.val) / DK K y) = _ from
    (hasL_fraction_DK K (i.val + j.val)).tsum_eq]
  simp only [eval_add, eval_mul, eval_X, eval_C]
  ring

end FibZeta.Analytic
