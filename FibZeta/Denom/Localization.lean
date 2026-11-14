/-
Adapted from uplift-universal-inc/qzeta_3-irrationality, lean/QZeta3/GenericMoments.lean (Apache-2.0,
Lean formalisation by F. Solomon Admasu). Changes: rewritten for the Fibonacci construction (nodes
`w^{-a}`, moments `ν_k`, tails `ψ_N`), with the α-denominators `1 − α_k` (`k ≤ K − 2`) added.
-/
import FibZeta.Defs
import Mathlib.Algebra.Polynomial.Lifts

/-!
# Lemma 3.1: the localization ring of the construction

`LocalizationData R τ K` lists the inverses that the construction of `Delta τ K` needs: `τ⁻¹`,
`(1 − w^n)⁻¹` for `1 ≤ n ≤ K` and `(1 − α_k)⁻¹` for `1 ≤ k ≤ K − 2`.  Then every coefficient of
`Delta τ K` lies in `R` (`LocalizationData.Delta_coeff_mem`).  No other denominator occurs: the
quotient by the monic `F_K` is integral and only `ν_k` with `k ≤ K − 2` is used.
-/

open Polynomial Finset

namespace FibZeta.Denom

variable {𝕜 : Type*} [Field 𝕜]

/-! ### General helpers -/

theorem F_monic (τ : 𝕜) (K : ℕ) : (F τ K).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _

theorem F_natDegree (τ : 𝕜) (K : ℕ) : (F τ K).natDegree = K := by
  unfold F
  rw [Polynomial.natDegree_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _,
    Finset.sum_congr rfl fun _ _ => Polynomial.natDegree_X_sub_C _]
  simp

/-- At a labelled node the derivative of `F` is the product of the other node differences. -/
theorem derivative_F_eval_eq_prod (τ : 𝕜) (K a : ℕ) (ha : a ∈ Icc 1 K) :
    (derivative (F τ K)).eval (node τ a) =
      ∏ b ∈ (Icc 1 K).erase a, (node τ a - node τ b) := by
  have hF : F τ K = (X - C (node τ a)) * ∏ b ∈ (Icc 1 K).erase a, (X - C (node τ b)) :=
    (Finset.mul_prod_erase _ _ ha).symm
  rw [hF, Polynomial.derivative_mul, Polynomial.derivative_sub,
    Polynomial.derivative_X, Polynomial.derivative_C]
  simp [Polynomial.eval_prod]

theorem node_eq (τ : 𝕜) (a : ℕ) : node τ a = ((-τ ^ 2)⁻¹) ^ a := by
  rw [node, inv_pow]

/-- Coefficientwise membership is equivalent to lifting the polynomial to a subring. -/
theorem coeff_mem_iff_lifts (R : Subring 𝕜) (f : 𝕜[X]) :
    (∀ i, f.coeff i ∈ R) ↔ f ∈ Polynomial.liftsRing R.subtype := by
  rw [← Polynomial.lifts_iff_liftsRing, Polynomial.lifts_iff_coeff_lifts]
  constructor
  · intro h i
    exact ⟨⟨f.coeff i, h i⟩, rfl⟩
  · intro h i
    obtain ⟨x, hx⟩ := h i
    exact hx ▸ x.property

theorem C_mem_lifts (R : Subring 𝕜) (x : 𝕜) (hx : x ∈ R) :
    C x ∈ Polynomial.liftsRing R.subtype :=
  (Polynomial.lifts_iff_liftsRing _ _).mp (Polynomial.C'_mem_lifts ⟨⟨x, hx⟩, rfl⟩)

theorem X_mem_lifts (R : Subring 𝕜) : (X : 𝕜[X]) ∈ Polynomial.liftsRing R.subtype :=
  (Polynomial.lifts_iff_liftsRing _ _).mp (Polynomial.X_mem_lifts R.subtype)

theorem det_coeff_mem {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : Subring 𝕜) (M : Matrix ι ι 𝕜[X])
    (hM : ∀ a b i, (M a b).coeff i ∈ R) : ∀ i, M.det.coeff i ∈ R := by
  apply (coeff_mem_iff_lifts R M.det).mpr
  let T := Polynomial.liftsRing R.subtype
  have hentry : ∀ a b, M a b ∈ T := fun a b => (coeff_mem_iff_lifts R _).mp (hM a b)
  rw [Matrix.det_apply']
  apply T.sum_mem
  intro σ _
  exact T.mul_mem (intCast_mem T _) (T.prod_mem fun i _ => hentry (σ i) i)

/-- Monic division by a polynomial with coefficients in `R` preserves coefficients in `R`. -/
theorem divByMonic_coeff_mem (R : Subring 𝕜) (f g : 𝕜[X]) (hg : g.Monic)
    (hf : ∀ i, f.coeff i ∈ R) (hgR : ∀ i, g.coeff i ∈ R) (i : ℕ) : (f /ₘ g).coeff i ∈ R := by
  obtain ⟨f₀, hf₀⟩ := (Polynomial.mem_lifts f).mp
    ((Polynomial.lifts_iff_liftsRing _ _).mpr ((coeff_mem_iff_lifts R f).mp hf))
  obtain ⟨g₀, hg₀⟩ := (Polynomial.mem_lifts g).mp
    ((Polynomial.lifts_iff_liftsRing _ _).mpr ((coeff_mem_iff_lifts R g).mp hgR))
  have hg₀m : g₀.Monic := by
    rw [← hg₀] at hg
    exact Polynomial.monic_of_injective Subtype.val_injective hg
  have hmap : (f₀ /ₘ g₀).map R.subtype = f /ₘ g := by
    rw [Polynomial.map_divByMonic _ hg₀m, hf₀, hg₀]
  rw [← hmap, Polynomial.coeff_map]
  exact ((f₀ /ₘ g₀).coeff i).property

/-- `F` has coefficients in any subring containing `w⁻¹ = (−τ²)⁻¹`. -/
theorem F_coeff_mem (R : Subring 𝕜) (τ : 𝕜) (hw : (-τ ^ 2)⁻¹ ∈ R) (K i : ℕ) :
    (F τ K).coeff i ∈ R := by
  apply (coeff_mem_iff_lifts R _).mpr
  let T := Polynomial.liftsRing R.subtype
  apply T.prod_mem
  intro a _
  rw [node_eq]
  exact T.sub_mem (X_mem_lifts R) (C_mem_lifts R _ (R.pow_mem hw a))

theorem quotient_coeff_mem (R : Subring 𝕜) (τ : 𝕜) (hw : (-τ ^ 2)⁻¹ ∈ R) (K : ℕ)
    (f : 𝕜[X]) (hf : ∀ i, f.coeff i ∈ R) (i : ℕ) : (f /ₘ F τ K).coeff i ∈ R :=
  divByMonic_coeff_mem R f _ (F_monic τ K) hf (F_coeff_mem R τ hw K) i

theorem Lpoly_eq_sum_range (τ : 𝕜) (f : 𝕜[X]) (n : ℕ) (hn : f.natDegree < n) :
    Lpoly τ f = ∑ j ∈ range n, f.coeff j * nu τ j := by
  change f.sum (fun j c => c * nu τ j) = _
  exact f.sum_over_range' (f := fun j c => c * nu τ j) (fun j => zero_mul (nu τ j)) n hn

@[simp] theorem nu_zero (τ : 𝕜) : nu τ 0 = 0 := by simp [nu]

theorem natDegree_quotient_le (τ : 𝕜) (K : ℕ) (f : 𝕜[X]) {n : ℕ} (hf : f.natDegree ≤ n) :
    (f /ₘ F τ K).natDegree ≤ n - K := by
  rw [Polynomial.natDegree_divByMonic _ (F_monic τ K), F_natDegree]
  omega

/-! ### The localization data -/

/-- The concrete localization assumptions needed by the construction (Lemma 3.1). -/
structure LocalizationData (R : Subring 𝕜) (τ : 𝕜) (K : ℕ) : Prop where
  base_mem : τ ∈ R
  inv_base_mem : τ⁻¹ ∈ R
  inv_geom_mem : ∀ n ∈ Icc 1 K, (1 - (-τ ^ 2) ^ n)⁻¹ ∈ R
  inv_alpha_mem : ∀ k ∈ Icc 1 (K - 2), (1 - alpha τ k)⁻¹ ∈ R

namespace LocalizationData

variable {R : Subring 𝕜} {τ : 𝕜} {K : ℕ} (h : LocalizationData R τ K)

include h

theorem w_mem : -τ ^ 2 ∈ R := R.neg_mem (R.pow_mem h.base_mem 2)

theorem inv_w_mem : (-τ ^ 2)⁻¹ ∈ R := by
  rw [inv_neg, ← inv_pow]
  exact R.neg_mem (R.pow_mem h.inv_base_mem 2)

theorem node_mem (a : ℕ) : node τ a ∈ R := by
  rw [node_eq]; exact R.pow_mem h.inv_w_mem a

theorem inv_node_mem (a : ℕ) : (node τ a)⁻¹ ∈ R := by
  rw [node, inv_inv]; exact R.pow_mem h.w_mem a

/-- `node a − node b = w^{-a} (1 − w^{a-b})` up to sign and a unit. -/
theorem inv_difference_mem (a b : ℕ) (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) (ha : a ≤ K) (hb : b ≤ K)
    (hab : a ≠ b) :
    (node τ a - node τ b)⁻¹ ∈ R := by
  set w : 𝕜 := -τ ^ 2 with hw
  by_cases hτ : τ = 0
  · have : node τ a - node τ b = 0 := by
      simp [node, hτ, zero_pow (show a ≠ 0 by omega), zero_pow (show b ≠ 0 by omega)]
    rw [this, inv_zero]; exact R.zero_mem
  have hw0 : w ≠ 0 := by rw [hw]; exact neg_ne_zero.mpr (pow_ne_zero 2 hτ)
  rcases Nat.lt_or_gt_of_ne hab with hlt | hlt
  · have hgeom := h.inv_geom_mem (b - a) (mem_Icc.mpr ⟨by omega, by omega⟩)
    have heq : node τ a - node τ b = (w ^ b)⁻¹ * (w ^ (b - a) - 1) := by
      simp only [node, ← hw]
      have : w ^ b = w ^ a * w ^ (b - a) := by rw [← pow_add]; congr 1; omega
      rw [this]
      field_simp
    rw [heq, mul_inv, inv_inv, show w ^ (b - a) - 1 = -(1 - w ^ (b - a)) by ring, inv_neg]
    exact R.mul_mem (R.pow_mem h.w_mem b) (R.neg_mem hgeom)
  · have hgeom := h.inv_geom_mem (a - b) (mem_Icc.mpr ⟨by omega, by omega⟩)
    have heq : node τ a - node τ b = (w ^ a)⁻¹ * (1 - w ^ (a - b)) := by
      simp only [node, ← hw]
      have : w ^ a = w ^ b * w ^ (a - b) := by rw [← pow_add]; congr 1; omega
      rw [this]
      field_simp
    rw [heq, mul_inv, inv_inv]
    exact R.mul_mem (R.pow_mem h.w_mem a) hgeom

theorem inverse_derivative_mem (a : ℕ) (ha : a ∈ Icc 1 K) :
    ((derivative (F τ K)).eval (node τ a))⁻¹ ∈ R := by
  rw [derivative_F_eval_eq_prod τ K a ha, ← Finset.prod_inv_distrib]
  exact R.prod_mem fun b hb => h.inv_difference_mem a b (mem_Icc.mp ha).1
    (mem_Icc.mp (mem_erase.mp hb).2).1 (mem_Icc.mp ha).2
    (mem_Icc.mp (mem_erase.mp hb).2).2 (mem_erase.mp hb).1.symm

theorem res_mem (k a : ℕ) (ha : a ∈ Icc 1 K) : res τ K k a ∈ R := by
  rw [res, div_eq_mul_inv]
  exact R.mul_mem (R.pow_mem (h.node_mem a) _) (h.inverse_derivative_mem a ha)

theorem psi_mem (N : ℕ) (hN : N ∈ Icc 1 K) : psi τ N ∈ R := by
  rw [psi, div_eq_mul_inv, ← inv_pow]
  exact R.mul_mem (R.pow_mem h.base_mem _) (R.pow_mem (h.inv_geom_mem N hN) 3)

theorem S_mem (a : ℕ) (ha : a ≤ K) : S τ a ∈ R := by
  unfold S
  apply R.sum_mem
  intro b hb
  exact h.psi_mem b (mem_Icc.mpr ⟨(mem_Icc.mp hb).1, (mem_Icc.mp hb).2.trans ha⟩)

theorem nu_mem (j : ℕ) (hj : j ≤ K - 2) : nu τ j ∈ R := by
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · rw [nu_zero]; exact R.zero_mem
  · rw [nu, div_eq_mul_inv, alpha]
    exact R.mul_mem (R.mul_mem (R.mul_mem (natCast_mem R j)
      (R.add_mem (natCast_mem R j) R.one_mem)) (R.mul_mem (R.neg_mem h.base_mem)
        (R.pow_mem h.w_mem j)))
      (h.inv_alpha_mem j (mem_Icc.mpr ⟨hj0, hj⟩))

theorem mLin_mem (k : ℕ) : mLin τ K k ∈ R := by
  unfold mLin
  apply R.neg_mem
  apply R.mul_mem (by simp)
  apply R.sum_mem
  intro a ha
  exact R.mul_mem (h.res_mem k a ha) (R.pow_mem h.base_mem a)

theorem Lpoly_mem (f : 𝕜[X]) (hf : ∀ i, f.coeff i ∈ R) (hdeg : f.natDegree ≤ K - 2) :
    Lpoly τ f ∈ R := by
  unfold Lpoly
  apply R.sum_mem
  intro i hi
  exact R.mul_mem (hf i) (h.nu_mem i
    ((Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hi)).trans hdeg))

theorem quotient_moment_mem (k : ℕ) (hk : k ≤ 2 * K - 2) :
    Lpoly τ (X ^ k /ₘ F τ K) ∈ R := by
  apply h.Lpoly_mem _ (quotient_coeff_mem R τ h.inv_w_mem K _ (fun i => by
    rw [coeff_X_pow]; split_ifs
    · exact R.one_mem
    · exact R.zero_mem))
  have := natDegree_quotient_le τ K (X ^ k : 𝕜[X]) (n := k) (by rw [natDegree_X_pow])
  omega

theorem mConst_mem (k : ℕ) (hk : k ≤ 2 * K - 2) : mConst τ K k ∈ R := by
  unfold mConst
  apply R.add_mem (h.quotient_moment_mem k hk)
  apply R.mul_mem (by simp)
  apply R.sum_mem
  intro a ha
  exact R.mul_mem (R.mul_mem (h.res_mem k a ha) (R.pow_mem h.base_mem a))
    (h.S_mem a (mem_Icc.mp ha).2)

theorem nrm_mem : nrm τ K ∈ R := by
  unfold nrm
  rw [← inv_pow]
  exact R.mul_mem (R.pow_mem (R.neg_mem R.one_mem) K) (R.pow_mem h.inv_w_mem _)

/-- **Lemma 3.1.** Every coefficient of `Delta τ K` lies in `R`. -/
theorem Delta_coeff_mem (i : ℕ) : (Delta τ K).coeff i ∈ R := by
  unfold Delta
  apply det_coeff_mem R
  intro a b j
  let T := Polynomial.liftsRing R.subtype
  have hp := T.add_mem (T.mul_mem (X_mem_lifts R)
      (C_mem_lifts R (nrm τ K * mLin τ K (a.val + b.val)) (R.mul_mem h.nrm_mem (h.mLin_mem _))))
    (C_mem_lifts R (nrm τ K * mConst τ K (a.val + b.val))
      (R.mul_mem h.nrm_mem (h.mConst_mem _ (by have := a.isLt; have := b.isLt; omega))))
  have he : ((X : 𝕜[X]) • (hankelLin τ K).map C + (hankelConst τ K).map C) a b =
      X * C (nrm τ K * mLin τ K (a.val + b.val)) + C (nrm τ K * mConst τ K (a.val + b.val)) := by
    simp [hankelLin, hankelConst]
  rw [he]
  exact (coeff_mem_iff_lifts R _).mpr hp j

end LocalizationData

end FibZeta.Denom
