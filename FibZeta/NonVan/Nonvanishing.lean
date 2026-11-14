import FibZeta.Statements
import FibZeta.NonVan.Algebra
import FibZeta.NonVan.Interp

-- Adapted from uplift-universal-inc/qzeta_3-irrationality, lean/QZeta3/Nonvanishing.lean and
-- lean/QZeta3/Frozen/Prop51.lean (Apache-2.0, Lean formalisation by F. Solomon Admasu). Changes: assembled
-- for the formal Hankel matrix of `Defs.lean` at `τ = t`, `X = Ξ`, with nodes `x_a = w^{−a}`.

/-!
# Proposition 5: `Δ_K(Ξ) ≠ 0` for infinitely many `K`

`nonvanishing : Nonvanishing` is proved outright: the argument only uses the formal functional
`L_Ξ` of `Defs.lean` (polynomial moments `ν_k` plus pole moments `2t^a(Ξ − S_a)`), so the
`EntryIdentity` (which identifies it with the real functional `Lfun`) is not needed.
`nonvanishing_of_entry` is the requested interface form.
-/

open Polynomial Finset Filter Topology

namespace FibZeta.NonVan

/-- The interpolation nodes `x_{a+1} = w^{−(a+1)}`. -/
noncomputable def nodeSeq (a : ℕ) : ℝ := node tR (a + 1)

theorem nodeSeq_injective : Function.Injective nodeSeq := by
  intro a b h
  have := node_injective h
  omega

theorem nodeSeq_inv_tendsto : Tendsto (fun a => (nodeSeq a)⁻¹) atTop (𝓝[≠] 0) := by
  have heq : (fun a => (nodeSeq a)⁻¹) = fun a => (-tR ^ 2 : ℝ) ^ (a + 1) := by
    funext a; simp [nodeSeq, node]
  rw [heq]
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_, Eventually.of_forall (fun a => w_pow_ne_zero (a + 1))⟩
  have hw : ‖(-tR ^ 2 : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_neg, abs_of_pos tsq_pos]; exact tsq_lt_one
  exact (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hw).comp (tendsto_add_atTop_nat 1)

/-- Every orthogonal numerator has the required Cauchy interpolant. -/
theorem cauchy_orthogonal_interpolant (n : ℕ) (Q : ℝ[X])
    (horth : ∀ j : Fin n, Ln n (X ^ j.val * Q) = 0) :
    ∃ P : ℝ[X],
      Tendsto (fun x => cauchyF x * Q.eval x - P.eval x) atTop (𝓝 0) ∧
      ∀ a, a < n → cauchyF (nodeSeq a) * Q.eval (nodeSeq a) - P.eval (nodeSeq a) = 0 := by
  refine ⟨cauchyPart Q, tendsto_cauchyPart_error Q, ?_⟩
  intro a ha
  apply cauchyPart_interpolates Q horth
  simp only [Finset.mem_Icc]
  omega

/-- **Proposition 5.** `Δ_K(Ξ) ≠ 0` for infinitely many `K`. -/
theorem nonvanishing : Nonvanishing := by
  intro N
  obtain ⟨n, hn, hdet⟩ := frequently_nonsingular_of_meromorphic_nonrational cauchyF nodeSeq
    nodeSeq_injective nodeSeq_inv_tendsto Ln meromorphicAt_cauchyF_inv cauchyF_nonrational
    (fun n _ Q _ _ horth => cauchy_orthogonal_interpolant n Q horth) N
  refine ⟨n, hn, ?_⟩
  rw [Delta_eval]
  exact mul_ne_zero (pow_ne_zero _ (nrm_ne_zero n)) hdet

/-- **Proposition 5**, in the requested interface form (the hypothesis is not used). -/
theorem nonvanishing_of_entry (_hE : EntryIdentity) : Nonvanishing := nonvanishing

end FibZeta.NonVan
