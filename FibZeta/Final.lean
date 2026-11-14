import FibZeta.Main
import FibZeta.Analytic.All
import FibZeta.NonVan.Nonvanishing
import FibZeta.Conj.ConjBound
import FibZeta.Cost.CostBound

/-!
# The theorem, modulo `Integrality`

Combines the proved ingredients `DecayBound` (`FibZeta.Analytic.decayBound`), `ConjBound`
(`FibZeta.Conj.conjBound`), `CostBound` (`FibZeta.Cost.costBound`) and `Nonvanishing`
(`FibZeta.NonVan.nonvanishing`) with the assembly `FibZeta.irrational_zetaF3_of`.
-/

namespace FibZeta

/-- Sanity check for the statement: the series defining `zetaF3` converges, to `5√5 Ξ`. -/
theorem hasSum_zetaF3 : HasSum (fun n : ℕ => 1 / ((Nat.fib (n + 1) : ℕ) : ℝ) ^ 3) zetaF3 := by
  have hs : Summable (fun N => psi tR (N + 1)) :=
    (summable_nat_add_iff 1).mpr Conj.summable_psi_tR
  have h := (hs.mul_left (5 * √5)).hasSum
  rw [zetaF3_eq, XiR, ← tsum_mul_left]
  convert h using 2 with n
  exact one_div_fib_cube (n + 1)

theorem irrational_zetaF3_of_integrality (hI : Integrality) : Irrational zetaF3 :=
  irrational_zetaF3_of Analytic.decayBound Conj.conjBound hI Cost.costBound NonVan.nonvanishing

end FibZeta
