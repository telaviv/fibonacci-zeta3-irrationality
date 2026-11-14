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

theorem irrational_zetaF3_of_integrality (hI : Integrality) : Irrational zetaF3 :=
  irrational_zetaF3_of Analytic.decayBound Conj.conjBound hI Cost.costBound NonVan.nonvanishing

end FibZeta
