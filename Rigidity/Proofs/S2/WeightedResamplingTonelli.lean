import PercolationClusterHomogenization.Proofs.Density.PowerVarianceBound
import PercolationClusterHomogenization.Proofs.Density.WeightedResamplingTonelli

/-!
# Weighted sums of resampling energies

Tonelli's theorem moves a nonnegative endpoint weight outside the sum of independent-copy
resampling energies.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory ProbabilityTheory LatticeProb
open scoped ENNReal

/-- The total resampling energy is measurable. -/
theorem measurable_totalResamplingEnergy {ι : Type*} [DecidableEq ι] [Countable ι]
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (F : (ι → ℝ) → ℝ) (hF : Measurable F) :
    Measurable (totalResamplingEnergy ν F) := by
  apply Measurable.tsum
  intro i
  have hu : Measurable (fun q : (ι → ℝ) × (ι → ℝ) =>
      Function.update q.1 i (q.2 i)) :=
    (measurable_updateAt i).comp (measurable_fst.prodMk (measurable_pi_apply i |>.comp measurable_snd))
  exact (((hF.comp measurable_fst).sub (hF.comp hu)).pow_const 2).ennreal_ofReal.lintegral_prod_right'

end Rigidity.Proofs.S2

namespace Rigidity.Proofs.S2

open MeasureTheory ProbabilityTheory LatticeProb
open scoped ENNReal

end Rigidity.Proofs.S2
