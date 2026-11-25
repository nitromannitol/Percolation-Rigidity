import Rigidity.Proofs.Assembly.PlanarDarioGu
import Rigidity.Proofs.Barlow.GaussianHolds

/-!
# Theorem 1.3 with the Gaussian upper bound of Barlow proved from very good balls

The input `BarlowGaussianUpperBoundTwo` (Theorem 4 of Dario–Gu, Barlow 2004, Theorem 1) is
proved from the very good balls of the planar infinite cluster (`ClusterVeryGoodBallsTwo`,
Barlow's Theorem 2.18 and Lemma 2.19) in `barlowGaussianUpperBoundTwo_of_veryGood`. The two
theorems below restate `fast_decay_of_sections_barlow` and `fast_decay_of_flux_gradient_barlow`
with that input replaced.
-/

namespace Rigidity.Assembly.WithPlanarInputs

open LatticeProb.Percolation Rigidity.Section5 Rigidity.Green Rigidity.Barlow

/-- **Theorem 1.3** in dimension two from the inputs `hSec` of Sections 2 and 4 of Dario and Gu and
the very good balls of the cluster. -/
theorem fast_decay_of_sections_veryGood (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hSec : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      ∃ σ : ℝ, 0 < σ ∧ DarioGuApproxLemmaTwo p σ ∧ DarioGuTwoScaleErrorTwo p σ ∧
        DarioGuDensityGaussianTwo p σ)
    (hVG : ClusterVeryGoodBallsTwo) : FastDecayStmt p :=
  fast_decay_of_sections_barlow p hpc hp1 hSec (barlowGaussianUpperBoundTwo_of_veryGood hVG)

/-- **Theorem 1.3** in dimension two from Proposition 2.13 and Theorem 3 of Dario and Gu and the
very good balls of the cluster. -/
theorem fast_decay_of_flux_gradient_veryGood (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hflux : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      ∃ σ : ℝ, 0 < σ ∧ DarioGuFluxWeakNormTwo p σ)
    (hG3 : DarioGuGradientBoundTwo) (hVG : ClusterVeryGoodBallsTwo) : FastDecayStmt p :=
  fast_decay_of_flux_gradient_barlow p hpc hp1 hflux hG3
    (barlowGaussianUpperBoundTwo_of_veryGood hVG)

end Rigidity.Assembly.WithPlanarInputs
