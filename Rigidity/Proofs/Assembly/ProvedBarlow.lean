import Rigidity.Proofs.Assembly.PlanarDarioGu
import Rigidity.Proofs.Barlow.UpperBoundHolds

/-!
# Theorem 1.3 with the Gaussian upper bound of Barlow proved

The Gaussian upper bound of Barlow on the planar infinite cluster
(`Rigidity.Green.BarlowGaussianUpperBoundTwo`, Theorem 4 of Dario and Gu) is proved with no
hypothesis (`Rigidity.Barlow.barlowGaussianUpperBoundTwo_holds`). The two forms of Theorem 1.3 in
`Rigidity.Assembly.WithPlanarInputs` that take it, `fast_decay_of_sections_barlow` and
`fast_decay_of_flux_gradient_barlow`, are restated here without it. What remains are the other
inputs of Theorem 1 of Dario and Gu: `hSec` (Lemma 4.1, Proposition 4.3 and Proposition A.7 of
Dario and Gu with a common exponent `σ`), or Proposition 2.13 and Theorem 3 (Remark 1.3).
-/

namespace Rigidity.Assembly.WithProvedBarlow

open LatticeProb.Percolation Rigidity.Section5 Rigidity.Green

/-- **Theorem 1.3** of the paper in dimension two from the inputs `hSec` of Sections 2 and 4 of
Dario and Gu, the Gaussian upper bound of Barlow being proved. -/
theorem fast_decay_of_sections (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hSec : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      ∃ σ : ℝ, 0 < σ ∧ DarioGuApproxLemmaTwo p σ ∧ DarioGuTwoScaleErrorTwo p σ ∧
        DarioGuDensityGaussianTwo p σ) : FastDecayStmt p :=
  Rigidity.Assembly.WithPlanarInputs.fast_decay_of_sections_barlow p hpc hp1 hSec
    Rigidity.Barlow.barlowGaussianUpperBoundTwo_holds

/-- **Theorem 1.3** of the paper in dimension two from Proposition 2.13 and Theorem 3 of Dario and
Gu, the Gaussian upper bound of Barlow being proved. -/
theorem fast_decay_of_flux_gradient (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hflux : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      ∃ σ : ℝ, 0 < σ ∧ DarioGuFluxWeakNormTwo p σ)
    (hG3 : DarioGuGradientBoundTwo) : FastDecayStmt p :=
  Rigidity.Assembly.WithPlanarInputs.fast_decay_of_flux_gradient_barlow p hpc hp1 hflux hG3
    Rigidity.Barlow.barlowGaussianUpperBoundTwo_holds

end Rigidity.Assembly.WithProvedBarlow
