import PercolationClusterHomogenization.External.ClusterDensity
import Rigidity.Proofs.S2.ScaleInputsFaithful
import LatticeProb.Prob.Percolation.OpenGraphTranslation
import LatticeProb.Prob.Percolation.LatticeBondTranslationLaw
import PercolationClusterHomogenization.Proofs.Density.ClusterDensityFromDarioGu

/-!
# Proposition 2.6, step:2.6-inputs: the density of the infinite cluster from Dario–Gu

The density input of Proposition 2.6 (paper L508-511 of the corrected draft; correction C35) from
the concentration of the density of the infinite cluster in triadic cubes
(`Rigidity.External.ClusterDensityConcentrationInput`, Dario–Gu, arXiv:1909.10439v4,
Proposition A.1), by a union bound over triadic cubes.

* A triadic cube `□` of size `3^m` is *bad* if `| |𝒞_∞ ∩ □|/|□| - θ | ≥ θ/2`; by Proposition A.1
  and Markov's inequality, `P[□ bad] ≤ 2 exp(-((θ/2C) 3^{dm/2})^{s₀})`, `s₀ = 2(d-1)/(3d²+2d-1)`
  (`measure_badCubeEvent_le`).
* At the scale `3^m ≤ r/(100d) < 3^{m+1}`, every ball of radius `r/100` whose centre is within
  `r/100` of `x` contains a triadic cube of size `3^m` among the `K_d = (6d+5)^d` cubes `nearCubes x m`;
  if that cube is good, the ball contains at least `(θ/2) 3^{dm} ≥ (θ/2)(300d)^{-d} r^d` vertices
  of `𝒞_∞`.
* The minimal scale is `M(x) = 100d · 3^{N(x)}`, `N(x)` the first scale from which every scale is
  good (`exists_minimalScale_of_summable`; Borel–Cantelli). `E[exp(M^s)] < ∞` uniformly in `x`, for
  `s = d s₀/4`, because `P[scale m bad] ≤ 2 K_d exp(-B 3^{2sm})` beats `exp((100d 3^{m+1})^s)`.
* If `θ(p) = 0`, almost surely there is no infinite cluster (translation invariance), and the
  statement is empty.

Main results.
* `clusterDensityInputFaithful_of_concentration`: Proposition A.1 gives the printed density
  sentence `ClusterDensityInputFaithful`.
* `clusterDensityInputProposed_of_concentration`: Proposition A.1 gives
  `ClusterDensityInputProposed` (with `clusterDensityInputProposed_of_faithful`).
-/

namespace Rigidity.Proofs.S2

open MeasureTheory LatticeProb.Percolation Rigidity.External Rigidity.Steps.S2 Classical

variable {d : ℕ}

/-! ### Triadic cubes -/

/-! ### Markov's inequality, translation invariance -/

/-! ### Exponents and summability -/

/-! ### The minimal scale -/

/-! ### The union bound -/

/-- Dario–Gu concentration gives the density lower bound in every dimension. -/
theorem clusterDensityInputFaithful_of_concentration (hDG : ClusterDensityConcentrationInput) :
    ClusterDensityInputFaithful := by
  intro d _ hd p hpc hp1
  exact clusterDensityInputFaithfulAt_of_concentration hd p (hDG d hd p hpc hp1)

/-- **The density input of Proposition 2.6 from Dario–Gu, Proposition A.1**: the proposed form
(centres in `B̄_r(x)`), through the printed sentence and `clusterDensityInputProposed_of_faithful`. -/
theorem clusterDensityInputProposed_of_concentration (hDG : ClusterDensityConcentrationInput) :
    ClusterDensityInputProposed :=
  clusterDensityInputProposed_of_faithful (clusterDensityInputFaithful_of_concentration hDG)

/-- Planar Dario–Gu concentration gives the uniform planar density lower bound. -/
theorem clusterDensityInputProposedAt_two_of_concentration
    (hDG : ClusterDensityConcentrationInputTwo) (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ClusterDensityInputProposedAt 2 p :=
  clusterDensityInputProposedAt_of_faithfulAt p
    (clusterDensityInputFaithfulAt_of_concentration le_rfl p (hDG p hpc hp1))

/-- The density-scale step in dimension two follows from planar concentration. -/
theorem densityScaleStep_two_of_concentration (p : unitInterval)
    (hDG : ClusterDensityConcentrationInputTwo) : DensityScaleStep 2 p :=
  fun hpc hp1 => clusterDensityInputProposedAt_two_of_concentration hDG p hpc hp1

/-- step:2.6-inputs, density, from Dario–Gu, Proposition A.1. -/
theorem densityScaleStep_of_concentration [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hDG : ClusterDensityConcentrationInput) : DensityScaleStep d p :=
  densityScaleStep_of_faithful hd p (clusterDensityInputFaithful_of_concentration hDG)

end Rigidity.Proofs.S2
