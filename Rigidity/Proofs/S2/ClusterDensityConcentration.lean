import Rigidity.Proofs.S2.InfluenceRootBoundHigh
import Rigidity.Proofs.S2.DensityConcentrationOfRoots
import Rigidity.Proofs.S2.PlanarDensityConcentration

/-!
# Concentration of the density of the infinite cluster in every dimension

Dario–Gu, arXiv:1909.10439v4, Proposition A.1: for bond percolation on `ℤ^d`, `d ≥ 2`,
`p_c(d) < p < 1`, there is `C < ∞` such that for every triadic cube `□` of size `3^m`,

`| |𝒞_∞ ∩ □| / |□| - θ(p) | ≤ 𝒪_{2(d-1)/(3d²+2d-1)}(C 3^{-dm/2})`.

The planar case is `planar_cluster_density_concentration`. In dimension `d ≥ 3` the influence
moment roots are summable with sum `C r^{3d+2} (3^m + 1)^d`, so the moment recursion gives the
estimate at every exponent at most `1/(γ + 1)`, `γ = ⌊(3d+3)/2⌋`, which is at least
`2(d-1)/(3d²+2d-1)`.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory LatticeProb.Percolation Rigidity.External

/-- The Dario–Gu exponent `2(d-1)/(3d²+2d-1)` is at most `1/(⌊(3d+3)/2⌋ + 1)`. -/
theorem densityExponent_le_inv (d : ℕ) (hd : 2 ≤ d) :
    2 * ((d : ℝ) - 1) / (3 * (d : ℝ) ^ 2 + 2 * (d : ℝ) - 1) ≤
      1 / (((3 * d + 3) / 2 + 1 : ℕ) : ℝ) := by
  have hD : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hγ : 2 * ((3 * d + 3) / 2 + 1) ≤ 3 * d + 5 := by omega
  have hγR : 2 * ((((3 * d + 3) / 2 + 1 : ℕ) : ℝ)) ≤ 3 * (d : ℝ) + 5 := by exact_mod_cast hγ
  have hg : (0 : ℝ) < (((3 * d + 3) / 2 + 1 : ℕ) : ℝ) := by positivity
  rw [div_le_div_iff₀ (by nlinarith) hg]
  nlinarith [mul_le_mul_of_nonneg_left hγR (by linarith : (0 : ℝ) ≤ (d : ℝ) - 1)]

/-- The Dario–Gu exponent is positive in dimension at least two. -/
theorem densityExponent_pos (d : ℕ) (hd : 2 ≤ d) :
    0 < 2 * ((d : ℝ) - 1) / (3 * (d : ℝ) ^ 2 + 2 * (d : ℝ) - 1) := by
  have hD : (2 : ℝ) ≤ d := by exact_mod_cast hd
  apply div_pos <;> nlinarith

/-- **Density concentration in dimension at least three** (Dario–Gu, Proposition A.1). -/
theorem clusterDensityConcentrationAt_of_three_le {d : ℕ} [NeZero d] (hd : 3 ≤ d)
    (p : unitInterval) (hp : criticalProbability d < (p : ℝ)) :
    ClusterDensityConcentrationAt d p := by
  have hγ : 3 * d + 2 ≤ 2 * ((3 * d + 3) / 2) := by omega
  exact clusterDensityConcentrationAt_of_rootBound
    ((densityInfluenceRootBound_of_three_le hd hp).mono hγ)
    (densityExponent_pos d (by omega)) (densityExponent_le_inv d (by omega))

/-- **Concentration of the density of the infinite cluster** (Dario–Gu, arXiv:1909.10439v4,
Proposition A.1), in every dimension `d ≥ 2`. -/
theorem cluster_density_concentration : ClusterDensityConcentrationInput := by
  intro d _ hd p hp hp1
  rcases (show d = 2 ∨ 3 ≤ d by omega) with rfl | hd3
  · exact planar_cluster_density_concentration p hp hp1
  · exact clusterDensityConcentrationAt_of_three_le hd3 p hp

end Rigidity.Proofs.S2
