import Rigidity.Proofs.Regularity.OrderOneLift
import Rigidity.Proofs.Regularity.PlanarAffineApproximationHolds

/-!
# The dimension of `𝒜_1` on the planar cluster

Theorem 2 (i) of Armstrong and Dario (arXiv:1609.09431v2) at `k = 1` in dimension two,
`dim 𝒜_1 ≤ 3` (`PlanarOrderOneDimensionTwo`), by Step 4 of the proof of Proposition 3.1 of
Armstrong, Kuusi and Mourrat (arXiv:1602.00512v1): every element of `𝒜_1` is a combination of the
constants and of the corrected planes of slopes `e₁, e₂` (`eq_clusterLiftMap_of_orderOne`), so `𝒜_1`
lies in the range of a linear map from `ℝ × ℝ²`.

The inputs are (7.18) at `k = 2` in the plane (`MesoscopicDegreeTwoPlanarInput`, the statement of
`ArmstrongDarioMesoscopicDegreeTwo` for `d = 2`) and the existence of the corrected planes, which
holds from the minimal scales and the order-zero regularity
(`planarCorrectedPlaneExistenceTwo_of_minimalScales`). With them the planar qualitative corrector
input follows (`supercriticalBondCorrectorInputTwo_of_mesoscopic`).
-/

namespace Rigidity.Proofs.Regularity

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Proofs.S2

/-- **Armstrong–Dario, Lemma 7.3, (7.18) at `k = 2`, in the plane**: the statement of
`ArmstrongDarioMesoscopicDegreeTwo` for `d = 2`. -/
def MesoscopicDegreeTwoPlanarInput : Prop :=
  ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
  ∃ s C₀ δ : ℝ, 0 < s ∧ 0 < C₀ ∧ 0 < δ ∧
  ∃ X : Configuration 2 → ℝ, Measurable X ∧ (∀ ω, 0 ≤ X ω) ∧ IsOsBond 2 p X s C₀ ∧
  ∃ C : ℝ, ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω,
    ∀ R : ℝ, 2 * X ω ≤ R → ∀ u : uniqueInfiniteComponent h → ℝ,
      (∀ z ∈ componentEuclideanBall (uniqueInfiniteComponent h) 0 R,
        (∀ w, (componentGraph (uniqueInfiniteComponent h)).Adj z w →
          w ∈ componentEuclideanBall (uniqueInfiniteComponent h) 0 R) →
        componentLaplacian (uniqueInfiniteComponent h) u z = 0) →
      ∀ r : ℝ, X ω ≤ r → r ≤ R / 2 →
        (⨅ w : clusterHarmonicQuadratic (uniqueInfiniteComponent h),
            clusterBallVolumeL2 (uniqueInfiniteComponent h) r (u - w)) ≤
          C * (r / R) ^ 3 * (⨅ w : clusterHarmonicQuadratic (uniqueInfiniteComponent h),
              clusterBallVolumeL2 (uniqueInfiniteComponent h) R (u - w)) +
            C * r ^ (-δ) * (r / R) * clusterBallVolumeL2 (uniqueInfiniteComponent h) R u

theorem mesoscopicDegreeTwoPlanarInput_of_mesoscopicDegreeTwo
    (h : ArmstrongDarioMesoscopicDegreeTwo) : MesoscopicDegreeTwoPlanarInput :=
  h 2 le_rfl

/-- The lift `(a, ξ) ↦ a + Σ ξᵢ gᵢ` as a linear map. -/
noncomputable def clusterLiftLinear {d : ℕ} {ω : Configuration d} (C : OpenComponent ω)
    (g : Fin d → C → ℝ) : (ℝ × EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] (C → ℝ) where
  toFun := clusterLiftMap C g
  map_add' := map_add (clusterLiftMap C g)
  map_smul' c ℓ := by
    funext x
    show c * ℓ.1 + ∑ i, (c • ℓ.2) i * g i x = c * (ℓ.1 + ∑ i, ℓ.2 i * g i x)
    rw [mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [PiLp.smul_apply, smul_eq_mul, mul_assoc]

/-- **Theorem 2 (i) at `k = 1` in the plane**: `dim 𝒜_1 ≤ 3`. -/
theorem planarOrderOneDimensionTwo_of_mesoscopic (hmeso : MesoscopicDegreeTwoPlanarInput)
    (hex : PlanarCorrectedPlaneExistenceTwo) : PlanarOrderOneDimensionTwo := by
  intro p hpc hp1
  obtain ⟨s₁, C₁, δ, -, -, hδ, X, -, -, -, A₀, hae₁⟩ := hmeso p hpc hp1
  have hθp : 0 < theta 2 p := Rigidity.Percolation.theta_pos_of_criticalProbability_lt 2 p hpc
  obtain ⟨s₂, C₂, -, -, hcube⟩ := exists_clusterCubeDensity_of_concentration (d := 2) le_rfl p
    (cluster_density_concentration 2 le_rfl p hpc hp1) (quadLocality 2 (capFraction 2 (theta 2 p / 2)))
  obtain ⟨M, -, -, -, hae₂⟩ := hcube 0
  filter_upwards [hae₁, hae₂, hex p hpc hp1] with ω h₁ h₂ h₃
  intro h
  choose g hg using fun i : Fin 2 => h₃ h (Pi.single i 1)
  have hle : harmonicGrowthSpace (uniqueInfiniteComponent h) 1 ≤
      LinearMap.range (clusterLiftLinear (uniqueInfiniteComponent h) g) := by
    intro u hu
    obtain ⟨ℓ, hℓ⟩ := eq_clusterLiftMap_of_orderOne (uniqueInfiniteComponent h)
      (by positivity : (0 : ℝ) < theta 2 p / 2) hδ (h₂ h) (h₁ h) hg hu
    exact ⟨ℓ, hℓ.symm⟩
  refine ⟨Submodule.finiteDimensional_of_le hle, (Submodule.finrank_mono hle).trans
    ((LinearMap.finrank_range_le _).trans (le_of_eq ?_))⟩
  rw [Module.finrank_prod, Module.finrank_self, finrank_euclideanSpace_fin]

/-- **`dim 𝒜_1 ≤ 3` in the plane** from (7.18) at `k = 2`, the minimal scales of Proposition 2.4
and the order-zero regularity. -/
theorem planarOrderOneDimensionTwo_of_minimalScales (hmeso : MesoscopicDegreeTwoPlanarInput)
    (hM5 : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      PlanarMinimalScalesTwo p)
    (hR3 : ArmstrongDarioOrderZeroTwo) : PlanarOrderOneDimensionTwo :=
  planarOrderOneDimensionTwo_of_mesoscopic hmeso
    (planarCorrectedPlaneExistenceTwo_of_minimalScales hM5 hR3)

/-- **The planar qualitative corrector input** (Theorem 2 (i), (ii) at `k = 1` in the plane) from
(7.18) at `k = 2`, the minimal scales of Proposition 2.4 and the order-zero regularity. -/
theorem supercriticalBondCorrectorInputTwo_of_mesoscopic (hmeso : MesoscopicDegreeTwoPlanarInput)
    (hM5 : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      PlanarMinimalScalesTwo p)
    (hR3 : ArmstrongDarioOrderZeroTwo) : SupercriticalBondCorrectorInputTwo :=
  supercriticalBondCorrectorInputTwo_of_orderOne hR3
    (planarCorrectedPlaneExistenceTwo_of_minimalScales hM5 hR3)
    (planarOrderOneDimensionTwo_of_minimalScales hmeso hM5 hR3)

end Rigidity.Proofs.Regularity
