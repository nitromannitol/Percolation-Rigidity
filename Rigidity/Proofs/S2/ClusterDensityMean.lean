import Rigidity.Proofs.S2.ClusterDensityFromDarioGu

/-!
# Mean density of the infinite cluster

Translation invariance makes the density in a triadic cube an unbiased estimator of the
infinite-cluster density.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory LatticeProb.Percolation Rigidity.External

variable {d : ℕ}

/-- The cluster count is the sum of the vertex membership indicators. -/
theorem infiniteClusterCount_eq_sum (m : ℕ) (k : Vertex d) (ω : Configuration d) :
    (infiniteClusterCount (triadicCube d m k) ω : ℝ) =
      ∑ y ∈ triadicCubeFinset d m k,
        (infiniteComponentEvent y).indicator (fun _ => (1 : ℝ)) ω := by
  rw [infiniteClusterCount_triadicCube, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hy : ω ∈ infiniteComponentEvent y <;> simp [hy]

/-- The infinite-cluster count in a triadic cube is integrable. -/
theorem integrable_infiniteClusterCount (p : unitInterval) (m : ℕ) (k : Vertex d) :
    Integrable (fun ω : Configuration d => (infiniteClusterCount (triadicCube d m k) ω : ℝ))
      (latticeBondLaw d p) := by
  simp_rw [infiniteClusterCount_eq_sum]
  exact integrable_finsetSum _ fun y _ =>
    (integrable_const (1 : ℝ)).indicator (measurableSet_infiniteComponentEvent y)

/-- The expected infinite-cluster count is the cube cardinality times `θ(p)`. -/
theorem integral_infiniteClusterCount (p : unitInterval) (m : ℕ) (k : Vertex d) :
    (∫ ω, (infiniteClusterCount (triadicCube d m k) ω : ℝ) ∂latticeBondLaw d p) =
      ((triadicCube d m k).ncard : ℝ) * theta d p := by
  simp_rw [infiniteClusterCount_eq_sum]
  rw [integral_finsetSum (triadicCubeFinset d m k) (f := fun y ω =>
    (infiniteComponentEvent y).indicator (fun _ => (1 : ℝ)) ω) (fun y _ =>
      (integrable_const (1 : ℝ)).indicator (measurableSet_infiniteComponentEvent y))]
  have hmean (y : Vertex d) :
      (∫ ω, (infiniteComponentEvent y).indicator (fun _ => (1 : ℝ)) ω ∂latticeBondLaw d p) =
        theta d p := by
    change (∫ ω, (infiniteComponentEvent y).indicator (1 : Configuration d → ℝ) ω
      ∂latticeBondLaw d p) = theta d p
    rw [integral_indicator_one (measurableSet_infiniteComponentEvent y), measureReal_def,
      measure_infiniteComponentEvent_eq p y]
    rfl
  simp only [hmean, Finset.sum_const, nsmul_eq_mul, ncard_triadicCube, card_triadicCubeFinset]

/-- The centered triadic density has mean zero. -/
theorem integral_centered_clusterDensity (p : unitInterval) (m : ℕ) (k : Vertex d) :
    (∫ ω, ((infiniteClusterCount (triadicCube d m k) ω : ℝ) /
      ((triadicCube d m k).ncard : ℝ) - theta d p) ∂latticeBondLaw d p) = 0 := by
  have hcard : ((triadicCube d m k).ncard : ℝ) ≠ 0 := by
    rw [ncard_triadicCube]
    positivity
  rw [integral_sub ((integrable_infiniteClusterCount p m k).div_const _)
    (integrable_const _), integral_div, integral_infiniteClusterCount]
  simp only [integral_const, probReal_univ, one_smul]
  field_simp
  ring

end Rigidity.Proofs.S2
