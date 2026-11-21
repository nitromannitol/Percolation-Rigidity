import Rigidity.Proofs.Cluster.PartitionReachMoments
import Rigidity.Proofs.Partition.AlmostSure

/-!
# Moments of the reach of the partition for supercritical percolation

For supercritical bond percolation on `ℤᵈ`, `d ≥ 2`, the size of the partition cube of a vertex
has a uniform exponential moment (Armstrong and Dario, Proposition 2.1 (iii), for the good cubes),
hence every moment of the reach of the partition is bounded uniformly in the vertex.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External
open scoped ENNReal

namespace Rigidity.Percolation

variable {d : ℕ}

/-- **Armstrong and Dario, Proposition 2.1 (iii), for the good cubes, in the plane.** -/
theorem exists_partition_size_moment_two {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ x : Vertex 2,
      Integrable (fun ω => Real.exp (TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x / θ))
        (latticeBondLaw 2 p) ∧
      (∫ ω, Real.exp (TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x / θ)
        ∂(latticeBondLaw 2 p)) ≤ 2 := by
  obtain ⟨C, c, hC, hc, hlarge⟩ := planar_wellConnectedIn_large_scale hpc
  exact (partition_estimates_of_large_scale (by norm_num) _ 7 C c hC hc hlarge).2.1

/-- **Armstrong and Dario, Proposition 2.1 (iii), for the good cubes, in dimension at least
three.** -/
theorem exists_partition_size_moment_of_three_le [NeZero d] (hd : 3 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ x : Vertex d,
      Integrable (fun ω => Real.exp (TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x / θ))
        (latticeBondLaw d p) ∧
      (∫ ω, Real.exp (TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x / θ)
        ∂(latticeBondLaw d p)) ≤ 2 := by
  have hp0 : 0 < (p : ℝ) := lt_of_le_of_lt (criticalProbability_nonneg d) hpc
  obtain ⟨width, hwidth, ρ, c, hρ, hρ₁, hc, hcρ, hcroot, hctwo, hprob⟩ :=
    (uniformCubeSlabConnectivity_of_criticalProbability_lt hd p hpc).exists_parameters
      ⟨0, by omega⟩ hp0
  obtain ⟨M, hM⟩ :=
    TriadicCube.eventually_measure_not_wellConnectedIn_threeQuarter_le_of_twoPoint_slabs
      (by omega) ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp [Fin.ext_iff]) width hwidth p ρ c hρ.le
      hρ₁ hc hcρ hcroot hctwo hprob
  let rate : ℝ := ((c / (2 * ((10 * d * width : ℕ) : ℝ))) / 2) / 40
  let C : ℝ := 1 + 4 * 7 ^ d * ((d + 1).factorial : ℝ) / (rate / 2) ^ (d + 1)
  have hrate : 0 < rate := by dsimp only [rate]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine (partition_estimates_of_large_scale (by omega) (latticeBondLaw d p) M C (rate / 2) hC
    (by positivity) fun Q hscale => ?_).2.1
  have hpow : M ≤ 3 ^ Q.scale := by
    calc
      M ≤ 2 ^ M := Nat.le_of_lt Nat.lt_two_pow_self
      _ ≤ 3 ^ M := by gcongr; omega
      _ ≤ 3 ^ Q.scale := pow_le_pow_right₀ (by omega) hscale
  exact hM Q hpow

/-- **Armstrong and Dario, Proposition 2.1 (iii), for the good cubes**, for supercritical bond
percolation on `ℤᵈ`, `d ≥ 2`. -/
theorem exists_partition_size_moment [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ x : Vertex d,
      Integrable (fun ω => Real.exp (TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x / θ))
        (latticeBondLaw d p) ∧
      (∫ ω, Real.exp (TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x / θ)
        ∂(latticeBondLaw d p)) ≤ 2 := by
  rcases Nat.eq_or_lt_of_le hd with rfl | h
  · exact exists_partition_size_moment_two hpc
  · exact exists_partition_size_moment_of_three_le h hpc

/-- **Moments of the reach of the partition** for supercritical bond percolation on `ℤᵈ`,
`d ≥ 2`: every moment of the reach is bounded uniformly in the vertex. -/
theorem exists_lintegral_partitionReach_pow_le_of_supercritical [NeZero d] (hd : 2 ≤ d)
    {p : unitInterval} (hpc : criticalProbability d < (p : ℝ)) (n : ℕ) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ z : Vertex d,
      ∫⁻ ω, partitionReach ω z ^ (n + 1) ∂(latticeBondLaw d p) ≤ C := by
  obtain ⟨θ, hθ, hmom⟩ := exists_partition_size_moment hd hpc
  exact exists_lintegral_partitionReach_pow_le _ hθ hmom n

end Rigidity.Percolation
