import Rigidity.Proofs.Partition.Measurability
import Rigidity.Proofs.Percolation.PlanarTriadicPartition
import Rigidity.Percolation.SlabTriadicPartition
import Rigidity.Percolation.Blocks.SlabConnectivity

/-!
# The partition into good cubes exists almost surely

Armstrong and Dario, Proposition 2.1 applied to the good cubes (Definition 2.9). For
supercritical bond percolation on `ℤᵈ`, `d ≥ 2`, a triadic cube of large scale fails to be
well-connected relative to its rounded three-quarter cube with probability at most
`C exp(-c 3ⁿ)`: in dimension two from rectangle crossings (`planar_wellConnectedIn_large_scale`),
in dimension at least three from slab connectivity. The same bound then holds for the
well-connected cubes of scale at least two, after enlarging the constant, and the stopping
construction gives, almost surely, a partition of `ℤᵈ` into good cubes, with sizes having a
uniform exponential moment and an approximately local partition.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory Rigidity.External
open scoped ENNReal

variable {d : ℕ}

/-- **Armstrong and Dario, Proposition 2.1, for the good cubes.** An exponential estimate for the
failure of well-connectedness of large cubes gives, almost surely, the partition into good
cubes, a uniform exponential moment of the size of the partition cube of a vertex, and the
approximate locality of the partition. -/
theorem partition_estimates_of_large_scale (hd : 0 < d) (μ : Measure (Configuration d))
    [IsProbabilityMeasure μ] (n₀ : ℕ) (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c)
    (hlarge : ∀ Q : TriadicCube d, n₀ ≤ Q.scale →
      μ {ω | ¬ Q.wellConnectedIn Q.threeQuarterCube.vertices ω} ≤
        ENNReal.ofReal (C * Real.exp (-c * (3 : ℝ) ^ Q.scale))) :
    (∀ᵐ ω ∂μ, PartitionEvent ω) ∧
    (∃ θ : ℝ, 0 < θ ∧ ∀ x : Vertex d,
      Integrable (fun ω => Real.exp (TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x / θ))
        μ ∧
      (∫ ω, Real.exp (TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x / θ) ∂μ) ≤ 2) ∧
    (∃ K k : ℝ, 0 < K ∧ 0 < k ∧ ∀ (A : TriadicCube d) (n : ℕ),
      μ {ω | ∃ x ∈ A.boundaryInterior n, ∃ Q R : TriadicCube d,
        x ∈ Q.vertices ∧ x ∈ R.vertices ∧ Q.IsMaximalStopping (TriadicCube.goodCubes ω) ∧
          R.IsMaximalStopping
            (TriadicCube.localGoodCentered (TriadicCube.goodCubes ω) A.vertices) ∧ Q ≠ R} ≤
        ENNReal.ofReal (K * (3 : ℝ) ^ ((A.scale : ℝ) - n) *
          Real.exp (-k * (3 : ℝ) ^ n))) := by
  have hlarge' : ∀ Q : TriadicCube d, max n₀ 2 ≤ Q.scale →
      μ {ω | Q ∉ TriadicCube.wellConnectedCubes ω} ≤
        ENNReal.ofReal (C * Real.exp (-c * (3 : ℝ) ^ Q.scale)) := by
    intro Q hQ
    have h2 : 2 ≤ Q.scale := le_of_max_le_right hQ
    have heq : {ω | Q ∉ TriadicCube.wellConnectedCubes ω} =
        {ω | ¬ Q.wellConnectedIn Q.threeQuarterCube.vertices ω} := by
      ext ω
      simp only [TriadicCube.wellConnectedCubes, Set.mem_setOf_eq, h2, true_and]
    rw [heq]
    exact hlarge Q (le_of_max_le_left hQ)
  have hall := TriadicCube.measure_le_exp_of_large_scale μ
    (fun Q => {ω | Q ∉ TriadicCube.wellConnectedCubes ω}) (max n₀ 2) C c hC hc hlarge'
  set B : ℝ := C + Real.exp (c * (3 : ℝ) ^ (max n₀ 2)) with hBdef
  have hB : 0 ≤ B := by positivity
  exact TriadicCube.wellConnected_partition_estimates hd μ TriadicCube.wellConnectedCubes
    TriadicCube.measurableSet_mem_wellConnectedCubes (ENNReal.ofReal B) ENNReal.ofReal_ne_top c hc
    (fun Q => by
      rw [← ENNReal.ofReal_mul hB]
      exact hall Q)

/-- The partition into good cubes exists almost surely for supercritical planar bond
percolation. -/
theorem ae_partitionEvent_two {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) :
    ∀ᵐ ω ∂(latticeBondLaw 2 p), PartitionEvent ω := by
  obtain ⟨C, c, hC, hc, hlarge⟩ := planar_wellConnectedIn_large_scale hpc
  exact (partition_estimates_of_large_scale (by norm_num) _ 7 C c hC hc hlarge).1

/-- The partition into good cubes exists almost surely for supercritical bond percolation in
dimension at least three. -/
theorem ae_partitionEvent_of_three_le [NeZero d] (hd : 3 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∀ᵐ ω ∂(latticeBondLaw d p), PartitionEvent ω := by
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
    (by positivity) fun Q hscale => ?_).1
  have hpow : M ≤ 3 ^ Q.scale := by
    calc
      M ≤ 2 ^ M := Nat.le_of_lt Nat.lt_two_pow_self
      _ ≤ 3 ^ M := by gcongr; omega
      _ ≤ 3 ^ Q.scale := pow_le_pow_right₀ (by omega) hscale
  exact hM Q hpow

/-- **The partition into good cubes** exists almost surely for supercritical bond percolation on
`ℤᵈ`, `d ≥ 2`. -/
theorem ae_partitionEvent [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∀ᵐ ω ∂(latticeBondLaw d p), PartitionEvent ω := by
  rcases Nat.eq_or_lt_of_le hd with rfl | h
  · exact ae_partitionEvent_two hpc
  · exact ae_partitionEvent_of_three_le h hpc

end Rigidity.Percolation
