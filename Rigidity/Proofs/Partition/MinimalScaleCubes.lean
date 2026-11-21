import Rigidity.Proofs.Partition.GeneralMinimalScaleMain
import Rigidity.Proofs.Partition.GoodCubesLocal
import Rigidity.Proofs.Partition.PartitionSize

/-!
# The first bound of the minimal scales on every triadic cube

Armstrong and Dario state Proposition 2.4 for the cubes `□_m` centred at the origin. Definition 3.7
applies Proposition 2.1 to the cubes on which the reverse Hölder inequality of Lemma 3.6 holds;
its hypothesis (2.2) asks for the probability bound of Lemma 3.6 on every triadic cube, hence for
`∑_{x ∈ R} size(𝒫(x))^τ ≤ C |R|` on every triadic cube `R` outside an event of
stretched-exponentially small probability. The counting proof gives this for every triadic cube.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-- **The tail of `Λ`-type sums of the partition `𝒫` on every triadic cube.** For supercritical
bond percolation on `ℤᵈ`, `d ≥ 2`, and `τ ∈ ℕ`, there are constants such that for every triadic
cube `R` of scale `m`, `P[∑_{x ∈ R} 3^{τ n(x)} > C 3^{d m}] ≤ C' exp(-c' 3^{m / (2 (d + τ + 1))})`,
`n(x)` the scale of the partition cube of `x`. -/
theorem exists_measure_sum_partitionCube_gt_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (τ : ℕ) :
    ∃ C : ℝ, ∃ C' : ℝ≥0∞, C' ≠ ∞ ∧ ∃ c' : ℝ, 0 < c' ∧ ∀ R : TriadicCube d,
      latticeBondLaw d p {ω | C * 3 ^ (d * R.scale) <
        ∑ x ∈ R.toIntegerCube.vertices, (3 : ℝ) ^ (τ * (partitionCube ω x).scale)} ≤
      C' * ENNReal.ofReal (Real.exp (-c' * ((3 : ℝ) ^ R.scale) ^
        (1 / ((2 * (d + τ + 1) : ℕ) : ℝ)))) := by
  obtain ⟨C1, c, hC1, hc, hq⟩ := exists_measure_not_mem_goodCubes_le hd hpc
  have hq' : ∀ T : TriadicCube d, latticeBondLaw d p {ω | T ∉ TriadicCube.goodCubes ω} ≤
      ENNReal.ofReal (C1 * Real.exp (-c * ((3 : ℝ) ^ T.scale) ^ (1 : ℝ))) := by
    intro T
    rw [Real.rpow_one]
    exact hq T
  obtain ⟨C, C', hC', c', hc', h⟩ := exists_measure_sum_stoppingSize_gt_le (by omega) p
    TriadicCube.goodCubes TriadicCube.measurableSet_mem_goodCubes
    TriadicCube.measurableSet_not_mem_goodCubes_localEdge hC1 hc one_pos le_rfl hq' τ
  refine ⟨C, C', hC', c', hc', fun R => le_trans (measure_mono_ae ?_) (h R)⟩
  filter_upwards [ae_partitionEvent hd hpc] with ω hP
  intro hω
  change C * 3 ^ (d * R.scale) <
    ∑ x ∈ R.toIntegerCube.vertices, (3 : ℝ) ^ (τ * (partitionCube ω x).scale) at hω
  change C * 3 ^ (d * R.scale) <
    ∑ x ∈ R.toIntegerCube.vertices, TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x ^ τ
  refine lt_of_lt_of_le hω (le_of_eq (Finset.sum_congr rfl fun x _ => ?_))
  rw [stoppingSize_goodCubes_eq hP x, ← pow_mul, Nat.mul_comm]

end Rigidity.Percolation
