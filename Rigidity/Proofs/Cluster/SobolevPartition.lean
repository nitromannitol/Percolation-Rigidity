import Rigidity.Proofs.Cluster.SobolevCube
import Rigidity.Proofs.Cluster.PartitionSobolev

/-!
# The Sobolev inequality on the cluster of a resolved cube in every dimension

Armstrong and Dario, Proposition 3.4 (case `∑_{C_*(U)} w = 0`), for the partition into good cubes
in every dimension `d ≥ 2`, for `s > d/(d-1)` and `s_* = sd/(s+d)`: the lattice Sobolev–Poincaré
inequality on integer cubes discharges the lattice Sobolev input of the deduction from Lemmas 3.2
and 3.3. There is `K(d, s)` with
`∑_{x ∈ C_*(U)} |w(x)|^s ≤ K (∑_{z ∈ C_*(U)} (3^{ρ(z)})^{s_* d} |∇w 1_{a≠0}|^{s_*}(z))^{s/s_*}`
for every cube `U` resolved by the partition and every `w` of mean zero on `C_*(U)`, with `ρ` the
reach scale of the coarse-graining data.
-/

open LatticeProb.Percolation Rigidity.External
open scoped Classical

namespace Rigidity.Percolation

variable {d : ℕ}

/-- **Armstrong and Dario, Proposition 3.4, for the partition into good cubes in every
dimension** (case `∑_{C_*(U)} w = 0`). -/
theorem exists_partition_sum_rpow_le_of_sum_eq_zero (hd : 2 ≤ d) {s t : ℝ}
    (hs : (d : ℝ) / (d - 1) < s) (ht : t = s * d / (s + d)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ω : Configuration d) (hP : PartitionEvent ω) (U : TriadicCube d)
      (hU : PartitionResolved ω U) (w : Vertex d → ℝ),
      ∑ x ∈ crossingClusterVertices ω U, w x = 0 →
        ∑ x ∈ crossingClusterVertices ω U, |w x| ^ s ≤
          K * (∑ z ∈ crossingClusterVertices ω U,
            ((3 : ℝ) ^ (partitionCoarseData (by omega) hP U hU).reachScale z) ^ (t * d) *
              gradNormIn (openGraph ω) (crossingClusterVertices ω U) w z ^ t) ^ (s / t) := by
  have hd0 : 0 < d := by omega
  have hd1 : (1 : ℝ) < d := by exact_mod_cast hd
  have hdm : (0 : ℝ) < d - 1 := by linarith
  have hsd : (d : ℝ) < s * (d - 1) := by rwa [div_lt_iff₀ hdm] at hs
  have hs1 : 1 ≤ s := by nlinarith
  have hsd0 : 0 < s + d := by linarith
  have ht1 : 1 ≤ t := by
    rw [ht, le_div_iff₀ hsd0]
    nlinarith
  have hts : t ≤ s := by
    rw [ht, div_le_iff₀ hsd0]
    nlinarith
  obtain ⟨S, hS, hLS⟩ := IntegerCube.exists_latticeSobolevOn hd hs ht
  obtain ⟨K, hK, h⟩ := exists_partition_sum_rpow_le_of_latticeSobolevOn hd0 hs1 ht1 hts hS
  refine ⟨K, hK, fun ω hP U hU w hw => h ω hP U hU (hLS _ ?_) w hw⟩
  show 0 < 3 ^ U.scale
  positivity

end Rigidity.Percolation
