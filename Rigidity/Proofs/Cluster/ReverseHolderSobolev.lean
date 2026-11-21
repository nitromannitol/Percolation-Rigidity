import Rigidity.Proofs.Cluster.ReverseHolder
import Rigidity.Proofs.Cluster.PartitionSobolev

/-!
# The Sobolev hypothesis of the reverse Hölder inequality from Proposition 3.4

The hypothesis `ClusterSobolevTwo` of `reverse_holder_of_sobolev` is Armstrong–Dario,
Proposition 3.4, with `s = 2` for functions of mean zero on the cluster. For the crossing cluster of a
triadic cube resolved by the partition into good cubes, in dimension `d ≥ 2`, it follows from
`Rigidity.Percolation.exists_partition_sum_rpow_le_of_latticeSobolevOn` with the exponents `2` and
`2_* = 2d/(d+2)`, given the lattice Sobolev–Poincaré inequality on the integer cube
(`clusterSobolevTwo_of_latticeSobolevOn`). The weight is the reach scale `ρ(z)` of the
coarse-graining data, `size(z) = 3^{ρ(z)}`; the weight `size^{2_* d}` obtained there is at most the
weight `size^{2d}` of Armstrong and Dario. The gradient magnitude `gradNormIn` of the open graph is the
square root of `clusterGradSq` (`gradNormIn_openGraph_eq`).
-/

namespace Rigidity.Proofs.Cluster

open LatticeProb.Percolation Rigidity.Percolation
open scoped BigOperators Classical

variable {d : ℕ}

theorem gradNormIn_openGraph_eq (ω : Configuration d) (S : Finset (Vertex d))
    (f : Vertex d → ℝ) (x : Vertex d) :
    gradNormIn (openGraph ω) S f x = √(clusterGradSq ω S f x) := by
  unfold gradNormIn clusterGradSq
  congr 2
  have hset : S.filter (fun y => (openGraph ω).Adj x y) =
      ((openGraph ω).neighborFinset x).filter (· ∈ S) := by
    ext y
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
    exact and_comm
  rw [← Finset.sum_filter, hset]

theorem one_le_lowerSobolevTwo (hd : 2 ≤ d) : 1 ≤ lowerSobolevTwo d := by
  unfold lowerSobolevTwo
  have h : (2 : ℝ) ≤ d := by exact_mod_cast hd
  rw [le_div_iff₀ (by linarith)]
  linarith

theorem lowerSobolevTwo_le_two : lowerSobolevTwo d ≤ 2 := by
  unfold lowerSobolevTwo
  have h : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  rw [div_le_iff₀ (by linarith)]
  linarith

/-- **Proposition 3.4 with `s = 2` as the Sobolev hypothesis of the reverse Hölder inequality.** In
dimension `d ≥ 2`, for every `S ≥ 0` there is `K` such that for every triadic cube `U` resolved by
the partition into good cubes, the lattice Sobolev–Poincaré inequality on `U` with the exponents `2`
and `2_*` and constant `S` gives `ClusterSobolevTwo` on the crossing cluster `C_*(U)` with the weight
`3^{ρ(z)}` and constant `K`. -/
theorem clusterSobolevTwo_of_latticeSobolevOn (hd : 2 ≤ d) {S : ℝ} (hS : 0 ≤ S) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ω : Configuration d) (hP : PartitionEvent ω) (U : TriadicCube d)
      (hU : PartitionResolved ω U),
      LatticeSobolevOn U.toIntegerCube.vertices 2 (lowerSobolevTwo d) S →
      ClusterSobolevTwo ω (crossingClusterVertices ω U)
        (fun z => (3 : ℝ) ^ (partitionCoarseData (by omega) hP U hU).reachScale z) K := by
  have h1 := one_le_lowerSobolevTwo hd
  have h2 := lowerSobolevTwo_le_two (d := d)
  obtain ⟨K, hK0, hK⟩ := exists_partition_sum_rpow_le_of_latticeSobolevOn (d := d) (by omega)
    (s := 2) (t := lowerSobolevTwo d) (by norm_num) h1 h2 hS
  refine ⟨K, hK0, fun ω hP U hU hLS w hw => ?_⟩
  have h := hK ω hP U hU hLS w hw
  set C := crossingClusterVertices ω U with hC
  have hq0 : 0 ≤ lowerSobolevTwo d := by linarith
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  calc ∑ x ∈ C, w x ^ 2 = ∑ x ∈ C, |w x| ^ (2 : ℝ) :=
        Finset.sum_congr rfl fun x _ => by rw [Real.rpow_two, sq_abs]
    _ ≤ K * (∑ z ∈ C, ((3 : ℝ) ^ (partitionCoarseData (by omega) hP U hU).reachScale z) ^
          (lowerSobolevTwo d * d) *
          gradNormIn (openGraph ω) C w z ^ lowerSobolevTwo d) ^ (2 / lowerSobolevTwo d) := h
    _ ≤ K * (∑ z ∈ C, ((3 : ℝ) ^ (partitionCoarseData (by omega) hP U hU).reachScale z) ^
          (2 * (d : ℝ)) * clusterGradSq ω C w z ^ (lowerSobolevTwo d / 2)) ^
            (2 / lowerSobolevTwo d) := by
        refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Finset.sum_nonneg fun z _ =>
          mul_nonneg (Real.rpow_nonneg (by positivity) _)
            (Real.rpow_nonneg (gradNormIn_nonneg _ _ _ _) _))
          (Finset.sum_le_sum fun z _ => ?_) (div_nonneg zero_le_two hq0)) hK0
        have hgrad : gradNormIn (openGraph ω) C w z ^ lowerSobolevTwo d =
            clusterGradSq ω C w z ^ (lowerSobolevTwo d / 2) := by
          rw [gradNormIn_openGraph_eq, Real.sqrt_eq_rpow,
            ← Real.rpow_mul (clusterGradSq_nonneg ω C w z)]
          congr 1
          ring
        rw [hgrad]
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (clusterGradSq_nonneg ω C w z) _)
        exact Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) (by nlinarith)

end Rigidity.Proofs.Cluster
