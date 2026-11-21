import Rigidity.Proofs.Cluster.CoarseNear

/-!
# Lemmas 3.2 and 3.3 with sums over partition cubes

The right sides of Lemmas 3.2 and 3.3 of Armstrong and Dario are sums over the partition cubes
`□ ⊆ cl_𝒫(U)` of `size(□)^{sd}`, respectively `size(□)^{sd-1}`, times the sum of
`|∇w 1_{a≠0}|^s` over `□ ∩ C_*(U)`. These are the vertex sums of `CoarseInequalities` regrouped by
`CoarseData.sum_cluster_eq_sum_parts`; partition cubes not meeting the cluster contribute zero and
are omitted.
-/

open LatticeProb.Percolation
open scoped Classical

namespace Rigidity.Percolation

variable {d : ℕ}

namespace CoarseData

variable {ω : Configuration d} (P : CoarseData d ω)

/-- **Armstrong and Dario, Lemma 3.2**, with the right side as a sum over partition cubes. -/
theorem sum_abs_sub_coarsen_rpow_le_sum_parts {K N m : ℕ} (h : P.RegionOverlap K N m)
    (hK : 1 ≤ K) (hN : 1 ≤ N) (w : Vertex d → ℝ) {s : ℝ} (hs : 1 ≤ s) :
    ∑ x ∈ P.cluster, |w x - P.coarsen w x| ^ s ≤
      ((N : ℝ) * K * 3 ^ (m * d) * (2 * √(d : ℝ))) ^ s *
        ∑ Q ∈ P.cluster.image P.part, ((3 : ℝ) ^ Q.scale) ^ (s * d) *
          ∑ z ∈ P.cluster.filter (· ∈ Q.vertices), gradNormIn (openGraph ω) P.cluster w z ^ s := by
  have hreg := P.sum_cluster_eq_sum_parts (β := ℝ) (fun Q => ((3 : ℝ) ^ Q.scale) ^ (s * d))
    (fun z => gradNormIn (openGraph ω) P.cluster w z ^ s)
  simp only [smul_eq_mul] at hreg
  rw [← hreg]
  exact P.sum_abs_sub_coarsen_rpow_le h hK hN w hs

/-- **Armstrong and Dario, Lemma 3.3**, with the right side as a sum over partition cubes. -/
theorem sum_gradNormIn_coarsen_rpow_le_sum_parts {K N m : ℕ} (h : P.PairOverlap K N m)
    (hK : 1 ≤ K) (hN : 1 ≤ N) (hd : 1 ≤ d) (w : Vertex d → ℝ) {s : ℝ} (hs : 1 ≤ s) :
    ∑ x ∈ P.domain, gradNormIn (nearestNeighborGraph d) P.domain (P.coarsen w) x ^ s ≤
      (2 * (d : ℝ) * N * K * 3 ^ (m * d) * (2 * √(d : ℝ))) ^ s *
        ∑ Q ∈ P.cluster.image P.part, ((3 : ℝ) ^ Q.scale) ^ (s * d - 1) *
          ∑ z ∈ P.cluster.filter (· ∈ Q.vertices), gradNormIn (openGraph ω) P.cluster w z ^ s := by
  have hreg := P.sum_cluster_eq_sum_parts (β := ℝ) (fun Q => ((3 : ℝ) ^ Q.scale) ^ (s * d - 1))
    (fun z => gradNormIn (openGraph ω) P.cluster w z ^ s)
  simp only [smul_eq_mul] at hreg
  rw [← hreg]
  exact P.sum_gradNormIn_coarsen_rpow_le h hK hN hd w hs

end CoarseData

end Rigidity.Percolation
