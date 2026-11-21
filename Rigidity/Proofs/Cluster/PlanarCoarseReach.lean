import Rigidity.Proofs.Cluster.CoarseReach
import Rigidity.Proofs.Cluster.PlanarCoarseData

/-!
# The planar coarsening error with the reach of the partition

The windows of the planar partition lie in the squares of side `9s` around the partition cubes,
which are their `4s`-neighbourhoods. Hence Lemma 3.2 of Armstrong and Dario holds on a resolved
planar cube with the reach scale of the planar coarse-graining data in place of the scale of the
partition cube of `z`, with the constant `C = (3/2) · 10² · 9² · 2√2`.
-/

open LatticeProb.Percolation Rigidity.Proofs.Section5
open scoped Classical

namespace Rigidity.Percolation

variable {ω : Configuration 2}

/-- The square of side `9s` around a planar triadic cube is its `4s`-neighbourhood. -/
theorem TriadicCube.ninefold_vertices_eq_thicken (Q : TriadicCube 2) :
    Q.ninefold.vertices = (Q.thicken 4).vertices := by
  ext x
  have h9 := Q.two_mul_ninefoldRadius
  have hn := TriadicCube.mem_ninefold (Q := Q) (x := x)
  rw [Finset.mem_coe] at hn
  rw [hn, IntegerCube.mem_vertices]
  refine forall_congr' fun i => ?_
  have hc := Q.two_mul_center_sub_corner i
  have hs : (Q.toIntegerCube.size : ℤ) = 3 ^ Q.scale := by
    simp only [TriadicCube.toIntegerCube, Nat.cast_pow, Nat.cast_ofNat]
  change |x i - Q.center i| ≤ Q.ninefoldRadius ↔
    Q.toIntegerCube.corner i - ((4 : ℕ) : ℤ) * (Q.toIntegerCube.size : ℤ) ≤ x i ∧
      x i < Q.toIntegerCube.corner i - ((4 : ℕ) : ℤ) * (Q.toIntegerCube.size : ℤ) +
        (((2 * 4 + 1) * Q.toIntegerCube.size : ℕ) : ℤ)
  push_cast
  rw [hs, abs_le]
  omega

/-- The window of the partition cube of a vertex of a resolved cube lies in the
`4s`-neighbourhood of the partition cube. -/
theorem planarClusterWindow_subset_thicken (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) {x : Vertex 2} (hx : x ∈ U.vertices) :
    planarClusterWindow ω U x ⊆ ((planarPartCube ω x).thicken 4).vertices := by
  intro y hy
  rw [← TriadicCube.ninefold_vertices_eq_thicken]
  exact TriadicCube.subset_ninefold_of_mem_planarSquares
    ((planarPartCube ω x).window_mem_planarSquares (hU x hx)
      (planarPartCube_subset_of_resolved hP hU hx)) (Finset.mem_filter.1 hy).1

/-- **Planar form of Armstrong and Dario, Lemma 3.2, with the reach scale.** On a cube `U`
resolved by the planar partition, for `1 ≤ s < ∞`,
`∑_{x ∈ C_*(U)} |w(x) - [w]_𝒫(x)|^s ≤ C^s ∑_{z ∈ C_*(U)} (3^{ρ(z)})^{2s} |∇w 1_{a≠0}|^s(z)`,
where `ρ(z)` is the reach scale of the planar coarse-graining data and
`C = (3/2) · 10² · 9² · 2√2`. -/
theorem planar_sum_abs_sub_coarseAnchor_rpow_le (hP : PlanarPartitionEvent ω)
    {U : TriadicCube 2} (hU : PlanarResolved ω U) (w : Vertex 2 → ℝ) {s : ℝ} (hs : 1 ≤ s) :
    ∑ x ∈ clusterVertices ω U, |w x - w (planarCoarseAnchor ω x)| ^ s ≤
      (3 / 2 * (2 * ((4 : ℕ) : ℝ) + 2) ^ 2 * (2 * ((4 : ℕ) : ℝ) + 1) ^ 2 *
        (2 * √((2 : ℕ) : ℝ))) ^ s *
        ∑ z ∈ clusterVertices ω U, ((3 : ℝ) ^ (planarCoarseData hP U hU).reachScale z) ^
          (s * ((2 : ℕ) : ℝ)) * gradNormIn (openGraph ω) (clusterVertices ω U) w z ^ s :=
  (planarCoarseData hP U hU).sum_abs_sub_coarsen_rpow_le_reach (c := 4)
    (fun x hx => Finset.inter_subset_left.trans
      (planarClusterWindow_subset_thicken hP hU (mem_clusterVertices.1 hx).1))
    (by norm_num) w hs

end Rigidity.Percolation
