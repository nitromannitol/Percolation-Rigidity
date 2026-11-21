import Rigidity.Proofs.Cluster.PlanarCoarseReach
import Rigidity.Proofs.Cluster.PlanarLatticeSobolev

/-!
# The Sobolev inequality on the cluster of a resolved planar cube

Armstrong and Dario, Proposition 3.4 with `d = 2` and `s = 2` (so `s_* = 1`), in the case
`∑_{C_*(U)} w = 0`, for the planar partition: there is a constant `K` such that for every
configuration of the planar partition event, every triadic cube `U` resolved by the planar
partition and every `w` of mean zero on `C_*(U)`,
`∑_{x ∈ C_*(U)} w(x)² ≤ K (∑_{z ∈ C_*(U)} ((3^{ρ(z)})² + 3^{ρ'(z)}) |∇w 1_{a≠0}|(z))²`,
with `ρ` and `ρ'` the reach scales of the planar coarse-graining data.
-/

open LatticeProb.Percolation Rigidity.Proofs.Section5
open scoped Classical

namespace Rigidity.Percolation

/-- **Armstrong and Dario, Proposition 3.4, for the planar partition with `s = 2`** (case
`∑_{C_*(U)} w = 0`). -/
theorem exists_planar_sum_sq_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ω : Configuration 2) (hP : PlanarPartitionEvent ω) (U : TriadicCube 2)
      (hU : PlanarResolved ω U) (w : Vertex 2 → ℝ),
      ∑ x ∈ clusterVertices ω U, w x = 0 →
        ∑ x ∈ clusterVertices ω U, w x ^ 2 ≤
          K * (∑ z ∈ clusterVertices ω U,
            (((3 : ℝ) ^ (planarCoarseData hP U hU).reachScale z) ^ 2 +
              (3 : ℝ) ^ (planarCoarseData hP U hU).pairReachScale z) *
              gradNormIn (openGraph ω) (clusterVertices ω U) w z) ^ 2 := by
  set C₂ : ℝ := 3 / 2 * (2 * ((4 : ℕ) : ℝ) + 2) ^ 2 * (2 * ((4 : ℕ) : ℝ) + 1) ^ 2 *
    (2 * √((2 : ℕ) : ℝ)) with hC₂
  set C₃ : ℝ := 2 * ((2 : ℕ) : ℝ) * (3 / 2 * (2 * ((4 : ℕ) : ℝ) + 2) ^ 2) *
    (2 * ((4 : ℕ) : ℝ) + 1) ^ 2 * (2 * √((2 : ℕ) : ℝ)) with hC₃
  have hC₂0 : 0 ≤ C₂ := by rw [hC₂]; positivity
  have hC₃0 : 0 ≤ C₃ := by rw [hC₃]; positivity
  refine ⟨2 ^ ((2 : ℝ) - 1) * (1 + 2 ^ ((2 : ℝ) - 1) + 2 ^ ((2 : ℝ) - 1) * 2 ^ ((2 : ℝ) - 1)) *
    (C₂ ^ (2 : ℝ) + 4 * (C₃ ^ (1 : ℝ)) ^ ((2 : ℝ) / 1)), by positivity, ?_⟩
  intro ω hP U hU w hw
  set P := planarCoarseData hP U hU with hPdef
  have hsize : 0 < U.toIntegerCube.size := by
    show 0 < 3 ^ U.scale
    positivity
  have h32 := planar_sum_abs_sub_coarseAnchor_rpow_le hP hU w (s := 2) (by norm_num)
  have h33 := planar_sum_gradNormIn_coarseAnchor_rpow_le hP hU w (s := 1) le_rfl
  have hmain := P.sum_rpow_le_of_latticeSobolevOn (s := 2) (t := 1) (by norm_num) le_rfl
    (by norm_num) (Real.rpow_nonneg hC₂0 _) (Real.rpow_nonneg hC₃0 _) (by norm_num)
    (a := fun z => ((3 : ℝ) ^ P.reachScale z) ^ ((2 : ℝ) * ((2 : ℕ) : ℝ)))
    (b := fun z => ((3 : ℝ) ^ P.pairReachScale z) ^ ((1 : ℝ) * ((2 : ℕ) : ℝ) - 1))
    (fun z => Real.rpow_nonneg (by positivity) _) (fun z => Real.rpow_nonneg (by positivity) _)
    (U.toIntegerCube.latticeSobolevOn_two hsize) w h32 h33 hw
  have hweight : ∀ z, (((3 : ℝ) ^ P.reachScale z) ^ ((2 : ℝ) * ((2 : ℕ) : ℝ))) ^ ((1 : ℝ) / 2) +
      ((3 : ℝ) ^ P.pairReachScale z) ^ ((1 : ℝ) * ((2 : ℕ) : ℝ) - 1) =
      ((3 : ℝ) ^ P.reachScale z) ^ 2 + (3 : ℝ) ^ P.pairReachScale z := by
    intro z
    rw [← Real.rpow_mul (x := (3 : ℝ) ^ P.reachScale z) (by positivity)]
    norm_num
  simp only [hweight, div_one, Real.rpow_one, Real.rpow_two, sq_abs] at hmain ⊢
  exact hmain

end Rigidity.Percolation
