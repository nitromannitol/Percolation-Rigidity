import Rigidity.Proofs.Cluster.PlanarCoarseReach
import Rigidity.Proofs.Percolation.PlanarCoarseWeights

/-!
# The reach scales of the planar coarse-graining data and the planar reach

On a cube resolved by the planar partition, the windows and pair windows lie in the squares of
side `9s` around partition cubes, so `3^{ρ(z)}` is at most the reach `planarReach ω z` of the
planar partition, and `3^{ρ'(z)}` at most three times it. The weights of the planar forms of
Lemmas 3.2, 3.3 and Proposition 3.4 of Armstrong and Dario therefore have all moments
(`exists_lintegral_planarReach_pow_le`).
-/

open LatticeProb.Percolation Rigidity.Proofs.Section5
open scoped ENNReal Classical

namespace Rigidity.Percolation

variable {ω : Configuration 2}

private theorem planar_bound_abs_sub_le_one_of_adj {u v : Vertex 2}
    (h : (nearestNeighborGraph 2).Adj u v) (k : Fin 2) : |u k - v k| ≤ 1 := by
  obtain ⟨l, hl | hl⟩ := h <;> subst hl <;> by_cases hkl : k = l <;> simp [LatticeProb.unit, hkl]

/-- A partition cube whose square of side `9s` contains `z` has side at most the reach at `z`. -/
theorem three_pow_scale_le_planarReach (hP : PlanarPartitionEvent ω) {x z : Vertex 2}
    (hz : z ∈ (planarPartCube ω x).ninefold.vertices) :
    (3 : ℝ≥0∞) ^ (planarPartCube ω x).scale ≤ planarReach ω z := by
  unfold planarReach
  exact le_iSup₂_of_le (planarPartCube ω x) ⟨(planarPartCube_spec hP x).2, Finset.mem_coe.2 hz⟩
    le_rfl

/-- The reach of the planar partition is at least one on the partition event. -/
theorem one_le_planarReach (hP : PlanarPartitionEvent ω) (z : Vertex 2) :
    1 ≤ planarReach ω z := by
  have hz : z ∈ (planarPartCube ω z).ninefold.vertices :=
    TriadicCube.subset_ninefold_of_mem_planarSquares
      (planarPartCube ω z).toIntegerCube_mem_planarSquares
      (((planarPartCube ω z).mem_toIntegerCube_vertices z).2 (planarPartCube_spec hP z).1)
  exact le_trans (one_le_pow₀ (by norm_num)) (three_pow_scale_le_planarReach hP hz)

/-- On a resolved cube, `3^{ρ(z)}` is at most the reach of the planar partition at `z`. -/
theorem three_pow_reachScale_le_planarReach (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) {z : Vertex 2} (hz : z ∈ clusterVertices ω U) :
    (3 : ℝ≥0∞) ^ (planarCoarseData hP U hU).reachScale z ≤ planarReach ω z := by
  set P := planarCoarseData hP U hU
  have hne : (P.cluster.filter fun x => z ∈ P.region x).Nonempty :=
    ⟨z, Finset.mem_filter.2 ⟨hz, P.mem_region_self hz⟩⟩
  obtain ⟨x, hx, hxs⟩ := Finset.exists_mem_eq_sup _ hne (fun x => (P.part x).scale)
  rw [Finset.mem_filter] at hx
  unfold CoarseData.reachScale
  rw [hxs]
  have hxU : x ∈ U.vertices := (mem_clusterVertices.1 hx.1).1
  exact three_pow_scale_le_planarReach hP (TriadicCube.subset_ninefold_of_mem_planarSquares
    ((planarPartCube ω x).window_mem_planarSquares (hU x hxU)
      (planarPartCube_subset_of_resolved hP hU hxU)) (Finset.mem_filter.1 hx.2).1)

/-- On a resolved cube, `3^{ρ'(z)}` is at most three times the reach of the planar partition at
`z`. -/
theorem three_pow_pairReachScale_le_planarReach (hP : PlanarPartitionEvent ω)
    {U : TriadicCube 2} (hU : PlanarResolved ω U) (z : Vertex 2) :
    (3 : ℝ≥0∞) ^ (planarCoarseData hP U hU).pairReachScale z ≤ 3 * planarReach ω z := by
  set P := planarCoarseData hP U hU
  by_cases hne : (P.edgesAcross.filter fun q => z ∈ P.pairRegion q.1 q.2).Nonempty
  · obtain ⟨q, hq, hqs⟩ := Finset.exists_mem_eq_sup _ hne (fun q => (P.part q.1).scale)
    rw [Finset.mem_filter] at hq
    unfold CoarseData.pairReachScale
    rw [hqs]
    have hqE := hq.1
    rw [CoarseData.edgesAcross, Finset.mem_filter, Finset.mem_product] at hqE
    obtain ⟨⟨hx, hy⟩, hadj, -⟩ := hqE
    change q.1 ∈ U.toIntegerCube.vertices at hx
    change q.2 ∈ U.toIntegerCube.vertices at hy
    rw [TriadicCube.mem_toIntegerCube_vertices] at hx hy
    have hnear : ∀ i, |q.1 i - q.2 i| ≤ 1 := planar_bound_abs_sub_le_one_of_adj hadj
    have hsc := planarPartCube_scales_close hP hnear
    have hsub := planarPartCube_subset_of_resolved hP hU hx
    have hsub' := planarPartCube_subset_of_resolved hP hU hy
    have hzR : z ∈ planarClusterPairRegion ω U q.1 q.2 := hq.2
    unfold planarClusterPairRegion at hzR
    split_ifs at hzR with h
    · have hspec := TriadicCube.pairWindow_spec (hU q.1 hx) hsub hsub' h hsc.2
        (planarPartCube_spec hP q.1).1 (planarPartCube_spec hP q.2).1 hnear
      have hR := three_pow_scale_le_planarReach hP
        (TriadicCube.subset_ninefold_of_mem_planarSquares hspec.1 (Finset.mem_filter.1 hzR).1)
      calc (3 : ℝ≥0∞) ^ (P.part q.1).scale ≤ planarReach ω z := hR
        _ ≤ 3 * planarReach ω z := le_mul_of_one_le_left zero_le (by norm_num)
    · have hnear' : ∀ i, |q.2 i - q.1 i| ≤ 1 := fun i => by rw [abs_sub_comm]; exact hnear i
      have hspec := TriadicCube.pairWindow_spec (hU q.2 hy) hsub' hsub (by omega) hsc.1
        (planarPartCube_spec hP q.2).1 (planarPartCube_spec hP q.1).1 hnear'
      have hR := three_pow_scale_le_planarReach hP
        (TriadicCube.subset_ninefold_of_mem_planarSquares hspec.1 (Finset.mem_filter.1 hzR).1)
      calc (3 : ℝ≥0∞) ^ (P.part q.1).scale ≤ 3 ^ ((planarPartCube ω q.2).scale + 1) :=
            pow_le_pow_right₀ (by norm_num) hsc.1
        _ = 3 * 3 ^ (planarPartCube ω q.2).scale := by ring
        _ ≤ 3 * planarReach ω z := by gcongr
  · have hempty := Finset.not_nonempty_iff_eq_empty.1 hne
    unfold CoarseData.pairReachScale
    rw [hempty, Finset.sup_empty]
    calc (3 : ℝ≥0∞) ^ (⊥ : ℕ) = 1 := pow_zero 3
      _ ≤ planarReach ω z := one_le_planarReach hP z
      _ ≤ 3 * planarReach ω z := le_mul_of_one_le_left zero_le (by norm_num)

end Rigidity.Percolation
