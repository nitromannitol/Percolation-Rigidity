import Rigidity.Proofs.Cluster.PlanarBoxCluster
import Rigidity.Proofs.Cluster.PlanarSobolevTwo
import Rigidity.Proofs.Cluster.PlanarReachBounds

/-!
# The Sobolev inequality on the cluster of a resolved integer square

Armstrong and Dario, Lemmas 3.2 and 3.3 and Proposition 3.4 with `d = 2` and `s = 2` (so
`s_* = 1`), in the case `∑_{C(B)} w = 0`, on the cluster `C(B)` of an integer square `B` resolved
by the planar partition (for instance the triple `3□'` of a triadic cube, which is not triadic).
The windows and pair windows inside `B` lie in the squares of side `9s` around the partition
cubes, so Lemmas 3.2 and 3.3 hold with the reach scales `ρ`, `ρ'` of the coarse-graining
data of `B`, and the lattice Sobolev inequality on the square `B` gives a constant `K` with
`∑_{x ∈ C(B)} w(x)² ≤ K (∑_{z ∈ C(B)} ((3^{ρ(z)})² + 3^{ρ'(z)}) |∇w 1_{a≠0}|(z))²`.
The reach scales are bounded by the reach of the planar partition, `3^{ρ(z)} ≤ planarReach ω z`
and `3^{ρ'(z)} ≤ 3 planarReach ω z`, which have all moments.
-/

open LatticeProb.Percolation Rigidity.Proofs.Section5
open scoped ENNReal Classical

namespace Rigidity.Percolation

variable {ω : Configuration 2}

private theorem boxSob_abs_sub_le_one_of_adj {d : ℕ} {u v : Vertex d}
    (h : (nearestNeighborGraph d).Adj u v) (k : Fin d) : |u k - v k| ≤ 1 := by
  obtain ⟨l, hl | hl⟩ := h <;> subst hl <;> by_cases hkl : k = l <;> simp [LatticeProb.unit, hkl]

/-- The window of the partition cube of a vertex of a resolved square lies in the
`4s`-neighbourhood of the partition cube. -/
theorem planarBoxClusterWindow_subset_thicken {B : IntegerCube 2}
    (hBr : PlanarBoxResolved ω B) {x : Vertex 2} (hx : x ∈ B.vertices) :
    planarBoxClusterWindow ω B x ⊆ ((planarPartCube ω x).thicken 4).vertices := by
  intro y hy
  rw [← TriadicCube.ninefold_vertices_eq_thicken]
  exact TriadicCube.subset_ninefold_of_mem_planarSquares
    ((planarPartCube ω x).boxWindow_mem_planarSquares (hBr x hx)) (Finset.mem_filter.1 hy).1

/-- The pair region of two lattice neighbours of a resolved square lies in the
`4s`-neighbourhood of the partition cube of the first. -/
theorem planarBoxClusterPairRegion_subset_thicken (hP : PlanarPartitionEvent ω)
    {B : IntegerCube 2} (hBr : PlanarBoxResolved ω B)
    {x y : Vertex 2} (hx : x ∈ B.vertices) (hy : y ∈ B.vertices)
    (hadj : (nearestNeighborGraph 2).Adj x y) :
    planarBoxClusterPairRegion ω B x y ⊆ ((planarPartCube ω x).thicken 4).vertices := by
  have hnear : ∀ i, |x i - y i| ≤ 1 := boxSob_abs_sub_le_one_of_adj hadj
  have hsc := planarPartCube_scales_close hP hnear
  have hsub := hBr x hx
  have hsub' := hBr y hy
  intro z hz
  unfold planarBoxClusterPairRegion at hz
  split_ifs at hz with h
  · have hspec := TriadicCube.boxPairWindow_spec hsub hsub' h hsc.2
      (planarPartCube_spec hP x).1 (planarPartCube_spec hP y).1 hnear
    rw [← TriadicCube.ninefold_vertices_eq_thicken]
    exact TriadicCube.subset_ninefold_of_mem_planarSquares hspec.1 (Finset.mem_filter.1 hz).1
  · have hnear' : ∀ i, |y i - x i| ≤ 1 := fun i => by rw [abs_sub_comm]; exact hnear i
    have hspec := TriadicCube.boxPairWindow_spec hsub' hsub (by omega) hsc.1
      (planarPartCube_spec hP y).1 (planarPartCube_spec hP x).1 hnear'
    have hz' : z ∈ ((planarPartCube ω y).thicken 4).vertices := by
      rw [← TriadicCube.ninefold_vertices_eq_thicken]
      exact TriadicCube.subset_ninefold_of_mem_planarSquares hspec.1 (Finset.mem_filter.1 hz).1
    exact TriadicCube.thicken_four_subset_of_near
      ⟨x, (planarPartCube_spec hP x).1, y, (planarPartCube_spec hP y).1, hnear⟩ (by omega) hz'

/-- **Planar form of Armstrong and Dario, Lemma 3.2, on a resolved square, with the reach
scale.** For `1 ≤ s < ∞`,
`∑_{x ∈ C(B)} |w(x) - [w]_𝒫(x)|^s ≤ C^s ∑_{z ∈ C(B)} (3^{ρ(z)})^{2s} |∇w 1_{a≠0}|^s(z)`,
where `ρ(z)` is the reach scale of the coarse-graining data of `B` and
`C = (3/2) · 10² · 9² · 2√2`. -/
theorem planarBox_sum_abs_sub_coarseAnchor_rpow_le (hP : PlanarPartitionEvent ω)
    {B : IntegerCube 2} (hBr : PlanarBoxResolved ω B)
    (w : Vertex 2 → ℝ) {s : ℝ} (hs : 1 ≤ s) :
    ∑ x ∈ boxClusterVertices ω B, |w x - w (planarCoarseAnchor ω x)| ^ s ≤
      (3 / 2 * (2 * ((4 : ℕ) : ℝ) + 2) ^ 2 * (2 * ((4 : ℕ) : ℝ) + 1) ^ 2 *
        (2 * √((2 : ℕ) : ℝ))) ^ s *
        ∑ z ∈ boxClusterVertices ω B, ((3 : ℝ) ^ (planarBoxCoarseData hP B hBr).reachScale z) ^
          (s * ((2 : ℕ) : ℝ)) * gradNormIn (openGraph ω) (boxClusterVertices ω B) w z ^ s :=
  (planarBoxCoarseData hP B hBr).sum_abs_sub_coarsen_rpow_le_reach (c := 4)
    (fun x hx => Finset.inter_subset_left.trans
      (planarBoxClusterWindow_subset_thicken hBr (mem_boxClusterVertices.1 hx).1))
    (by norm_num) w hs

/-- **Planar form of Armstrong and Dario, Lemma 3.3, on a resolved square, with the pair reach
scale.** For `1 ≤ s < ∞`,
`∑_{x ∈ B} |∇[w]_𝒫|^s(x) ≤ C^s ∑_{z ∈ C(B)} (3^{ρ'(z)})^{2s-1} |∇w 1_{a≠0}|^s(z)`,
where `ρ'(z)` is the pair reach scale of the coarse-graining data of `B` and
`C = 4 · (3/2) · 10² · 9² · 2√2`. -/
theorem planarBox_sum_gradNormIn_coarseAnchor_rpow_le (hP : PlanarPartitionEvent ω)
    {B : IntegerCube 2} (hBr : PlanarBoxResolved ω B)
    (w : Vertex 2 → ℝ) {s : ℝ} (hs : 1 ≤ s) :
    ∑ x ∈ B.vertices, gradNormIn (nearestNeighborGraph 2) B.vertices
        (fun x => w (planarCoarseAnchor ω x)) x ^ s ≤
      (2 * ((2 : ℕ) : ℝ) * (3 / 2 * (2 * ((4 : ℕ) : ℝ) + 2) ^ 2) * (2 * ((4 : ℕ) : ℝ) + 1) ^ 2 *
        (2 * √((2 : ℕ) : ℝ))) ^ s *
        ∑ z ∈ boxClusterVertices ω B,
          ((3 : ℝ) ^ (planarBoxCoarseData hP B hBr).pairReachScale z) ^
            (s * ((2 : ℕ) : ℝ) - 1) * gradNormIn (openGraph ω) (boxClusterVertices ω B) w z ^ s :=
  (planarBoxCoarseData hP B hBr).sum_gradNormIn_coarsen_rpow_le_reach (c := 4)
    (fun q hq => by
      have hq' := hq
      rw [CoarseData.edgesAcross, Finset.mem_filter, Finset.mem_product] at hq'
      obtain ⟨⟨hx, hy⟩, hadj, -⟩ := hq'
      exact Finset.inter_subset_left.trans
        (planarBoxClusterPairRegion_subset_thicken hP hBr hx hy hadj))
    le_rfl w hs

/-- **Armstrong and Dario, Proposition 3.4, for the planar partition with `s = 2`, on a resolved
integer square** (case `∑_{C(B)} w = 0`). -/
theorem exists_planarBox_sum_sq_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ω : Configuration 2) (hP : PlanarPartitionEvent ω) (B : IntegerCube 2)
      (_ : 0 < B.size) (hBr : PlanarBoxResolved ω B) (w : Vertex 2 → ℝ),
      ∑ x ∈ boxClusterVertices ω B, w x = 0 →
        ∑ x ∈ boxClusterVertices ω B, w x ^ 2 ≤
          K * (∑ z ∈ boxClusterVertices ω B,
            (((3 : ℝ) ^ (planarBoxCoarseData hP B hBr).reachScale z) ^ 2 +
              (3 : ℝ) ^ (planarBoxCoarseData hP B hBr).pairReachScale z) *
              gradNormIn (openGraph ω) (boxClusterVertices ω B) w z) ^ 2 := by
  set C₂ : ℝ := 3 / 2 * (2 * ((4 : ℕ) : ℝ) + 2) ^ 2 * (2 * ((4 : ℕ) : ℝ) + 1) ^ 2 *
    (2 * √((2 : ℕ) : ℝ)) with hC₂
  set C₃ : ℝ := 2 * ((2 : ℕ) : ℝ) * (3 / 2 * (2 * ((4 : ℕ) : ℝ) + 2) ^ 2) *
    (2 * ((4 : ℕ) : ℝ) + 1) ^ 2 * (2 * √((2 : ℕ) : ℝ)) with hC₃
  have hC₂0 : 0 ≤ C₂ := by rw [hC₂]; positivity
  have hC₃0 : 0 ≤ C₃ := by rw [hC₃]; positivity
  refine ⟨2 ^ ((2 : ℝ) - 1) * (1 + 2 ^ ((2 : ℝ) - 1) + 2 ^ ((2 : ℝ) - 1) * 2 ^ ((2 : ℝ) - 1)) *
    (C₂ ^ (2 : ℝ) + 4 * (C₃ ^ (1 : ℝ)) ^ ((2 : ℝ) / 1)), by positivity, ?_⟩
  intro ω hP B hB hBr w hw
  set P := planarBoxCoarseData hP B hBr with hPdef
  have hsize : 0 < B.size := hB
  have h32 := planarBox_sum_abs_sub_coarseAnchor_rpow_le hP hBr w (s := 2) (by norm_num)
  have h33 := planarBox_sum_gradNormIn_coarseAnchor_rpow_le hP hBr w (s := 1) le_rfl
  have hmain := P.sum_rpow_le_of_latticeSobolevOn (s := 2) (t := 1) (by norm_num) le_rfl
    (by norm_num) (Real.rpow_nonneg hC₂0 _) (Real.rpow_nonneg hC₃0 _) (by norm_num)
    (a := fun z => ((3 : ℝ) ^ P.reachScale z) ^ ((2 : ℝ) * ((2 : ℕ) : ℝ)))
    (b := fun z => ((3 : ℝ) ^ P.pairReachScale z) ^ ((1 : ℝ) * ((2 : ℕ) : ℝ) - 1))
    (fun z => Real.rpow_nonneg (by positivity) _) (fun z => Real.rpow_nonneg (by positivity) _)
    (B.latticeSobolevOn_two hsize) w h32 h33 hw
  have hweight : ∀ z, (((3 : ℝ) ^ P.reachScale z) ^ ((2 : ℝ) * ((2 : ℕ) : ℝ))) ^ ((1 : ℝ) / 2) +
      ((3 : ℝ) ^ P.pairReachScale z) ^ ((1 : ℝ) * ((2 : ℕ) : ℝ) - 1) =
      ((3 : ℝ) ^ P.reachScale z) ^ 2 + (3 : ℝ) ^ P.pairReachScale z := by
    intro z
    rw [← Real.rpow_mul (x := (3 : ℝ) ^ P.reachScale z) (by positivity)]
    norm_num
  simp only [hweight, div_one, Real.rpow_one, Real.rpow_two, sq_abs] at hmain ⊢
  exact hmain

/-- On a resolved square, `3^{ρ(z)}` is at most the reach of the planar partition at `z`. -/
theorem three_pow_reachScale_le_planarReach_box (hP : PlanarPartitionEvent ω)
    {B : IntegerCube 2} (hBr : PlanarBoxResolved ω B)
    {z : Vertex 2} (hz : z ∈ boxClusterVertices ω B) :
    (3 : ℝ≥0∞) ^ (planarBoxCoarseData hP B hBr).reachScale z ≤ planarReach ω z := by
  set P := planarBoxCoarseData hP B hBr
  have hne : (P.cluster.filter fun x => z ∈ P.region x).Nonempty :=
    ⟨z, Finset.mem_filter.2 ⟨hz, P.mem_region_self hz⟩⟩
  obtain ⟨x, hx, hxs⟩ := Finset.exists_mem_eq_sup _ hne (fun x => (P.part x).scale)
  rw [Finset.mem_filter] at hx
  unfold CoarseData.reachScale
  rw [hxs]
  have hxB : x ∈ B.vertices := (mem_boxClusterVertices.1 hx.1).1
  exact three_pow_scale_le_planarReach hP (TriadicCube.subset_ninefold_of_mem_planarSquares
    ((planarPartCube ω x).boxWindow_mem_planarSquares (hBr x hxB))
    (Finset.mem_filter.1 hx.2).1)

/-- On a resolved square, `3^{ρ'(z)}` is at most three times the reach of the planar partition at
`z`. -/
theorem three_pow_pairReachScale_le_planarReach_box (hP : PlanarPartitionEvent ω)
    {B : IntegerCube 2} (hBr : PlanarBoxResolved ω B)
    (z : Vertex 2) :
    (3 : ℝ≥0∞) ^ (planarBoxCoarseData hP B hBr).pairReachScale z ≤ 3 * planarReach ω z := by
  set P := planarBoxCoarseData hP B hBr
  by_cases hne : (P.edgesAcross.filter fun q => z ∈ P.pairRegion q.1 q.2).Nonempty
  · obtain ⟨q, hq, hqs⟩ := Finset.exists_mem_eq_sup _ hne (fun q => (P.part q.1).scale)
    rw [Finset.mem_filter] at hq
    unfold CoarseData.pairReachScale
    rw [hqs]
    have hqE := hq.1
    rw [CoarseData.edgesAcross, Finset.mem_filter, Finset.mem_product] at hqE
    obtain ⟨⟨hx, hy⟩, hadj, -⟩ := hqE
    have hnear : ∀ i, |q.1 i - q.2 i| ≤ 1 := boxSob_abs_sub_le_one_of_adj hadj
    have hsc := planarPartCube_scales_close hP hnear
    have hsub := hBr q.1 hx
    have hsub' := hBr q.2 hy
    have hzR : z ∈ planarBoxClusterPairRegion ω B q.1 q.2 := hq.2
    unfold planarBoxClusterPairRegion at hzR
    split_ifs at hzR with h
    · have hspec := TriadicCube.boxPairWindow_spec hsub hsub' h hsc.2
        (planarPartCube_spec hP q.1).1 (planarPartCube_spec hP q.2).1 hnear
      have hR := three_pow_scale_le_planarReach hP
        (TriadicCube.subset_ninefold_of_mem_planarSquares hspec.1 (Finset.mem_filter.1 hzR).1)
      calc (3 : ℝ≥0∞) ^ (P.part q.1).scale ≤ planarReach ω z := hR
        _ ≤ 3 * planarReach ω z := le_mul_of_one_le_left zero_le (by norm_num)
    · have hnear' : ∀ i, |q.2 i - q.1 i| ≤ 1 := fun i => by rw [abs_sub_comm]; exact hnear i
      have hspec := TriadicCube.boxPairWindow_spec hsub' hsub (by omega) hsc.1
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
