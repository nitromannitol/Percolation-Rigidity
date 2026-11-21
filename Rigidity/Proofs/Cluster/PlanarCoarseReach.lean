import Rigidity.Proofs.Cluster.CoarseReach
import Rigidity.Proofs.Cluster.PlanarCoarseData

/-!
# The planar coarsening error with the reach of the partition

The windows of the planar partition lie in the squares of side `9s` around the partition cubes,
which are their `4s`-neighbourhoods; the pair window of two adjacent partition cubes lies in the
`4s`-neighbourhood of the smaller one, hence of either. Hence Lemmas 3.2 and 3.3 of Armstrong and
Dario hold on a resolved planar cube with the reach scales of the planar coarse-graining data in
place of the scale of the partition cube of `z`, with the constants `(3/2) · 10² · 9² · 2√2` and
`4 · (3/2) · 10² · 9² · 2√2`.
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

private theorem planar_reach_abs_sub_le_one_of_adj {d : ℕ} {u v : Vertex d}
    (h : (nearestNeighborGraph d).Adj u v) (k : Fin d) : |u k - v k| ≤ 1 := by
  obtain ⟨l, hl | hl⟩ := h <;> subst hl <;> by_cases hkl : k = l <;> simp [LatticeProb.unit, hkl]

/-- The `4s'`-neighbourhood of a triadic cube near a triadic cube of larger scale lies in the
`4s`-neighbourhood of the larger one. -/
theorem TriadicCube.thicken_four_subset_of_near {d : ℕ} {Q Q' : TriadicCube d} (h : Q.Near Q')
    (hsc : Q'.scale < Q.scale) : (Q'.thicken 4).vertices ⊆ (Q.thicken 4).vertices := by
  obtain ⟨a, ha, b, hb, hab⟩ := h
  rw [← Q.mem_toIntegerCube_vertices, IntegerCube.mem_vertices] at ha
  rw [← Q'.mem_toIntegerCube_vertices, IntegerCube.mem_vertices] at hb
  have hs : 3 * Q'.toIntegerCube.size ≤ Q.toIntegerCube.size := by
    change 3 * 3 ^ Q'.scale ≤ 3 ^ Q.scale
    calc 3 * 3 ^ Q'.scale = 3 ^ (Q'.scale + 1) := by ring
      _ ≤ 3 ^ Q.scale := Nat.pow_le_pow_right (by norm_num) hsc
  have hs' : 3 * (Q'.toIntegerCube.size : ℤ) ≤ (Q.toIntegerCube.size : ℤ) := by exact_mod_cast hs
  intro v hv
  rw [IntegerCube.mem_vertices] at hv ⊢
  intro i
  obtain ⟨h1, h2⟩ := ha i
  obtain ⟨h3, h4⟩ := hb i
  obtain ⟨h5, h6⟩ := hv i
  have h7 := abs_le.1 (hab i)
  change Q'.toIntegerCube.corner i - ((4 : ℕ) : ℤ) * (Q'.toIntegerCube.size : ℤ) ≤ v i at h5
  change v i < Q'.toIntegerCube.corner i - ((4 : ℕ) : ℤ) * (Q'.toIntegerCube.size : ℤ) +
    (((2 * 4 + 1) * Q'.toIntegerCube.size : ℕ) : ℤ) at h6
  change Q.toIntegerCube.corner i - ((4 : ℕ) : ℤ) * (Q.toIntegerCube.size : ℤ) ≤ v i ∧
    v i < Q.toIntegerCube.corner i - ((4 : ℕ) : ℤ) * (Q.toIntegerCube.size : ℤ) +
      (((2 * 4 + 1) * Q.toIntegerCube.size : ℕ) : ℤ)
  push_cast at h5 h6 ⊢
  constructor <;> omega

/-- The pair region of two lattice neighbours of a resolved cube lies in the `4s`-neighbourhood of
the partition cube of the first. -/
theorem planarClusterPairRegion_subset_thicken (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) {x y : Vertex 2} (hx : x ∈ U.vertices) (hy : y ∈ U.vertices)
    (hadj : (nearestNeighborGraph 2).Adj x y) :
    planarClusterPairRegion ω U x y ⊆ ((planarPartCube ω x).thicken 4).vertices := by
  have hnear : ∀ i, |x i - y i| ≤ 1 := planar_reach_abs_sub_le_one_of_adj hadj
  have hsc := planarPartCube_scales_close hP hnear
  have hsub := planarPartCube_subset_of_resolved hP hU hx
  have hsub' := planarPartCube_subset_of_resolved hP hU hy
  intro z hz
  unfold planarClusterPairRegion at hz
  split_ifs at hz with h
  · have hspec := TriadicCube.pairWindow_spec (hU x hx) hsub hsub' h hsc.2
      (planarPartCube_spec hP x).1 (planarPartCube_spec hP y).1 hnear
    rw [← TriadicCube.ninefold_vertices_eq_thicken]
    exact TriadicCube.subset_ninefold_of_mem_planarSquares hspec.1 (Finset.mem_filter.1 hz).1
  · have hnear' : ∀ i, |y i - x i| ≤ 1 := fun i => by rw [abs_sub_comm]; exact hnear i
    have hspec := TriadicCube.pairWindow_spec (hU y hy) hsub' hsub (by omega) hsc.1
      (planarPartCube_spec hP y).1 (planarPartCube_spec hP x).1 hnear'
    have hz' : z ∈ ((planarPartCube ω y).thicken 4).vertices := by
      rw [← TriadicCube.ninefold_vertices_eq_thicken]
      exact TriadicCube.subset_ninefold_of_mem_planarSquares hspec.1 (Finset.mem_filter.1 hz).1
    exact TriadicCube.thicken_four_subset_of_near
      ⟨x, (planarPartCube_spec hP x).1, y, (planarPartCube_spec hP y).1, hnear⟩ (by omega) hz'

/-- **Planar form of Armstrong and Dario, Lemma 3.3, with the pair reach scale.** On a cube `U`
resolved by the planar partition, for `1 ≤ s < ∞`,
`∑_{x ∈ U} |∇[w]_𝒫|^s(x) ≤ C^s ∑_{z ∈ C_*(U)} (3^{ρ'(z)})^{2s-1} |∇w 1_{a≠0}|^s(z)`,
where `ρ'(z)` is the pair reach scale of the planar coarse-graining data and
`C = 4 · (3/2) · 10² · 9² · 2√2`. -/
theorem planar_sum_gradNormIn_coarseAnchor_rpow_le (hP : PlanarPartitionEvent ω)
    {U : TriadicCube 2} (hU : PlanarResolved ω U) (w : Vertex 2 → ℝ) {s : ℝ} (hs : 1 ≤ s) :
    ∑ x ∈ U.toIntegerCube.vertices, gradNormIn (nearestNeighborGraph 2) U.toIntegerCube.vertices
        (fun x => w (planarCoarseAnchor ω x)) x ^ s ≤
      (2 * ((2 : ℕ) : ℝ) * (3 / 2 * (2 * ((4 : ℕ) : ℝ) + 2) ^ 2) * (2 * ((4 : ℕ) : ℝ) + 1) ^ 2 *
        (2 * √((2 : ℕ) : ℝ))) ^ s *
        ∑ z ∈ clusterVertices ω U, ((3 : ℝ) ^ (planarCoarseData hP U hU).pairReachScale z) ^
          (s * ((2 : ℕ) : ℝ) - 1) * gradNormIn (openGraph ω) (clusterVertices ω U) w z ^ s :=
  (planarCoarseData hP U hU).sum_gradNormIn_coarsen_rpow_le_reach (c := 4)
    (fun q hq => by
      have hq' := hq
      rw [CoarseData.edgesAcross, Finset.mem_filter, Finset.mem_product] at hq'
      obtain ⟨⟨hx, hy⟩, hadj, -⟩ := hq'
      change q.1 ∈ U.toIntegerCube.vertices at hx
      change q.2 ∈ U.toIntegerCube.vertices at hy
      rw [TriadicCube.mem_toIntegerCube_vertices] at hx hy
      exact Finset.inter_subset_left.trans
        (planarClusterPairRegion_subset_thicken hP hU hx hy hadj))
    le_rfl w hs

end Rigidity.Percolation
