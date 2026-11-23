import Rigidity.Proofs.Dirichlet.PlanarMuTest
import Rigidity.Proofs.Cluster.PlanarCoarseReach

/-!
# The cluster of a cube and the clusters of its tiles

Let `U` be resolved by the planar partition and `T ⊆ U` a triadic cube. A vertex `x` of `C_*(U)`
is joined to the anchor of its partition cube inside the window of its partition cube, which lies
in the square of side `9s` around the partition cube, `s = 3^{s(x)}`, hence in the square of side
`10 s` around `x`. If this square lies in `T`, then `x ∈ C_*(T)`
(`mem_clusterVertices_of_far`). So the vertices of `C_*(U) ∩ T` outside `C_*(T)` lie in the
boundary layer of `T` of width `5 · 3^k + 1` when all partition cubes have scale at most `k`
(`card_sdiff_clusterVertices_le`), which is the bound `|(C_*(□_m) ∩ (y + □_n)) \ C_*(y + □_n)| ≤
|∂_𝒫(y + □_n)|` in Step 1 of the proof of Armstrong and Dario, Lemma 6.3.
-/

open Finset LatticeProb LatticeHC LatticeProb.Percolation Rigidity.Percolation
open Rigidity.Proofs.Section5
open scoped Classical

namespace Rigidity.Dirichlet

variable {ω : Configuration 2}

/-- A point of a triadic cube is within half the side of the centre. -/
theorem TriadicCube.abs_sub_center_le {Q : TriadicCube 2} {x : Vertex 2} (hx : x ∈ Q.vertices)
    (i : Fin 2) : 2 * |x i - Q.center i| < Q.side := by
  have h := hx i
  rw [show 2 * (x i - Q.side * Q.index i) = 2 * (x i - Q.center i) by rfl, abs_mul] at h
  simpa using h

/-- **A vertex far from the boundary of a subcube is in the cluster of the subcube.** -/
theorem mem_clusterVertices_of_far (hP : PlanarPartitionEvent ω) {U T : TriadicCube 2}
    (hU : PlanarResolved ω U) {x : Vertex 2} (hx : x ∈ clusterVertices ω U)
    (hfar : ∀ y : Vertex 2, (∀ i, |x i - y i| ≤ 5 * 3 ^ (planarPartCube ω x).scale) →
      y ∈ T.vertices) : x ∈ clusterVertices ω T := by
  have hxC := mem_clusterVertices.1 hx
  set Q := planarPartCube ω x
  have hxQ := (planarPartCube_spec hP x).1
  have hwin : ∀ y ∈ planarClusterWindow ω U x, y ∈ T.vertices := by
    intro y hy
    have hy9 : y ∈ (↑Q.ninefold.vertices : Set (Vertex 2)) := by
      rw [TriadicCube.ninefold_vertices_eq_thicken]
      exact Finset.mem_coe.2 (planarClusterWindow_subset_thicken hP hU hxC.1 hy)
    rw [TriadicCube.mem_ninefold] at hy9
    refine hfar y fun i => ?_
    have h1 := hy9 i
    have h2 := TriadicCube.abs_sub_center_le hxQ i
    have hr := Q.two_mul_ninefoldRadius
    have hs : Q.side = 3 ^ Q.scale := rfl
    have hab := abs_sub_le (x i) (Q.center i) (y i)
    rw [abs_sub_comm (Q.center i) (y i)] at hab
    have : 2 * |x i - y i| ≤ 10 * 3 ^ Q.scale := by
      rw [hs] at h2
      linarith
    linarith
  obtain ⟨W, hW⟩ := joinedWithin_planarClusterWindow hP hU hxC
  have hxT : x ∈ T.vertices := hfar x fun i => by simp
  refine mem_clusterVertices.2 ⟨hxT, ⟨W, fun v hv => ?_⟩⟩
  exact hwin v (hW v hv)

/-- **The vertices of `C_*(U) ∩ T` outside `C_*(T)` lie in a boundary layer of `T`.** -/
theorem sdiff_clusterVertices_subset_cubeLayer (hP : PlanarPartitionEvent ω) {U T : TriadicCube 2}
    (hU : PlanarResolved ω U) {k : ℕ}
    (hk : ∀ x ∈ U.vertices, (planarPartCube ω x).scale ≤ k) :
    (clusterVertices ω U).filter (fun x => x ∈ T.vertices) \ clusterVertices ω T ⊆
      cubeLayer T.toIntegerCube (5 * 3 ^ k + 1) := by
  intro x hx
  obtain ⟨hxF, hxT⟩ := Finset.mem_sdiff.1 hx
  obtain ⟨hxU, hxTv⟩ := Finset.mem_filter.1 hxF
  have hxTc : x ∈ T.toIntegerCube.vertices := (T.mem_toIntegerCube_vertices x).2 hxTv
  refine Finset.mem_filter.2 ⟨hxTc, ?_⟩
  by_contra hnot
  push Not at hnot
  apply hxT
  refine mem_clusterVertices_of_far hP hU hxU fun y hy => ?_
  have hsk : (5 : ℤ) * 3 ^ (planarPartCube ω x).scale ≤ 5 * 3 ^ k := by
    have := pow_le_pow_right₀ (show (1 : ℤ) ≤ 3 by norm_num)
      (hk x (mem_clusterVertices.1 hxU).1)
    linarith
  rw [← T.mem_toIntegerCube_vertices, IntegerCube.mem_vertices]
  intro i
  have h1 := hnot i
  have h2 := hy i
  rw [abs_le] at h2
  push_cast at h1
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- **The number of vertices of `C_*(U) ∩ T` outside `C_*(T)`** is at most
`4 (5 · 3^k + 1) · side(T)`. -/
theorem card_sdiff_clusterVertices_le (hP : PlanarPartitionEvent ω) {U T : TriadicCube 2}
    (hU : PlanarResolved ω U) {k : ℕ}
    (hk : ∀ x ∈ U.vertices, (planarPartCube ω x).scale ≤ k) :
    (((clusterVertices ω U).filter (fun x => x ∈ T.vertices) \ clusterVertices ω T).card : ℝ) ≤
      2 * 2 * ((5 * 3 ^ k + 1 : ℕ) : ℝ) * (3 ^ T.scale : ℕ) := by
  have hsub := sdiff_clusterVertices_subset_cubeLayer (T := T) hP hU hk
  have hL : 0 < T.toIntegerCube.size := by change 0 < 3 ^ T.scale; positivity
  have h := card_cubeLayer_div_le T.toIntegerCube hL (5 * 3 ^ k + 1)
  have hV : (0 : ℝ) < (T.toIntegerCube.size : ℝ) ^ 2 := by positivity
  rw [div_le_div_iff₀ hV (by exact_mod_cast hL)] at h
  have hc : (((clusterVertices ω U).filter (fun x => x ∈ T.vertices) \
      clusterVertices ω T).card : ℝ) ≤ (cubeLayer T.toIntegerCube (5 * 3 ^ k + 1)).card := by
    exact_mod_cast Finset.card_le_card hsub
  have hs : (T.toIntegerCube.size : ℝ) = ((3 ^ T.scale : ℕ) : ℝ) := rfl
  rw [hs] at h hV
  have hpos : (0 : ℝ) < ((3 ^ T.scale : ℕ) : ℝ) := by positivity
  have h' : ((cubeLayer T.toIntegerCube (5 * 3 ^ k + 1)).card : ℝ) ≤
      2 * 2 * ((5 * 3 ^ k + 1 : ℕ) : ℝ) * ((3 ^ T.scale : ℕ) : ℝ) := by
    have e : ((3 ^ T.scale : ℕ) : ℝ) ^ 2 = ((3 ^ T.scale : ℕ) : ℝ) * ((3 ^ T.scale : ℕ) : ℝ) :=
      sq _
    rw [e] at h
    refine le_of_mul_le_mul_right ?_ hpos
    calc ((cubeLayer T.toIntegerCube (5 * 3 ^ k + 1)).card : ℝ) * ((3 ^ T.scale : ℕ) : ℝ)
        ≤ 2 * 2 * ((5 * 3 ^ k + 1 : ℕ) : ℝ) *
          (((3 ^ T.scale : ℕ) : ℝ) * ((3 ^ T.scale : ℕ) : ℝ)) := h
      _ = 2 * 2 * ((5 * 3 ^ k + 1 : ℕ) : ℝ) * ((3 ^ T.scale : ℕ) : ℝ) *
          ((3 ^ T.scale : ℕ) : ℝ) := by ring
  exact hc.trans h'

end Rigidity.Dirichlet
