import Rigidity.Proofs.Regularity.PlanarHarmonicApproximationSquares

/-!
# The clusters of the squares and the infinite cluster in the plane

The proofs of Lemmas 7.1 and 7.3 of Armstrong and Dario (arXiv:1609.09431v2) use two inclusions
between the clusters `C_*(□_j)` of the triadic squares and the infinite cluster `𝒞_∞`, valid above
the minimal scale: `C_*(□_j) ⊆ 𝒞_∞`, and `𝒞_∞ ∩ □_m ⊆ C_*(□_{m + 1})` ("due to the definition of
`𝒳`", proof of Lemma 7.3). For the planar partition:

* if the square `U` is resolved and meets an infinite open cluster `C`, then `C_*(U) ⊆ C`
  (`mem_supp_of_mem_clusterVertices`): the vertices of `C_*(U)` are joined inside `U` to the
  anchors of their partition cubes, the anchors inside a resolved cube are joined inside it, and a
  vertex of an infinite cluster is joined to the anchor of its partition cube;
* if the partition cubes of the vertices of `□_m` have scale at most `m - 2`, every vertex of an
  infinite open cluster in `□_m` lies in `C_*(□_{m + 1})` (`mem_clusterVertices_succ`): it is
  joined to the anchor of its partition cube inside the square of side `9 s` around that cube,
  which lies in `□_{m + 1}`.
-/

namespace Rigidity.Proofs.Regularity

open Finset LatticeProb LatticeProb.Percolation Rigidity.External Rigidity.Percolation
open Rigidity.Proofs.S2 Rigidity.Proofs.Section5

variable {ω : Configuration 2}

theorem mem_triadicCube_zero_iff {j : ℕ} {x : Vertex 2} :
    x ∈ (⟨j, 0⟩ : TriadicCube 2).vertices ↔ ∀ i, 2 * |x i| < 3 ^ j := by
  simp only [TriadicCube.vertices, TriadicCube.side, Set.mem_setOf_eq, Pi.zero_apply, mul_zero,
    sub_zero, abs_mul]
  simp

theorem mem_square_iff_int {m : ℕ} {x : Vertex 2} :
    x ∈ triadicCubeFinset 2 m 0 ↔ ∀ i, 2 * |x i| < 3 ^ m := by
  rw [mem_square_iff]
  refine forall_congr' fun i => ?_
  constructor
  · intro h
    have h' : 2 * |(x i : ℝ)| < 3 ^ m := by linarith
    exact_mod_cast h'
  · intro h
    have h' : ((2 * |x i| : ℤ) : ℝ) < ((3 ^ m : ℤ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    linarith

/-- **The cluster of a resolved square lies in the infinite cluster it meets.** -/
theorem mem_supp_of_mem_clusterVertices (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) (C : OpenComponent ω) (hinf : C.supp.Infinite) {x₀ : Vertex 2}
    (hx₀U : x₀ ∈ U.vertices) (hx₀C : x₀ ∈ C.supp) {y : Vertex 2}
    (hy : y ∈ clusterVertices ω U) : y ∈ C.supp := by
  have hy' := mem_clusterVertices.1 hy
  have hC : (openGraph ω).connectedComponentMk x₀ = C :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 hx₀C
  have hx₀inf : ((openGraph ω).connectedComponentMk x₀).supp.Infinite := by rw [hC]; exact hinf
  obtain ⟨-, -, hB⟩ := (planarPartCube ω x₀).planarAnchor_spec (planarPartCube_meshed hP x₀).1
    (planarPartCube_large hP x₀)
  have h1 := (planarPartCube ω x₀).reachIn_anchor_of_infinite hB (planarPartCube_spec hP x₀).1
    hx₀inf
  have h2 := reachIn_planarAnchor_of_resolved hP hU hy'.1 hx₀U
  obtain ⟨W₁, -⟩ := hy'.2.trans h2
  obtain ⟨W₂, -⟩ := h1
  have hr : (openGraph ω).Reachable y x₀ := ⟨W₁.append W₂⟩
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff, ← hC]
  exact SimpleGraph.ConnectedComponent.eq.2 hr

/-- **A vertex of an infinite cluster in `□_m` lies in `C_*(□_{m + 1})`** when the partition
cubes of the vertices of `□_m` have scale at most `m - 2`. -/
theorem mem_clusterVertices_succ (hP : PlanarPartitionEvent ω) (C : OpenComponent ω)
    (hinf : C.supp.Infinite) {m : ℕ}
    (hsize : ∀ x ∈ triadicCubeFinset 2 m 0, (planarPartCube ω x).scale + 2 ≤ m) {x : Vertex 2}
    (hx : x ∈ triadicCubeFinset 2 m 0) (hxC : x ∈ C.supp) :
    x ∈ clusterVertices ω ⟨m + 1, 0⟩ := by
  have hC : (openGraph ω).connectedComponentMk x = C :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 hxC
  have hxinf : ((openGraph ω).connectedComponentMk x).supp.Infinite := by rw [hC]; exact hinf
  set Q := planarPartCube ω x with hQdef
  have hxQ : x ∈ Q.vertices := (planarPartCube_spec hP x).1
  obtain ⟨-, -, hB⟩ := Q.planarAnchor_spec (planarPartCube_meshed hP x).1
    (planarPartCube_large hP x)
  have h1 := Q.reachIn_anchor_of_infinite hB hxQ hxinf
  have hs : Q.scale + 2 ≤ m := hsize x hx
  have hxm := mem_square_iff_int.1 hx
  -- the square of side `9 s` around `Q` lies in `□_{m + 1}`
  have hsub : (↑Q.ninefold.vertices : Set (Vertex 2)) ⊆ (⟨m + 1, 0⟩ : TriadicCube 2).vertices := by
    intro y hy
    rw [TriadicCube.mem_ninefold] at hy
    rw [mem_triadicCube_zero_iff]
    intro i
    have h9 := Q.two_mul_ninefoldRadius
    have hxc := Q.abs_sub_center_le hxQ i
    have hyc := hy i
    have hxi := hxm i
    have hpow : (9 : ℤ) * 3 ^ Q.scale ≤ 3 ^ m := by
      have : (3 : ℤ) ^ m = 3 ^ (Q.scale + 2) * 3 ^ (m - (Q.scale + 2)) := by
        rw [← pow_add]; congr 1; omega
      rw [this, pow_add]
      have h1 : (1 : ℤ) ≤ 3 ^ (m - (Q.scale + 2)) := one_le_pow₀ (by norm_num)
      have h2 : (0 : ℤ) ≤ 3 ^ Q.scale := by positivity
      nlinarith
    have hm1 : (3 : ℤ) ^ (m + 1) = 3 * 3 ^ m := by ring
    rw [hm1]
    have hR : 2 * Q.ninefoldRadius + 1 = 9 * 3 ^ Q.scale := h9
    have hy1 := abs_le.1 hyc
    have hx1 := le_abs_self (x i - Q.center i)
    have hx2 := neg_abs_le (x i - Q.center i)
    have hx3 := le_abs_self (x i)
    have hx4 := neg_abs_le (x i)
    rcases abs_cases (y i) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith
  have hreach : ReachIn ω (⟨m + 1, 0⟩ : TriadicCube 2).vertices x (Q.planarAnchor ω) :=
    h1.symm.mono hsub
  have hxm1 : x ∈ (⟨m + 1, 0⟩ : TriadicCube 2).vertices := by
    rw [mem_triadicCube_zero_iff]
    intro i
    have := hxm i
    have h3 : (3 : ℤ) ^ m ≤ 3 ^ (m + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  exact mem_clusterVertices.2 ⟨hxm1, hreach⟩

end Rigidity.Proofs.Regularity
