import Rigidity.Proofs.Regularity.PlanarHomogenizedGradient

/-!
# The coarsened function against the discrete homogenized solution on a planar square

Armstrong and Dario (arXiv:1609.09431v2), proof of Lemma 7.1, Step 2: with `w` harmonic for the
lattice Laplacian on the interior of the lattice square `□_{i+3}` and `[u]_𝒫(y) = u(z̄(y))`, where
`z̄(y)` is the anchor of the partition cube of `y`,
`Σ_{□_{i+2}} ([u]_𝒫 - w)² ≤ 2 Σ_y (u - w)²(z̄(y)) + 2 Σ_y (w(z̄(y)) - w(y))²`.

* The first sum counts each anchor `z` at most `size(□_𝒫(z))² ≤ δ²` times, and the anchors lie
  in `C_*(□_{i+3})`: it is at most `δ² Σ_{C_*(□_{i+3})} (u - w)²`. Here the uniform bound
  `size(□_𝒫) ≤ δ` replaces the Hölder step with the moments of the sizes in the source.
* Each term of the second sum is at most `(2 δ ‖∇w‖_∞)²`, with the interior gradient bound
  `abs_grad_le_of_cubeInterior`.
-/

namespace Rigidity.Proofs.Regularity

open Finset LatticeProb LatticeHC LatticeProb.Percolation Rigidity.Percolation Rigidity.Dirichlet
open Rigidity.Proofs.S2 Rigidity.Proofs.Cluster
open scoped Classical

variable {ω : Configuration 2}

/-- The lattice Laplacian is minus the constant-coefficient operator with unit conductances. -/
theorem latticeLaplacian_eq_neg_condLaplacian (f : Vertex 2 → ℝ) (x : Vertex 2) :
    latticeLaplacian f x = -condLaplacian (constCond fun _ => (1 : ℝ)) f x := by
  simp only [latticeLaplacian, condLaplacian, constCond, one_mul]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- The square `□_{i+2}` lies in the interior of the lattice square `□_{i+3}`. -/
theorem mem_cubeInterior_of_mem_square {i : ℕ} {y : Vertex 2}
    (hy : y ∈ triadicCubeFinset 2 (i + 2) 0) :
    y ∈ cubeInterior (⟨i + 3, 0⟩ : TriadicCube 2).toIntegerCube := by
  unfold cubeInterior
  rw [Finset.mem_filter, IntegerCube.mem_vertices]
  have hc := two_mul_toIntegerCube_corner_add (i + 3)
  have hs := cast_toIntegerCube_size_zero (i + 3)
  have h3 : (3 : ℤ) ^ (i + 3) = 3 * 3 ^ (i + 2) := by ring
  have h1 : (1 : ℤ) ≤ 3 ^ (i + 2) := one_le_pow₀ (by norm_num)
  have hy' := mem_square_iff_int.1 hy
  refine ⟨fun k => ?_, fun k => ?_⟩ <;>
  · have a1 := hc k
    have a2 := hy' k
    have a3 := le_abs_self (y k)
    have a4 := neg_abs_le (y k)
    generalize |y k| = b at a2 a3 a4
    constructor <;> omega

/-- A function harmonic on the interior of the lattice square `□_{i+3}` is lattice harmonic on
`□_{i+2}`. -/
theorem mem_squareHarmonic_of_cubeInterior {i : ℕ} {w : Vertex 2 → ℝ}
    (hw : ∀ x ∈ cubeInterior (⟨i + 3, 0⟩ : TriadicCube 2).toIntegerCube,
      condLaplacian (constCond fun _ => (1 : ℝ)) w x = 0) : w ∈ squareHarmonic (i + 2) := by
  intro y hy
  rw [latticeLaplacian_eq_neg_condLaplacian, hw y (mem_cubeInterior_of_mem_square hy), neg_zero]

/-- **The anchors on `□_{i+2}`**: the sum over `□_{i+2}` of a nonnegative function at the anchors
is at most `δ²` times its sum over `C_*(□_{i+3})`. -/
theorem sum_coarseAnchor_le (hP : PlanarPartitionEvent ω) {i : ℕ}
    (hres : PlanarResolved ω ⟨i + 3, 0⟩) {φ : Vertex 2 → ℝ} (hφ : ∀ z, 0 ≤ φ z) {δ : ℝ}
    (hδ : ∀ y ∈ triadicCubeFinset 2 (i + 3) 0, (3 : ℝ) ^ (planarPartCube ω y).scale ≤ δ) :
    ∑ y ∈ triadicCubeFinset 2 (i + 2) 0, φ (planarCoarseAnchor ω y) ≤
      δ ^ 2 * ∑ z ∈ clusterVertices ω ⟨i + 3, 0⟩, φ z := by
  have hsub : (triadicCubeFinset 2 (i + 2) 0).image (planarCoarseAnchor ω) ⊆
      clusterVertices ω ⟨i + 3, 0⟩ := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hz
    have hyU : y ∈ (⟨i + 3, 0⟩ : TriadicCube 2).vertices := by
      rw [mem_triadicCube_zero_iff]
      intro k
      have := (mem_square_iff_int.1 hy) k
      have h3 : (3 : ℤ) ^ (i + 2) ≤ 3 ^ (i + 3) := pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
    exact mem_clusterVertices.2 (planarAnchor_mem_planarCubeCluster hP hres hyU)
  rw [Finset.sum_comp]
  have hcount : ∀ z ∈ (triadicCubeFinset 2 (i + 2) 0).image (planarCoarseAnchor ω),
      (((triadicCubeFinset 2 (i + 2) 0).filter fun y => planarCoarseAnchor ω y = z).card : ℝ) ≤
        δ ^ 2 := by
    intro z hz
    have hzU := hsub hz
    have hzsq : z ∈ triadicCubeFinset 2 (i + 3) 0 := by
      have := mem_clusterVertices.1 hzU
      exact mem_square_iff_int.2 (mem_triadicCube_zero_iff.1 this.1)
    have hle : ((triadicCubeFinset 2 (i + 2) 0).filter fun y => planarCoarseAnchor ω y = z) ⊆
        (planarPartCube ω z).toIntegerCube.vertices := by
      intro y hy
      obtain ⟨-, hyz⟩ := Finset.mem_filter.1 hy
      have hzQ : z ∈ (planarPartCube ω y).vertices := by
        rw [← hyz]
        exact ((planarPartCube ω y).planarAnchor_spec (planarPartCube_meshed hP y).1
          (planarPartCube_large hP y)).1
      rw [TriadicCube.mem_toIntegerCube_vertices, planarPartCube_eq_of_mem hP hzQ]
      exact (planarPartCube_spec hP y).1
    have hcard := Finset.card_le_card hle
    rw [IntegerCube.card_vertices_eq] at hcard
    have h1 : (((triadicCubeFinset 2 (i + 2) 0).filter fun y =>
        planarCoarseAnchor ω y = z).card : ℝ) ≤
          (((planarPartCube ω z).toIntegerCube.size ^ 2 : ℕ) : ℝ) := by exact_mod_cast hcard
    have h2 : (((planarPartCube ω z).toIntegerCube.size ^ 2 : ℕ) : ℝ) =
        ((3 : ℝ) ^ (planarPartCube ω z).scale) ^ 2 := by
      change (((3 ^ (planarPartCube ω z).scale : ℕ) ^ 2 : ℕ) : ℝ) = _
      push_cast; rfl
    rw [h2] at h1
    exact h1.trans (pow_le_pow_left₀ (by positivity) (hδ z hzsq) 2)
  calc ∑ z ∈ (triadicCubeFinset 2 (i + 2) 0).image (planarCoarseAnchor ω),
        ((triadicCubeFinset 2 (i + 2) 0).filter fun y => planarCoarseAnchor ω y = z).card • φ z
      ≤ ∑ z ∈ (triadicCubeFinset 2 (i + 2) 0).image (planarCoarseAnchor ω), δ ^ 2 * φ z :=
        Finset.sum_le_sum fun z hz => by
          rw [nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right (hcount z hz) (hφ z)
    _ = δ ^ 2 * ∑ z ∈ (triadicCubeFinset 2 (i + 2) 0).image (planarCoarseAnchor ω), φ z :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ δ ^ 2 * ∑ z ∈ clusterVertices ω ⟨i + 3, 0⟩, φ z :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum_of_subset_of_nonneg hsub fun z _ _ => hφ z) (sq_nonneg _)

/-- **The homogenized solution at the anchors**: for `w` harmonic on the interior of `□_{i+3}`,
`i ≥ 2`, and partition cubes of scale at most `i` on `□_{i+2}`, with sides at most `δ`,
`|w(z̄(y)) - w(y)| ≤ 2 δ · 80 · 3^{-i} (Σ_{edges in □_{i+3}} |∇w|²)^{1/2}` for `y ∈ □_{i+2}`. -/
theorem abs_sub_coarseAnchor_homogenized_le (hP : PlanarPartitionEvent ω) {i : ℕ} (hi : 2 ≤ i)
    {w : Vertex 2 → ℝ}
    (hw : ∀ x ∈ cubeInterior (⟨i + 3, 0⟩ : TriadicCube 2).toIntegerCube,
      condLaplacian (constCond fun _ => (1 : ℝ)) w x = 0)
    {δ : ℝ} {y : Vertex 2} (hy : y ∈ triadicCubeFinset 2 (i + 2) 0)
    (hδ : (3 : ℝ) ^ (planarPartCube ω y).scale ≤ δ) (hsmall : (planarPartCube ω y).scale ≤ i) :
    |w (planarCoarseAnchor ω y) - w y| ≤ 2 * δ * (80 / 3 ^ i *
      √(innerEdgeEnergy (constCond fun _ => (1 : ℝ)) (⟨i + 3, 0⟩ : TriadicCube 2).toIntegerCube
        w)) := by
  set Q := planarPartCube ω y with hQ
  have hyQ : y ∈ Q.vertices := (planarPartCube_spec hP y).1
  have haQ : planarCoarseAnchor ω y ∈ Q.vertices :=
    (Q.planarAnchor_spec (planarPartCube_meshed hP y).1 (planarPartCube_large hP y)).1
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G = 80 / 3 ^ i *
      √(innerEdgeEnergy (constCond fun _ => (1 : ℝ)) (⟨i + 3, 0⟩ : TriadicCube 2).toIntegerCube
        w) := ⟨_, rfl⟩
  rw [← hG]
  have hG0 : 0 ≤ G := by rw [hG]; positivity
  have hsc : (3 : ℤ) ^ Q.scale ≤ 3 ^ i := pow_le_pow_right₀ (by norm_num) hsmall
  have hi9 : (9 : ℤ) ≤ 3 ^ i := by
    have : (3 : ℤ) ^ 2 ≤ 3 ^ i := pow_le_pow_right₀ (by norm_num) hi
    linarith
  have h32 : (3 : ℤ) ^ (i + 2) = 9 * 3 ^ i := by ring
  have hbound := abs_sub_le_of_grad_le w y (planarCoarseAnchor ω y) (G := G) fun p hp l => by
    rw [hG]
    refine abs_grad_le_of_cubeInterior hi hw (fun k => ?_) l
    have a1 := hp k
    have a2 := (mem_square_iff_int.1 hy) k
    have a3 := Q.abs_sub_center_le hyQ k
    have a4 := Q.abs_sub_center_le haQ k
    have b1 := le_abs_self (y k)
    have b2 := neg_abs_le (y k)
    have b5 := le_abs_self (y k - Q.center k)
    have b6 := neg_abs_le (y k - Q.center k)
    have b7 := le_abs_self (planarCoarseAnchor ω y k - Q.center k)
    have b8 := neg_abs_le (planarCoarseAnchor ω y k - Q.center k)
    rw [h32] at a2
    rcases abs_cases (p k) with ⟨hpk, _⟩ | ⟨hpk, _⟩ <;> rw [hpk] <;>
    generalize |y k| = c1 at a2 b1 b2 <;>
    generalize |y k - Q.center k| = c3 at a3 b5 b6
    <;> generalize |planarCoarseAnchor ω y k - Q.center k| = c4 at a4 b7 b8
    <;> generalize (3 : ℤ) ^ Q.scale = S at a3 a4 hsc
    <;> generalize (3 : ℤ) ^ i = T at hsc hi9 a2 ⊢
    <;> rcases min_cases (y k) (planarCoarseAnchor ω y k) with ⟨hm, _⟩ | ⟨hm, _⟩ <;>
    rcases max_cases (y k) (planarCoarseAnchor ω y k) with ⟨hM, _⟩ | ⟨hM, _⟩ <;>
    rw [hm, hM] at a1 <;> omega
  have hlen : (((|planarCoarseAnchor ω y 0 - y 0| + |planarCoarseAnchor ω y 1 - y 1|) : ℤ) : ℝ) ≤
      2 * (3 : ℝ) ^ Q.scale := by
    have e : ∀ k, |planarCoarseAnchor ω y k - y k| + 1 ≤ 3 ^ Q.scale := by
      intro k
      have a3 := Q.abs_sub_center_le hyQ k
      have a4 := Q.abs_sub_center_le haQ k
      have := abs_sub_le (planarCoarseAnchor ω y k) (Q.center k) (y k)
      rw [abs_sub_comm (Q.center k) (y k)] at this
      linarith
    have h0 := e 0
    have h1 := e 1
    have hZ : (|planarCoarseAnchor ω y 0 - y 0| + |planarCoarseAnchor ω y 1 - y 1| : ℤ) ≤
        2 * 3 ^ Q.scale := by linarith
    have : ((|planarCoarseAnchor ω y 0 - y 0| + |planarCoarseAnchor ω y 1 - y 1| : ℤ) : ℝ) ≤
        (((2 * 3 ^ Q.scale : ℤ)) : ℝ) := by exact_mod_cast hZ
    simpa using this
  calc |w (planarCoarseAnchor ω y) - w y|
      ≤ (((|planarCoarseAnchor ω y 0 - y 0| + |planarCoarseAnchor ω y 1 - y 1|) : ℤ) : ℝ) * G :=
        hbound
    _ ≤ 2 * (3 : ℝ) ^ Q.scale * G := mul_le_mul_of_nonneg_right hlen hG0
    _ ≤ 2 * δ * G := by gcongr

/-- **The coarsened function against the homogenized solution on `□_{i+2}`**. -/
theorem sum_sq_coarse_sub_homogenized_le (hP : PlanarPartitionEvent ω) (C : OpenComponent ω)
    (u : C → ℝ) {i : ℕ} (hi : 2 ≤ i) (hres : PlanarResolved ω ⟨i + 3, 0⟩) {w : Vertex 2 → ℝ}
    (hw : ∀ x ∈ cubeInterior (⟨i + 3, 0⟩ : TriadicCube 2).toIntegerCube,
      condLaplacian (constCond fun _ => (1 : ℝ)) w x = 0) {δ : ℝ}
    (hδ : ∀ y ∈ triadicCubeFinset 2 (i + 3) 0, (3 : ℝ) ^ (planarPartCube ω y).scale ≤ δ)
    (hsmall : ∀ y ∈ triadicCubeFinset 2 (i + 2) 0, (planarPartCube ω y).scale ≤ i) :
    ∑ y ∈ triadicCubeFinset 2 (i + 2) 0, (planarCoarse C u y - w y) ^ 2 ≤
      2 * δ ^ 2 * ∑ z ∈ clusterVertices ω ⟨i + 3, 0⟩, (Rigidity.Section3.extend C u z - w z) ^ 2 +
        2 * 9 ^ (i + 2) * (2 * δ * (80 / 3 ^ i *
          √(innerEdgeEnergy (constCond fun _ => (1 : ℝ))
            (⟨i + 3, 0⟩ : TriadicCube 2).toIntegerCube w))) ^ 2 := by
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G = 2 * δ * (80 / 3 ^ i *
      √(innerEdgeEnergy (constCond fun _ => (1 : ℝ)) (⟨i + 3, 0⟩ : TriadicCube 2).toIntegerCube
        w)) := ⟨_, rfl⟩
  rw [← hG]
  have hpt : ∀ y ∈ triadicCubeFinset 2 (i + 2) 0, (planarCoarse C u y - w y) ^ 2 ≤
      2 * (Rigidity.Section3.extend C u (planarCoarseAnchor ω y) - w (planarCoarseAnchor ω y)) ^ 2 +
        2 * G ^ 2 := by
    intro y hy
    have hyU : y ∈ triadicCubeFinset 2 (i + 3) 0 := by
      rw [mem_square_iff_int] at hy ⊢
      intro k
      have := hy k
      have h3 : (3 : ℤ) ^ (i + 2) ≤ 3 ^ (i + 3) := pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
    have hb := abs_sub_coarseAnchor_homogenized_le hP hi hw hy (hδ y hyU) (hsmall y hy)
    rw [← hG] at hb
    have hb2 : (w (planarCoarseAnchor ω y) - w y) ^ 2 ≤ G ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hb 2
    have e : planarCoarse C u y - w y =
        (Rigidity.Section3.extend C u (planarCoarseAnchor ω y) - w (planarCoarseAnchor ω y)) +
          (w (planarCoarseAnchor ω y) - w y) := by
      unfold planarCoarse; ring
    rw [e]
    nlinarith [sq_nonneg ((Rigidity.Section3.extend C u (planarCoarseAnchor ω y) -
      w (planarCoarseAnchor ω y)) - (w (planarCoarseAnchor ω y) - w y))]
  have hA := sum_coarseAnchor_le hP hres
    (φ := fun z => (Rigidity.Section3.extend C u z - w z) ^ 2) (fun z => sq_nonneg _) hδ
  calc ∑ y ∈ triadicCubeFinset 2 (i + 2) 0, (planarCoarse C u y - w y) ^ 2
      ≤ ∑ y ∈ triadicCubeFinset 2 (i + 2) 0,
          (2 * (Rigidity.Section3.extend C u (planarCoarseAnchor ω y) -
            w (planarCoarseAnchor ω y)) ^ 2 + 2 * G ^ 2) := Finset.sum_le_sum hpt
    _ = 2 * ∑ y ∈ triadicCubeFinset 2 (i + 2) 0,
          (Rigidity.Section3.extend C u (planarCoarseAnchor ω y) - w (planarCoarseAnchor ω y)) ^ 2 +
        2 * 9 ^ (i + 2) * G ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul,
          card_square_eq]
        ring
    _ ≤ 2 * (δ ^ 2 * ∑ z ∈ clusterVertices ω ⟨i + 3, 0⟩,
          (Rigidity.Section3.extend C u z - w z) ^ 2) + 2 * 9 ^ (i + 2) * G ^ 2 := by
        gcongr
    _ = _ := by ring

end Rigidity.Proofs.Regularity
