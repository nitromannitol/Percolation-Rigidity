import Rigidity.Proofs.Dirichlet.LemmaSixThreeLattice

/-!
# The tilewise affine approximation

The tilewise affine approximation `ℓ̃(x) = ℓ_{y_i}(x)` for `x` in the tile `y_i + □`,
`y_i = z + N i`, `i = ⌊(x − z)/N⌋`, agrees with the affine approximations on the faces of the
tiles and has, on every tile, inner energy at most `N^d p(y_i) · ā p(y_i)` for the constant
conductances `ā`. So it satisfies the mesoscopic hypotheses of `edgeEnergy_patch_cubeCutoff_le`
with `δ = 0` and `ṽ − ℓ = 0`; for constant conductances (no percolation), Lemma 6.3 holds with
`ṽ = ℓ̃` (`edgeEnergy_patch_tileAffine_le`), the case in which the maximizers of `ν` are the
affine functions themselves.
-/

open Finset LatticeProb LatticeHC

namespace Rigidity.Dirichlet

open Rigidity.Percolation LatticeProb.Percolation

variable {d : ℕ}

/-- The index `⌊(x − z)/N⌋` of the tile containing `x`. -/
def tileIndex (z : Vertex d) (N : ℕ) (x : Vertex d) : Vertex d := fun k => (x k - z k) / N

theorem tileIndex_eq_of_mem {N : ℕ} (hN : 0 < N) (z : Vertex d) {i x : Vertex d}
    (hx : x ∈ (cornerCube (z + (N : ℤ) • i) N).vertices) : tileIndex z N x = i := by
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  rw [IntegerCube.mem_vertices] at hx
  funext k
  have h := hx k
  simp only [cornerCube, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
  exact ((Int.ediv_emod_unique (a := x k - z k) (r := x k - z k - N * i k) (q := i k) hN').mpr
    ⟨by ring, by linarith [h.1], by linarith [h.2]⟩).1

/-- The tilewise affine approximation of `g`. -/
noncomputable def tileAffine (N : ℕ) (g : Vertex d → ℝ) (z x : Vertex d) : ℝ :=
  cubeAffine N g (z + (N : ℤ) • tileIndex z N x) x

theorem tileAffine_eq_of_mem {N : ℕ} (hN : 0 < N) (g : Vertex d → ℝ) (z : Vertex d)
    {i x : Vertex d} (hx : x ∈ (cornerCube (z + (N : ℤ) • i) N).vertices) :
    tileAffine N g z x = cubeAffine N g (z + (N : ℤ) • i) x := by
  rw [tileAffine, tileIndex_eq_of_mem hN z hx]

/-- The affine approximation has constant discrete gradient, the mesoscopic slope. -/
theorem cubeAffine_add_unit_sub (N : ℕ) (g : Vertex d → ℝ) (y x : Vertex d) (j : Fin d) :
    cubeAffine N g y (x + unit j) - cubeAffine N g y x = cubeSlope N g y j := by
  simp only [cubeAffine, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib, add_unit_apply]
  rw [Finset.sum_eq_single j]
  · rw [if_pos rfl]
    push_cast
    ring
  · intro k _ hk
    rw [if_neg hk, add_zero, sub_self]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- Across the upper face `j` of the tile with index `i` lies the tile with index `i + e_j`. -/
theorem add_unit_mem_of_mem_upperFace {N : ℕ} (hN : 0 < N) (z : Vertex d) {i : Vertex d}
    {j : Fin d} {x : Vertex d} (hx : x ∈ (cornerCube (z + (N : ℤ) • i) N).upperFace j) :
    x + unit j ∈ (cornerCube (z + (N : ℤ) • (i + unit j)) N).lowerFace j := by
  have hxT := (IntegerCube.mem_upperFace _ j x).mp hx
  have h1 := (IntegerCube.mem_vertices _ x).mp hxT.1
  have h2 := hxT.2
  simp only [cornerCube, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2
  rw [IntegerCube.mem_lowerFace, IntegerCube.mem_vertices]
  simp only [cornerCube, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hNz : (1 : ℤ) ≤ N := by exact_mod_cast hN
  refine ⟨fun k => ?_, ?_⟩
  · by_cases hk : k = j
    · subst hk
      simp only [unit, Pi.single_eq_same]
      constructor <;> nlinarith
    · simp only [unit, Pi.single_eq_of_ne hk]
      have := h1 k
      constructor <;> nlinarith
  · simp only [unit, Pi.single_eq_same]
    linarith

/-- **The faces**: on the upper face `j` of a tile, `ℓ̃` is the affine approximation of the tile,
and across the face it is the affine approximation of the next tile. -/
theorem tileAffine_upperFace {N : ℕ} (hN : 0 < N) (g : Vertex d → ℝ) (z : Vertex d)
    {i : Vertex d} {j : Fin d} {x : Vertex d}
    (hx : x ∈ (cornerCube (z + (N : ℤ) • i) N).upperFace j) :
    tileAffine N g z x = cubeAffine N g (z + (N : ℤ) • i) x ∧
      tileAffine N g z (x + unit j) =
        cubeAffine N g (z + (N : ℤ) • i + (N : ℤ) • unit j) (x + unit j) := by
  have hxT := (IntegerCube.mem_upperFace _ j x).mp hx
  refine ⟨tileAffine_eq_of_mem hN g z hxT.1, ?_⟩
  have hmem := ((IntegerCube.mem_lowerFace _ j _).mp (add_unit_mem_of_mem_upperFace hN z hx)).1
  rw [tileAffine_eq_of_mem hN g z hmem, smul_add, add_assoc]

/-- **The face hypothesis of Lemma 6.3 from the faces of the tiles**: if `ṽ = ℓ_{y_i}` on the
upper and lower faces of every tile (`v_y ∈ ℓ_y + 𝒞₀`) and `ṽ = ℓ̃` off the tiled cube, then
`ṽ` agrees with the affine approximations across every face. -/
theorem face_of_eq_cubeAffine_on_faces {N : ℕ} (hN : 0 < N) (g : Vertex d → ℝ) (z : Vertex d)
    (M : ℕ) (v : Vertex d → ℝ)
    (hfaces : ∀ i ∈ (cornerCube 0 M).vertices, ∀ j : Fin d,
      ∀ x ∈ (cornerCube (z + (N : ℤ) • i) N).upperFace j ∪
          (cornerCube (z + (N : ℤ) • i) N).lowerFace j,
        v x = cubeAffine N g (z + (N : ℤ) • i) x)
    (hout : ∀ x, x ∉ (cornerCube z (M * N)).vertices → v x = tileAffine N g z x)
    {i : Vertex d} (hi : i ∈ (cornerCube 0 M).vertices) {j : Fin d} {x : Vertex d}
    (hx : x ∈ (cornerCube (z + (N : ℤ) • i) N).upperFace j) :
    v x = cubeAffine N g (z + (N : ℤ) • i) x ∧
      v (x + unit j) = cubeAffine N g (z + (N : ℤ) • i + (N : ℤ) • unit j) (x + unit j) := by
  refine ⟨hfaces i hi j x (Finset.mem_union_left _ hx), ?_⟩
  have hlow := add_unit_mem_of_mem_upperFace hN z hx
  have hmem := ((IntegerCube.mem_lowerFace _ j _).mp hlow).1
  by_cases hT : x + unit j ∈ (cornerCube z (M * N)).vertices
  · obtain ⟨i', hi', hxi'⟩ := exists_mem_tile hN z M hT
    have hii : i' = i + unit j :=
      (tileIndex_eq_of_mem hN z hxi').symm.trans (tileIndex_eq_of_mem hN z hmem)
    subst hii
    rw [hfaces _ hi' j _ (Finset.mem_union_right _ hlow), smul_add, add_assoc]
  · rw [hout _ hT]
    exact (tileAffine_upperFace hN g z hx).2

/-- **The tiles**: for constant conductances `a_k ≥ 0`, the inner energy of `ℓ̃` on a tile is at
most `N^d Σ_k a_k p_k(y_i)²`. -/
theorem innerEdgeEnergy_tileAffine_le (a : Fin d → ℝ) (ha : ∀ k, 0 ≤ a k) {N : ℕ} (hN : 0 < N)
    (g : Vertex d → ℝ) (z i : Vertex d) :
    innerEdgeEnergy (constCond a) (cornerCube (z + (N : ℤ) • i) N) (tileAffine N g z) ≤
      (N : ℝ) ^ d * ∑ k, a k * cubeSlope N g (z + (N : ℤ) • i) k ^ 2 := by
  set T := cornerCube (z + (N : ℤ) • i) N
  have hcard : (#T.vertices : ℝ) = (N : ℝ) ^ d := by
    rw [card_vertices]
    simp [T, cornerCube]
  rw [innerEdgeEnergy, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have hterm : ∀ x ∈ T.vertices.filter (fun x => x + unit j ∈ T.vertices),
      constCond a (x, j) * (tileAffine N g z (x + unit j) - tileAffine N g z x) ^ 2 =
        a j * cubeSlope N g (z + (N : ℤ) • i) j ^ 2 := by
    intro x hx
    obtain ⟨hxT, hxj⟩ := Finset.mem_filter.mp hx
    rw [tileAffine_eq_of_mem hN g z hxj, tileAffine_eq_of_mem hN g z hxT,
      cubeAffine_add_unit_sub]
    rfl
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  have hfil : (#(T.vertices.filter (fun x => x + unit j ∈ T.vertices)) : ℝ) ≤ (N : ℝ) ^ d := by
    rw [← hcard]
    exact_mod_cast Finset.card_filter_le _ _
  exact mul_le_mul_of_nonneg_right hfil (mul_nonneg (ha j) (sq_nonneg _))

/-- **Lemma 6.3 for constant conductances**: the patch of the tilewise affine approximation
and the homogenized solution has energy at most the homogenized energy plus the face, layer and
tile terms. -/
theorem edgeEnergy_patch_tileAffine_le (hd : 0 < d) (a : Fin d → ℝ) {lam Λ : ℝ}
    (hlam : 0 < lam) (ha : ∀ j, lam ≤ a j ∧ a j ≤ Λ) (Q : IntegerCube d)
    {u : Vertex d → ℝ} (hu : ∀ x ∈ (shrinkCube Q 1).vertices, condLaplacian (constCond a) u x = 0)
    {r : ℕ} (hr : 0 < r) (z : Vertex d) (M : ℕ) {N : ℕ} (hN : 0 < N)
    (hsub : (cornerCube z ((M + 1) * N)).vertices ⊆ (shrinkCube Q (r + 3)).vertices)
    {D : ℕ} (hT1 : ∀ k, z k ≤ Q.corner k + D)
    (hT2 : ∀ k, Q.corner k + Q.size ≤ z k + (M * N : ℕ) + D) {ρ : ℕ} (hρ : 0 < ρ) :
    edgeEnergy (constCond a) Q.vertices
        (patch (cubeCutoff (cornerCube z (M * N)) ρ) (tileAffine N u z) u) ≤
      edgeEnergy (constCond a) Q.vertices u +
        3 * (Λ * (d * (3 * ((1 + d) * 2 ^ d * (N : ℝ) ^ 3 * (10 * d * Λ / (lam * (r : ℝ) ^ 2)) +
            1 / N) * ∑ x ∈ Q.vertices, ∑ k : Fin d, (u (x + unit k) - u x) ^ 2))) +
        2 * ∑ x ∈ cubeLayer Q (D + ρ + N + 1), ∑ k : Fin d, a k * (u (x + unit k) - u x) ^ 2 +
        3 * Λ * ∑ x ∈ cubeLayer Q (D + ρ + 2), ∑ j : Fin d, (u (x + unit j) - u x) ^ 2 +
        6 * Λ * (d * (1 / (ρ : ℝ)) ^ 2) *
          ∑ i ∈ (cornerCube 0 M).vertices, ∑ x ∈ (cornerCube (z + (N : ℤ) • i) N).vertices,
            (u x - cubeAffine N u (z + (N : ℤ) • i) x) ^ 2 := by
  have ha0 : ∀ k, 0 ≤ a k := fun k => hlam.le.trans (ha k).1
  have hNd : (0 : ℝ) < (N : ℝ) ^ d := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  have h := edgeEnergy_patch_cubeCutoff_le hd a hlam ha (constCond a) (fun e => ha0 e.2)
    (fun e => (ha e.2).2) Q hu hr z M hN hsub hT1 hT2 hρ (tileAffine N u z) (fun _ => 0)
    (fun _ => le_rfl)
    (fun i _ => by
      rw [div_le_iff₀ hNd, mul_zero, add_zero, mul_comm]
      exact innerEdgeEnergy_tileAffine_le a ha0 hN u z i)
    (fun i _ j x hx _ => tileAffine_upperFace hN u z hx)
  have hX : ∑ i ∈ (cornerCube 0 M).vertices, ∑ x ∈ (cornerCube (z + (N : ℤ) • i) N).vertices,
      (tileAffine N u z x - cubeAffine N u (z + (N : ℤ) • i) x) ^ 2 = 0 :=
    Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun x hx => by
      rw [tileAffine_eq_of_mem hN u z hx, sub_self, zero_pow two_ne_zero]
  rw [hX, zero_add, Finset.sum_const_zero, mul_zero, add_zero] at h
  exact h

end Rigidity.Dirichlet
