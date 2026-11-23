import Rigidity.Proofs.Dirichlet.PlanarErrorTerms

/-!
# Sums over the tiles in Lemma 6.3

For a block of `M²` tiles of side `K = 3^k` inside `shrinkCube □_m (r + 3)`:

* the slopes of the homogenized solution on the tiles satisfy
  `Σ_i |p_i|² ≤ K⁻² Σ_{edges in □_m} |∇u_h|²` (`sum_sq_cubeSlope_tiles_le`);
* if `|ν(T, ξ) − σ|ξ|²/2| ≤ ε |ξ|²` on the tiles and all partition cubes of `□_m` have scale at
  most `k₀`, the errors of the tiles satisfy
  `Σ_i δ_i ≤ (ε + 2 (5 · 3^{k₀} + 1)/K) K⁻² Σ_{edges in □_m} |∇u_h|²` (`sum_tileError_le`);
* the `L²` distances of the patch to the affine approximations satisfy
  `Σ_i Σ_{tile} (ṽ − ℓ_i)² ≤ 4 P_T Σ_{edges in □_m} |∇u_h|²`, with `P_T` the Poincaré constant of
  the tiles (`sum_sq_tilePatch_tiles_le`).
-/

open Finset LatticeProb LatticeHC LatticeProb.Percolation Rigidity.Percolation
open Rigidity.Proofs.Section5
open scoped Classical

namespace Rigidity.Dirichlet

variable {ω : Configuration 2}

/-- **The slopes on the tiles.** -/
theorem sum_sq_cubeSlope_tiles_le (Q : IntegerCube 2) (uh : Vertex 2 → ℝ) {z : Vertex 2}
    {M N : ℕ} (hN : 0 < N)
    (hsub : (cornerCube z (M * N)).vertices ⊆ (shrinkCube Q 1).vertices) :
    ∑ i ∈ (cornerCube 0 M).vertices, ∑ j, cubeSlope N uh (z + (N : ℤ) • i) j ^ 2 ≤
      (∑ y ∈ Q.vertices, ∑ j : Fin 2,
        (if y + unit j ∈ Q.vertices then (uh (y + unit j) - uh y) ^ 2 else 0)) / (N : ℝ) ^ 2 := by
  have hV : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  have h1 : ∀ i, ∑ j, cubeSlope N uh (z + (N : ℤ) • i) j ^ 2 ≤
      ∑ j : Fin 2, (∑ y ∈ (cornerCube (z + (N : ℤ) • i) N).vertices,
        (uh (y + unit j) - uh y) ^ 2) / (N : ℝ) ^ 2 :=
    fun i => Finset.sum_le_sum fun j _ => sq_cubeSlope_le N uh _ j
  refine (Finset.sum_le_sum fun i _ => h1 i).trans ?_
  rw [Finset.sum_comm]
  simp only [← Finset.sum_div]
  refine div_le_div_of_nonneg_right ?_ hV.le
  have hblock : ∀ j : Fin 2, ∑ i ∈ (cornerCube 0 M).vertices,
      ∑ y ∈ (cornerCube (z + (N : ℤ) • i) N).vertices, (uh (y + unit j) - uh y) ^ 2 =
      ∑ y ∈ (cornerCube z (M * N)).vertices, (uh (y + unit j) - uh y) ^ 2 := fun j =>
    (sum_cornerCube_mul hN z M _).symm
  simp only [hblock]
  have hB : (cornerCube z (M * N)).vertices ⊆ Q.vertices :=
    hsub.trans (shrinkCube_vertices_subset_self Q 1)
  calc ∑ j : Fin 2, ∑ y ∈ (cornerCube z (M * N)).vertices, (uh (y + unit j) - uh y) ^ 2
      = ∑ y ∈ (cornerCube z (M * N)).vertices, ∑ j : Fin 2, (uh (y + unit j) - uh y) ^ 2 :=
        Finset.sum_comm
    _ = ∑ y ∈ (cornerCube z (M * N)).vertices, ∑ j : Fin 2,
          (if y + unit j ∈ Q.vertices then (uh (y + unit j) - uh y) ^ 2 else 0) :=
        Finset.sum_congr rfl fun y hy => Finset.sum_congr rfl fun j _ =>
          (if_pos (add_unit_mem_of_mem_shrinkCube Q le_rfl (hsub hy) j).2).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hB fun _ _ _ =>
        Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity

/-- Shrinking a cube more gives a smaller cube. -/
theorem shrinkCube_vertices_mono (Q : IntegerCube 2) {s t : ℕ} (hst : s ≤ t) :
    (shrinkCube Q t).vertices ⊆ (shrinkCube Q s).vertices := by
  intro x hx
  rw [mem_shrinkCube_iff] at hx ⊢
  intro i
  have h := hx i
  constructor <;> omega

/-- The parent of a triadic cube of `□_m` of smaller scale lies in `□_m`. -/
theorem TriadicCube.parent_vertices_subset {T U : TriadicCube 2} (hTU : T.vertices ⊆ U.vertices)
    (hs : T.scale + 1 ≤ U.scale) : T.parent.vertices ⊆ U.vertices :=
  TriadicCube.vertices_subset_of_mem_of_scale_le (T.vertices_subset_parent T.center_mem)
    (hTU T.center_mem) hs

/-- **The errors of the tiles.** -/
theorem sum_tileError_le (hP : PlanarPartitionEvent ω) {m k k₀ : ℕ}
    (hU : PlanarResolved ω ⟨m, 0⟩)
    (hk₀ : ∀ x ∈ (⟨m, 0⟩ : TriadicCube 2).vertices, (planarPartCube ω x).scale ≤ k₀)
    {σ ε : ℝ} (hε0 : 0 ≤ ε)
    (hconv : ∀ T : TriadicCube 2, T.scale = k → T.vertices ⊆ (⟨m, 0⟩ : TriadicCube 2).vertices →
      ∀ ξ : Fin 2 → ℝ, |planarNu ω T ξ - σ * (∑ j, ξ j ^ 2) / 2| ≤ ε * ∑ j, ξ j ^ 2)
    {z₀ : Vertex 2} (hz₀ : ∀ t, (3 : ℤ) ^ k ∣ z₀ t + (3 : ℤ) ^ k / 2) (uh : Vertex 2 → ℝ)
    {M r : ℕ}
    (hsub : (cornerCube z₀ ((M + 1) * 3 ^ k)).vertices ⊆
      (shrinkCube (⟨m, 0⟩ : TriadicCube 2).toIntegerCube (r + 3)).vertices) :
    ∑ i ∈ (cornerCube 0 M).vertices, tileError ω m k z₀ σ uh i ≤
      (ε + 2 * (5 * 3 ^ k₀ + 1) / ((3 ^ k : ℕ) : ℝ)) *
        ((∑ y ∈ (⟨m, 0⟩ : TriadicCube 2).toIntegerCube.vertices, ∑ j : Fin 2,
          (if y + unit j ∈ (⟨m, 0⟩ : TriadicCube 2).toIntegerCube.vertices then
            (uh (y + unit j) - uh y) ^ 2 else 0)) / ((3 ^ k : ℕ) : ℝ) ^ 2) := by
  set Q := (⟨m, 0⟩ : TriadicCube 2).toIntegerCube
  have hK : (0 : ℝ) < ((3 ^ k : ℕ) : ℝ) := by positivity
  have hpt : ∀ i ∈ (cornerCube 0 M).vertices, tileError ω m k z₀ σ uh i ≤
      (ε + 2 * (5 * 3 ^ k₀ + 1) / ((3 ^ k : ℕ) : ℝ)) *
        ∑ j, cubeSlope (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • i) j ^ 2 := by
    intro i hi
    have hTU := gridTile_vertices_subset_of_block hz₀ hsub (mem_cornerCube_succ hi)
    have hX := card_sdiff_clusterVertices_le (T := gridTile k z₀ i) hP hU hk₀
    have hν := hconv _ rfl hTU (fun j => cubeSlope (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • i) j)
    unfold tileError
    set P2 := ∑ j, cubeSlope (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • i) j ^ 2
    have hP2 : 0 ≤ P2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    set X := (((clusterVertices ω ⟨m, 0⟩).filter (fun x => x ∈ (gridTile k z₀ i).vertices) \
      clusterVertices ω (gridTile k z₀ i)).card : ℝ)
    have hscale : (gridTile k z₀ i).scale = k := rfl
    rw [hscale] at hX
    have h2 : P2 * X / (2 * ((3 ^ k : ℕ) : ℝ) ^ 2) ≤
        2 * (5 * 3 ^ k₀ + 1) / ((3 ^ k : ℕ) : ℝ) * P2 := by
      rw [div_le_iff₀ (by positivity)]
      have : P2 * X ≤ P2 * (2 * 2 * ((5 * 3 ^ k₀ + 1 : ℕ) : ℝ) * ((3 ^ k : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hX hP2
      have e : 2 * (5 * 3 ^ k₀ + 1) / ((3 ^ k : ℕ) : ℝ) * P2 * (2 * ((3 ^ k : ℕ) : ℝ) ^ 2) =
          P2 * (2 * 2 * ((5 * 3 ^ k₀ + 1 : ℕ) : ℝ) * ((3 ^ k : ℕ) : ℝ)) := by
        push_cast
        field_simp
      linarith
    linarith
  have hslope := sum_sq_cubeSlope_tiles_le Q uh (z := z₀) (M := M) (N := 3 ^ k) (by positivity)
    (fun x hx => shrinkCube_vertices_mono Q (show 1 ≤ r + 3 by omega)
      (hsub (cornerCube_mul_subset_succ z₀ M (3 ^ k) hx)))
  calc _ ≤ ∑ i ∈ (cornerCube 0 M).vertices, (ε + 2 * (5 * 3 ^ k₀ + 1) / ((3 ^ k : ℕ) : ℝ)) *
        ∑ j, cubeSlope (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • i) j ^ 2 := Finset.sum_le_sum hpt
    _ = _ := by rw [← Finset.mul_sum]
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left ?_ ?_
        · exact_mod_cast hslope
        · positivity

/-- **The `L²` distances of the patch to the affine approximations on the tiles.** -/
theorem sum_sq_tilePatch_tiles_le {K₀ : ℝ} (hK₀0 : 0 ≤ K₀)
    (hK₀ : ∀ (ω : Configuration 2), PlanarPartitionEvent ω → ∀ (U : TriadicCube 2)
      (k : ℕ), k ≤ U.scale →
      (∀ x ∈ U.parent.vertices, (planarPartCube ω x).scale ≤ k) →
      ∀ f : Vertex 2 → ℝ,
      (∀ x, ¬(x ∈ clusterVertices ω U ∧ U.IsInterior x) → f x = 0) →
      ∑ x ∈ clusterVertices ω U, f x ^ 2 ≤
        4 * (1 + 9 / 8 * 9 ^ k) * K₀ * 9 ^ (U.scale + 1) * 81 ^ k *
          ∑ z ∈ clusterVertices ω U, ∑ j : Fin 2,
            (if z + unit j ∈ clusterVertices ω U ∧ (openGraph ω).Adj z (z + unit j) then
              (f (z + unit j) - f z) ^ 2 else 0))
    (hP : PlanarPartitionEvent ω) {m k k₀ : ℕ} (hk₀k : k₀ ≤ k) (hkm : k + 1 ≤ m)
    (hk₀ : ∀ x ∈ (⟨m, 0⟩ : TriadicCube 2).vertices, (planarPartCube ω x).scale ≤ k₀)
    {z₀ : Vertex 2} (hz₀ : ∀ t, (3 : ℤ) ^ k ∣ z₀ t + (3 : ℤ) ^ k / 2) (uh : Vertex 2 → ℝ)
    {M r : ℕ}
    (hsub : (cornerCube z₀ ((M + 1) * 3 ^ k)).vertices ⊆
      (shrinkCube (⟨m, 0⟩ : TriadicCube 2).toIntegerCube (r + 3)).vertices) :
    ∑ i ∈ (cornerCube 0 M).vertices,
        ∑ x ∈ (cornerCube (z₀ + ((3 ^ k : ℕ) : ℤ) • i) (3 ^ k)).vertices,
          (tilePatch ω k z₀ uh x - cubeAffine (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • i) x) ^ 2 ≤
      4 * (1 + 9 / 8 * 9 ^ k₀) * K₀ * 9 ^ (k + 1) * 81 ^ k₀ *
        (4 * ∑ y ∈ (⟨m, 0⟩ : TriadicCube 2).toIntegerCube.vertices, ∑ j : Fin 2,
          (if y + unit j ∈ (⟨m, 0⟩ : TriadicCube 2).toIntegerCube.vertices then
            (uh (y + unit j) - uh y) ^ 2 else 0)) := by
  set Q := (⟨m, 0⟩ : TriadicCube 2).toIntegerCube
  set PT := 4 * (1 + 9 / 8 * 9 ^ k₀) * K₀ * 9 ^ (k + 1) * 81 ^ k₀
  have hPT : 0 ≤ PT := by positivity
  have hpt : ∀ i ∈ (cornerCube 0 M).vertices,
      ∑ x ∈ (cornerCube (z₀ + ((3 ^ k : ℕ) : ℤ) • i) (3 ^ k)).vertices,
        (tilePatch ω k z₀ uh x - cubeAffine (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • i) x) ^ 2 ≤
      PT * (4 * 9 ^ k * ∑ j, cubeSlope (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • i) j ^ 2) := by
    intro i hi
    have hTU := gridTile_vertices_subset_of_block hz₀ hsub (mem_cornerCube_succ hi)
    have hpar := TriadicCube.parent_vertices_subset hTU (by change k + 1 ≤ m; exact hkm)
    exact sum_sq_tilePatch_sub_le hK₀0 hK₀ hP hz₀ uh hk₀k fun x hx => hk₀ x (hpar hx)
  have hslope := sum_sq_cubeSlope_tiles_le Q uh (z := z₀) (M := M) (N := 3 ^ k) (by positivity)
    (fun x hx => shrinkCube_vertices_mono Q (show 1 ≤ r + 3 by omega)
      (hsub (cornerCube_mul_subset_succ z₀ M (3 ^ k) hx)))
  have hK2 : ((3 ^ k : ℕ) : ℝ) ^ 2 = 9 ^ k := by
    push_cast
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [hK2] at hslope
  calc _ ≤ ∑ i ∈ (cornerCube 0 M).vertices,
        PT * (4 * 9 ^ k * ∑ j, cubeSlope (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • i) j ^ 2) :=
        Finset.sum_le_sum hpt
    _ = PT * (4 * 9 ^ k * ∑ i ∈ (cornerCube 0 M).vertices,
          ∑ j, cubeSlope (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • i) j ^ 2) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ PT * (4 * 9 ^ k * ((∑ y ∈ Q.vertices, ∑ j : Fin 2,
          (if y + unit j ∈ Q.vertices then (uh (y + unit j) - uh y) ^ 2 else 0)) / 9 ^ k)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) hPT
        exact_mod_cast hslope
    _ = _ := by
        congr 1
        field_simp

end Rigidity.Dirichlet
