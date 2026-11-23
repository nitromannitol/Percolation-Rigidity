import Rigidity.Proofs.Dirichlet.PlanarTilePatch
import Rigidity.Proofs.Dirichlet.LemmaSixThreeCoarse

/-!
# Lemma 6.3 of Armstrong and Dario in dimension two

Let `□_m` be resolved, with all partition cubes of its vertices of scale at most `k₀ ≤ k`, and
suppose that `|ν(T, ξ) − σ|ξ|²/2| ≤ ε |ξ|²` on the triadic cubes `T ⊆ □_m` of scale `k`. Tile a
block of `□_m` by the triadic cubes of scale `k` and let `ṽ` be the patch of the maximizers of `ν`
on the tiles along the affine approximations of the homogenized solution `u_h`
(`tilePatch`). Then the hypotheses of the lattice Lemma 6.3
(`innerEdgeEnergy_patch_dirichletSolution_div_le`) hold for the cluster conductance of `□_m`:
the energy of `ṽ` on a tile is at most `σ |p|² + 2 δ`, with
`δ = |ν(T, p) − σ|p|²/2| + |p|² |(C_*(□_m) ∩ T) \ C_*(T)| / (2 |T|)`
(`innerEdgeEnergy_tilePatch_le`), and `ṽ` is affine on the faces of the tiles
(`tilePatch_eq_of_not_isInterior`). This gives the energy estimate (ii) of Lemma 6.3 of the source
on the edges inside `□_m` (`planar_lemmaSixThree`).
-/

open Finset LatticeProb LatticeHC LatticeProb.Percolation Rigidity.Percolation
open Rigidity.Proofs.Section5
open scoped Classical

namespace Rigidity.Dirichlet

variable {ω : Configuration 2}

/-- A vertex of the upper face of a tile is not interior to it. -/
theorem not_isInterior_of_mem_upperFace {k : ℕ} {z₀ : Vertex 2}
    (hz₀ : ∀ t, (3 : ℤ) ^ k ∣ z₀ t + (3 : ℤ) ^ k / 2) {i x : Vertex 2} {j : Fin 2}
    (hx : x ∈ (cornerCube (z₀ + ((3 ^ k : ℕ) : ℤ) • i) (3 ^ k)).upperFace j) :
    ¬ (gridTile k z₀ i).IsInterior x := by
  intro hint
  have h1 := (TriadicCube.add_sub_unit_mem_of_isInterior hint j).1
  rw [← TriadicCube.mem_toIntegerCube_vertices, gridTile_toIntegerCube hz₀] at h1
  obtain ⟨-, hface⟩ := (IntegerCube.mem_upperFace _ j x).1 hx
  rw [IntegerCube.mem_vertices] at h1
  have h2 := (h1 j).2
  simp only [Pi.add_apply, unit, Pi.single_eq_same, cornerCube] at h2 hface
  omega

/-- The step across the upper face of a tile lands on the lower face of the next tile, where it
is not interior. -/
theorem add_unit_mem_next_tile {k : ℕ} {z₀ : Vertex 2} {i x : Vertex 2} {j : Fin 2}
    (hx : x ∈ (cornerCube (z₀ + ((3 ^ k : ℕ) : ℤ) • i) (3 ^ k)).upperFace j) :
    x + unit j ∈ (cornerCube (z₀ + ((3 ^ k : ℕ) : ℤ) • (i + unit j)) (3 ^ k)).vertices := by
  obtain ⟨hxv, hface⟩ := (IntegerCube.mem_upperFace _ j x).1 hx
  rw [IntegerCube.mem_vertices] at hxv ⊢
  intro t
  have h := hxv t
  simp only [cornerCube, Pi.add_apply, Pi.smul_apply, smul_eq_mul, unit, Pi.single_apply]
    at h hface ⊢
  by_cases htj : t = j
  · subst htj
    simp only [if_true] at h ⊢
    constructor <;> nlinarith
  · simp only [if_neg htj, add_zero] at h ⊢
    exact h

theorem not_isInterior_next_tile {k : ℕ} {z₀ : Vertex 2}
    (hz₀ : ∀ t, (3 : ℤ) ^ k ∣ z₀ t + (3 : ℤ) ^ k / 2) {i x : Vertex 2} {j : Fin 2}
    (hx : x ∈ (cornerCube (z₀ + ((3 ^ k : ℕ) : ℤ) • i) (3 ^ k)).upperFace j) :
    ¬ (gridTile k z₀ (i + unit j)).IsInterior (x + unit j) := by
  intro hint
  have h1 := (TriadicCube.add_sub_unit_mem_of_isInterior hint j).2
  rw [add_sub_cancel_right, ← TriadicCube.mem_toIntegerCube_vertices,
    gridTile_toIntegerCube hz₀] at h1
  obtain ⟨hxv, -⟩ := (IntegerCube.mem_upperFace _ j x).1 hx
  rw [IntegerCube.mem_vertices] at h1 hxv
  have h2 := (h1 j).1
  have h3 := (hxv j).2
  simp only [cornerCube, Pi.add_apply, Pi.smul_apply, smul_eq_mul, unit, Pi.single_eq_same]
    at h2 h3
  nlinarith

/-- The error `δ` of the tile `i` in Lemma 6.3: the convergence error of `ν` on the tile and the
affine energy of the vertices of `C_*(□_m)` in the tile outside the cluster of the tile. -/
noncomputable def tileError (ω : Configuration 2) (m k : ℕ) (z₀ : Vertex 2) (σ : ℝ)
    (uh : Vertex 2 → ℝ) (i : Vertex 2) : ℝ :=
  |planarNu ω (gridTile k z₀ i) (fun j => cubeSlope (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • i) j) -
      σ * (∑ j, cubeSlope (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • i) j ^ 2) / 2| +
    (∑ j, cubeSlope (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • i) j ^ 2) *
      (((clusterVertices ω ⟨m, 0⟩).filter (fun x => x ∈ (gridTile k z₀ i).vertices) \
        clusterVertices ω (gridTile k z₀ i)).card : ℝ) / (2 * ((3 ^ k : ℕ) : ℝ) ^ 2)

theorem tileError_nonneg (ω : Configuration 2) (m k : ℕ) (z₀ : Vertex 2) (σ : ℝ)
    (uh : Vertex 2 → ℝ) (i : Vertex 2) : 0 ≤ tileError ω m k z₀ σ uh i := by
  unfold tileError
  have : 0 ≤ ∑ j, cubeSlope (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • i) j ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  positivity

/-- The volume of a tile. -/
theorem gridTile_volume (k : ℕ) (z₀ i : Vertex 2) :
    (gridTile k z₀ i).volume = ((3 ^ k : ℕ) : ℝ) ^ 2 := by
  change (9 : ℝ) ^ k = ((3 ^ k : ℕ) : ℝ) ^ 2
  push_cast
  rw [← pow_mul, mul_comm, pow_mul]
  norm_num

/-- **The energy of the patch on a tile in the form of the lattice Lemma 6.3.** -/
theorem innerEdgeEnergy_tilePatch_div_le (hP : PlanarPartitionEvent ω) {m k : ℕ}
    {z₀ : Vertex 2} (hz₀ : ∀ t, (3 : ℤ) ^ k ∣ z₀ t + (3 : ℤ) ^ k / 2) {σ : ℝ}
    (uh : Vertex 2 → ℝ) {i : Vertex 2}
    (hTU : (gridTile k z₀ i).vertices ⊆ (⟨m, 0⟩ : TriadicCube 2).vertices)
    (hres : PlanarResolved ω (gridTile k z₀ i)) :
    innerEdgeEnergy (clusterCond ω ⟨m, 0⟩) (cornerCube (z₀ + ((3 ^ k : ℕ) : ℤ) • i) (3 ^ k))
        (tilePatch ω k z₀ uh) / ((3 ^ k : ℕ) : ℝ) ^ 2 ≤
      ∑ j, σ * cubeSlope (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • i) j ^ 2 +
        2 * tileError ω m k z₀ σ uh i := by
  have h := innerEdgeEnergy_tilePatch_le hP hz₀ uh hTU hres
  rw [gridTile_volume] at h
  have hK : (0 : ℝ) < ((3 ^ k : ℕ) : ℝ) ^ 2 := by positivity
  set P2 := ∑ j, cubeSlope (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • i) j ^ 2
  set ν := planarNu ω (gridTile k z₀ i)
    (fun j => cubeSlope (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • i) j)
  set X := (((clusterVertices ω ⟨m, 0⟩).filter (fun x => x ∈ (gridTile k z₀ i).vertices) \
    clusterVertices ω (gridTile k z₀ i)).card : ℝ)
  have hsum : ∑ j, σ * cubeSlope (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • i) j ^ 2 = σ * P2 := by
    rw [← Finset.mul_sum]
  rw [hsum]
  unfold tileError
  rw [div_le_iff₀ hK]
  have habs := le_abs_self (ν - σ * P2 / 2)
  have e : 2 * (P2 * X / (2 * ((3 ^ k : ℕ) : ℝ) ^ 2)) * ((3 ^ k : ℕ) : ℝ) ^ 2 = P2 * X := by
    field_simp
  nlinarith

/-- The tiles of a block inside `shrinkCube □_m (r + 3)` are triadic cubes inside `□_m`. -/
theorem gridTile_vertices_subset_of_block {m k : ℕ} {z₀ : Vertex 2}
    (hz₀ : ∀ t, (3 : ℤ) ^ k ∣ z₀ t + (3 : ℤ) ^ k / 2) {M r : ℕ}
    (hsub : (cornerCube z₀ ((M + 1) * 3 ^ k)).vertices ⊆
      (shrinkCube (⟨m, 0⟩ : TriadicCube 2).toIntegerCube (r + 3)).vertices)
    {i : Vertex 2} (hi : i ∈ (cornerCube 0 (M + 1)).vertices) :
    (gridTile k z₀ i).vertices ⊆ (⟨m, 0⟩ : TriadicCube 2).vertices := by
  intro y hy
  rw [← TriadicCube.mem_toIntegerCube_vertices, gridTile_toIntegerCube hz₀] at hy
  have h1 := hsub (tile_subset z₀ (M + 1) hi hy)
  rw [← TriadicCube.mem_toIntegerCube_vertices]
  exact shrinkCube_vertices_subset_self _ _ h1

/-- **Armstrong and Dario, Lemma 6.3 (ii), in dimension two**, before bounding the errors of the
tiles and the `L²` distances to the affine approximations. -/
theorem planar_lemmaSixThree (hP : PlanarPartitionEvent ω) {m k : ℕ}
    (hk : ∀ x ∈ (⟨m, 0⟩ : TriadicCube 2).vertices, (planarPartCube ω x).scale ≤ k)
    {σ : ℝ} (hσ : 0 < σ) (w : Vertex 2 → ℝ) {r : ℕ} (hr : 0 < r) {z₀ : Vertex 2}
    (hz₀ : ∀ t, (3 : ℤ) ^ k ∣ z₀ t + (3 : ℤ) ^ k / 2) (M : ℕ)
    (hsub : (cornerCube z₀ ((M + 1) * 3 ^ k)).vertices ⊆
      (shrinkCube (⟨m, 0⟩ : TriadicCube 2).toIntegerCube (r + 3)).vertices)
    {D : ℕ} (hT1 : ∀ t, z₀ t ≤ (⟨m, 0⟩ : TriadicCube 2).toIntegerCube.corner t + D)
    (hT2 : ∀ t, (⟨m, 0⟩ : TriadicCube 2).toIntegerCube.corner t +
      (⟨m, 0⟩ : TriadicCube 2).toIntegerCube.size ≤ z₀ t + (M * 3 ^ k : ℕ) + D)
    {ρ : ℕ} (hρ : 0 < ρ) {γ p : ℝ} (hγ0 : 0 < γ) (hγ : γ ≤ 1 / 16) (hp : 2 < p)
    (hγp : γ * (p / (p - 2)) < 1) :
    innerEdgeEnergy (clusterCond ω ⟨m, 0⟩) (⟨m, 0⟩ : TriadicCube 2).toIntegerCube
        (patch (cubeCutoff (cornerCube z₀ (M * 3 ^ k)) ρ)
          (tilePatch ω k z₀ (dirichletSolution (constCond fun _ => σ)
            (cubeInterior (⟨m, 0⟩ : TriadicCube 2).toIntegerCube) w))
          (dirichletSolution (constCond fun _ => σ)
            (cubeInterior (⟨m, 0⟩ : TriadicCube 2).toIntegerCube) w)) /
        (((⟨m, 0⟩ : TriadicCube 2).toIntegerCube.size : ℕ) : ℝ) ^ 2 ≤
      innerEdgeEnergy (constCond fun _ => σ) (⟨m, 0⟩ : TriadicCube 2).toIntegerCube
          (dirichletSolution (constCond fun _ => σ)
            (cubeInterior (⟨m, 0⟩ : TriadicCube 2).toIntegerCube) w) /
          (((⟨m, 0⟩ : TriadicCube 2).toIntegerCube.size : ℕ) : ℝ) ^ 2 +
        (6 * ((3 ^ k : ℕ) : ℝ) ^ 2 * ∑ i ∈ (cornerCube 0 M).vertices,
            tileError ω m k z₀ σ (dirichletSolution (constCond fun _ => σ)
              (cubeInterior (⟨m, 0⟩ : TriadicCube 2).toIntegerCube) w) i +
          3 * (max σ 1 * ((2 : ℕ) * (3 * ((1 + (2 : ℕ)) * 2 ^ 2 * ((3 ^ k : ℕ) : ℝ) ^ 3 *
            (10 * (2 : ℕ) * max σ 1 / (σ * (r : ℝ) ^ 2)) + 1 / ((3 ^ k : ℕ) : ℝ)) *
              ∑ x ∈ (⟨m, 0⟩ : TriadicCube 2).toIntegerCube.vertices, ∑ j : Fin 2,
                (if x + unit j ∈ (⟨m, 0⟩ : TriadicCube 2).toIntegerCube.vertices then
                  (dirichletSolution (constCond fun _ => σ)
                    (cubeInterior (⟨m, 0⟩ : TriadicCube 2).toIntegerCube) w (x + unit j) -
                  dirichletSolution (constCond fun _ => σ)
                    (cubeInterior (⟨m, 0⟩ : TriadicCube 2).toIntegerCube) w x) ^ 2 else 0)))) +
          6 * max σ 1 * ((2 : ℕ) * (1 / (ρ : ℝ)) ^ 2) *
            (∑ i ∈ (cornerCube 0 M).vertices,
                ∑ x ∈ (cornerCube (z₀ + ((3 ^ k : ℕ) : ℤ) • i) (3 ^ k)).vertices,
                (tilePatch ω k z₀ (dirichletSolution (constCond fun _ => σ)
                    (cubeInterior (⟨m, 0⟩ : TriadicCube 2).toIntegerCube) w) x -
                  cubeAffine (3 ^ k) (dirichletSolution (constCond fun _ => σ)
                    (cubeInterior (⟨m, 0⟩ : TriadicCube 2).toIntegerCube) w)
                    (z₀ + ((3 ^ k : ℕ) : ℤ) • i) x) ^ 2 +
              ∑ i ∈ (cornerCube 0 M).vertices,
                ∑ x ∈ (cornerCube (z₀ + ((3 ^ k : ℕ) : ℤ) • i) (3 ^ k)).vertices,
                (dirichletSolution (constCond fun _ => σ)
                    (cubeInterior (⟨m, 0⟩ : TriadicCube 2).toIntegerCube) w x -
                  cubeAffine (3 ^ k) (dirichletSolution (constCond fun _ => σ)
                    (cubeInterior (⟨m, 0⟩ : TriadicCube 2).toIntegerCube) w)
                    (z₀ + ((3 ^ k : ℕ) : ℤ) • i) x) ^ 2)) /
          (((⟨m, 0⟩ : TriadicCube 2).toIntegerCube.size : ℕ) : ℝ) ^ 2 +
        (2 + 3 * max σ 1 / σ) *
          (2 * ((∑ x ∈ cubeLayer (⟨m, 0⟩ : TriadicCube 2).toIntegerCube (D + ρ + 3 ^ k + 1),
              ∑ j : Fin 2, (if x + unit j ∈ (⟨m, 0⟩ : TriadicCube 2).toIntegerCube.vertices then
                σ * (w (x + unit j) - w x) ^ 2 else 0)) /
                (((⟨m, 0⟩ : TriadicCube 2).toIntegerCube.size : ℕ) : ℝ) ^ 2) +
            88 * max σ 1 * Real.exp (γ + 4 * γ ^ 2) *
              ((2 * ((2 : ℕ) : ℝ)) ^ (p / (p - 2)) / (1 - γ * (p / (p - 2)))) ^ (1 - 2 / p) *
              ((((D + ρ + 3 ^ k : ℕ) : ℝ) + 1) /
                (⟨m, 0⟩ : TriadicCube 2).toIntegerCube.size) ^ γ *
              ((∑ x ∈ (⟨m, 0⟩ : TriadicCube 2).toIntegerCube.vertices, √(∑ j : Fin 2,
                  (if x + unit j ∈ (⟨m, 0⟩ : TriadicCube 2).toIntegerCube.vertices then
                    (w (x + unit j) - w x) ^ 2 else 0)) ^ p) /
                (((⟨m, 0⟩ : TriadicCube 2).toIntegerCube.size : ℕ) : ℝ) ^ 2) ^ (2 / p)) := by
  set Q := (⟨m, 0⟩ : TriadicCube 2).toIntegerCube
  set uh := dirichletSolution (constCond fun _ => σ) (cubeInterior Q) w
  have hL : 0 < Q.size := by change 0 < 3 ^ m; positivity
  have hK : 0 < 3 ^ k := by positivity
  have hres : ∀ i ∈ (cornerCube 0 (M + 1)).vertices, PlanarResolved ω (gridTile k z₀ i) :=
    fun i hi y hy => hk y (gridTile_vertices_subset_of_block hz₀ hsub hi hy)
  have hTU := fun i (hi : i ∈ (cornerCube 0 (M + 1)).vertices) =>
    gridTile_vertices_subset_of_block hz₀ hsub hi
  have hsub' : (cornerCube z₀ ((M + 1) * 3 ^ k)).vertices ⊆ (shrinkCube Q (r + 3)).vertices :=
    hsub
  refine innerEdgeEnergy_patch_dirichletSolution_div_le (d := 2) (by norm_num) (fun _ => σ)
    (lam := σ) (Λ := max σ 1) hσ (fun _ => ⟨le_rfl, le_max_left _ _⟩) (clusterCond ω ⟨m, 0⟩)
    (fun e => clusterCond_nonneg _ e) (fun e => (clusterCond_le_one _ e).trans (le_max_right _ _))
    Q hL w hr z₀ M hK hsub' hT1 hT2 hρ (tilePatch ω k z₀ uh) (tileError ω m k z₀ σ uh)
    (fun i => tileError_nonneg ω m k z₀ σ uh i) (fun i hi => ?_) (fun i hi j x hx hc => ?_)
    hγ0 hγ hp hγp
  · exact innerEdgeEnergy_tilePatch_div_le hP hz₀ uh (hTU i (mem_cornerCube_succ hi))
      (hres i (mem_cornerCube_succ hi))
  · have hi1 := mem_cornerCube_succ hi
    have hxT : x ∈ (cornerCube (z₀ + ((3 ^ k : ℕ) : ℤ) • i) (3 ^ k)).vertices :=
      ((IntegerCube.mem_upperFace _ j x).1 hx).1
    have hnext : i + unit j ∈ (cornerCube 0 (M + 1)).vertices := by
      rw [IntegerCube.mem_vertices] at hi ⊢
      intro t
      have h := hi t
      simp only [cornerCube, Pi.zero_apply, zero_add, Pi.add_apply, unit, Pi.single_apply] at h ⊢
      split_ifs <;> constructor <;> push_cast <;> omega
    refine ⟨tilePatch_eq_of_not_isInterior hP uh hxT (hres i hi1)
      (not_isInterior_of_mem_upperFace hz₀ hx), ?_⟩
    have h2 := tilePatch_eq_of_not_isInterior hP uh (add_unit_mem_next_tile hx) (hres _ hnext)
      (not_isInterior_next_tile hz₀ hx)
    rw [h2, smul_add, add_assoc]

end Rigidity.Dirichlet
