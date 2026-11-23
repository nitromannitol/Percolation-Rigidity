import Rigidity.Proofs.Dirichlet.PlanarClusterTiles
import Rigidity.Proofs.Dirichlet.PlanarLemmaSixTwo
import Rigidity.Proofs.Percolation.PlanarNuDirichlet
import Rigidity.Proofs.Dirichlet.PlanarPoincareZero

/-!
# The maximizers of `ν` on the tiles, patched along the affine approximations

Fix a point `z₀` of the triadic grid of scale `k` and `K = 3^k`. Every vertex `x` lies in exactly
one tile `T(x) = z₀ + K i + □_K` (`tileIdx`). For a function `u_h` (the homogenized solution), the
tile `i` carries the slope `p_i` and the affine approximation `ℓ_i` of `u_h` on it
(`cubeSlope`, `cubeAffine`). The patched function `ṽ` is, at `x ∈ C_*(T(x))`, the maximizer of
`ν(T(x), p_i)` shifted so that it equals `ℓ_i` at the boundary vertices of `C_*(T(x))`
(Armstrong and Dario, Lemma 4.3 and (4.9), `exists_planarNu_maximizer_affine`), and `ℓ_i(x)`
elsewhere, as in the proof of Lemma 6.3 of the source. Then

* `ṽ = ℓ_i` at the vertices of the tile `i` which are not interior to it, in particular on the
  faces of the tiles (`tilePatch_eq_of_not_isInterior`), which is the face condition of the lattice
  Lemma 6.3;
* the energy of `ṽ` on the open edges of `C_*(□_m)` inside the tile is at most
  `2 |T| ν(T, p_i) + 2 |p_i|² |(C_*(□_m) ∩ T) \ C_*(T)|` (`innerEdgeEnergy_tilePatch_le`).
-/

open Finset LatticeProb LatticeHC LatticeProb.Percolation Rigidity.Percolation Rigidity.Proofs.Section5
open scoped Classical

namespace Rigidity.Dirichlet

variable {ω : Configuration 2}

/-- The index of the tile containing `x`. -/
def tileIdx (K : ℕ) (z₀ x : Vertex 2) : Vertex 2 := fun t => (x t - z₀ t) / K

theorem mem_tile_tileIdx {K : ℕ} (hK : 0 < K) (z₀ x : Vertex 2) :
    x ∈ (cornerCube (z₀ + (K : ℤ) • tileIdx K z₀ x) K).vertices := by
  rw [IntegerCube.mem_vertices]
  intro t
  have hK' : (0 : ℤ) < K := by exact_mod_cast hK
  have h1 := Int.mul_ediv_add_emod (x t - z₀ t) K
  have h2 := Int.emod_nonneg (x t - z₀ t) hK'.ne'
  have h3 := Int.emod_lt_of_pos (x t - z₀ t) hK'
  simp only [cornerCube, Pi.add_apply, Pi.smul_apply, smul_eq_mul, tileIdx]
  constructor <;> linarith

theorem tileIdx_eq_of_mem {K : ℕ} (hK : 0 < K) (z₀ : Vertex 2) {i x : Vertex 2}
    (hx : x ∈ (cornerCube (z₀ + (K : ℤ) • i) K).vertices) : tileIdx K z₀ x = i := by
  rw [IntegerCube.mem_vertices] at hx
  funext t
  have hK' : (0 : ℤ) < K := by exact_mod_cast hK
  have h := hx t
  simp only [cornerCube, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
  simp only [tileIdx]
  exact ((Int.ediv_emod_unique (a := x t - z₀ t) (r := x t - z₀ t - K * i t) (q := i t)
    hK').2 ⟨by ring, by linarith [h.1], by linarith [h.2]⟩).1

/-- The maximizer of `ν(T, p)`, with the constant of its affine boundary values, on the partition
event for a resolved cube (and `0` otherwise). -/
noncomputable def nuMax (ω : Configuration 2) (T : TriadicCube 2) (p : Fin 2 → ℝ) :
    ClusterFun ω T × ℝ :=
  if h : PlanarPartitionEvent ω ∧ PlanarResolved ω T then
    (Classical.choose (exists_planarNu_maximizer_affine h.1 h.2 p),
      Classical.choose (Classical.choose_spec (exists_planarNu_maximizer_affine h.1 h.2 p)).2.2.2)
  else (0, 0)

theorem nuMax_spec (hP : PlanarPartitionEvent ω) {T : TriadicCube 2} (hT : PlanarResolved ω T)
    (p : Fin 2 → ℝ) :
    (nuMax ω T p).1 ∈ clusterHarmonic ω T ∧
      planarNu ω T p = clusterForm ω T (nuMax ω T p).1 (nuMax ω T p).1 / 2 / T.volume ∧
      ∀ x : ↥(clusterVertices ω T), ¬ T.IsInterior x.1 →
        (nuMax ω T p).1 x = ∑ i, p i * (x.1 i : ℝ) + (nuMax ω T p).2 := by
  have h : PlanarPartitionEvent ω ∧ PlanarResolved ω T := ⟨hP, hT⟩
  unfold nuMax
  rw [dif_pos h]
  obtain ⟨hv, -, hν, hc⟩ := Classical.choose_spec (exists_planarNu_maximizer_affine h.1 h.2 p)
  exact ⟨hv, hν, Classical.choose_spec hc⟩

/-- The patch of the maximizers of `ν` on the tiles along the affine approximations of `uh`. -/
noncomputable def tilePatch (ω : Configuration 2) (k : ℕ) (z₀ : Vertex 2) (uh : Vertex 2 → ℝ)
    (x : Vertex 2) : ℝ :=
  if hx : x ∈ clusterVertices ω (gridTile k z₀ (tileIdx (3 ^ k) z₀ x)) then
    (nuMax ω (gridTile k z₀ (tileIdx (3 ^ k) z₀ x))
        (fun j => cubeSlope (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • tileIdx (3 ^ k) z₀ x) j)).1
        ⟨x, hx⟩ -
      (nuMax ω (gridTile k z₀ (tileIdx (3 ^ k) z₀ x))
        (fun j => cubeSlope (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • tileIdx (3 ^ k) z₀ x) j)).2 -
      ∑ j, cubeSlope (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • tileIdx (3 ^ k) z₀ x) j *
        ((z₀ + ((3 ^ k : ℕ) : ℤ) • tileIdx (3 ^ k) z₀ x) j : ℝ) +
      cubeAffine (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • tileIdx (3 ^ k) z₀ x)
        (z₀ + ((3 ^ k : ℕ) : ℤ) • tileIdx (3 ^ k) z₀ x)
  else cubeAffine (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • tileIdx (3 ^ k) z₀ x) x

/-- The affine approximation is affine with the slope of the cube. -/
theorem cubeAffine_eq_add (N : ℕ) (g : Vertex 2 → ℝ) (y x : Vertex 2) :
    cubeAffine N g y x = cubeAffine N g y y + ∑ j, cubeSlope N g y j * ((x j - y j : ℤ) : ℝ) := by
  simp only [cubeAffine, sub_self, Int.cast_zero, mul_zero, Finset.sum_const_zero, add_zero]

theorem cubeAffine_add_unit_sub (N : ℕ) (g : Vertex 2 → ℝ) (y x : Vertex 2) (j : Fin 2) :
    cubeAffine N g y (x + unit j) - cubeAffine N g y x = cubeSlope N g y j := by
  rw [cubeAffine_eq_add N g y (x + unit j), cubeAffine_eq_add N g y x]
  have h : ∀ i : Fin 2, ((((x + unit j) i - y i : ℤ) : ℝ)) =
      (((x i - y i : ℤ) : ℝ)) + if i = j then 1 else 0 := by
    intro i
    simp only [Pi.add_apply, unit, Pi.single_apply]
    split_ifs <;> push_cast <;> ring
  simp only [h, mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/-- **The patch is the affine approximation at the vertices of a tile not interior to it.** -/
theorem tilePatch_eq_of_not_isInterior (hP : PlanarPartitionEvent ω) {k : ℕ} {z₀ : Vertex 2}
    (uh : Vertex 2 → ℝ) {i x : Vertex 2}
    (hx : x ∈ (cornerCube (z₀ + ((3 ^ k : ℕ) : ℤ) • i) (3 ^ k)).vertices)
    (hres : PlanarResolved ω (gridTile k z₀ i))
    (hint : ¬ (gridTile k z₀ i).IsInterior x) :
    tilePatch ω k z₀ uh x = cubeAffine (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • i) x := by
  have hidx : tileIdx (3 ^ k) z₀ x = i := tileIdx_eq_of_mem (by positivity) z₀ hx
  subst hidx
  unfold tilePatch
  split_ifs with hxC
  · obtain ⟨-, -, hbd⟩ := nuMax_spec hP hres
      (fun j => cubeSlope (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • tileIdx (3 ^ k) z₀ x) j)
    rw [hbd ⟨x, hxC⟩ hint, cubeAffine_eq_add (3 ^ k) uh _ x]
    simp only [Int.cast_sub, mul_sub, Finset.sum_sub_distrib]
    ring
  · rfl

/-- On the cluster of its tile, the patch is the maximizer up to a constant. -/
theorem tilePatch_eq_of_mem (ω : Configuration 2) {k : ℕ} {z₀ : Vertex 2} (uh : Vertex 2 → ℝ)
    {i x : Vertex 2} (hx : x ∈ (cornerCube (z₀ + ((3 ^ k : ℕ) : ℤ) • i) (3 ^ k)).vertices)
    (hxC : x ∈ clusterVertices ω (gridTile k z₀ i)) :
    tilePatch ω k z₀ uh x =
      clusterExtend ω (gridTile k z₀ i)
          (nuMax ω (gridTile k z₀ i) (fun j => cubeSlope (3 ^ k) uh
            (z₀ + ((3 ^ k : ℕ) : ℤ) • i) j)).1 x -
        (nuMax ω (gridTile k z₀ i)
          (fun j => cubeSlope (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • i) j)).2 -
        ∑ j, cubeSlope (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • i) j *
          ((z₀ + ((3 ^ k : ℕ) : ℤ) • i) j : ℝ) +
        cubeAffine (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • i) (z₀ + ((3 ^ k : ℕ) : ℤ) • i) := by
  have hidx : tileIdx (3 ^ k) z₀ x = i := tileIdx_eq_of_mem (by positivity) z₀ hx
  subst hidx
  unfold tilePatch
  rw [dif_pos hxC, clusterExtend_apply_of_mem _ hxC]

/-- Off the cluster of its tile, the patch is the affine approximation. -/
theorem tilePatch_eq_of_not_mem (ω : Configuration 2) {k : ℕ} {z₀ : Vertex 2}
    (uh : Vertex 2 → ℝ) {i x : Vertex 2}
    (hx : x ∈ (cornerCube (z₀ + ((3 ^ k : ℕ) : ℤ) • i) (3 ^ k)).vertices)
    (hxC : x ∉ clusterVertices ω (gridTile k z₀ i)) :
    tilePatch ω k z₀ uh x = cubeAffine (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • i) x := by
  have hidx : tileIdx (3 ^ k) z₀ x = i := tileIdx_eq_of_mem (by positivity) z₀ hx
  subst hidx
  unfold tilePatch
  rw [dif_neg hxC]

/-- **The energy of the patch on a tile.** -/
theorem innerEdgeEnergy_tilePatch_le (hP : PlanarPartitionEvent ω) {m k : ℕ} {z₀ : Vertex 2}
    (hz₀ : ∀ t, (3 : ℤ) ^ k ∣ z₀ t + (3 : ℤ) ^ k / 2) (uh : Vertex 2 → ℝ) {i : Vertex 2}
    (hTU : (gridTile k z₀ i).vertices ⊆ (⟨m, 0⟩ : TriadicCube 2).vertices)
    (hres : PlanarResolved ω (gridTile k z₀ i)) :
    innerEdgeEnergy (clusterCond ω ⟨m, 0⟩) (cornerCube (z₀ + ((3 ^ k : ℕ) : ℤ) • i) (3 ^ k))
        (tilePatch ω k z₀ uh) ≤
      2 * (gridTile k z₀ i).volume * planarNu ω (gridTile k z₀ i)
          (fun j => cubeSlope (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • i) j) +
        (∑ j, cubeSlope (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • i) j ^ 2) *
          (((clusterVertices ω ⟨m, 0⟩).filter (fun x => x ∈ (gridTile k z₀ i).vertices) \
            clusterVertices ω (gridTile k z₀ i)).card : ℝ) := by
  set T := gridTile k z₀ i
  set Tc := cornerCube (z₀ + ((3 ^ k : ℕ) : ℤ) • i) (3 ^ k)
  have hTc : T.toIntegerCube = Tc := gridTile_toIntegerCube hz₀ i
  have hmemT : ∀ y, y ∈ Tc.vertices ↔ y ∈ T.vertices := fun y => by
    rw [← hTc, TriadicCube.mem_toIntegerCube_vertices]
  set p : Fin 2 → ℝ := fun j => cubeSlope (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • i) j
  set vm := (nuMax ω T p).1
  set ext := clusterExtend ω T vm
  set CT := clusterVertices ω T
  set CU := clusterVertices ω ⟨m, 0⟩
  set X := (CU.filter fun x => x ∈ T.vertices) \ CT
  set v := tilePatch ω k z₀ uh
  obtain ⟨hvm, hν, -⟩ := nuMax_spec hP hres p
  have hCTsub : CT ⊆ CU := clusterVertices_subset hTU
  -- the energy as a sum over the vertices of the tile
  have hE : innerEdgeEnergy (clusterCond ω ⟨m, 0⟩) Tc v =
      ∑ x ∈ Tc.vertices, ∑ j : Fin 2, (if x + unit j ∈ Tc.vertices then
        clusterCond ω ⟨m, 0⟩ (x, j) * (v (x + unit j) - v x) ^ 2 else 0) := by
    unfold innerEdgeEnergy
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_filter]
  rw [hE]
  have hterm : ∀ x ∈ Tc.vertices, ∑ j : Fin 2, (if x + unit j ∈ Tc.vertices then
      clusterCond ω ⟨m, 0⟩ (x, j) * (v (x + unit j) - v x) ^ 2 else 0) ≤
      (if x ∈ CT then ∑ j : Fin 2, (if x + unit j ∈ CT ∧ (openGraph ω).Adj x (x + unit j) then
        (ext (x + unit j) - ext x) ^ 2 else 0) else 0) +
      (if x ∈ X then ∑ j, p j ^ 2 else 0) := by
    intro x hx
    by_cases hxC : x ∈ CT
    · rw [if_pos hxC, if_neg (fun h => (Finset.mem_sdiff.1 h).2 hxC), add_zero]
      refine Finset.sum_le_sum fun j _ => ?_
      split_ifs with h1 h2
      · have hc := clusterCond_le_one (ω := ω) ⟨m, 0⟩ (x, j)
        rw [show v (x + unit j) = _ from tilePatch_eq_of_mem ω uh h1 h2.1,
          show v x = _ from tilePatch_eq_of_mem ω uh hx hxC]
        have e : ∀ a b c d : ℝ, (a - c - d + b) - (ext x - c - d + b) = a - ext x := by
          intros; ring
        rw [e]
        calc clusterCond ω ⟨m, 0⟩ (x, j) * (ext (x + unit j) - ext x) ^ 2
            ≤ 1 * (ext (x + unit j) - ext x) ^ 2 :=
              mul_le_mul_of_nonneg_right hc (sq_nonneg _)
          _ = _ := one_mul _
      · -- the edge is not an open edge of `C_*(T)`, so the conductance vanishes
        have hc : clusterCond ω ⟨m, 0⟩ (x, j) = 0 := by
          unfold clusterCond
          rw [if_neg]
          rintro ⟨-, -, hadj⟩
          exact h2 ⟨mem_clusterVertices_of_adj hP hres hxC ((hmemT _).1 h1) hadj, hadj⟩
        rw [hc, zero_mul]
      · positivity
      · positivity
    · rw [if_neg hxC, zero_add]
      by_cases hxX : x ∈ X
      · rw [if_pos hxX]
        refine Finset.sum_le_sum fun j _ => ?_
        split_ifs with h1
        · by_cases hc0 : clusterCond ω ⟨m, 0⟩ (x, j) = 0
          · rw [hc0, zero_mul]
            positivity
          · have hcl : clusterCond ω ⟨m, 0⟩ (x, j) = 1 := by
              rcases clusterCond_eq_zero_or (ω := ω) ⟨m, 0⟩ (x, j) with h | h
              · exact absurd h hc0
              · exact le_antisymm (clusterCond_le_one _ _) h
            have hadj : (openGraph ω).Adj x (x + unit j) := by
              unfold clusterCond at hcl
              split_ifs at hcl with hh
              · exact hh.2.2
              · norm_num at hcl
            have hyC : x + unit j ∉ CT := fun hy =>
              hxC (mem_clusterVertices_of_adj hP hres hy ((hmemT _).1 hx) hadj.symm)
            rw [show v (x + unit j) = _ from tilePatch_eq_of_not_mem ω uh h1 hyC,
              show v x = _ from tilePatch_eq_of_not_mem ω uh hx hxC,
              cubeAffine_add_unit_sub, hcl, one_mul]
        · positivity
      · rw [if_neg hxX]
        refine Finset.sum_nonpos fun j _ => ?_
        split_ifs with h1
        · have hc0 : clusterCond ω ⟨m, 0⟩ (x, j) = 0 := by
            unfold clusterCond
            rw [if_neg]
            rintro ⟨hxU, -, -⟩
            exact hxX (Finset.mem_sdiff.2 ⟨Finset.mem_filter.2 ⟨hxU, (hmemT x).1 hx⟩, hxC⟩)
          rw [hc0, zero_mul]
        · exact le_rfl
  have hCTc : CT ⊆ Tc.vertices := fun x hx => by
    rw [← hTc]
    exact Finset.filter_subset _ _ hx
  have hXc : X ⊆ Tc.vertices := fun x hx => by
    rw [hmemT]
    exact (Finset.mem_filter.1 (Finset.mem_sdiff.1 hx).1).2
  calc _ ≤ ∑ x ∈ Tc.vertices, ((if x ∈ CT then ∑ j : Fin 2,
          (if x + unit j ∈ CT ∧ (openGraph ω).Adj x (x + unit j) then
            (ext (x + unit j) - ext x) ^ 2 else 0) else 0) +
        (if x ∈ X then ∑ j, p j ^ 2 else 0)) := Finset.sum_le_sum hterm
    _ = ∑ x ∈ CT, ∑ j : Fin 2,
          (if x + unit j ∈ CT ∧ (openGraph ω).Adj x (x + unit j) then
            (ext (x + unit j) - ext x) ^ 2 else 0) + (∑ j, p j ^ 2) * X.card := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_ite_mem,
          Finset.inter_eq_right.mpr hCTc, Finset.inter_eq_right.mpr hXc, Finset.sum_const,
          nsmul_eq_mul, mul_comm]
    _ = 2 * T.volume * planarNu ω T p + (∑ j, p j ^ 2) * X.card := by
        congr 1
        have hvm' : (fun x : ↥CT => ext x) = vm := by
          funext x
          exact clusterExtend_apply_of_mem vm x.2
        have hcf := clusterForm_eq_sum_edges (ω := ω) T ext
        rw [hvm'] at hcf
        rw [← hcf, hν]
        have := T.volume_pos
        field_simp
        rfl

/-- The energy of an affine function on the open edges of a cluster. -/
theorem clusterForm_affine_le (T : TriadicCube 2) (p : Fin 2 → ℝ) :
    clusterForm ω T (clusterAffine ω T p) (clusterAffine ω T p) ≤
      (clusterVertices ω T).card * ∑ j, p j ^ 2 := by
  have hcf := clusterForm_eq_sum_edges (ω := ω) T (fun x => ∑ i, p i * (x i : ℝ))
  have e : (fun x : ↥(clusterVertices ω T) => (fun x : Vertex 2 => ∑ i, p i * (x i : ℝ)) x) =
      clusterAffine ω T p := rfl
  rw [e] at hcf
  rw [hcf, ← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun j _ => ?_
  split_ifs
  · have h : ∑ i, p i * ((x + unit j) i : ℝ) - ∑ i, p i * (x i : ℝ) = p j := by
      rw [← Finset.sum_sub_distrib]
      simp only [Pi.add_apply, unit, Pi.single_apply, Int.cast_add, mul_add, add_sub_cancel_left]
      simp
    rw [h]
  · positivity

/-- **The patch is close to the affine approximations in `L²` on a tile**, by the Poincaré
inequality on the cluster of the tile (`exists_planar_sum_sq_le_of_eq_zero`). -/
theorem sum_sq_tilePatch_sub_le {K₀ : ℝ} (hK₀0 : 0 ≤ K₀)
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
    (hP : PlanarPartitionEvent ω) {k k₀ : ℕ} {z₀ : Vertex 2}
    (hz₀ : ∀ t, (3 : ℤ) ^ k ∣ z₀ t + (3 : ℤ) ^ k / 2) (uh : Vertex 2 → ℝ) {i : Vertex 2}
    (hk₀ : k₀ ≤ k)
    (hscale : ∀ x ∈ (gridTile k z₀ i).parent.vertices, (planarPartCube ω x).scale ≤ k₀) :
    ∑ x ∈ (cornerCube (z₀ + ((3 ^ k : ℕ) : ℤ) • i) (3 ^ k)).vertices,
        (tilePatch ω k z₀ uh x - cubeAffine (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • i) x) ^ 2 ≤
      4 * (1 + 9 / 8 * 9 ^ k₀) * K₀ * 9 ^ (k + 1) * 81 ^ k₀ *
        (4 * 9 ^ k * ∑ j, cubeSlope (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • i) j ^ 2) := by
  set T := gridTile k z₀ i
  set Tc := cornerCube (z₀ + ((3 ^ k : ℕ) : ℤ) • i) (3 ^ k)
  have hTc : T.toIntegerCube = Tc := gridTile_toIntegerCube hz₀ i
  have hmemT : ∀ y, y ∈ Tc.vertices ↔ y ∈ T.vertices := fun y => by
    rw [← hTc, TriadicCube.mem_toIntegerCube_vertices]
  have hres : PlanarResolved ω T := fun y hy =>
    (hscale y (T.vertices_subset_parent hy)).trans hk₀
  set p : Fin 2 → ℝ := fun j => cubeSlope (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • i) j
  set ℓ := cubeAffine (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • i)
  set CT := clusterVertices ω T
  set vm := (nuMax ω T p).1
  set ext := clusterExtend ω T vm
  obtain ⟨hvm, hν, -⟩ := nuMax_spec hP hres p
  set f : Vertex 2 → ℝ := fun x => if x ∈ CT then tilePatch ω k z₀ uh x - ℓ x else 0 with hf
  have hCTc : CT ⊆ Tc.vertices := fun x hx => by
    rw [← hTc]
    exact Finset.filter_subset _ _ hx
  -- the patch minus the affine approximation is `f` on the tile
  have hsum : ∑ x ∈ Tc.vertices, (tilePatch ω k z₀ uh x - ℓ x) ^ 2 = ∑ x ∈ CT, f x ^ 2 := by
    rw [← Finset.sum_subset hCTc]
    · exact Finset.sum_congr rfl fun x hx => by rw [hf]; simp only [if_pos hx]
    · intro x hx hxC
      rw [tilePatch_eq_of_not_mem ω uh hx hxC, sub_self]
      ring
  -- `f` vanishes off the interior vertices of `C_*(T)`
  have hf0 : ∀ x, ¬(x ∈ CT ∧ T.IsInterior x) → f x = 0 := by
    intro x hx
    simp only [hf]
    split_ifs with hxC
    · have hint : ¬ T.IsInterior x := fun h => hx ⟨hxC, h⟩
      rw [tilePatch_eq_of_not_isInterior hP uh (hCTc hxC) hres hint, sub_self]
    · rfl
  have hP6 := hK₀ ω hP T k₀ (by change k₀ ≤ k; exact hk₀) hscale f hf0
  -- the energy of `f`
  have hval : ∀ x ∈ CT, f x = ext x - (nuMax ω T p).2 -
      ∑ j, p j * ((z₀ + ((3 ^ k : ℕ) : ℤ) • i) j : ℝ) + ℓ (z₀ + ((3 ^ k : ℕ) : ℤ) • i) - ℓ x := by
    intro x hx
    simp only [hf, if_pos hx]
    rw [tilePatch_eq_of_mem ω uh (hCTc hx) hx]
  have hEf : ∑ z ∈ CT, ∑ j : Fin 2,
      (if z + unit j ∈ CT ∧ (openGraph ω).Adj z (z + unit j) then (f (z + unit j) - f z) ^ 2
        else 0) ≤ 2 * clusterForm ω T vm vm + 2 * (CT.card * ∑ j, p j ^ 2) := by
    have hvm' : (fun x : ↥CT => ext x) = vm := by
      funext x
      exact clusterExtend_apply_of_mem vm x.2
    have hcf := clusterForm_eq_sum_edges (ω := ω) T ext
    rw [hvm'] at hcf
    rw [hcf]
    have hterm : ∀ z ∈ CT, ∀ j : Fin 2,
        (if z + unit j ∈ CT ∧ (openGraph ω).Adj z (z + unit j) then (f (z + unit j) - f z) ^ 2
          else 0) ≤
        2 * (if z + unit j ∈ CT ∧ (openGraph ω).Adj z (z + unit j) then
          (ext (z + unit j) - ext z) ^ 2 else 0) + 2 * p j ^ 2 := by
      intro z hz j
      split_ifs with h
      · rw [hval _ h.1, hval z hz]
        have e : ext (z + unit j) - (nuMax ω T p).2 -
            ∑ j, p j * ((z₀ + ((3 ^ k : ℕ) : ℤ) • i) j : ℝ) + ℓ (z₀ + ((3 ^ k : ℕ) : ℤ) • i) -
              ℓ (z + unit j) -
            (ext z - (nuMax ω T p).2 - ∑ j, p j * ((z₀ + ((3 ^ k : ℕ) : ℤ) • i) j : ℝ) +
              ℓ (z₀ + ((3 ^ k : ℕ) : ℤ) • i) - ℓ z) =
            (ext (z + unit j) - ext z) - p j := by
          have := cubeAffine_add_unit_sub (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • i) z j
          linarith
        rw [e]
        nlinarith [sq_nonneg (ext (z + unit j) - ext z + p j)]
      · positivity
    calc _ ≤ ∑ z ∈ CT, ∑ j : Fin 2,
          (2 * (if z + unit j ∈ CT ∧ (openGraph ω).Adj z (z + unit j) then
            (ext (z + unit j) - ext z) ^ 2 else 0) + 2 * p j ^ 2) :=
          Finset.sum_le_sum fun z hz => Finset.sum_le_sum fun j _ => hterm z hz j
      _ = _ := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
          ring
  -- the energy of the maximizer is at most that of the affine function
  have hvmE : clusterForm ω T vm vm ≤ CT.card * ∑ j, p j ^ 2 := by
    have hle := planarNu_le_of_affine_boundary (ω := ω) (U := T) p
      (w := clusterAffine ω T p) (by rw [sub_self]; exact Submodule.zero_mem _)
    have hvol := T.volume_pos
    rw [hν, div_le_div_iff_of_pos_right hvol, div_le_div_iff_of_pos_right (by norm_num)] at hle
    exact hle.trans (clusterForm_affine_le T p)
  have hCT : (CT.card : ℝ) ≤ 9 ^ k := by
    have h1 : CT.card ≤ T.toIntegerCube.vertices.card := Finset.card_le_card (Finset.filter_subset _ _)
    rw [IntegerCube.card_vertices] at h1
    have h2 : (T.toIntegerCube.size : ℝ) ^ 2 = 9 ^ k := by
      change ((3 ^ k : ℕ) : ℝ) ^ 2 = 9 ^ k
      push_cast
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    have : (CT.card : ℝ) ≤ (T.toIntegerCube.size : ℝ) ^ 2 := by exact_mod_cast h1
    linarith
  have hp0 : 0 ≤ ∑ j, p j ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hconst : 0 ≤ 4 * (1 + 9 / 8 * 9 ^ k₀) * K₀ * 9 ^ (T.scale + 1) * 81 ^ k₀ := by
    positivity
  rw [hsum]
  refine hP6.trans ?_
  change 4 * (1 + 9 / 8 * 9 ^ k₀) * K₀ * 9 ^ (k + 1) * 81 ^ k₀ * _ ≤ _
  refine mul_le_mul_of_nonneg_left ?_ hconst
  nlinarith

end Rigidity.Dirichlet
