import Rigidity.Proofs.Dirichlet.LemmaSixThreeHomogenized
import Rigidity.Proofs.Dirichlet.CubeCutoff

/-!
# The regions of a cutoff and the boundary strip

For a cutoff `η` and a finite set `U` we split `U` into the points where `η = 1` along all edges,
the points where `η = 0` along all edges, and the remaining strip. For the cube cutoff
`η = cubeCutoff T ρ` of the tiled cube `T` (ramp width `ρ`), the first and the last lie in `T`; if
`T` reaches depth `D` in every direction of `Q`, the second and the strip lie in the boundary
layer of `Q` of width `D + ρ + 2`, and the tiles meeting the strip lie in the layer of width
`D + ρ + N + 1`.

These are the regions `□_m ∖ □°`, `□° ∖ □°_int` and `□°_int` of the proof of Armstrong–Dario,
Lemma 6.3, Step 3, on the lattice.
-/

open Finset LatticeProb LatticeHC

namespace Rigidity.Dirichlet

open Rigidity.Percolation LatticeProb.Percolation

variable {d : ℕ}

/-- The points of `U` where `η = 1` along all edges. -/
noncomputable def cutoffInner (η : Vertex d → ℝ) (U : Finset (Vertex d)) : Finset (Vertex d) :=
  U.filter fun x => ∀ j : Fin d, η x = 1 ∧ η (x + unit j) = 1

/-- The points of `U` where `η = 0` along all edges. -/
noncomputable def cutoffOuter (η : Vertex d → ℝ) (U : Finset (Vertex d)) : Finset (Vertex d) :=
  U.filter fun x => ∀ j : Fin d, η x = 0 ∧ η (x + unit j) = 0

/-- The remaining points of `U`. -/
noncomputable def cutoffStrip (η : Vertex d → ℝ) (U : Finset (Vertex d)) : Finset (Vertex d) :=
  U.filter fun x => ¬(∀ j : Fin d, η x = 1 ∧ η (x + unit j) = 1) ∧
    ¬(∀ j : Fin d, η x = 0 ∧ η (x + unit j) = 0)

theorem disjoint_cutoffInner_cutoffOuter (hd : 0 < d) (η : Vertex d → ℝ)
    (U : Finset (Vertex d)) : Disjoint (cutoffInner η U) (cutoffOuter η U) := by
  refine Finset.disjoint_left.mpr fun x h1 h2 => ?_
  have e1 := ((Finset.mem_filter.mp h1).2 ⟨0, hd⟩).1
  have e0 := ((Finset.mem_filter.mp h2).2 ⟨0, hd⟩).1
  rw [e1] at e0
  exact one_ne_zero e0

theorem disjoint_union_cutoffStrip (η : Vertex d → ℝ) (U : Finset (Vertex d)) :
    Disjoint (cutoffInner η U ∪ cutoffOuter η U) (cutoffStrip η U) := by
  refine Finset.disjoint_left.mpr fun x h1 h2 => ?_
  have hs := (Finset.mem_filter.mp h2).2
  rcases Finset.mem_union.mp h1 with h | h
  · exact hs.1 (Finset.mem_filter.mp h).2
  · exact hs.2 (Finset.mem_filter.mp h).2

theorem cutoffInner_union_cutoffOuter_union_cutoffStrip (η : Vertex d → ℝ)
    (U : Finset (Vertex d)) : cutoffInner η U ∪ cutoffOuter η U ∪ cutoffStrip η U = U := by
  ext x
  simp only [cutoffInner, cutoffOuter, cutoffStrip, Finset.mem_union, Finset.mem_filter]
  tauto

/-- Outside the cube `T`, the cube cutoff of `T` vanishes. -/
theorem cubeCutoff_eq_zero_of_not_mem (T : IntegerCube d) (ρ : ℕ) {x : Vertex d}
    (hx : x ∉ T.vertices) : cubeCutoff T ρ x = 0 := by
  by_contra h
  exact hx (mem_vertices_of_cubeCutoff_ne_zero T ρ h).1

/-- **Lemma 6.3 (i) on the lattice**: off `T` the patch is the outer function. -/
theorem patch_cubeCutoff_of_not_mem (T : IntegerCube d) (ρ : ℕ) (v w : Vertex d → ℝ)
    {x : Vertex d} (hx : x ∉ T.vertices) : patch (cubeCutoff T ρ) v w x = w x :=
  patch_of_eq_zero v w (cubeCutoff_eq_zero_of_not_mem T ρ hx)

theorem cutoffInner_cubeCutoff_subset (hd : 0 < d) (T : IntegerCube d) (ρ : ℕ)
    (U : Finset (Vertex d)) : cutoffInner (cubeCutoff T ρ) U ⊆ T.vertices := by
  intro x hx
  have h1 := ((Finset.mem_filter.mp hx).2 ⟨0, hd⟩).1
  exact (mem_vertices_of_cubeCutoff_ne_zero T ρ (by rw [h1]; exact one_ne_zero)).1

theorem cutoffStrip_cubeCutoff_subset (T : IntegerCube d) (ρ : ℕ) (U : Finset (Vertex d)) :
    cutoffStrip (cubeCutoff T ρ) U ⊆ T.vertices := by
  intro x hx
  have hs := ((Finset.mem_filter.mp hx).2).2
  push Not at hs
  obtain ⟨j, hj⟩ := hs
  by_cases h0 : cubeCutoff T ρ x = 0
  · have h1 := mem_vertices_of_cubeCutoff_ne_zero T ρ (hj h0)
    have h2 := (h1.2 j).2
    rwa [add_sub_cancel_right] at h2
  · exact (mem_vertices_of_cubeCutoff_ne_zero T ρ h0).1

/-- Where the cube cutoff is not one, some coordinate is within `ρ` of the faces of `T`. -/
theorem exists_coord_of_cubeCutoff_ne_one (T : IntegerCube d) {ρ : ℕ} (hρ : 0 < ρ)
    {y : Vertex d} (hy : cubeCutoff T ρ y ≠ 1) :
    ∃ k, y k < T.corner k + ρ ∨ T.corner k + T.size < y k + ρ + 1 := by
  by_contra h
  push Not at h
  exact hy (cubeCutoff_eq_one T hρ fun k => ⟨(h k).1, (h k).2⟩)

/-- **The outer region and the strip lie in a boundary layer of `Q`.** -/
theorem cutoffOuter_union_cutoffStrip_subset_cubeLayer (hd : 0 < d) (Q T : IntegerCube d)
    {ρ : ℕ} (hρ : 0 < ρ) (D : ℕ) (hT1 : ∀ k, T.corner k ≤ Q.corner k + D)
    (hT2 : ∀ k, Q.corner k + Q.size ≤ T.corner k + T.size + D) :
    cutoffOuter (cubeCutoff T ρ) Q.vertices ∪ cutoffStrip (cubeCutoff T ρ) Q.vertices ⊆
      cubeLayer Q (D + ρ + 2) := by
  intro x hx
  have hxQ : x ∈ Q.vertices := by
    rcases Finset.mem_union.mp hx with h | h
    · exact (Finset.mem_filter.mp h).1
    · exact (Finset.mem_filter.mp h).1
  have hnot : ¬(∀ j : Fin d, cubeCutoff T ρ x = 1 ∧ cubeCutoff T ρ (x + unit j) = 1) := by
    rcases Finset.mem_union.mp hx with h | h
    · intro hall
      have e0 := ((Finset.mem_filter.mp h).2 ⟨0, hd⟩).1
      rw [(hall ⟨0, hd⟩).1] at e0
      exact one_ne_zero e0
    · exact ((Finset.mem_filter.mp h).2).1
  refine Finset.mem_filter.mpr ⟨hxQ, ?_⟩
  push Not at hnot
  obtain ⟨j, hj⟩ := hnot
  push_cast
  by_cases h1 : cubeCutoff T ρ x = 1
  · obtain ⟨k, hk⟩ := exists_coord_of_cubeCutoff_ne_one T hρ (hj h1)
    refine ⟨k, ?_⟩
    rw [add_unit_apply] at hk
    have h01 : (0 : ℤ) ≤ (if k = j then 1 else 0) ∧ (if k = j then (1 : ℤ) else 0) ≤ 1 := by
      split_ifs <;> norm_num
    have := hT1 k
    have := hT2 k
    rcases hk with hk | hk
    · left
      linarith
    · right
      linarith
  · obtain ⟨k, hk⟩ := exists_coord_of_cubeCutoff_ne_one T hρ h1
    refine ⟨k, ?_⟩
    have := hT1 k
    have := hT2 k
    rcases hk with hk | hk
    · left
      linarith
    · right
      linarith

/-- The tiles `y_i + □` with `i ∈ {0, …, M − 1}^d` lie in the tiled cube. -/
theorem tile_subset {N : ℕ} (z : Vertex d) (M : ℕ) {i : Vertex d}
    (hi : i ∈ (cornerCube 0 M).vertices) :
    (cornerCube (z + (N : ℤ) • i) N).vertices ⊆ (cornerCube z (M * N)).vertices := by
  intro x hx
  rw [IntegerCube.mem_vertices] at hi hx ⊢
  intro t
  have h1 := hi t
  have h2 := hx t
  simp only [cornerCube, Pi.zero_apply, zero_add, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul] at h1 h2 ⊢
  push_cast
  constructor
  · nlinarith
  · have : (N : ℤ) * i t + N ≤ (M : ℤ) * N := by nlinarith
    nlinarith

/-- **The tiles cover the tiled cube.** -/
theorem exists_mem_tile {N : ℕ} (hN : 0 < N) (z : Vertex d) (M : ℕ) {x : Vertex d}
    (hx : x ∈ (cornerCube z (M * N)).vertices) :
    ∃ i ∈ (cornerCube 0 M).vertices, x ∈ (cornerCube (z + (N : ℤ) • i) N).vertices := by
  classical
  have h := sum_cornerCube_mul hN z M (fun y => if y = x then (1 : ℝ) else 0)
  rw [Finset.sum_ite_eq', if_pos hx] at h
  obtain ⟨i, hi, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (h ▸ one_ne_zero)
  refine ⟨i, hi, ?_⟩
  by_contra hxi
  exact hne (Finset.sum_eq_zero fun y hy => if_neg fun hyx : y = x => hxi (hyx ▸ hy))

theorem subset_biUnion_tiles {N : ℕ} (hN : 0 < N) (z : Vertex d) (M : ℕ) :
    (cornerCube z (M * N)).vertices ⊆
      (cornerCube 0 M).vertices.biUnion fun i => (cornerCube (z + (N : ℤ) • i) N).vertices := by
  intro x hx
  obtain ⟨i, hi, hxi⟩ := exists_mem_tile hN z M hx
  exact Finset.mem_biUnion.mpr ⟨i, hi, hxi⟩

/-- The indices of the tiles meeting a set `S`. -/
noncomputable def tilesMeeting (z : Vertex d) (M N : ℕ) (S : Finset (Vertex d)) :
    Finset (Vertex d) :=
  (cornerCube 0 M).vertices.filter fun i => ∃ x ∈ S, x ∈ (cornerCube (z + (N : ℤ) • i) N).vertices

theorem tilesMeeting_subset (z : Vertex d) (M N : ℕ) (S : Finset (Vertex d)) :
    tilesMeeting z M N S ⊆ (cornerCube 0 M).vertices :=
  Finset.filter_subset _ _

theorem subset_biUnion_tilesMeeting {N : ℕ} (hN : 0 < N) (z : Vertex d) (M : ℕ)
    {S : Finset (Vertex d)} (hS : S ⊆ (cornerCube z (M * N)).vertices) :
    S ⊆ (tilesMeeting z M N S).biUnion fun i => (cornerCube (z + (N : ℤ) • i) N).vertices := by
  intro x hx
  obtain ⟨i, hi, hxi⟩ := exists_mem_tile hN z M (hS hx)
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, x, hx, hxi⟩, hxi⟩

/-- **The tiles meeting a set in a layer lie in a wider layer.** -/
theorem tilesMeeting_subset_cubeLayer {Q : IntegerCube d} {z : Vertex d} {M N : ℕ}
    (hTQ : (cornerCube z (M * N)).vertices ⊆ Q.vertices) {S : Finset (Vertex d)} {w : ℕ}
    (hS : S ⊆ cubeLayer Q w) {i : Vertex d} (hi : i ∈ tilesMeeting z M N S) :
    (cornerCube (z + (N : ℤ) • i) N).vertices ⊆ cubeLayer Q (w + N - 1) := by
  obtain ⟨hiM, s, hs, hsi⟩ := Finset.mem_filter.mp hi
  intro x hx
  refine Finset.mem_filter.mpr ⟨hTQ (tile_subset z M hiM hx), ?_⟩
  obtain ⟨_, k, hk⟩ := Finset.mem_filter.mp (hS hs)
  refine ⟨k, ?_⟩
  rw [IntegerCube.mem_vertices] at hx hsi
  have h1 := hx k
  have h2 := hsi k
  simp only [cornerCube] at h1 h2
  have hN1 : (1 : ℤ) ≤ N := by
    have : (0 : ℤ) < N := by
      rcases Nat.eq_zero_or_pos N with h0 | h0
      · subst h0
        simp at h1
        omega
      · exact_mod_cast h0
    omega
  have hcast : (((w + N - 1 : ℕ) : ℤ)) = (w : ℤ) + N - 1 := by omega
  rw [hcast]
  rcases hk with hk | hk
  · left
    linarith
  · right
    linarith

end Rigidity.Dirichlet
