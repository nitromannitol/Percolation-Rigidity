/-
Copied from Lattice-High-Contrast-Homogenization (https://github.com/nitromannitol/Lattice-High-Contrast-Homogenization),
commit f47a932a9f7a07e1692bfe4aae564d02e8ca0944, file `LatticeHC/Support/Lattice/Membership.lean` (Apache License 2.0,
Copyright 2026 Ahmed Bou-Rabee and Yuval Peres).
Changes: imports `LatticeHC.*` renamed to `Rigidity.Vendor.LHCH.*`; namespace `LatticeHC` kept.
-/
import Rigidity.Vendor.LHCH.Model.Coarse

/-!
# Coordinatewise membership in lattice cubes and in their edge sets

A site lies in `z + {0, …, L}^d` when each coordinate lies between `z_i` and `z_i + L`; an edge
`(x, j)` lies in that cube when, in addition, `x_j + 1 ≤ z_j + L`, equivalently when both of its
endpoints do. This module states these facts once, for every module that needs them, together with
the translation covariance of the edge set of a cube, of sums over it and of its face weights.
-/

namespace LatticeHC

open LatticeProb

noncomputable section

variable {d : ℕ}

/-- A site lies in the cube `z + {0, …, L}^d` exactly when its coordinates lie between those of `z`
and those of `z` plus `L`. -/
theorem mem_latticeCube_iff_coord (z x : Site d) (L : ℕ) :
    x ∈ latticeCube z L ↔ ∀ i, z i ≤ x i ∧ x i ≤ z i + (L : ℤ) := by
  simp only [latticeCube, qbox, Finset.mem_image, Fintype.mem_piFinset, Finset.mem_Icc]
  constructor
  · rintro ⟨w, hw, rfl⟩ i
    obtain ⟨h1, h2⟩ := hw i
    simp only [Pi.add_apply]
    constructor <;> omega
  · intro h
    refine ⟨x - z, fun i => ?_, ?_⟩
    · obtain ⟨h1, h2⟩ := h i
      simp only [Pi.sub_apply]
      constructor <;> omega
    · ext i
      simp only [Pi.add_apply, Pi.sub_apply]
      omega

/-- The coordinate `i` of `x + e_j` is `x_i + 1` if `i = j` and `x_i` otherwise. -/
theorem add_unit_apply_coord (x : Site d) (j i : Fin d) :
    (x + unit j) i = x i + if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst h; simp [unit]
  · simp [unit, h]

/-- An edge lies in the cube exactly when each of its coordinates does, the coordinate in the
direction of the edge being at most `z_j + L - 1`. -/
theorem mem_edgesOf_iff_coord (z : Site d) (L : ℕ) (e : Edge d) :
    e ∈ edgesOf z L ↔ ∀ i, (i = e.2 ∧ z i ≤ e.1 i ∧ e.1 i + 1 ≤ z i + L) ∨
      (i ≠ e.2 ∧ z i ≤ e.1 i ∧ e.1 i ≤ z i + L) := by
  simp only [edgesOf, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true,
    Edge.tgt, mem_latticeCube_iff_coord, add_unit_apply_coord]
  constructor
  · rintro ⟨h1, h2⟩ i
    have a1 := h1 i
    have a2 := h2 i
    by_cases hi : i = e.2
    · left
      subst hi
      simp only [if_true] at a2
      exact ⟨rfl, by omega⟩
    · right
      simp only [hi, if_false] at a2
      exact ⟨hi, by omega⟩
  · intro h
    refine ⟨fun i => ?_, fun i => ?_⟩
    · rcases h i with ⟨hi, h1, h2⟩ | ⟨hi, h1, h2⟩
      · subst hi
        omega
      · omega
    · rcases h i with ⟨hi, h1, h2⟩ | ⟨hi, h1, h2⟩
      · subst hi
        simp only [if_true]
        omega
      · simp only [hi, if_false]
        omega

/-- A vertex of the cube with a neighbour `x ± e_j` outside the cube lies on the vertex boundary. -/
theorem mem_vertexBoundary_of_unit_not_mem {z x : Site d} {L : ℕ} (hx : x ∈ latticeCube z L)
    (j : Fin d) (h : x + unit j ∉ latticeCube z L ∨ x - unit j ∉ latticeCube z L) :
    x ∈ vertexBoundary z L := by
  classical
  unfold vertexBoundary
  rw [Finset.mem_filter]
  refine ⟨hx, ?_⟩
  rcases h with h | h
  · exact ⟨x + unit j, Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, by simp⟩, h⟩
  · exact ⟨x - unit j, Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, by simp⟩, h⟩

/-- Moving one coordinate of a site by one step is adding the unit vector. -/
theorem update_add_unit (x : Site d) (i : Fin d) (t : ℤ) :
    Function.update x i t + unit i = Function.update x i (t + 1) := by
  funext k
  by_cases h : k = i
  · subst h; simp [unit]
  · simp [unit, h]

/-- An edge lies in a cube exactly when both of its endpoints do. -/
theorem mem_edgesOf_iff_endpoints_mem {z : Site d} {R : ℕ} {e : Edge d} :
    e ∈ edgesOf z R ↔ e.src ∈ latticeCube z R ∧ e.tgt ∈ latticeCube z R := by
  simp only [edgesOf, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true,
    Edge.src]

/-- An edge `(x, i)` lies in the cube when both its endpoints do. -/
theorem mem_edgesOf_iff (z : Site d) (L : ℕ) (x : Site d) (i : Fin d) :
    (x, i) ∈ edgesOf z L ↔ x ∈ latticeCube z L ∧ x + unit i ∈ latticeCube z L :=
  mem_edgesOf_iff_endpoints_mem

/-- A translate of an edge lies in the cube `P + (z + {0, …, L}^d)` exactly when the edge lies in
`z + {0, …, L}^d`. -/
theorem add_mem_edgesOf_add_iff (P z : Site d) (L : ℕ) (e : Edge d) :
    (P + e.1, e.2) ∈ edgesOf (P + z) L ↔ e ∈ edgesOf z L := by
  simp only [mem_edgesOf_iff_coord, Pi.add_apply]
  refine forall_congr' fun i => ?_
  constructor
  · rintro (⟨h, h1, h2⟩ | ⟨h, h1, h2⟩)
    · exact Or.inl ⟨h, by omega, by omega⟩
    · exact Or.inr ⟨h, by omega, by omega⟩
  · rintro (⟨h, h1, h2⟩ | ⟨h, h1, h2⟩)
    · exact Or.inl ⟨h, by omega, by omega⟩
    · exact Or.inr ⟨h, by omega, by omega⟩

/-- A sum over the edges of `P + z + {0, …, L}^d` is the sum over the edges of `z + {0, …, L}^d`
of the translated summand. -/
theorem sum_edgesOf_translate (P z : Site d) (L : ℕ) (f : Edge d → ℝ) :
    ∑ e ∈ edgesOf (P + z) L, f e = ∑ e ∈ edgesOf z L, f (P + e.1, e.2) := by
  refine Finset.sum_nbij' (fun e => (e.1 - P, e.2)) (fun e => (P + e.1, e.2))
    (fun e he => ?_) (fun e he => ?_) (fun e _ => by simp) (fun e _ => by simp)
    (fun e _ => by simp)
  · rw [← add_mem_edgesOf_add_iff P z L]
    simpa using he
  · exact (add_mem_edgesOf_add_iff P z L e).2 he

/-- The face weight is translation covariant: `w_{P + z + □}(P + x, j) = w_{z + □}(x, j)`. -/
theorem faceWeight_translate (P z : Site d) (L : ℕ) (e : Edge d) :
    faceWeight (P + z) L (P + e.1, e.2) = faceWeight z L e := by
  unfold faceWeight faceCount
  congr 2
  refine Finset.filter_congr fun i _ => ?_
  simp only [Pi.add_apply]
  refine and_congr_right fun _ => ?_
  omega

end

end LatticeHC
