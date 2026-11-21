/-
Copied from Lattice-High-Contrast-Homogenization (https://github.com/nitromannitol/Lattice-High-Contrast-Homogenization),
commit f47a932a9f7a07e1692bfe4aae564d02e8ca0944, file `LatticeHC/Support/AppendixA/CoarseDuality.lean` (Apache License 2.0,
Copyright 2026 Ahmed Bou-Rabee and Yuval Peres).
Changes: imports `LatticeHC.*` renamed to `Rigidity.Vendor.LHCH.*`; namespace `LatticeHC` kept.
-/
import Rigidity.Vendor.LHCH.Support.AppendixA.CoefficientUpper
import Rigidity.Vendor.LHCH.Support.AppendixA.FaceWeight
import Rigidity.Vendor.LHCH.Support.Lattice.Membership

/-!
# The mean gradient and the duality of the coarse-grained matrices

A function equal to `p · x` on the vertex boundary of a lattice cube `□` of side `L ≥ 1` has mean
gradient `𝒢_□(u) = p`. Along each line of edges in direction `j` the face weight is constant and the
gradients telescope to `p_j L`, and in each direction the face weights sum to `L^d`. Testing the
maximum defining `B_□` with the minimizer defining `A_□` then gives
`2 p · q ≤ p · A_□ p + q · B_□ q`, the nonnegativity of `𝒥(□, p, q)` in `(e:J-response)`, hence
the duality `A_□⁻¹ ⪯ B_□`.
-/

namespace LatticeHC

open LatticeProb Matrix

variable {d : ℕ}

/-- The face weight of the edge `(x + e_j, j)` is that of `(x, j)`: it depends only on the
coordinates other than `j`. -/
lemma faceWeight_add_unit (z : Site d) (L : ℕ) (x : Site d) (j : Fin d) :
    faceWeight z L (x + unit j, j) = faceWeight z L (x, j) := by
  unfold faceWeight faceCount
  congr 2
  refine Finset.filter_congr fun i _ => ?_
  by_cases hij : i = j
  · simp [hij]
  · simp only [add_unit_apply_ne hij]

/-- A sum over the edges of the cube in direction `j` is a sum over the sites `x` of the cube with
`x + e_j` in the cube. -/
lemma sum_edgesOf_filter (z : Site d) (L : ℕ) (j : Fin d) (f : Edge d → ℝ) :
    ∑ e ∈ (edgesOf z L).filter (fun e => e.2 = j), f e =
      ∑ x ∈ (latticeCube z L).filter (fun x => x + unit j ∈ latticeCube z L), f (x, j) := by
  classical
  refine Finset.sum_nbij' (fun e => e.1) (fun x => (x, j)) ?_ ?_ ?_ ?_ ?_
  · intro e he
    obtain ⟨he1, he2⟩ := Finset.mem_filter.1 he
    simp only [edgesOf, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true,
      Edge.tgt, he2] at he1
    exact Finset.mem_filter.2 he1
  · intro x hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.1 hx
    refine Finset.mem_filter.2 ⟨?_, rfl⟩
    simp only [edgesOf, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true,
      Edge.tgt]
    exact ⟨hx1, hx2⟩
  · intro e he
    have h2 : e.2 = j := (Finset.mem_filter.1 he).2
    exact Prod.ext rfl h2.symm
  · intro x _
    rfl
  · intro e he
    have h2 : e.2 = j := (Finset.mem_filter.1 he).2
    rw [← h2]

/-- Summation by parts along `e_j`: if `w` is invariant under `x ↦ x + e_j` and `h` vanishes at
every site of `C` whose `e_j`-neighbour on either side is outside `C`, then
`Σ_{x ∈ C, x + e_j ∈ C} w(x) (h(x + e_j) - h(x)) = 0`. -/
private lemma sum_weight_mul_sub_eq_zero (C : Finset (Site d)) (j : Fin d) (w h : Site d → ℝ)
    (hw : ∀ x, w (x + unit j) = w x)
    (hT : ∀ x ∈ C, x + unit j ∉ C → h x = 0) (hB : ∀ x ∈ C, x - unit j ∉ C → h x = 0) :
    ∑ x ∈ C.filter (fun x => x + unit j ∈ C), w x * (h (x + unit j) - h x) = 0 := by
  classical
  set S := C.filter (fun x => x + unit j ∈ C) with hS
  have hinj : Set.InjOn (fun x : Site d => x + unit j) (S : Set (Site d)) :=
    fun a _ b _ hab => add_right_cancel hab
  have h1 : ∑ x ∈ S, w x * h (x + unit j) = ∑ x ∈ C, w x * h x := by
    have himg : ∑ y ∈ S.image (fun x => x + unit j), w y * h y =
        ∑ x ∈ S, w x * h (x + unit j) := by
      rw [Finset.sum_image hinj]
      exact Finset.sum_congr rfl fun x _ => by rw [hw x]
    rw [← himg]
    refine Finset.sum_subset ?_ ?_
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
      exact (Finset.mem_filter.1 hx).2
    · intro y hyC hyS
      have hy : y - unit j ∉ C := fun hm => hyS (Finset.mem_image.2
        ⟨y - unit j, Finset.mem_filter.2 ⟨hm, by simpa using hyC⟩, by simp⟩)
      rw [hB y hyC hy, mul_zero]
  have h2 : ∑ x ∈ S, w x * h x = ∑ x ∈ C, w x * h x := by
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro x hxC hxS
    have hx : x + unit j ∉ C := fun hm => hxS (Finset.mem_filter.2 ⟨hxC, hm⟩)
    rw [hT x hxC hx, mul_zero]
  simp only [mul_sub, Finset.sum_sub_distrib, h1, h2, sub_self]

/-- A function equal to `p · x` on the vertex boundary has mean gradient `p`. -/
theorem cubeMeanGrad_eq_of_boundary (z : Site d) {L : ℕ} (hL : 1 ≤ L) (p : Fin d → ℝ)
    (u : Site d → ℝ) (hu : ∀ x ∈ vertexBoundary z L, u x = affine p x) :
    cubeMeanGrad z L u = p := by
  classical
  funext j
  set C := latticeCube z L with hC
  set S := C.filter (fun x => x + unit j ∈ C) with hS
  set h : Site d → ℝ := fun x => u x - affine p x with hh
  have hbdry : ∀ x ∈ C, (x + unit j ∉ C ∨ x - unit j ∉ C) → h x = 0 := fun x hx hn => by
    simp only [hh, hu x (mem_vertexBoundary_of_unit_not_mem hx j hn), sub_self]
  have hzero : ∑ x ∈ S, faceWeight z L (x, j) * (h (x + unit j) - h x) = 0 :=
    sum_weight_mul_sub_eq_zero C j (fun x => faceWeight z L (x, j)) h
      (fun x => faceWeight_add_unit z L x j) (fun x hx hn => hbdry x hx (Or.inl hn))
      (fun x hx hn => hbdry x hx (Or.inr hn))
  have hvol : ∑ x ∈ S, faceWeight z L (x, j) = (L : ℝ) ^ d := by
    rw [← sum_faceWeight_eq z hL j, sum_edgesOf_filter]
  have hpt : ∀ x, faceWeight z L (x, j) * (u (x + unit j) - u x) =
      faceWeight z L (x, j) * p j + faceWeight z L (x, j) * (h (x + unit j) - h x) := by
    intro x
    have := affine_add_unit p x j
    simp only [hh]
    linear_combination (faceWeight z L (x, j)) * this
  have hLd : ((L : ℝ) ^ d) ≠ 0 := by
    have : (0 : ℝ) < L := by exact_mod_cast hL
    positivity
  unfold cubeMeanGrad
  rw [sum_edgesOf_filter]
  simp only [Edge.tgt, Edge.src]
  rw [Finset.sum_congr rfl (fun x _ => hpt x), Finset.sum_add_distrib, hzero, add_zero,
    ← Finset.sum_mul, hvol]
  field_simp

/-- `2 p · q ≤ p · A_□ p + q · B_□ q`. -/
theorem two_mul_dotProduct_le_coarse (c : Edge d → ℝ) (z : Site d) {L : ℕ} (hL : 1 ≤ L)
    (hc : ∀ e ∈ edgesOf z L, 0 < c e) (p q : Fin d → ℝ) :
    2 * (p ⬝ᵥ q) ≤ p ⬝ᵥ (coarseA c z L hc *ᵥ p) + q ⬝ᵥ (coarseB c z L hc *ᵥ q) := by
  obtain ⟨u, hu, hE⟩ := ((coarseA_spec c z L hc).2 p).1
  have hG := cubeMeanGrad_eq_of_boundary z hL p u hu
  have hB := ((coarseB_spec c z L hc).2 q).2 ⟨u, rfl⟩
  rw [hG, ← hE, dotProduct_comm q p] at hB
  linarith

end LatticeHC
