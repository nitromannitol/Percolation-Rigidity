/-
Copied from Lattice-High-Contrast-Homogenization (https://github.com/nitromannitol/Lattice-High-Contrast-Homogenization),
commit f47a932a9f7a07e1692bfe4aae564d02e8ca0944, file `LatticeHC/Support/WeakNorm/TorusEven.lean` (Apache License 2.0,
Copyright 2026 Ahmed Bou-Rabee and Yuval Peres).
Changes: imports `LatticeHC.*` renamed to `Rigidity.Vendor.LHCH.*`; namespace `LatticeHC` kept.
-/
import Rigidity.Vendor.LHCH.Model.Symmetry
import Rigidity.Vendor.LHCH.Support.WeakNorm.TorusNeumann

/-!
# An even solution of the Neumann problem on the torus

If `u` has period `2N`, mean zero and is invariant under every coordinate reflection, then `∇*∇ w =
u` has a periodic solution with the same invariance: symmetrize a solution one coordinate at a time,
`w ↦ (w + w ∘ r_k)/2`, since the reflections commute with `∇*∇` and with each other.
-/

open LatticeProb

noncomputable section

namespace LatticeHC

variable {d : ℕ}

/-- Reflections in two coordinates commute. -/
theorem reflectSite_comm_reflectSite (k l : Fin d) (x : Site d) :
    reflectSite k (reflectSite l x) = reflectSite l (reflectSite k x) := by
  funext i
  by_cases hk : i = k <;> by_cases hl : i = l <;> simp_all [reflectSite]

/-- The reflection of a site shifted by an integer multiple of `e_i`: the shift is reversed if
`i = k`. -/
theorem reflectSite_add_smul_unit (k i : Fin d) (n : ℤ) (x : Site d) :
    reflectSite k (x + n • unit i) =
      if i = k then reflectSite k x - n • unit i else reflectSite k x + n • unit i := by
  funext j
  by_cases hj : j = k <;> by_cases hi : i = k <;> by_cases hji : j = i <;>
    simp_all [reflectSite, unit]
  omega

/-- A function of period `2N` is also invariant under the translation by `-2N e_i`. -/
theorem isTorusPeriodic_sub_smul_unit (N : ℕ) (w : Site d → ℝ) (hw : IsTorusPeriodic N w)
    (x : Site d) (i : Fin d) : w (x - (2 * (N : ℤ)) • unit i) = w x := by
  have h := hw (x - (2 * (N : ℤ)) • unit i) i
  rw [sub_add_cancel] at h
  exact h.symm

/-- Averaging a function of period `2N` over the reflection in the coordinate `k` preserves the
period `2N`. -/
theorem isTorusPeriodic_reflect_average (N : ℕ) (k : Fin d) (w : Site d → ℝ)
    (hw : IsTorusPeriodic N w) :
    IsTorusPeriodic N (fun x => (w x + w (reflectSite k x)) / 2) := by
  intro x i
  beta_reduce
  rw [reflectSite_add_smul_unit]
  by_cases hi : i = k
  · rw [if_pos hi, hw x i, isTorusPeriodic_sub_smul_unit N w hw]
  · rw [if_neg hi, hw x i, hw (reflectSite k x) i]

/-- The discrete Laplacian of a function composed with the reflection in the coordinate `k` is the
reflection of the discrete Laplacian: the two neighbour terms in the direction `k` are swapped. -/
theorem latticeLaplacian_comp_reflectSite (k : Fin d) (w : Site d → ℝ) (x : Site d) :
    latticeLaplacian (fun y => w (reflectSite k y)) x = latticeLaplacian w (reflectSite k x) := by
  unfold latticeLaplacian
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 := reflectSite_add_smul_unit k i 1 x
  have h2 := reflectSite_add_smul_unit k i (-1) x
  simp only [one_smul, neg_smul, ← sub_eq_add_neg, sub_neg_eq_add] at h1 h2 ⊢
  by_cases hi : i = k
  · rw [if_pos hi] at h1 h2
    rw [h1, h2]
    ring
  · rw [if_neg hi] at h1 h2
    rw [h1, h2]

/-- The discrete Laplacian of the average of two functions is the average of their discrete
Laplacians. -/
theorem latticeLaplacian_average (f g : Site d → ℝ) (x : Site d) :
    latticeLaplacian (fun y => (f y + g y) / 2) x =
      (latticeLaplacian f x + latticeLaplacian g x) / 2 := by
  unfold latticeLaplacian
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Averaging a solution of `∇*∇ w = u` over the reflection in the coordinate `k` gives a solution
when `u` is invariant under that reflection. -/
theorem latticeLaplacian_reflect_average_eq (k : Fin d) (w u : Site d → ℝ)
    (hw : ∀ x, latticeLaplacian w x = u x) (hu : ∀ x, u (reflectSite k x) = u x) (x : Site d) :
    latticeLaplacian (fun y => (w y + w (reflectSite k y)) / 2) x = u x := by
  rw [latticeLaplacian_average, latticeLaplacian_comp_reflectSite, hw, hw, hu]
  ring

/-- Starting from a periodic solution of `∇*∇ w = u`, for every finite set `s` of coordinates
there is a periodic solution invariant under the reflections in the coordinates of `s`. -/
theorem exists_isTorusPeriodic_latticeLaplacian_eq_reflect_invariant (N : ℕ) (u : Site d → ℝ)
    (heven : ∀ x (k : Fin d), u (reflectSite k x) = u x) (w₀ : Site d → ℝ)
    (hp₀ : IsTorusPeriodic N w₀) (hw₀ : ∀ x, latticeLaplacian w₀ x = u x) (s : Finset (Fin d)) :
    ∃ w : Site d → ℝ, IsTorusPeriodic N w ∧ (∀ x, ∀ k ∈ s, w (reflectSite k x) = w x) ∧
      ∀ x, latticeLaplacian w x = u x := by
  induction s using Finset.induction_on with
  | empty => exact ⟨w₀, hp₀, fun x k hk => by simp at hk, hw₀⟩
  | insert a s ha ih =>
    obtain ⟨w, hp, hinv, hw⟩ := ih
    refine ⟨fun y => (w y + w (reflectSite a y)) / 2, isTorusPeriodic_reflect_average N a w hp,
      ?_, latticeLaplacian_reflect_average_eq a w u hw (fun x => heven x a)⟩
    intro x k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · simp only [reflectSite_reflectSite_eq_self]
      ring
    · beta_reduce
      rw [reflectSite_comm_reflectSite a k, hinv x k hk, hinv (reflectSite a x) k hk]

/-- **An even solution of the Neumann problem on the torus**: if `u` has period `2N`, mean zero
over the period box, and is invariant under every coordinate reflection `x_k ↦ −x_k`, then
`∇*∇ w = u` has a solution of period `2N` with the same invariance (average a solution over the
reflections, which commute with `∇*∇` and fix `u`). -/
theorem exists_even_isTorusPeriodic_latticeLaplacian_eq (N : ℕ) (hN : 0 < N) (u : Site d → ℝ)
    (hu : IsTorusPeriodic N u) (heven : ∀ x (k : Fin d), u (reflectSite k x) = u x)
    (hmean : ∑ x ∈ torusBox d N, u x = 0) :
    ∃ w : Site d → ℝ, IsTorusPeriodic N w ∧ (∀ x (k : Fin d), w (reflectSite k x) = w x) ∧
      ∀ x, latticeLaplacian w x = u x := by
  obtain ⟨w₀, hp₀, hw₀⟩ := exists_isTorusPeriodic_latticeLaplacian_eq N hN u hu hmean
  obtain ⟨w, hp, hinv, hw⟩ := exists_isTorusPeriodic_latticeLaplacian_eq_reflect_invariant N u
    heven w₀ hp₀ hw₀ Finset.univ
  exact ⟨w, hp, fun x k => hinv x k (Finset.mem_univ k), hw⟩

end LatticeHC

end
