/-
Copied from Lattice-High-Contrast-Homogenization (https://github.com/nitromannitol/Lattice-High-Contrast-Homogenization),
commit f47a932a9f7a07e1692bfe4aae564d02e8ca0944, file `LatticeHC/Support/Lattice/Subdivision.lean` (Apache License 2.0,
Copyright 2026 Ahmed Bou-Rabee and Yuval Peres).
Changes: imports `LatticeHC.*` renamed to `Rigidity.Vendor.LHCH.*`; namespace `LatticeHC` kept.
-/
import Rigidity.Vendor.LHCH.Support.Lattice.Membership

/-!
# Weighted edge sums under subdivision of a lattice cube

The cube `Z + {0, …, mN}^d` is the union of its children `Z + m y + {0, …, m}^d`, and since face
weights add under subdivision, the face-weighted sum of an edge function over the cube is the sum
over the children of their face-weighted sums. This is the translation-general, public form of the
identity behind (e:matrix-sandwich).
-/

open LatticeProb

noncomputable section

namespace LatticeHC

variable {d : ℕ}

/-- The coordinate-`i` factor of the indicator of `edgesOf z L` times the face weight, for an edge
in direction `j` whose `i`-th coordinate is `t`, and a cube whose `i`-th corner is `a`: it is `0`
off the cube, and inside it is `1/2` if `i ≠ j` and `t` is a boundary value `a` or `a + L`, else
`1`. -/
private noncomputable def subdivisionEdgeFactor (L : ℕ) (j i : Fin d) (a t : ℤ) : ℝ :=
  if (i = j ∧ a ≤ t ∧ t + 1 ≤ a + L) ∨ (i ≠ j ∧ a ≤ t ∧ t ≤ a + L) then
    (if i ≠ j ∧ (t = a ∨ t = a + L) then 1 / 2 else 1) else 0

/-- The face weight is a product over the coordinates. -/
lemma faceWeight_eq_prod_ite (z : Site d) (L : ℕ) (e : Edge d) :
    faceWeight z L e = ∏ i, if i ≠ e.2 ∧ (e.1 i = z i ∨ e.1 i = z i + (L : ℤ)) then
      (1 / 2 : ℝ) else 1 := by
  classical
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one, faceWeight, faceCount]

/-- The indicator of an edge of the cube times its face weight is a product over coordinates. -/
private lemma ite_mem_edgesOf_faceWeight_eq_prod (z : Site d) (L : ℕ) (e : Edge d) :
    (open Classical in if e ∈ edgesOf z L then faceWeight z L e else 0) =
      ∏ i, subdivisionEdgeFactor L e.2 i (z i) (e.1 i) := by
  classical
  unfold subdivisionEdgeFactor
  rw [Fintype.prod_ite_zero, faceWeight_eq_prod_ite]
  simp only [← mem_edgesOf_iff_coord]

/-- The coordinate factors add under subdivision: the children of a cube with corner `a` and side
`m N` have corners `a + m s`, `s < N`, and side `m`. -/
private lemma sum_subdivisionEdgeFactor (m : ℕ) (hm : 1 ≤ m) (j i : Fin d) (a t : ℤ) (N : ℕ)
    (hN : 1 ≤ N) :
    ∑ s ∈ Finset.range N, subdivisionEdgeFactor m j i (a + (m : ℤ) * s) t =
      subdivisionEdgeFactor (m * N) j i a t := by
  induction N, hN using Nat.le_induction with
  | base => simp [subdivisionEdgeFactor]
  | succ N hN ih =>
    rw [Finset.sum_range_succ, ih]
    have e1 : ((m * (N + 1) : ℕ) : ℤ) = (m : ℤ) * N + m := by push_cast; ring
    have e2 : ((m * N : ℕ) : ℤ) = (m : ℤ) * N := by push_cast; ring
    have hmN : (1 : ℤ) ≤ (m : ℤ) * N := by
      have : (1 : ℤ) ≤ m := by exact_mod_cast hm
      have : (1 : ℤ) ≤ N := by exact_mod_cast hN
      nlinarith
    have hm' : (1 : ℤ) ≤ m := by exact_mod_cast hm
    unfold subdivisionEdgeFactor
    rw [e1, e2]
    generalize (m : ℤ) * N = MN at *
    by_cases hij : i = j <;> simp only [hij, true_and, ne_eq, not_true_eq_false, false_and,
      or_false, not_false_eq_true, false_or] <;>
      split_ifs <;> first | (exfalso; omega) | norm_num

open Classical in
/-- The face weights add under subdivision, edge by edge. -/
private lemma sum_ite_mem_edgesOf_children (Z : Site d) (m N : ℕ) (hm : 1 ≤ m) (hN : 1 ≤ N)
    (e : Edge d) :
    ∑ y ∈ Fintype.piFinset fun _ : Fin d => Finset.range N,
      (if e ∈ edgesOf (Z + fun i => (m : ℤ) * (y i : ℤ)) m then
        faceWeight (Z + fun i => (m : ℤ) * (y i : ℤ)) m e else 0) =
    if e ∈ edgesOf Z (m * N) then faceWeight Z (m * N) e else 0 := by
  simp only [ite_mem_edgesOf_faceWeight_eq_prod, Pi.add_apply]
  rw [Finset.sum_prod_piFinset (Finset.range N)
    (fun i s => subdivisionEdgeFactor m e.2 i (Z i + (m : ℤ) * s) (e.1 i))]
  exact Finset.prod_congr rfl fun i _ => sum_subdivisionEdgeFactor m hm e.2 i (Z i) (e.1 i) N hN

/-- A child `Z + m y + {0, …, m}^d`, `y ∈ {0, …, N - 1}^d`, of `Z + {0, …, m N}^d` lies in it. -/
lemma latticeCube_subdivision_child_subset (Z : Site d) (m N : ℕ) {y : Fin d → ℕ}
    (hy : y ∈ Fintype.piFinset fun _ : Fin d => Finset.range N) :
    latticeCube (Z + fun i => (m : ℤ) * (y i : ℤ)) m ⊆ latticeCube Z (m * N) := by
  intro x hx
  rw [mem_latticeCube_iff_coord] at hx ⊢
  intro i
  have hyi : y i < N := Finset.mem_range.1 (Fintype.mem_piFinset.1 hy i)
  have h1 : (y i : ℤ) + 1 ≤ N := by exact_mod_cast hyi
  have h2 : (m : ℤ) * (y i + 1) ≤ m * N := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg m)
  have h3 : (0 : ℤ) ≤ m * y i := mul_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg _)
  obtain ⟨a, b⟩ := hx i
  simp only [Pi.add_apply] at a b
  push_cast
  constructor <;> nlinarith

/-- The edges of a child cube are edges of the big cube. -/
lemma edgesOf_subdivision_child_subset (Z : Site d) (m N : ℕ) {y : Fin d → ℕ}
    (hy : y ∈ Fintype.piFinset fun _ : Fin d => Finset.range N) :
    edgesOf (Z + fun i => (m : ℤ) * (y i : ℤ)) m ⊆ edgesOf Z (m * N) := by
  intro e he
  simp only [edgesOf, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at he ⊢
  exact ⟨latticeCube_subdivision_child_subset Z m N hy he.1,
    latticeCube_subdivision_child_subset Z m N hy he.2⟩

/-- **Weighted edge sums add under subdivision.** The cube `Z + {0, …, mN}^d` is the union of its
children `Z + m y + {0, …, m}^d`, `y ∈ {0, …, N − 1}^d`, and since the face weights add,
`Σ_{e ⊂ □} w_□(e) f(e)` is the sum over the children of `Σ_{e ⊂ child} w_child(e) f(e)`. -/
theorem sum_weighted_edgesOf_children (Z : Site d) (m N : ℕ) (hm : 1 ≤ m) (hN : 1 ≤ N)
    (f : Edge d → ℝ) :
    ∑ e ∈ edgesOf Z (m * N), faceWeight Z (m * N) e * f e =
      ∑ y ∈ Fintype.piFinset (fun _ : Fin d => Finset.range N),
        ∑ e ∈ edgesOf (Z + fun i => (m : ℤ) * (y i : ℤ)) m,
          faceWeight (Z + fun i => (m : ℤ) * (y i : ℤ)) m e * f e := by
  classical
  have h1 : ∀ y ∈ Fintype.piFinset fun _ : Fin d => Finset.range N,
      ∑ e ∈ edgesOf (Z + fun i => (m : ℤ) * (y i : ℤ)) m,
          faceWeight (Z + fun i => (m : ℤ) * (y i : ℤ)) m e * f e =
        ∑ e ∈ edgesOf Z (m * N),
          (if e ∈ edgesOf (Z + fun i => (m : ℤ) * (y i : ℤ)) m then
            faceWeight (Z + fun i => (m : ℤ) * (y i : ℤ)) m e else 0) * f e := by
    intro y hy
    simp only [ite_mul, zero_mul]
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 (edgesOf_subdivision_child_subset Z m N hy)]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [← Finset.sum_mul, sum_ite_mem_edgesOf_children Z m N hm hN e, if_pos he]

/-- Every integer point of `[0, m N]` lies in one of the intervals `[m s, m s + m]` with `s < N`. -/
theorem exists_block_index_of_le_mul (m N : ℕ) (hN : 1 ≤ N) (t : ℤ) (h0 : 0 ≤ t)
    (h1 : t ≤ (m : ℤ) * N) : ∃ s : ℕ, s < N ∧ (m : ℤ) * s ≤ t ∧ t ≤ (m : ℤ) * s + m := by
  induction N, hN using Nat.le_induction with
  | base => exact ⟨0, by omega, by simpa using h0, by simpa using h1⟩
  | succ N hN ih =>
    by_cases ht : t ≤ (m : ℤ) * N
    · obtain ⟨s, hs, h2, h3⟩ := ih ht
      exact ⟨s, by omega, h2, h3⟩
    · have e1 : (m : ℤ) * ((N + 1 : ℕ) : ℤ) = (m : ℤ) * N + m := by push_cast; ring
      rw [e1] at h1
      exact ⟨N, by omega, by omega, by omega⟩

/-- Every site of the cube `Z + {0, …, m N}^d` lies in a child cube `Z + m y + {0, …, m}^d` with
`y ∈ {0, …, N - 1}^d`. -/
theorem exists_subdivision_child_of_mem_latticeCube (Z : Site d) (m N : ℕ) (hN : 1 ≤ N)
    {x : Site d} (hx : x ∈ latticeCube Z (m * N)) :
    ∃ y ∈ Fintype.piFinset (fun _ : Fin d => Finset.range N),
      x ∈ latticeCube (Z + fun i => (m : ℤ) * (y i : ℤ)) m := by
  rw [mem_latticeCube_iff_coord] at hx
  have h : ∀ i, ∃ s : ℕ, s < N ∧ (m : ℤ) * s ≤ x i - Z i ∧ x i - Z i ≤ (m : ℤ) * s + m := by
    intro i
    obtain ⟨h0, h1⟩ := hx i
    push_cast at h1
    exact exists_block_index_of_le_mul m N hN (x i - Z i) (by omega) (by omega)
  choose s hs using h
  refine ⟨s, Fintype.mem_piFinset.2 fun i => Finset.mem_range.2 (hs i).1, ?_⟩
  rw [mem_latticeCube_iff_coord]
  intro i
  simp only [Pi.add_apply]
  have := hs i
  constructor <;> omega

/-- Every site of the cube `{0, …, m N}^d` lies in a child cube `m y + {0, …, m}^d` with
`y ∈ {0, …, N - 1}^d`. -/
theorem exists_child_cube_of_mem_latticeCube (m N : ℕ) (hN : 1 ≤ N) {x : Site d}
    (hx : x ∈ latticeCube (0 : Site d) (m * N)) :
    ∃ y ∈ Fintype.piFinset (fun _ : Fin d => Finset.range N),
      x ∈ latticeCube (fun i => (m : ℤ) * (y i : ℤ)) m := by
  simpa only [zero_add] using exists_subdivision_child_of_mem_latticeCube 0 m N hN hx

end LatticeHC

end
