/-
Copied from Lattice-High-Contrast-Homogenization (https://github.com/nitromannitol/Lattice-High-Contrast-Homogenization),
commit f47a932a9f7a07e1692bfe4aae564d02e8ca0944, file `LatticeHC/Support/AppendixA/FaceWeight.lean` (Apache License 2.0,
Copyright 2026 Ahmed Bou-Rabee and Yuval Peres).
Changes: imports `LatticeHC.*` renamed to `Rigidity.Vendor.LHCH.*`; namespace `LatticeHC` kept.
-/
import Rigidity.Vendor.LHCH.Model.Coarse
import Rigidity.Vendor.LHCH.Support.Lattice.Membership

/-!
# The face weights in each direction sum to the volume

For a lattice cube `□ = z + {0, …, L}^d` with `L ≥ 1`, the face weights of the edges of `□`
in a fixed direction `j` sum to `L^d` (Appendix A.1, `ss:coarse-def`).

The edges in direction `j` are the `(x, j)` with `x ∈ □` and `x_j < z_j + L`. The face
weight `2^{-k(e)}` is the product over `i ≠ j` of `1/2` if `x_i ∈ {z_i, z_i + L}` and `1`
otherwise. So the sum is `L · Π_{i ≠ j} (1/2 + (L - 1) + 1/2) = L^d`.
-/

namespace LatticeHC

open LatticeProb

variable {d : ℕ}

noncomputable section

/-- A coordinate other than `j` of `x + e_j` is unchanged. -/
lemma add_unit_apply_ne {x : Site d} {j k : Fin d} (h : k ≠ j) :
    (x + unit j) k = x k := by
  simp [unit, h]

/-- The first coordinate of the edge `x + e_j` of the cube, in coordinates relative to `z`: the
direction `j` ranges over `{0, …, L - 1}` and the other directions over `{0, …, L}`. -/
private def edgeBox (L : ℕ) (j : Fin d) : Finset (Site d) :=
  Fintype.piFinset fun i : Fin d =>
    if i = j then Finset.Ico (0 : ℤ) (L : ℤ) else Finset.Icc (0 : ℤ) (L : ℤ)

/-- The coordinate factor of the face weight of an edge in direction `j`: `1` in the direction `j`,
and `1/2` in a direction `i ≠ j` whose coordinate is a boundary value `0` or `L`. -/
private def faceFactor (L : ℕ) (j : Fin d) (i : Fin d) (t : ℤ) : ℝ :=
  if i = j then 1 else if t = 0 ∨ t = (L : ℤ) then 1 / 2 else 1

/-- The edges of `□ = z + {0, …, L}^d` in direction `j` are exactly the pairs `(z + y, j)`
with `y` in `edgeBox L j`. -/
private lemma filter_edgesOf_eq_image (z : Site d) (L : ℕ) (j : Fin d) :
    (edgesOf z L).filter (fun e => e.2 = j) =
      (edgeBox L j).image (fun y => (z + y, j)) := by
  classical
  ext e
  obtain ⟨x, i⟩ := e
  simp only [Finset.mem_filter, mem_edgesOf_iff, Finset.mem_image]
  constructor
  · rintro ⟨⟨hx, htgt⟩, hi⟩
    subst i
    refine ⟨x - z, ?_, ?_⟩
    · rw [edgeBox, Fintype.mem_piFinset]
      intro k
      have h1 := (mem_latticeCube_iff_coord z x L).1 hx k
      have h2 := (mem_latticeCube_iff_coord z (x + unit j) L).1 htgt k
      by_cases hk : k = j
      · subst k
        rw [if_pos rfl, Finset.mem_Ico]
        rw [add_unit_apply_coord, if_pos rfl] at h2
        simp only [Pi.sub_apply]
        omega
      · rw [if_neg hk, Finset.mem_Icc]
        rw [add_unit_apply_ne hk] at h2
        simp only [Pi.sub_apply]
        omega
    · rw [Prod.mk.injEq]
      exact ⟨by funext k; simp, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    rw [edgeBox, Fintype.mem_piFinset] at hy
    have hxy : x = z + y := by simpa using (congrArg Prod.fst hyx).symm
    have hij : i = j := by simpa using (congrArg Prod.snd hyx).symm
    rw [hxy, hij]
    refine ⟨⟨?_, ?_⟩, rfl⟩
    · rw [mem_latticeCube_iff_coord]
      intro k
      have hk := hy k
      by_cases hkj : k = j
      · subst k
        rw [if_pos rfl, Finset.mem_Ico] at hk
        simp only [Pi.add_apply]
        omega
      · rw [if_neg hkj, Finset.mem_Icc] at hk
        simp only [Pi.add_apply]
        omega
    · rw [mem_latticeCube_iff_coord]
      intro k
      have hk := hy k
      by_cases hkj : k = j
      · subst k
        rw [if_pos rfl, Finset.mem_Ico] at hk
        rw [add_unit_apply_coord, if_pos rfl]
        simp only [Pi.add_apply]
        omega
      · rw [if_neg hkj, Finset.mem_Icc] at hk
        rw [add_unit_apply_ne hkj]
        simp only [Pi.add_apply]
        omega

/-- The face weight of the edge `(z + y, j)` factors as a product over the coordinates of `y`. -/
private lemma faceWeight_add_eq_prod (z : Site d) (L : ℕ) (j : Fin d) (y : Site d) :
    faceWeight z L (z + y, j) = ∏ i : Fin d, faceFactor L j i (y i) := by
  classical
  have hfilter : (Finset.univ.filter fun i : Fin d =>
      i ≠ j ∧ ((z + y) i = z i ∨ (z + y) i = z i + (L : ℤ))) =
      Finset.univ.filter fun i : Fin d => i ≠ j ∧ (y i = 0 ∨ y i = (L : ℤ)) := by
    refine Finset.filter_congr fun i _ => ?_
    constructor
    · rintro ⟨hij, h | h⟩
      · refine ⟨hij, Or.inl ?_⟩
        simp only [Pi.add_apply] at h
        omega
      · refine ⟨hij, Or.inr ?_⟩
        simp only [Pi.add_apply] at h
        omega
    · rintro ⟨hij, h | h⟩
      · refine ⟨hij, Or.inl ?_⟩
        simp only [Pi.add_apply, h, add_zero]
      · refine ⟨hij, Or.inr ?_⟩
        simp only [Pi.add_apply, h]
  have hfac : ∀ i : Fin d,
      (if i ≠ j ∧ (y i = 0 ∨ y i = (L : ℤ)) then (1 / 2 : ℝ) else 1) =
        faceFactor L j i (y i) := by
    intro i
    by_cases hP : i ≠ j ∧ (y i = 0 ∨ y i = (L : ℤ))
    · rw [if_pos hP, faceFactor, if_neg hP.1, if_pos hP.2]
    · rw [if_neg hP]
      by_cases hij : i = j
      · rw [faceFactor, if_pos hij]
      · have hne : ¬ (y i = 0 ∨ y i = (L : ℤ)) := fun h => hP ⟨hij, h⟩
        rw [faceFactor, if_neg hij, if_neg hne]
  calc faceWeight z L (z + y, j)
      = (1 / 2 : ℝ) ^ ((Finset.univ.filter fun i : Fin d =>
          i ≠ j ∧ (y i = 0 ∨ y i = (L : ℤ))).card) := by
        rw [faceWeight, faceCount, hfilter]
    _ = ∏ i : Fin d,
          (if i ≠ j ∧ (y i = 0 ∨ y i = (L : ℤ)) then (1 / 2 : ℝ) else 1) := by
        rw [Finset.prod_ite, Finset.prod_const]
        simp
    _ = ∏ i : Fin d, faceFactor L j i (y i) :=
        Finset.prod_congr rfl fun i _ => hfac i

/-- Each coordinate factor of the face weight sums to `L` over its box. -/
private lemma sum_faceFactor (L : ℕ) (hL : 1 ≤ L) (j i : Fin d) :
    ∑ t ∈ (if i = j then Finset.Ico (0 : ℤ) (L : ℤ)
        else Finset.Icc (0 : ℤ) (L : ℤ)), faceFactor L j i t = (L : ℝ) := by
  classical
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    have h1 : ∀ t, faceFactor L i i t = 1 := fun t => by rw [faceFactor, if_pos rfl]
    rw [Finset.sum_congr rfl (fun t _ => h1 t), Finset.sum_const, nsmul_eq_mul, mul_one,
      Int.card_Ico]
    simp
  · rw [if_neg hij]
    have hft : ∀ t, faceFactor L j i t =
        if t = 0 ∨ t = (L : ℤ) then (1 / 2 : ℝ) else 1 := by
      intro t
      rw [faceFactor, if_neg hij]
    rw [Finset.sum_congr rfl (fun t _ => hft t), Finset.sum_ite, Finset.sum_const,
      Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, mul_one]
    have hP : (Finset.Icc (0 : ℤ) (L : ℤ)).filter (fun t => t = 0 ∨ t = (L : ℤ)) =
        ({0, (L : ℤ)} : Finset ℤ) := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨h0, hLt⟩, h | h⟩
        · exact Or.inl h
        · exact Or.inr h
      · rintro (h | h)
        · subst h
          exact ⟨⟨le_rfl, by omega⟩, Or.inl rfl⟩
        · subst h
          exact ⟨⟨by omega, le_rfl⟩, Or.inr rfl⟩
    have hlt : (0 : ℤ) ≠ (L : ℤ) := by omega
    have hcardP : ((Finset.Icc (0 : ℤ) (L : ℤ)).filter
        (fun t => t = 0 ∨ t = (L : ℤ))).card = 2 := by
      rw [hP, Finset.card_pair hlt]
    have hcardIcc : (Finset.Icc (0 : ℤ) (L : ℤ)).card = L + 1 := by
      rw [Int.card_Icc]
      simp
    have hcardNot : ((Finset.Icc (0 : ℤ) (L : ℤ)).filter
        (fun t => ¬ (t = 0 ∨ t = (L : ℤ)))).card = L - 1 := by
      rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _), hcardIcc,
        hcardP]
      omega
    rw [hcardP, hcardNot]
    have hcast : ((L - 1 : ℕ) : ℝ) = (L : ℝ) - 1 := by
      rw [Nat.cast_sub hL]
      norm_num
    rw [hcast]
    norm_num

/-- `Σ_{e ⊂ □, e ∥ e_j} w_□(e) = L^d` for `L ≥ 1` (Appendix A.1, `ss:coarse-def`). -/
theorem sum_faceWeight_eq (z : Site d) {L : ℕ} (hL : 1 ≤ L) (j : Fin d) :
    ∑ e ∈ (edgesOf z L).filter (fun e => e.2 = j), faceWeight z L e = (L : ℝ) ^ d := by
  classical
  rw [filter_edgesOf_eq_image]
  have hinj : Set.InjOn (fun y => (z + y, j)) (edgeBox L j) := by
    intro a _ b _ h
    have h' : z + a = z + b := by simpa using congrArg Prod.fst h
    exact add_left_cancel h'
  rw [Finset.sum_image (f := fun e => faceWeight z L e) hinj]
  calc ∑ y ∈ edgeBox L j, faceWeight z L (z + y, j)
      = ∑ y ∈ edgeBox L j, ∏ i : Fin d, faceFactor L j i (y i) :=
        Finset.sum_congr rfl fun y _ => faceWeight_add_eq_prod z L j y
    _ = ∏ i : Fin d, ∑ t ∈ (if i = j then Finset.Ico (0 : ℤ) (L : ℤ)
          else Finset.Icc (0 : ℤ) (L : ℤ)), faceFactor L j i t := by
        rw [edgeBox, ← Finset.prod_univ_sum]
    _ = ∏ i : Fin d, (L : ℝ) :=
        Finset.prod_congr rfl fun i _ => sum_faceFactor L hL j i
    _ = (L : ℝ) ^ d := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end

end LatticeHC
