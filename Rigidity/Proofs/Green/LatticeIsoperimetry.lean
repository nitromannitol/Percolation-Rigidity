import Rigidity.Proofs.Green.CoarseIsoperimetry
import Rigidity.Vendor.LHCH.Support.Analysis.LatticeSobolev

/-!
# The isoperimetric inequality of `ℤ^d`

For `d ≥ 2`, every finite `F ⊆ ℤ^d` has at least `|F|^{(d-1)/d}` boundary edges
(`latticeIsoperimetry`). This is the lattice `ℓ¹` Sobolev inequality
`LatticeHC.sum_rpow_le_sum_abs_grad` (copied from Lattice-High-Contrast-Homogenization into
`Rigidity.Vendor.LHCH`) for the indicator `1_F`: the gradient term `|1_F(x + e_j) - 1_F(x)|` is
one exactly when one of `x, x + e_j` lies in `F`, and these pairs are counted by the boundary
edges of `F` in the directions `+e_j` and `-e_j`.
-/

open LatticeProb LatticeProb.Percolation
open scoped Classical

namespace Rigidity.Green

variable {d : ℕ}

theorem unit_injective : Function.Injective (unit : Fin d → Vertex d) := by
  intro i j h
  by_contra hij
  have := congrFun h i
  simp [unit, hij] at this

theorem add_unit_ne_sub_unit (z : Vertex d) (i j : Fin d) : z + unit i ≠ z - unit j := by
  intro h
  have := congrFun h i
  by_cases hij : i = j
  · subst hij
    simp only [unit, Pi.add_apply, Pi.sub_apply, Pi.single_eq_same] at this
    omega
  · simp only [unit, Pi.add_apply, Pi.sub_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne hij] at this
    omega

/-- The boundary edges at `z` in the directions `+e_j` and `-e_j` are distinct. -/
theorem card_add_card_le_boundary (F : Finset (Vertex d)) (z : Vertex d) :
    (Finset.univ.filter fun j : Fin d => z + unit j ∉ F).card +
        (Finset.univ.filter fun j : Fin d => z - unit j ∉ F).card ≤
      (((nearestNeighborGraph d).neighborFinset z).filter fun w => w ∉ F).card := by
  set Ap := (Finset.univ.filter fun j : Fin d => z + unit j ∉ F).image fun j => z + unit j
  set Am := (Finset.univ.filter fun j : Fin d => z - unit j ∉ F).image fun j => z - unit j
  have hp : Ap.card = (Finset.univ.filter fun j : Fin d => z + unit j ∉ F).card :=
    Finset.card_image_of_injective _ fun i j h => unit_injective (add_right_injective z h)
  have hm : Am.card = (Finset.univ.filter fun j : Fin d => z - unit j ∉ F).card :=
    Finset.card_image_of_injective _ fun i j h => unit_injective (sub_right_injective h)
  have hdisj : Disjoint Ap Am := by
    rw [Finset.disjoint_left]
    intro w hw hw'
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hw'
    exact add_unit_ne_sub_unit z i j hj.symm
  have hsub : Ap ∪ Am ⊆ ((nearestNeighborGraph d).neighborFinset z).filter fun w => w ∉ F := by
    intro w hw
    rw [Finset.mem_filter, SimpleGraph.mem_neighborFinset, Graph.Zd.adj_iff]
    rcases Finset.mem_union.mp hw with hw | hw
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
      exact ⟨⟨i, Or.inl rfl⟩, (Finset.mem_filter.mp hi).2⟩
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
      exact ⟨⟨i, Or.inr rfl⟩, (Finset.mem_filter.mp hi).2⟩
  rw [← hp, ← hm, ← Finset.card_union_of_disjoint hdisj]
  exact Finset.card_le_card hsub

/-- **The isoperimetric inequality of `ℤ^d`**, `d ≥ 2`: `|F|^{(d-1)/d} ≤ |∂F|`. -/
theorem latticeIsoperimetry (hd : 2 ≤ d) : LatticeIsoperimetry d := by
  intro F
  set v : Vertex d → ℝ := fun x => if x ∈ F then 1 else 0 with hv
  set S' : Finset (Vertex d) := F ∪ F.biUnion fun z => Finset.univ.image fun j => z - unit j
    with hS'def
  have hvS : ∀ x, x ∉ F → v x = 0 := fun x hx => by simp [hv, hx]
  have hS' : ∀ x (j : Fin d), v (x + unit j) ≠ v x → x ∈ S' := by
    intro x j hne
    by_cases hx : x ∈ F
    · exact Finset.mem_union_left _ hx
    · have hxj : x + unit j ∈ F := by
        by_contra hxj
        apply hne
        simp [hv, hx, hxj]
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨_, hxj, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, by simp⟩⟩)
  have key := LatticeHC.sum_rpow_le_sum_abs_grad hd F S' v hvS hS'
  have hlhs : ∑ x ∈ F, |v x| ^ ((d : ℝ) / (d - 1)) = F.card := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    simp [hv, hx]
  rw [hlhs] at key
  refine key.trans ?_
  set A : Fin d → ℕ := fun j => (F.filter fun x => x + unit j ∉ F).card with hA
  set B : Fin d → ℕ := fun j => (F.filter fun x => x - unit j ∉ F).card with hB
  have hN : ∑ j : Fin d, (A j + B j) ≤ edgeBoundaryCard (nearestNeighborGraph d) F := by
    have hE : edgeBoundaryCard (nearestNeighborGraph d) F = ∑ z ∈ F,
        (((nearestNeighborGraph d).neighborFinset z).filter (fun w => w ∉ F)).card := by
      unfold edgeBoundaryCard
      exact Finset.sum_congr rfl fun z _ => by congr
    have hswapA : ∑ j : Fin d, A j =
        ∑ z ∈ F, (Finset.univ.filter fun j : Fin d => z + unit j ∉ F).card := by
      simp only [hA, Finset.card_filter]
      exact Finset.sum_comm
    have hswapB : ∑ j : Fin d, B j =
        ∑ z ∈ F, (Finset.univ.filter fun j : Fin d => z - unit j ∉ F).card := by
      simp only [hB, Finset.card_filter]
      exact Finset.sum_comm
    rw [Finset.sum_add_distrib, hswapA, hswapB, ← Finset.sum_add_distrib, hE]
    exact Finset.sum_le_sum fun z _ => card_add_card_le_boundary F z
  have hterm : ∀ x (j : Fin d), |v (x + unit j) - v x| =
      (if x ∈ F ∧ x + unit j ∉ F then 1 else 0) + (if x ∉ F ∧ x + unit j ∈ F then 1 else 0) := by
    intro x j
    by_cases hx : x ∈ F <;> by_cases hxj : x + unit j ∈ F <;> simp [hv, hx, hxj]
  have h1 : ∀ j : Fin d, ∑ x ∈ S', ((if x ∈ F ∧ x + unit j ∉ F then 1 else 0) +
      (if x ∉ F ∧ x + unit j ∈ F then 1 else 0) : ℝ) ≤ (A j : ℝ) + B j := by
    intro j
    rw [Finset.sum_add_distrib, Finset.sum_boole, Finset.sum_boole]
    refine add_le_add ?_ ?_
    · exact_mod_cast Finset.card_le_card fun x hx => by
        obtain ⟨-, hxF, hxj⟩ := Finset.mem_filter.mp hx
        exact Finset.mem_filter.mpr ⟨hxF, hxj⟩
    · exact_mod_cast Finset.card_le_card_of_injOn (fun x => x + unit j) (by
        intro x hx
        obtain ⟨-, hxF, hxj⟩ := Finset.mem_filter.mp hx
        exact Finset.mem_filter.mpr ⟨hxj, by simpa using hxF⟩)
        (fun x _ y _ h => add_right_cancel h)
  have hR : ∑ x ∈ S', ∑ j : Fin d, |v (x + unit j) - v x| ≤
      ((∑ j : Fin d, (A j + B j) : ℕ) : ℝ) := by
    calc ∑ x ∈ S', ∑ j : Fin d, |v (x + unit j) - v x|
        = ∑ j : Fin d, ∑ x ∈ S', ((if x ∈ F ∧ x + unit j ∉ F then 1 else 0) +
            (if x ∉ F ∧ x + unit j ∈ F then 1 else 0) : ℝ) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun x _ => hterm x j
      _ ≤ ∑ j : Fin d, ((A j : ℝ) + B j) := Finset.sum_le_sum fun j _ => h1 j
      _ = ((∑ j : Fin d, (A j + B j) : ℕ) : ℝ) := by
          rw [Nat.cast_sum]
          simp only [Nat.cast_add]
  exact hR.trans (by exact_mod_cast hN)

end Rigidity.Green
