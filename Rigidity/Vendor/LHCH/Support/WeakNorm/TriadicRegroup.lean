/-
Copied from Lattice-High-Contrast-Homogenization (https://github.com/nitromannitol/Lattice-High-Contrast-Homogenization),
commit f47a932a9f7a07e1692bfe4aae564d02e8ca0944, file `LatticeHC/Support/WeakNorm/TriadicRegroup.lean` (Apache License 2.0,
Copyright 2026 Ahmed Bou-Rabee and Yuval Peres).
Changes: imports `LatticeHC.*` renamed to `Rigidity.Vendor.LHCH.*`; namespace `LatticeHC` kept.
-/
import Rigidity.Vendor.LHCH.Support.WeakNorm.Multiscale

/-!
# Regrouping the children of a triadic cube by their parents

A sum over the children at scale `k` of a triadic cube is a double sum over the children at scale `k
+ 1` and their `3^d` children, through the bijection `y = 3 y' + y''`; the numbers of children
multiply accordingly.
-/

open LatticeProb

noncomputable section

namespace LatticeHC

variable {d : ℕ}

/-- Membership in the index set `{0, …, 3^j − 1}^d`: every coordinate is below `3^j`. -/
theorem mem_triadicIndex {j : ℕ} {y : Fin d → ℕ} :
    y ∈ triadicIndex d j ↔ ∀ i, y i < 3 ^ j := by
  simp [triadicIndex, Fintype.mem_piFinset]

/-- **Regrouping the children by their parents.** For `k < n`, a sum over the children at scale
`k` of `Z + {0, …, 3^n}^d` is the sum over the children `□'` at scale `k + 1` of the sum over the
`3^d` children of `□'` at scale `k`: the index `y ∈ {0, …, 3^{n−k} − 1}^d` is `3 y' + y''` with
`y' ∈ {0, …, 3^{n−k−1} − 1}^d` and `y'' ∈ {0, 1, 2}^d`. -/
theorem sum_triadicIndex_regroup {β : Type*} [AddCommMonoid β] (Z : Site d) {n k : ℕ}
    (hkn : k < n) (f : Site d → β) :
    ∑ y ∈ triadicIndex d (n - k), f (triadicCorner Z k y) =
      ∑ y ∈ triadicIndex d (n - (k + 1)), ∑ y' ∈ triadicIndex d 1,
        f (triadicCorner (triadicCorner Z (k + 1) y) k y') := by
  have hn : n - k = (n - (k + 1)) + 1 := by omega
  rw [← Finset.sum_product' (f := fun y y' =>
    f (triadicCorner (triadicCorner Z (k + 1) y) k y'))]
  refine Finset.sum_nbij' (fun y => ((fun i => y i / 3), (fun i => y i % 3)))
    (fun p => fun i => 3 * p.1 i + p.2 i) ?_ ?_ ?_ ?_ ?_
  · intro y hy
    rw [mem_triadicIndex] at hy
    rw [Finset.mem_product, mem_triadicIndex, mem_triadicIndex]
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have := hy i
      rw [hn, pow_succ] at this
      exact Nat.div_lt_of_lt_mul (by linarith)
    · exact Nat.mod_lt _ (by norm_num)
  · rintro ⟨y, y'⟩ hp
    rw [Finset.mem_product, mem_triadicIndex, mem_triadicIndex] at hp
    rw [mem_triadicIndex, hn]
    intro i
    have h1 := hp.1 i
    have h2 := hp.2 i
    rw [pow_one] at h2
    rw [pow_succ]
    omega
  · intro y _
    funext i
    simp only
    omega
  · rintro ⟨y, y'⟩ hp
    rw [Finset.mem_product, mem_triadicIndex, mem_triadicIndex] at hp
    refine Prod.ext ?_ ?_
    · funext i
      have h2 : y' i < 3 ^ 1 := hp.2 i
      rw [pow_one] at h2
      show (3 * y i + y' i) / 3 = y i
      omega
    · funext i
      have h2 : y' i < 3 ^ 1 := hp.2 i
      rw [pow_one] at h2
      show (3 * y i + y' i) % 3 = y' i
      omega
  · intro y _
    congr 1
    funext i
    simp only [triadicCorner, Pi.add_apply]
    have h := Nat.div_add_mod (y i) 3
    generalize y i / 3 = a at h ⊢
    generalize y i % 3 = b at h ⊢
    rw [← h]
    push_cast
    ring

/-- The number of children multiplies: `|{0, …, 3^{n−k} − 1}^d| = |{0, …, 3^{n−k−1} − 1}^d| · 3^d`
for `k < n`. -/
theorem card_triadicIndex_succ {n k : ℕ} (hkn : k < n) :
    (triadicIndex d (n - k)).card =
      (triadicIndex d (n - (k + 1))).card * (triadicIndex d 1).card := by
  have hn : n - k = (n - (k + 1)) + 1 := by omega
  simp only [triadicIndex, Fintype.card_piFinset, Finset.card_range, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  rw [hn, ← mul_pow, ← pow_add]

end LatticeHC

end
