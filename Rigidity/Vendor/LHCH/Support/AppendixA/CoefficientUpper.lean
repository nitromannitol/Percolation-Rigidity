/-
Copied from Lattice-High-Contrast-Homogenization (https://github.com/nitromannitol/Lattice-High-Contrast-Homogenization),
commit f47a932a9f7a07e1692bfe4aae564d02e8ca0944, file `LatticeHC/Support/AppendixA/CoefficientUpper.lean` (Apache License 2.0,
Copyright 2026 Ahmed Bou-Rabee and Yuval Peres).
Changes: imports `LatticeHC.*` renamed to `Rigidity.Vendor.LHCH.*`; namespace `LatticeHC` kept.
-/
import Rigidity.Vendor.LHCH.Model.Coarse

/-!
# The upper bound on the coarse-grained matrix `A_□`

Testing `(e:AB)` with the affine function `p · x` gives
`p · A_□ p ≤ E_□(p · x) = Σ_j p_j² L^{-d} Σ_{e ∥ e_j} w_□(e) c_e`, the first half of
`(e:coefficient-upper)`.
-/

namespace LatticeHC

open LatticeProb Matrix

variable {d : ℕ}

/-- For a site `x` and a direction `j`, `affine p (x + e_j) - affine p x = p j`. -/
lemma affine_add_unit (p : Fin d → ℝ) (x : Site d) (j : Fin d) :
    affine p (x + unit j) - affine p x = p j := by
  have hcast : ∀ i : Fin d, (((unit j) i : ℤ) : ℝ) = if i = j then (1 : ℝ) else 0 := by
    intro i
    rw [unit, Pi.single_apply]
    by_cases h : i = j <;> simp [h]
  simp only [affine, Pi.add_apply, Int.cast_add, hcast, mul_add, Finset.sum_add_distrib]
  simp

/-- The gradient of `affine p` along an edge `e` is `p e.2`. -/
lemma affine_tgt_sub_src (p : Fin d → ℝ) (e : Edge d) :
    affine p e.tgt - affine p e.src = p e.2 :=
  affine_add_unit p e.1 e.2

/-- `p · A_□ p ≤ Σ_j p_j² L^{-d} Σ_{e ∥ e_j} w_□(e) c_e`. -/
theorem dotProduct_coarseA_le (c : Edge d → ℝ) (z : Site d) (L : ℕ)
    (hc : ∀ e ∈ edgesOf z L, 0 < c e) (p : Fin d → ℝ) :
    p ⬝ᵥ (coarseA c z L hc *ᵥ p) ≤
      ∑ j, p j ^ 2 * (((L : ℝ) ^ d)⁻¹ *
        ∑ e ∈ (edgesOf z L).filter (fun e => e.2 = j), faceWeight z L e * c e) := by
  have hmem : cubeEnergy c z L (affine p) ∈
      {E | ∃ u : Site d → ℝ, (∀ x ∈ vertexBoundary z L, u x = affine p x) ∧
        E = cubeEnergy c z L u} :=
    ⟨affine p, fun _ _ => rfl, rfl⟩
  have hbound : p ⬝ᵥ (coarseA c z L hc *ᵥ p) ≤ cubeEnergy c z L (affine p) :=
    ((coarseA_spec c z L hc).2 p).2 hmem
  refine hbound.trans (le_of_eq ?_)
  have hfiber : ∀ j : Fin d,
      ∑ e ∈ (edgesOf z L).filter (fun e => e.2 = j),
          faceWeight z L e * c e * (p e.2) ^ 2 =
        (p j) ^ 2 * ∑ e ∈ (edgesOf z L).filter (fun e => e.2 = j),
          faceWeight z L e * c e := by
    intro j
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [(Finset.mem_filter.1 he).2]
    ring
  rw [cubeEnergy]
  have hgrad : ∑ e ∈ edgesOf z L,
        faceWeight z L e * c e * (affine p e.tgt - affine p e.src) ^ 2 =
      ∑ e ∈ edgesOf z L, faceWeight z L e * c e * (p e.2) ^ 2 := by
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [affine_tgt_sub_src]
  rw [hgrad]
  calc ((L : ℝ) ^ d)⁻¹ * ∑ e ∈ edgesOf z L, faceWeight z L e * c e * (p e.2) ^ 2
      = ((L : ℝ) ^ d)⁻¹ * ∑ j, ∑ e ∈ (edgesOf z L).filter (fun e => e.2 = j),
          faceWeight z L e * c e * (p e.2) ^ 2 := by
          rw [Finset.sum_fiberwise (edgesOf z L) (fun e => e.2)
            (fun e => faceWeight z L e * c e * (p e.2) ^ 2)]
    _ = ∑ j, ((L : ℝ) ^ d)⁻¹ * ∑ e ∈ (edgesOf z L).filter (fun e => e.2 = j),
          faceWeight z L e * c e * (p e.2) ^ 2 := by
          rw [Finset.mul_sum]
    _ = ∑ j, ((L : ℝ) ^ d)⁻¹ * ((p j) ^ 2 *
          ∑ e ∈ (edgesOf z L).filter (fun e => e.2 = j), faceWeight z L e * c e) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hfiber j]
    _ = ∑ j, p j ^ 2 * (((L : ℝ) ^ d)⁻¹ *
          ∑ e ∈ (edgesOf z L).filter (fun e => e.2 = j), faceWeight z L e * c e) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          ring

end LatticeHC
