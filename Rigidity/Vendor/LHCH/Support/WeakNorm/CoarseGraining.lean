/-
Copied from Lattice-High-Contrast-Homogenization (https://github.com/nitromannitol/Lattice-High-Contrast-Homogenization),
commit f47a932a9f7a07e1692bfe4aae564d02e8ca0944, file `LatticeHC/Support/WeakNorm/CoarseGraining.lean` (Apache License 2.0,
Copyright 2026 Ahmed Bou-Rabee and Yuval Peres).
Changes: imports `LatticeHC.*` renamed to `Rigidity.Vendor.LHCH.*`; namespace `LatticeHC` kept.
-/
import Rigidity.Vendor.LHCH.Support.AppendixA.CoarseDefs

/-!
# The coarse-graining inequality for the mean gradient

The lattice form of the gradient half of AK25 (2.36): on a lattice cube `□`, for every function
`w` and every `q ∈ ℝ^d`, `(q · 𝒢_□(w))² ≤ (q · B_□ q) 𝓔_□(w)`. It is the Cauchy–Schwarz
inequality with the coarse-grained matrix `B_□` in place of the pointwise conductances: test the
maximization defining `B_□` in (e:AB) with the multiples `t w` of `w`. It bounds child averages of
the mean gradient by the additivity defect without any pointwise ellipticity.
-/

namespace LatticeHC

open LatticeProb Matrix

noncomputable section

variable {d : ℕ}

/-- The energy `𝓔_□` is quadratic: `𝓔_□(t w) = t² 𝓔_□(w)`. -/
theorem cubeEnergy_smul_fun (c : Edge d → ℝ) (z : Site d) (L : ℕ) (t : ℝ)
    (w : Site d → ℝ) : cubeEnergy c z L (t • w) = t ^ 2 * cubeEnergy c z L w := by
  simp only [cubeEnergy, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  ring

/-- The mean gradient `𝒢_□` is linear: `q · 𝒢_□(t w) = t (q · 𝒢_□(w))`. -/
theorem dotProduct_cubeMeanGrad_smul (z : Site d) (L : ℕ) (q : Fin d → ℝ) (t : ℝ)
    (w : Site d → ℝ) : q ⬝ᵥ cubeMeanGrad z L (t • w) = t * (q ⬝ᵥ cubeMeanGrad z L w) := by
  simp only [dotProduct, cubeMeanGrad, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun e _ => ?_
  ring

/-- **The coarse-graining inequality for the mean gradient** (AK25 (2.36), gradient half): for
conductances positive on the edges of `□`, `(q · 𝒢_□(w))² ≤ (q · B_□ q) 𝓔_□(w)`. The maximization
defining `B_□` in (e:AB), tested with `t w`, gives `2 t (q · 𝒢_□(w)) − t² 𝓔_□(w) ≤ q · B_□ q` for
every real `t`; take `t = (q · 𝒢_□(w)) / 𝓔_□(w)`, or note that `q · 𝒢_□(w) = 0` when
`𝓔_□(w) = 0`. -/
theorem sq_dotProduct_cubeMeanGrad_le (c : Edge d → ℝ) (z : Site d) (L : ℕ)
    (hc : ∀ e ∈ edgesOf z L, 0 < c e) (q : Fin d → ℝ) (w : Site d → ℝ) :
    (q ⬝ᵥ cubeMeanGrad z L w) ^ 2 ≤
      (q ⬝ᵥ (coarseB c z L hc *ᵥ q)) * cubeEnergy c z L w := by
  set g := q ⬝ᵥ cubeMeanGrad z L w with hg
  set E := cubeEnergy c z L w with hE
  set β := q ⬝ᵥ (coarseB c z L hc *ᵥ q) with hβ
  have htest : ∀ t : ℝ, 2 * (t * g) - t ^ 2 * E ≤ β := fun t =>
    (coarseB_spec c z L hc).2 q |>.2
      ⟨t • w, by rw [dotProduct_cubeMeanGrad_smul, cubeEnergy_smul_fun]⟩
  have hE0 : 0 ≤ E := cubeEnergy_nonneg c z L hc w
  rcases hE0.lt_or_eq with hEpos | hEzero
  · have h := htest (g / E)
    have hkey : 2 * (g / E * g) - (g / E) ^ 2 * E = g ^ 2 / E := by
      field_simp
      ring
    rw [hkey, div_le_iff₀ hEpos] at h
    linarith
  · have hg0 : g = 0 := by
      by_contra hne
      have h := htest ((β + 1) / (2 * g))
      rw [← hEzero] at h
      have hcalc : 2 * ((β + 1) / (2 * g) * g) - ((β + 1) / (2 * g)) ^ 2 * 0 = β + 1 := by
        field_simp
        ring
      linarith
    rw [hg0, ← hEzero]
    simp

end

end LatticeHC
