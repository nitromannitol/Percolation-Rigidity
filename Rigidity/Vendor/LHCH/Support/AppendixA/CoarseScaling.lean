/-
Copied from Lattice-High-Contrast-Homogenization (https://github.com/nitromannitol/Lattice-High-Contrast-Homogenization),
commit f47a932a9f7a07e1692bfe4aae564d02e8ca0944, file `LatticeHC/Support/AppendixA/CoarseScaling.lean` (Apache License 2.0,
Copyright 2026 Ahmed Bou-Rabee and Yuval Peres).
Changes: imports `LatticeHC.*` renamed to `Rigidity.Vendor.LHCH.*`; namespace `LatticeHC` kept.
-/
import Rigidity.Vendor.LHCH.Model.Coarse

/-!
# Homogeneity and monotonicity of the coarse-grained matrices

`A_□` and `B_□` are homogeneous of degrees `1` and `-1` in the conductances. `A_□` is nondecreasing
and `B_□` nonincreasing in the conductances, as quadratic forms (proof of `p:coarse` and
the normalization in Step 2 of `p:finite-range`).
-/

namespace LatticeHC

open LatticeProb Matrix

variable {d : ℕ}

/-- Scaling the conductances multiplies the energy by the same factor. -/
private lemma cubeEnergy_smul (c : Edge d → ℝ) (z : Site d) (L : ℕ) (r : ℝ)
    (u : Site d → ℝ) :
    cubeEnergy (fun e => r * c e) z L u = r * cubeEnergy c z L u := by
  have h : ∑ e ∈ edgesOf z L, faceWeight z L e * (r * c e) * (u e.tgt - u e.src) ^ 2 =
      r * ∑ e ∈ edgesOf z L, faceWeight z L e * c e * (u e.tgt - u e.src) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ => by ring
  simp only [cubeEnergy]
  rw [h]
  ring

/-- Scaling the test function multiplies the energy by the square of the factor. -/
private lemma cubeEnergy_scale (c : Edge d → ℝ) (z : Site d) (L : ℕ) (r : ℝ)
    (u : Site d → ℝ) :
    cubeEnergy c z L (fun x => r * u x) = r ^ 2 * cubeEnergy c z L u := by
  have h : ∑ e ∈ edgesOf z L, faceWeight z L e * c e *
        ((fun x => r * u x) e.tgt - (fun x => r * u x) e.src) ^ 2 =
      r ^ 2 * ∑ e ∈ edgesOf z L, faceWeight z L e * c e * (u e.tgt - u e.src) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ => by ring
  simp only [cubeEnergy]
  rw [h]
  ring

/-- Scaling the test function scales the mean gradient by the same factor. -/
private lemma cubeMeanGrad_scale (z : Site d) (L : ℕ) (r : ℝ) (u : Site d → ℝ) :
    cubeMeanGrad z L (fun x => r * u x) = r • cubeMeanGrad z L u := by
  ext j
  have h : ∑ e ∈ (edgesOf z L).filter (fun e => e.2 = j),
        faceWeight z L e * ((fun x => r * u x) e.tgt - (fun x => r * u x) e.src) =
      r * ∑ e ∈ (edgesOf z L).filter (fun e => e.2 = j),
        faceWeight z L e * (u e.tgt - u e.src) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ => by ring
  simp only [cubeMeanGrad, Pi.smul_apply, smul_eq_mul]
  rw [h]
  ring

/-- `r⁻¹ ^ 2 * r = r⁻¹` for every real `r`, including `r = 0`. -/
private lemma inv_sq_mul_self (r : ℝ) : r⁻¹ ^ 2 * r = r⁻¹ := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  · field_simp

/-- Scaling the test function by `r` and the conductances by `r` relates the objective of `c`
to the objective of `r c`:
`2 p · 𝒢_□(r u) - ℰ_□(r u) = r (2 p · 𝒢_□(u) - ℰ_{r c}(u))`. -/
private lemma objective_scale (c : Edge d → ℝ) (z : Site d) (L : ℕ) (r : ℝ)
    (p : Fin d → ℝ) (u : Site d → ℝ) :
    2 * (p ⬝ᵥ cubeMeanGrad z L (fun x => r * u x)) -
        cubeEnergy c z L (fun x => r * u x) =
      r * (2 * (p ⬝ᵥ cubeMeanGrad z L u) -
        cubeEnergy (fun e => r * c e) z L u) := by
  rw [cubeMeanGrad_scale, cubeEnergy_scale, cubeEnergy_smul, dotProduct_smul]
  simp only [smul_eq_mul]
  ring

/-- Scaling the test function by `r⁻¹` and the conductances by `r` relates the objective of `r c`
to the objective of `c`:
`2 p · 𝒢_□(r⁻¹ u) - ℰ_{r c}(r⁻¹ u) = r⁻¹ (2 p · 𝒢_□(u) - ℰ_c(u))`. -/
private lemma objective_scale_inv (c : Edge d → ℝ) (z : Site d) (L : ℕ) (r : ℝ)
    (p : Fin d → ℝ) (u : Site d → ℝ) :
    2 * (p ⬝ᵥ cubeMeanGrad z L (fun x => r⁻¹ * u x)) -
        cubeEnergy (fun e => r * c e) z L (fun x => r⁻¹ * u x) =
      r⁻¹ * (2 * (p ⬝ᵥ cubeMeanGrad z L u) - cubeEnergy c z L u) := by
  rw [cubeMeanGrad_scale, cubeEnergy_scale, cubeEnergy_smul, dotProduct_smul]
  simp only [smul_eq_mul]
  rw [show r⁻¹ ^ 2 * (r * cubeEnergy c z L u) = r⁻¹ * cubeEnergy c z L u by
    rw [← mul_assoc, inv_sq_mul_self]]
  ring

/-- If `c ≤ c'` on the edges of `□`, the energy of `c` is at most that of `c'`
(face weights and squares are nonnegative). -/
private lemma cubeEnergy_mono (c c' : Edge d → ℝ) (z : Site d) (L : ℕ)
    (hle : ∀ e ∈ edgesOf z L, c e ≤ c' e) (u : Site d → ℝ) :
    cubeEnergy c z L u ≤ cubeEnergy c' z L u := by
  have hsum : ∑ e ∈ edgesOf z L, faceWeight z L e * c e * (u e.tgt - u e.src) ^ 2
      ≤ ∑ e ∈ edgesOf z L, faceWeight z L e * c' e * (u e.tgt - u e.src) ^ 2 := by
    refine Finset.sum_le_sum fun e he => ?_
    have hw : 0 ≤ faceWeight z L e := by unfold faceWeight; positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hle e he) hw) (sq_nonneg _)
  simp only [cubeEnergy]
  exact mul_le_mul_of_nonneg_left hsum (inv_nonneg.2 (pow_nonneg (Nat.cast_nonneg L) d))

/-- `A_□(t c) = t A_□(c)` and `B_□(t c) = t⁻¹ B_□(c)` for `t > 0`, as quadratic forms. -/
theorem coarse_smul (c : Edge d → ℝ) (z : Site d) (L : ℕ) (hc : ∀ e ∈ edgesOf z L, 0 < c e)
    {t : ℝ} (ht : 0 < t) (p : Fin d → ℝ) :
    p ⬝ᵥ (coarseA (fun e => t * c e) z L (fun e he => mul_pos ht (hc e he)) *ᵥ p) =
        t * (p ⬝ᵥ (coarseA c z L hc *ᵥ p)) ∧
      p ⬝ᵥ (coarseB (fun e => t * c e) z L (fun e he => mul_pos ht (hc e he)) *ᵥ p) =
        t⁻¹ * (p ⬝ᵥ (coarseB c z L hc *ᵥ p)) := by
  have hA : p ⬝ᵥ (coarseA (fun e => t * c e) z L (fun e he => mul_pos ht (hc e he)) *ᵥ p) =
      t * (p ⬝ᵥ (coarseA c z L hc *ᵥ p)) :=
    IsLeast.unique
      ((coarseA_spec (fun e => t * c e) z L (fun e he => mul_pos ht (hc e he))).2 p)
      (by
        constructor
        · obtain ⟨u, hu, hE⟩ := ((coarseA_spec c z L hc).2 p).1
          exact ⟨u, hu, by rw [hE, cubeEnergy_smul]⟩
        · intro y hy
          obtain ⟨u, hu, rfl⟩ := hy
          have hlow : p ⬝ᵥ (coarseA c z L hc *ᵥ p) ≤ cubeEnergy c z L u :=
            ((coarseA_spec c z L hc).2 p).2 ⟨u, hu, rfl⟩
          calc t * (p ⬝ᵥ (coarseA c z L hc *ᵥ p))
              ≤ t * cubeEnergy c z L u := mul_le_mul_of_nonneg_left hlow (le_of_lt ht)
            _ = cubeEnergy (fun e => t * c e) z L u := (cubeEnergy_smul c z L t u).symm)
  have hB : p ⬝ᵥ (coarseB (fun e => t * c e) z L (fun e he => mul_pos ht (hc e he)) *ᵥ p) =
      t⁻¹ * (p ⬝ᵥ (coarseB c z L hc *ᵥ p)) :=
    IsGreatest.unique
      ((coarseB_spec (fun e => t * c e) z L (fun e he => mul_pos ht (hc e he))).2 p)
      (by
        constructor
        · obtain ⟨u, hE⟩ := ((coarseB_spec c z L hc).2 p).1
          exact ⟨fun x => t⁻¹ * u x, by rw [hE, objective_scale_inv]⟩
        · intro y hy
          obtain ⟨u, rfl⟩ := hy
          have hup : 2 * (p ⬝ᵥ cubeMeanGrad z L (fun x => t * u x)) -
              cubeEnergy c z L (fun x => t * u x) ≤ p ⬝ᵥ (coarseB c z L hc *ᵥ p) :=
            ((coarseB_spec c z L hc).2 p).2 ⟨fun x => t * u x, rfl⟩
          have hscale : 2 * (p ⬝ᵥ cubeMeanGrad z L u) - cubeEnergy (fun e => t * c e) z L u
              = t⁻¹ * (2 * (p ⬝ᵥ cubeMeanGrad z L (fun x => t * u x)) -
                  cubeEnergy c z L (fun x => t * u x)) := by
            rw [objective_scale]
            rw [← mul_assoc, inv_mul_cancel₀ ht.ne', one_mul]
          calc 2 * (p ⬝ᵥ cubeMeanGrad z L u) - cubeEnergy (fun e => t * c e) z L u
              = t⁻¹ * (2 * (p ⬝ᵥ cubeMeanGrad z L (fun x => t * u x)) -
                  cubeEnergy c z L (fun x => t * u x)) := hscale
            _ ≤ t⁻¹ * (p ⬝ᵥ (coarseB c z L hc *ᵥ p)) :=
                mul_le_mul_of_nonneg_left hup (inv_nonneg.2 (le_of_lt ht)))
  exact ⟨hA, hB⟩

/-- For `c ≤ c'` on the edges of `□`: `p · A_□(c) p ≤ p · A_□(c') p` and
`p · B_□(c') p ≤ p · B_□(c) p`. -/
theorem coarse_mono (c c' : Edge d → ℝ) (z : Site d) (L : ℕ) (hc : ∀ e ∈ edgesOf z L, 0 < c e)
    (hc' : ∀ e ∈ edgesOf z L, 0 < c' e) (hle : ∀ e ∈ edgesOf z L, c e ≤ c' e)
    (p : Fin d → ℝ) :
    p ⬝ᵥ (coarseA c z L hc *ᵥ p) ≤ p ⬝ᵥ (coarseA c' z L hc' *ᵥ p) ∧
      p ⬝ᵥ (coarseB c' z L hc' *ᵥ p) ≤ p ⬝ᵥ (coarseB c z L hc *ᵥ p) := by
  constructor
  · obtain ⟨u', hu', hE'⟩ := ((coarseA_spec c' z L hc').2 p).1
    have h1 : p ⬝ᵥ (coarseA c z L hc *ᵥ p) ≤ cubeEnergy c z L u' :=
      ((coarseA_spec c z L hc).2 p).2 ⟨u', hu', rfl⟩
    have h2 : cubeEnergy c z L u' ≤ cubeEnergy c' z L u' := cubeEnergy_mono c c' z L hle u'
    exact h1.trans (h2.trans (le_of_eq hE'.symm))
  · obtain ⟨u', hE'⟩ := ((coarseB_spec c' z L hc').2 p).1
    have h1 : 2 * (p ⬝ᵥ cubeMeanGrad z L u') - cubeEnergy c z L u'
        ≤ p ⬝ᵥ (coarseB c z L hc *ᵥ p) :=
      ((coarseB_spec c z L hc).2 p).2 ⟨u', rfl⟩
    have h2 : cubeEnergy c z L u' ≤ cubeEnergy c' z L u' := cubeEnergy_mono c c' z L hle u'
    calc p ⬝ᵥ (coarseB c' z L hc' *ᵥ p)
        = 2 * (p ⬝ᵥ cubeMeanGrad z L u') - cubeEnergy c' z L u' := hE'
      _ ≤ 2 * (p ⬝ᵥ cubeMeanGrad z L u') - cubeEnergy c z L u' := by linarith
      _ ≤ p ⬝ᵥ (coarseB c z L hc *ᵥ p) := h1

end LatticeHC
