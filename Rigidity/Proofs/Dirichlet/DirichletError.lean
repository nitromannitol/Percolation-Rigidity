import Rigidity.Proofs.Dirichlet.EnergyComparison

/-!
# The homogenization error from the energy comparisons

The proof of Armstrong–Dario, Proposition 6.1, from Lemmas 6.2 and 6.3: if `u` is `c`-harmonic on
`U`, the function `v = ũ_hom` equals `u` off `U` and the energy chain
`e_hom ≤ e_trial ≤ E(u) + δ₁`, `E(v) ≤ e_hom + δ₂` holds, then with conductances in
`{0} ∪ [λ, ∞)` the open-edge energy of `v − u` is at most `(δ₁ + δ₂)/λ`. A Poincaré inequality
for `v − u` with constant `P` (Proposition 3.4 of the source, an input here) and the `L²` estimate
`Σ (v − u_hom)² ≤ δ₃` (Lemma 6.3 (iii)) then give
`Σ (u − u_hom)² ≤ 2 P (δ₁ + δ₂)/λ + 2 δ₃`.
-/

open LatticeProb LatticeHC

namespace Rigidity.Dirichlet

variable {d : ℕ}

/-- **Armstrong–Dario, Proposition 6.1, from its three inputs.** -/
theorem sum_sq_sub_le_of_energy_chain (c : Edge d → ℝ) {lam : ℝ} (hlam : 0 < lam)
    (hc : ∀ e, c e = 0 ∨ lam ≤ c e) {U S : Finset (Site d)} (hS : CoversEdges U S)
    {u v uHom : Site d → ℝ} (hu : ∀ x ∈ U, condLaplacian c u x = 0)
    (hvu : ∀ x, x ∉ U → v x = u x) {eHom eTrial δ₁ δ₂ δ₃ P : ℝ} (hP0 : 0 ≤ P)
    (hmin : eHom ≤ eTrial) (h₁ : eTrial ≤ edgeEnergy c S u + δ₁)
    (h₂ : edgeEnergy c S v ≤ eHom + δ₂) (T : Finset (Site d))
    (hP : ∑ x ∈ T, (v x - u x) ^ 2 ≤ P * ∑ x ∈ S, ∑ j : Fin d,
      (if c (x, j) = 0 then 0 else ((v - u) (x + unit j) - (v - u) x) ^ 2))
    (h₃ : ∑ x ∈ T, (v x - uHom x) ^ 2 ≤ δ₃) :
    ∑ x ∈ T, (u x - uHom x) ^ 2 ≤ 2 * (P * ((δ₁ + δ₂) / lam)) + 2 * δ₃ := by
  have hE := edgeEnergy_sub_le_add c hS hu hvu hmin h₁ h₂
  have hgrad := sum_sq_grad_le_edgeEnergy_div c hlam hc S (v - u)
  have hvu2 : ∑ x ∈ T, (v x - u x) ^ 2 ≤ P * ((δ₁ + δ₂) / lam) :=
    hP.trans (mul_le_mul_of_nonneg_left (hgrad.trans
      (div_le_div_of_nonneg_right hE hlam.le)) hP0)
  have hpt : ∀ x ∈ T, (u x - uHom x) ^ 2 ≤ 2 * (v x - u x) ^ 2 + 2 * (v x - uHom x) ^ 2 := by
    intro x _
    nlinarith [sq_nonneg (v x - u x + (v x - uHom x))]
  calc ∑ x ∈ T, (u x - uHom x) ^ 2
      ≤ ∑ x ∈ T, (2 * (v x - u x) ^ 2 + 2 * (v x - uHom x) ^ 2) := Finset.sum_le_sum hpt
    _ = 2 * ∑ x ∈ T, (v x - u x) ^ 2 + 2 * ∑ x ∈ T, (v x - uHom x) ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ 2 * (P * ((δ₁ + δ₂) / lam)) + 2 * δ₃ := by linarith

end Rigidity.Dirichlet
