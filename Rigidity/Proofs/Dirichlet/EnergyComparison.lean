import Rigidity.Proofs.Dirichlet.BoundaryData

/-!
# Energy comparison for the homogenization error

For arbitrary conductances `c`, if `u` is `c`-harmonic on `U` and `v = u` off `U`, then the energy
of `v − u` is the energy excess `E(v) − E(u)`. If moreover `c(e) ≥ λ > 0` at every edge with
`c(e) ≠ 0`, this controls the squared gradient of `v − u` along those edges.

These are the two steps of the proof of Armstrong–Dario, Proposition 6.1, from Lemmas 6.2 and
6.3: with `u ∈ 𝒜_*(□_m)`, the homogenized solution `u_hom`, the function `ũ` of Lemma 6.2 and the
function `ũ_hom` of Lemma 6.3 equal to `u` on the boundary of the cluster, the chain
`E_hom(u_hom) ≤ E_hom(ũ) ≤ E(u) + δ₁` and `E(ũ_hom) ≤ E_hom(u_hom) + δ₂` gives
`E(ũ_hom − u) ≤ δ₁ + δ₂` (`edgeEnergy_sub_le_add`). The source argues by the parallelogram law
and the minimality of `u`; the Pythagoras identity of the Dirichlet problem gives the same bound
with constant `1`.
-/

open LatticeProb LatticeHC

namespace Rigidity.Dirichlet

variable {d : ℕ}

/-- **Energy excess**: if `u` is `c`-harmonic on `U` and `v = u` off `U`, then
`E(v − u) = E(v) − E(u)`. -/
theorem edgeEnergy_sub_eq_of_condLaplacian (c : Edge d → ℝ) {U S : Finset (Site d)}
    (hS : CoversEdges U S) {u v : Site d → ℝ} (hu : ∀ x ∈ U, condLaplacian c u x = 0)
    (hvu : ∀ x, x ∉ U → v x = u x) :
    edgeEnergy c S (v - u) = edgeEnergy c S v - edgeEnergy c S u := by
  rw [edgeEnergy_eq_add_of_condLaplacian c hS hu hvu]
  ring

/-- **The energy chain of Armstrong–Dario, Proposition 6.1**: if `u` is `c`-harmonic on `U`,
`v = u` off `U`, and the real numbers `eHom` (the homogenized energy of `u_hom`) and `eTrial`
(the homogenized energy of a competitor) satisfy `eHom ≤ eTrial ≤ E(u) + δ₁` and
`E(v) ≤ eHom + δ₂`, then `E(v − u) ≤ δ₁ + δ₂`. -/
theorem edgeEnergy_sub_le_add (c : Edge d → ℝ) {U S : Finset (Site d)}
    (hS : CoversEdges U S) {u v : Site d → ℝ} (hu : ∀ x ∈ U, condLaplacian c u x = 0)
    (hvu : ∀ x, x ∉ U → v x = u x) {eHom eTrial δ₁ δ₂ : ℝ} (hmin : eHom ≤ eTrial)
    (h₁ : eTrial ≤ edgeEnergy c S u + δ₁) (h₂ : edgeEnergy c S v ≤ eHom + δ₂) :
    edgeEnergy c S (v - u) ≤ δ₁ + δ₂ := by
  rw [edgeEnergy_sub_eq_of_condLaplacian c hS hu hvu]
  linarith

/-- **Ellipticity on open edges**: if every conductance is `0` or at least `λ > 0`, the squared
gradient of `w` along the edges with nonzero conductance is at most `E(w)/λ`. -/
theorem sum_sq_grad_le_edgeEnergy_div (c : Edge d → ℝ) {lam : ℝ} (hlam : 0 < lam)
    (hc : ∀ e, c e = 0 ∨ lam ≤ c e) (S : Finset (Site d)) (w : Site d → ℝ) :
    ∑ x ∈ S, ∑ j : Fin d, (if c (x, j) = 0 then 0 else (w (x + unit j) - w x) ^ 2) ≤
      edgeEnergy c S w / lam := by
  rw [le_div_iff₀ hlam, edgeEnergy, Finset.sum_mul]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  split_ifs with h
  · rw [h, zero_mul, zero_mul]
  · rcases hc (x, j) with h' | h'
    · exact absurd h' h
    · rw [mul_comm]
      exact mul_le_mul_of_nonneg_right h' (sq_nonneg _)

end Rigidity.Dirichlet
