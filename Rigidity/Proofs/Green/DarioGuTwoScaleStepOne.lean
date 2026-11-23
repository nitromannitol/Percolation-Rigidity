import Rigidity.Proofs.Green.DarioGuFluxInput
import Rigidity.Proofs.Green.DarioGuTwoScaleEnergy

/-!
# The equation of the two-scale expansion (Step 1 of Proposition 4.3 of Dario–Gu)

Step 1 of the proof of Proposition 4.3 of Dario–Gu (lines 2245-2274 of the source) computes
`(∂_t - ∇·a∇) h` for the two-scale expansion `h = θ^{-1}(p̄ + Σ_k D_k p̄ χ_{e_k})` and writes it as
`f + D^*·F + ξ` ((4.25)-(4.26)); "the details are left to the reader". This file proves the
spatial part of the computation at a point `x` of the cluster, for any function `P` in place of
`p̄(t, · - y)`, from the corrector equation at `x` written in divergence form,
`Σ_i (g_{k,i}(x - e_i) - g_{k,i}(x)) = 0` with `g_{k,i} = a_i (δ_{ik} + D_i χ_k)` (`openFlux`):

`Δ (P + Σ_k D_k P χ_k)(x) = Σ_i (F_i(x - e_i) - F_i(x)) + Σ_{k,i} g̃_{k,i}(x) D_i D_k P(x)
  + (σ/2) Σ_k D_k D_k P(x)`,

with `F_i = a_i (D_i D_i P - Σ_k χ_k D_i D_k P)` (`stepOneF`) and `g̃_{k,i} = g_{k,i} - (σ/2) δ_{ik}` the
centered flux (`openLaplacian_twoScale`). Compared with (4.26), the flux term pairs the centered flux
`g̃` itself (not the translated flux `g̃*`) with the forward differences `D_i D_k P`, the divergence
term carries the corrector at the base point of each edge, and the discrete Laplacian of `P` is
`Σ_k D_k D_k P` (forward second differences).
-/

open scoped Classical
open LatticeProb LatticeProb.Percolation

namespace Rigidity.Green

/-- The forward difference `D_k u(x) = u(x + e_k) - u(x)`. -/
noncomputable def fwdDiff (k : Fin 2) (u : Vertex 2 → ℝ) (x : Vertex 2) : ℝ :=
  u (x + unit k) - u x

/-- The flux `g_{k,i}(x) = a_i(x) (δ_{ik} + D_i χ_k(x))` of the corrected plane `x_k + χ_k`. -/
noncomputable def openFlux (ω : Configuration 2) (χ : Fin 2 → Vertex 2 → ℝ) (k i : Fin 2)
    (x : Vertex 2) : ℝ :=
  openCond ω i x * ((if i = k then 1 else 0) + (χ k (x + unit i) - χ k x))

/-- The vector field `F_i = a_i (D_i D_i P - Σ_k χ_k D_i D_k P)` of the divergence term. -/
noncomputable def stepOneF (ω : Configuration 2) (χ : Fin 2 → Vertex 2 → ℝ) (P : Vertex 2 → ℝ)
    (i : Fin 2) (z : Vertex 2) : ℝ :=
  openCond ω i z * (fwdDiff i (fwdDiff i P) z - ∑ k : Fin 2, χ k z * fwdDiff i (fwdDiff k P) z)

theorem centeredFlux_eq_openFlux (ω : Configuration 2) (σ : ℝ) (χ : Fin 2 → Vertex 2 → ℝ)
    (k i : Fin 2) (x : Vertex 2) :
    centeredFlux ω σ χ k i x = openFlux ω χ k i x - σ / 2 * (if i = k then 1 else 0) := by
  unfold centeredFlux openFlux openCond unit
  split_ifs <;> ring

/-- **Step 1 of Proposition 4.3 of Dario–Gu (spatial part)**: the Laplacian of the open graph of
the two-scale expansion `P + Σ_k D_k P χ_k` at a point `x` where the corrector equation holds. -/
theorem openLaplacian_twoScale (ω : Configuration 2) (σ : ℝ) (χ : Fin 2 → Vertex 2 → ℝ)
    (P : Vertex 2 → ℝ) (x : Vertex 2)
    (hχ : ∀ k : Fin 2, ∑ i : Fin 2, (openFlux ω χ k i (x - unit i) - openFlux ω χ k i x) = 0) :
    openLaplacian ω (fun z => P z + ∑ k : Fin 2, fwdDiff k P z * χ k z) x =
      ∑ i : Fin 2, (stepOneF ω χ P i (x - unit i) - stepOneF ω χ P i x) +
        ∑ k : Fin 2, ∑ i : Fin 2, centeredFlux ω σ χ k i x * fwdDiff i (fwdDiff k P) x +
        σ / 2 * ∑ k : Fin 2, fwdDiff k (fwdDiff k P) x := by
  have h0 := hχ 0
  have h1 := hχ 1
  simp only [centeredFlux_eq_openFlux]
  rw [openLaplacian_eq_sum]
  simp only [openFlux, stepOneF, fwdDiff, Fin.sum_univ_two, sub_add_cancel, Fin.isValue,
    if_true, show ((1 : Fin 2) = 0) = False from by decide,
    show ((0 : Fin 2) = 1) = False from by decide, if_false] at h0 h1 ⊢
  linear_combination (P x - P (x + unit 0)) * h0 + (P x - P (x + unit 1)) * h1

end Rigidity.Green
