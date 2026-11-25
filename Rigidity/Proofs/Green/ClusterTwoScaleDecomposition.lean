import Rigidity.Proofs.Green.DarioGuTwoScaleCorrectorEq

/-!
# The equation of the two-scale expansion with a cutoff (Step 3 of Theorem 5 of Dario–Gu)

Step 3 of the proof of Theorem 5 of Dario–Gu (lines 1454-1490 of the source, (3.23)-(3.25))
computes `(∂_t - ∇·a∇) w` for the two-scale expansion `w = ū + Υ Σ_k D_k ū χ_{e_k}` of (3.22) and
writes it as a sum of six terms. This file proves the computation at a point `x` of the cluster for
unit conductances, for any functions `U` (in place of `ū(t, ·)` at the lattice points) and `F_k`
(in place of `Υ D_k ū`), from the corrector equation at `x` in divergence form
(`sum_openFlux_div_eq_zero`):

`Δ (U + Σ_k F_k χ_k)(x) = Σ_i (H_i(x) - H_i(x - e_i)) + Σ_{k,i} g̃_{k,i}(x) D_i F_k(x)
  + (σ/2) Σ_k D_k F_k(x)`,

with `H_i(z) = a_i(z) (D_i U(z) - F_i(z + e_i) + Σ_k χ_k(z) D_i F_k(z))` (`cutoffField`) and the
centered flux `g̃_{k,i}` (`openLaplacian_cutoffTwoScale`). For `F_k = Υ D_k U`,
`H_i = a_i ((1 - Υ) D_i U - D_i F_i + Σ_k χ_k D_i F_k)` (`cutoffField_of_cutoff`): the divergence of
the first part is the term (3.25)-c1, the flux term is (3.25)-d and the rest is of the form
(3.25)-e. Compared with (3.23)-(3.24), the flux term pairs the centered flux `g̃` itself (not the
translated flux `g̃*`) with the forward differences `D_i F_k`, the divergence term carries the
corrector at the base point of each edge and the extra field `-a_i D_i F_i`, and the discrete
Laplacian is `Σ_k D_k F_k` (forward differences). The left side of (3.25) is printed with the
operator `∂_t - D^*·a D`; the computation (3.23) is for `∂_t + D^*·a D = ∂_t - ∇·a∇`.

`timeDeriv_sub_openLaplacian_cutoffTwoScale` adds the time derivative: if `∂_t U(x) = (σ/2) L`
(the equation (3.9) of `ū` with `L = Δū(t, x)`, written `L = L_in + L_out`), then
`∂_t w - Δw` is the sum of `(σ/2)(L_in - Σ_k D_k F_k)` (the term (3.25)-a for `L_in = ∇·(Υ∇ū)`),
`(σ/2) L_out` ((3.25)-c2 for `L_out = ∇·((1 - Υ)∇ū)`), `Σ_k ∂_t F_k χ_k` ((3.25)-b), and the
divergence and flux terms above.
-/

open scoped Classical
open LatticeProb LatticeProb.Percolation

namespace Rigidity.Green

/-- The field `H_i(z) = a_i(z) (D_i U(z) - F_i(z + e_i) + Σ_k χ_k(z) D_i F_k(z))` of the divergence
term of the two-scale expansion `U + Σ_k F_k χ_k`. -/
noncomputable def cutoffField (ω : Configuration 2) (χ : Fin 2 → Vertex 2 → ℝ)
    (U : Vertex 2 → ℝ) (F : Fin 2 → Vertex 2 → ℝ) (i : Fin 2) (z : Vertex 2) : ℝ :=
  openCond ω i z * (fwdDiff i U z - F i (z + unit i) + ∑ k : Fin 2, χ k z * fwdDiff i (F k) z)

/-- **The Laplacian of the two-scale expansion with general coefficients** (Dario–Gu, (3.23)-(3.24),
spatial part) at a point `x` where the corrector equation holds. -/
theorem openLaplacian_cutoffTwoScale (ω : Configuration 2) (σ : ℝ) (χ : Fin 2 → Vertex 2 → ℝ)
    (U : Vertex 2 → ℝ) (F : Fin 2 → Vertex 2 → ℝ) (x : Vertex 2)
    (hχ : ∀ k : Fin 2, ∑ i : Fin 2, (openFlux ω χ k i (x - unit i) - openFlux ω χ k i x) = 0) :
    openLaplacian ω (fun z => U z + ∑ k : Fin 2, F k z * χ k z) x =
      ∑ i : Fin 2, (cutoffField ω χ U F i x - cutoffField ω χ U F i (x - unit i)) +
        ∑ k : Fin 2, ∑ i : Fin 2, centeredFlux ω σ χ k i x * fwdDiff i (F k) x +
        σ / 2 * ∑ k : Fin 2, fwdDiff k (F k) x := by
  have h0 := hχ 0
  have h1 := hχ 1
  simp only [centeredFlux_eq_openFlux]
  rw [openLaplacian_eq_sum]
  simp only [openFlux, cutoffField, fwdDiff, Fin.sum_univ_two, sub_add_cancel, Fin.isValue,
    if_true, show ((1 : Fin 2) = 0) = False from by decide,
    show ((0 : Fin 2) = 1) = False from by decide, if_false] at h0 h1 ⊢
  linear_combination (-F 0 x) * h0 + (-F 1 x) * h1

/-- The same identity for the corrector of the cluster (`IsDGCorrector`) at a point of the
cluster. -/
theorem openLaplacian_cutoffTwoScale_of_corrector {ω : Configuration 2} {K : OpenComponent ω}
    {y : Vertex 2} {χ : Fin 2 → Vertex 2 → ℝ} (hχ : Rigidity.Green.IsDGCorrector K y χ) (σ : ℝ)
    (U : Vertex 2 → ℝ) (F : Fin 2 → Vertex 2 → ℝ) {x : Vertex 2} (hx : x ∈ K.supp) :
    openLaplacian ω (fun z => U z + ∑ k : Fin 2, F k z * χ k z) x =
      ∑ i : Fin 2, (cutoffField ω χ U F i x - cutoffField ω χ U F i (x - unit i)) +
        ∑ k : Fin 2, ∑ i : Fin 2, centeredFlux ω σ χ k i x * fwdDiff i (F k) x +
        σ / 2 * ∑ k : Fin 2, fwdDiff k (F k) x :=
  openLaplacian_cutoffTwoScale ω σ χ U F x (sum_openFlux_div_eq_zero hχ hx)

/-- For the coefficients `F_k = Υ D_k U` of (3.22), the divergence field is
`H_i = a_i ((1 - Υ) D_i U - D_i F_i + Σ_k χ_k D_i F_k)`. -/
theorem cutoffField_of_cutoff (ω : Configuration 2) (χ : Fin 2 → Vertex 2 → ℝ)
    (U Υ : Vertex 2 → ℝ) (i : Fin 2) (z : Vertex 2) :
    cutoffField ω χ U (fun k w => Υ w * fwdDiff k U w) i z =
      openCond ω i z * ((1 - Υ z) * fwdDiff i U z - fwdDiff i (fun w => Υ w * fwdDiff i U w) z +
        ∑ k : Fin 2, χ k z * fwdDiff i (fun w => Υ w * fwdDiff k U w) z) := by
  unfold cutoffField
  congr 1
  simp only [fwdDiff]
  ring

/-- The time derivative of the two-scale expansion `U + Σ_k F_k χ_k` at a lattice point. -/
theorem hasDerivAt_cutoffTwoScale {U : ℝ → Vertex 2 → ℝ} {F : Fin 2 → ℝ → Vertex 2 → ℝ}
    (χ : Fin 2 → Vertex 2 → ℝ) {x : Vertex 2} {t U' : ℝ} {F' : Fin 2 → ℝ}
    (hU : HasDerivAt (fun s => U s x) U' t) (hF : ∀ k, HasDerivAt (fun s => F k s x) (F' k) t) :
    HasDerivAt (fun s => U s x + ∑ k : Fin 2, F k s x * χ k x)
      (U' + ∑ k : Fin 2, F' k * χ k x) t :=
  hU.add (HasDerivAt.fun_sum fun k _ => (hF k).mul_const (χ k x))

/-- **Dario–Gu, (3.25)** at a point `x` where the corrector equation holds, for unit
conductances: if `∂_t U(x) = (σ/2) (L_in + L_out)` (the equation (3.9)), then `∂_t w - Δ w` for
`w = U + Σ_k F_k χ_k` is the sum of `(σ/2) (L_in - Σ_k D_k F_k)` (the term a), `Σ_k ∂_t F_k χ_k`
(b), `(σ/2) L_out` (c2), `-Σ_i (H_i(x) - H_i(x - e_i))` (c1 and e) and
`-Σ_{k,i} g̃_{k,i} D_i F_k` (d). -/
theorem timeDeriv_sub_openLaplacian_cutoffTwoScale (ω : Configuration 2) (σ : ℝ)
    (χ : Fin 2 → Vertex 2 → ℝ) (U : Vertex 2 → ℝ) (F : Fin 2 → Vertex 2 → ℝ) (x : Vertex 2)
    (hχ : ∀ k : Fin 2, ∑ i : Fin 2, (openFlux ω χ k i (x - unit i) - openFlux ω χ k i x) = 0)
    {U' Lin Lout : ℝ} (F' : Fin 2 → ℝ) (hU' : U' = σ / 2 * (Lin + Lout)) :
    (U' + ∑ k : Fin 2, F' k * χ k x) -
        openLaplacian ω (fun z => U z + ∑ k : Fin 2, F k z * χ k z) x =
      σ / 2 * (Lin - ∑ k : Fin 2, fwdDiff k (F k) x) + ∑ k : Fin 2, F' k * χ k x +
        σ / 2 * Lout -
        ∑ i : Fin 2, (cutoffField ω χ U F i x - cutoffField ω χ U F i (x - unit i)) -
        ∑ k : Fin 2, ∑ i : Fin 2, centeredFlux ω σ χ k i x * fwdDiff i (F k) x := by
  rw [openLaplacian_cutoffTwoScale ω σ χ U F x hχ, hU']
  ring

end Rigidity.Green
