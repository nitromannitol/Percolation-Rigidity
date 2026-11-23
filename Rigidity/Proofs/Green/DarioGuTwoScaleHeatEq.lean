import Rigidity.Proofs.Green.DarioGuTwoScaleCorrectorEq
import Rigidity.Proofs.Green.DarioGuTwoScaleTime

/-!
# The equation of the two-scale expansion on the cluster (Step 1 of Proposition 4.3)

At a point `x` of the cluster, the two-scale expansion `h(t, ·, y)` of (4.1) satisfies
`∂_t h(t, x, y) = Δh(t, ·, y)(x) + θ^{-1} G(t, x)` (`hasDerivAt_dgTwoScale_eq`), where, with
`P = p̄(t, · - y)` on the lattice,
`G = (∂_t P - (σ/2) Σ_k D_k D_k P) + Σ_k ∂_t D_k P χ_k - Σ_i (F_i(x - e_i) - F_i(x)) - Σ_{k,i} g̃_{k,i} D_i D_k P`
(`twoScaleSource`): the terms `f`, `D^*·F` and `ξ` of (4.25)-(4.26) of Dario–Gu in the form of
`openLaplacian_twoScale`.
-/

open scoped Classical
open LatticeProb LatticeProb.Percolation Rigidity.External

namespace Rigidity.Green

theorem openLaplacian_const_mul (ω : Configuration 2) (c : ℝ) (u : Vertex 2 → ℝ) (x : Vertex 2) :
    openLaplacian ω (fun z => c * u z) x = c * openLaplacian ω u x := by
  unfold openLaplacian
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- The source term `G` of the equation of the two-scale expansion (see the module docstring). -/
noncomputable def twoScaleSource (ω : Configuration 2) (σ : ℝ) (χ : Fin 2 → Vertex 2 → ℝ)
    (t : ℝ) (y x : Vertex 2) : ℝ :=
  (latticeGaussianTimeDeriv σ t x y -
      σ / 2 * ∑ k : Fin 2, fwdDiff k (fwdDiff k fun z => latticeGaussian σ t z y) x) +
    ∑ k : Fin 2, fwdDiff k (fun z => latticeGaussianTimeDeriv σ t z y) x * χ k x -
    ∑ i : Fin 2, (stepOneF ω χ (fun z => latticeGaussian σ t z y) i (x - unit i) -
      stepOneF ω χ (fun z => latticeGaussian σ t z y) i x) -
    ∑ k : Fin 2, ∑ i : Fin 2, centeredFlux ω σ χ k i x *
      fwdDiff i (fwdDiff k fun z => latticeGaussian σ t z y) x

/-- **Step 1 of Proposition 4.3 of Dario–Gu** for the two-scale expansion: at `x ∈ 𝒞_∞`,
`∂_t h(t, x, y) = Δ h(t, ·, y)(x) + θ^{-1} G(t, x)`. -/
theorem hasDerivAt_dgTwoScale_eq {ω : Configuration 2} {K : OpenComponent ω} {y : Vertex 2}
    {χ : Fin 2 → Vertex 2 → ℝ} (hχ : IsDGCorrector K y χ) {σ θ t : ℝ} (hσ : 0 < σ) (ht : 0 < t)
    {x : Vertex 2} (hx : x ∈ K.supp) :
    HasDerivAt (fun s => dgTwoScale σ θ χ s x y)
      (openLaplacian ω (fun z => dgTwoScale σ θ χ t z y) x +
        θ⁻¹ * twoScaleSource ω σ χ t y x) t := by
  refine (hasDerivAt_dgTwoScale_time hσ ht χ x y).congr_deriv ?_
  have hL := openLaplacian_twoScale_of_corrector hχ σ (fun z => latticeGaussian σ t z y) hx
  have e : (fun z => dgTwoScale σ θ χ t z y) = fun z => θ⁻¹ *
      ((fun z => latticeGaussian σ t z y) z + ∑ k : Fin 2,
        fwdDiff k (fun z => latticeGaussian σ t z y) z * χ k z) := by
    funext z
    rfl
  rw [e, openLaplacian_const_mul, hL]
  unfold twoScaleSource
  simp only [fwdDiff, unit, Fin.sum_univ_two]
  ring

end Rigidity.Green
