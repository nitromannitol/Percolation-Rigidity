import Rigidity.Proofs.Smoothing.GaussianTorus
import Rigidity.Proofs.Smoothing.FourierMaximum

/-!
# The Fourier criterion for the lattice Gaussian shift inequality

If the Fourier coefficients of the torus periodization are summable and nonnegative, the lattice
Gaussian is maximal at the origin. This is the Fourier comparison in Micciancio and Regev,
*Worst-case to average-case reductions based on Gaussian measures*, SIAM J. Comput. 37 (2007),
Lemma 2.9.
-/

open Module

namespace Rigidity.Smoothing

/-- Nonnegative summable torus Fourier coefficients imply the Gaussian shift inequality. -/
theorem gaussian_shift_le_of_fourier_nonneg {E d : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Fintype d] (b : Basis d ℝ E) {a : ℝ}
    (ha : 0 < a) (g : C(UnitAddTorus d, ℂ))
    (hg : ∀ x : d → ℝ, g (fun i => (x i : UnitAddCircle)) =
      ((∑' z : Submodule.span ℤ (Set.range b),
        Real.exp (-a * ‖(z : E) + b.equivFun.symm x‖ ^ 2) : ℝ) : ℂ))
    (hs : Summable (UnitAddTorus.mFourierCoeff g))
    (hnonneg : ∀ n, ∃ c : ℝ, 0 ≤ c ∧ UnitAddTorus.mFourierCoeff g n = c) (x : E) :
    Summable (fun z : Submodule.span ℤ (Set.range b) => Real.exp (-a * ‖(z : E) + x‖ ^ 2)) ∧
    Summable (fun z : Submodule.span ℤ (Set.range b) => Real.exp (-a * ‖(z : E)‖ ^ 2)) ∧
    (∑' z : Submodule.span ℤ (Set.range b), Real.exp (-a * ‖(z : E) + x‖ ^ 2)) ≤
      ∑' z : Submodule.span ℤ (Set.range b), Real.exp (-a * ‖(z : E)‖ ^ 2) := by
  refine ⟨summable_gaussian_add _ ha x, summable_gaussian _ ha, ?_⟩
  have h := norm_le_re_zero_of_nonneg_fourier g hs hnonneg
    (fun i => (b.equivFun x i : UnitAddCircle))
  have hz : g 0 = ((∑' z : Submodule.span ℤ (Set.range b),
      Real.exp (-a * ‖(z : E) + b.equivFun.symm 0‖ ^ 2) : ℝ) : ℂ) := by
    simpa only [Pi.zero_apply, AddCircle.coe_zero, ← Pi.zero_def] using hg 0
  have hx := hg (b.equivFun x)
  have hsum : 0 ≤ ∑' z : Submodule.span ℤ (Set.range b),
      Real.exp (-a * ‖(z : E) + x‖ ^ 2) := tsum_nonneg fun _ => (Real.exp_pos _).le
  rw [hx] at h
  simp only [LinearEquiv.symm_apply_apply] at h
  rw [hz] at h
  simpa only [LinearEquiv.map_zero, add_zero, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hsum, Complex.ofReal_re] using h

end Rigidity.Smoothing
