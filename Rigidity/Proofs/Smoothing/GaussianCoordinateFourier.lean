import Rigidity.Proofs.Smoothing.HaarChangeOfVariables
import Rigidity.Proofs.Smoothing.DualFrequencies
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Gaussian Fourier integrals in lattice coordinates

A Gaussian Fourier integral in coordinates of a lattice basis is a positive constant times the
Fourier transform at the corresponding dual frequency. This is the change-of-variables step in
Micciancio and Regev, *Worst-case to average-case reductions based on Gaussian measures*, SIAM J.
Comput. 37 (2007), Lemma 2.9.
-/

open MeasureTheory Module
open scoped FourierTransform

namespace Rigidity.Smoothing

/-- Gaussian Fourier integrals in basis coordinates differ by a positive constant. -/
theorem exists_gaussian_coordinate_fourier {E d : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Fintype d] (b : Basis d ℝ E) (a : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : d → ℤ,
      (∫ x : d → ℝ,
        Complex.exp (((-2 * Real.pi * ∑ i, x i * (n i : ℝ) : ℝ) : ℂ) * Complex.I) *
          Complex.exp (-(a : ℂ) * ‖b.equivFun.symm x‖ ^ 2)) =
        C • 𝓕 (fun y : E => Complex.exp (-(a : ℂ) * ‖y‖ ^ 2)) (dualFrequency b n) := by
  obtain ⟨C, hC, hchange⟩ := exists_integral_comp_linearEquiv
    (volume : Measure (d → ℝ)) (volume : Measure E) b.equivFun.symm
  refine ⟨C, hC, ?_⟩
  intro n
  let f : E → ℂ := fun y =>
    Complex.exp (((-2 * Real.pi * inner ℝ y (dualFrequency b n) : ℝ) : ℂ) * Complex.I) *
      Complex.exp (-(a : ℂ) * ‖y‖ ^ 2)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hphase (x : d → ℝ) : inner ℝ (b.equivFun.symm x) (dualFrequency b n) =
      ∑ i, x i * (n i : ℝ) := by
    rw [real_inner_comm, inner_dualFrequency_equivFun_symm]
  simpa only [Real.fourier_eq', f, smul_eq_mul, hphase] using hchange f hf

end Rigidity.Smoothing
