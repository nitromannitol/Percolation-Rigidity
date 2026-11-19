import Rigidity.Proofs.Smoothing.HaarIntegrable
import Rigidity.Proofs.Smoothing.GaussianCoordinateFourier

/-!
# Integrability of coordinate Gaussian Fourier integrands

A Gaussian times a Fourier character remains integrable after a linear change to lattice basis
coordinates. This is used to unfold the Gaussian periodization in Micciancio and Regev,
*Worst-case to average-case reductions based on Gaussian measures*, SIAM J. Comput. 37 (2007),
Lemma 2.9.
-/

open MeasureTheory Module

namespace Rigidity.Smoothing

/-- Gaussian Fourier integrands are integrable in basis coordinates. -/
theorem integrable_gaussian_coordinate_fourier {E d : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Fintype d] (b : Basis d ℝ E) {a : ℝ} (ha : 0 < a) (n : d → ℤ) :
    Integrable (fun x : d → ℝ =>
      Complex.exp (((-2 * Real.pi * ∑ i, x i * (n i : ℝ) : ℝ) : ℂ) * Complex.I) *
        Complex.exp (-(a : ℂ) * ‖b.equivFun.symm x‖ ^ 2)) := by
  have hb : 0 < (a : ℂ).re := by simpa using ha
  have hbase := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := E) hb
    (-2 * (Real.pi : ℂ) * Complex.I) (dualFrequency b n)
  have hcomp := integrable_comp_linearEquiv (volume : Measure (d → ℝ))
    (volume : Measure E) b.equivFun.symm hbase
  apply hcomp.congr
  filter_upwards [] with x
  simp only [← Complex.exp_add]
  rw [inner_dualFrequency_equivFun_symm]
  congr 1
  push_cast
  ring

end Rigidity.Smoothing
