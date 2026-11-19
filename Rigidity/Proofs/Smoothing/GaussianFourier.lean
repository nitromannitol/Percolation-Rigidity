import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Positivity of Gaussian Fourier transforms

The Fourier transform of a positive Gaussian on a finite-dimensional real inner-product space is
positive. This is the positivity ingredient in the lattice Gaussian shift inequality of
Micciancio and Regev, *Worst-case to average-case reductions based on Gaussian measures*, SIAM J.
Comput. 37 (2007), Lemma 2.9.
-/

open scoped FourierTransform

namespace Rigidity.Smoothing

/-- The Fourier transform of a Gaussian is a positive real number. -/
theorem gaussian_fourier_pos {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {a : ℝ} (ha : 0 < a) (w : E) :
    ∃ c : ℝ, 0 < c ∧ 𝓕 (fun v : E => Complex.exp (-(a : ℂ) * ‖v‖ ^ 2)) w = c := by
  refine ⟨(Real.pi / a) ^ (Module.finrank ℝ E / 2 : ℝ) *
    Real.exp (-(Real.pi ^ 2 * ‖w‖ ^ 2) / a), by positivity, ?_⟩
  rw [fourier_gaussian_innerProductSpace (by simpa using ha)]
  rw [Complex.ofReal_mul, Complex.ofReal_cpow (by positivity), Complex.ofReal_exp]
  push_cast
  ring_nf

end Rigidity.Smoothing
