import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# Fourier characters in torus coordinates

The Fourier character of an integer frequency on the coordinate torus is the exponential of its
coordinate pairing. This identifies the Fourier integrand in the lattice Gaussian argument of
Micciancio and Regev, *Worst-case to average-case reductions based on Gaussian measures*, SIAM J.
Comput. 37 (2007), Lemma 2.9.
-/

namespace Rigidity.Smoothing

/-- The negative torus Fourier character is the exponential of the coordinate pairing. -/
theorem mFourier_neg_coe {d : Type*} [Fintype d] (n : d → ℤ) (x : d → ℝ) :
    UnitAddTorus.mFourier (-n) (fun i => (x i : UnitAddCircle)) =
      Complex.exp (((-2 * Real.pi * ∑ i, x i * (n i : ℝ) : ℝ) : ℂ) * Complex.I) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.neg_apply, fourier_coe_apply,
    Int.cast_neg, ← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

end Rigidity.Smoothing
