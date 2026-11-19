import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# A maximum principle for nonnegative Fourier coefficients

A continuous function on a finite-dimensional torus whose Fourier coefficients are summable and
nonnegative attains its maximum norm at the origin. This is the Fourier-positivity step in the
Gaussian shift inequality of Micciancio and Regev, *Worst-case to average-case reductions based on
Gaussian measures*, SIAM J. Comput. 37 (2007), Lemma 2.9.
-/

namespace Rigidity.Smoothing

/-- A summable nonnegative Fourier series has maximum norm at the origin. -/
theorem norm_le_re_zero_of_nonneg_fourier {d : Type*} [Fintype d]
    (f : C(UnitAddTorus d, ℂ)) (hs : Summable (UnitAddTorus.mFourierCoeff f))
    (hnonneg : ∀ n, ∃ c : ℝ, 0 ≤ c ∧ UnitAddTorus.mFourierCoeff f n = c)
    (x : UnitAddTorus d) : ‖f x‖ ≤ (f 0).re := by
  have hz : HasSum (fun n => (UnitAddTorus.mFourierCoeff f n).re) (f 0).re := by
    have h := Complex.hasSum_re (UnitAddTorus.hasSum_mFourier_series_apply_of_summable hs 0)
    simpa only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.zero_apply, fourier_eval_zero,
      Finset.prod_const_one, smul_eq_mul, mul_one] using h
  have hx := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hs x
  refine hx.norm_le_of_bounded hz fun n => ?_
  obtain ⟨c, hc, hcoeff⟩ := hnonneg n
  have hnorm : ‖UnitAddTorus.mFourier n x‖ = 1 := by
    simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, norm_prod, fourier_apply,
      Circle.norm_coe, Finset.prod_const_one]
  rw [hcoeff, smul_eq_mul, norm_mul, hnorm, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hc, Complex.ofReal_re]

end Rigidity.Smoothing
