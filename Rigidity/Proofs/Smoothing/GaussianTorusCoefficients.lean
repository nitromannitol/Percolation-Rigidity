import Rigidity.Proofs.Smoothing.GaussianTorus
import Rigidity.Proofs.Smoothing.IntegerCoordinates
import Rigidity.Proofs.Smoothing.TorusPeriodizationIntegral
import Rigidity.Proofs.Smoothing.TorusCharacters
import Rigidity.Proofs.Smoothing.GaussianCoordinateIntegrable

/-!
# Fourier coefficients of a lattice Gaussian

The Fourier coefficients of the lattice Gaussian periodization are the Gaussian Fourier transform
at the dual frequencies, multiplied by a positive constant depending only on the lattice basis.
This is the Poisson summation step in Micciancio and Regev, *Worst-case to average-case reductions
based on Gaussian measures*, SIAM J. Comput. 37 (2007), Lemma 2.9.
-/

open MeasureTheory Module
open scoped FourierTransform

namespace Rigidity.Smoothing

/-- Fourier coefficients of a periodized Gaussian are scaled values at the dual frequencies. -/
theorem gaussian_torus_coefficients {E d : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Fintype d] (b : Basis d ℝ E) {a : ℝ} (ha : 0 < a) (g : C(UnitAddTorus d, ℂ))
    (hg : ∀ x : d → ℝ, g (fun i => (x i : UnitAddCircle)) =
      ((∑' z : Submodule.span ℤ (Set.range b),
        Real.exp (-a * ‖(z : E) + b.equivFun.symm x‖ ^ 2) : ℝ) : ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : d → ℤ,
      UnitAddTorus.mFourierCoeff g n =
        C • 𝓕 (fun y : E => Complex.exp (-(a : ℂ) * ‖y‖ ^ 2)) (dualFrequency b n) := by
  classical
  let b0 : Basis d ℝ (d → ℝ) := Pi.basisFun ℝ d
  let L0 : Submodule ℤ (d → ℝ) := Submodule.span ℤ (Set.range b0)
  let L1 : Submodule ℤ E := Submodule.span ℤ (Set.range b)
  let e : L0 ≃ L1 := (integerCoordinates b0).symm.trans (integerCoordinates b)
  have he (z : L0) : ((e z : L1) : E) = b.equivFun.symm (z : d → ℝ) := by
    let k := (integerCoordinates b0).symm z
    have hk : (fun i => (k i : ℝ)) = (z : d → ℝ) := by
      have h := (coe_integerCoordinates b0 k).symm
      simpa only [b0, Pi.basisFun_equivFun, LinearEquiv.refl_symm, LinearEquiv.refl_apply,
        k, Equiv.apply_symm_apply] using h
    change (integerCoordinates b k : E) = _
    rw [coe_integerCoordinates, hk]
  let H : (d → ℝ) → ℂ := fun x => ((Real.exp (-a * ‖b.equivFun.symm x‖ ^ 2) : ℝ) : ℂ)
  have hper : ∀ x : d → ℝ, g (fun i => (x i : UnitAddCircle)) =
      ∑' z : L0, H ((z : d → ℝ) + x) := by
    intro x
    calc
      g (fun i => (x i : UnitAddCircle)) =
          ∑' z : L1, ((Real.exp (-a * ‖(z : E) + b.equivFun.symm x‖ ^ 2) : ℝ) : ℂ) := by
        rw [hg x, Complex.ofReal_tsum]
      _ = ∑' z : L0,
          ((Real.exp (-a * ‖((e z : L1) : E) + b.equivFun.symm x‖ ^ 2) : ℝ) : ℂ) :=
        (e.tsum_eq _).symm
      _ = ∑' z : L0, H ((z : d → ℝ) + x) := by
        apply tsum_congr
        intro z
        simp only [H, he, map_add]
  obtain ⟨C, hC, hfourier⟩ := exists_gaussian_coordinate_fourier b a
  refine ⟨C, hC, ?_⟩
  intro n
  have hint : Integrable (fun x : d → ℝ =>
      UnitAddTorus.mFourier (-n) (fun i => (x i : UnitAddCircle)) * H x) := by
    simpa only [mFourier_neg_coe, H, Complex.ofReal_exp, Complex.ofReal_neg,
      Complex.ofReal_mul, Complex.ofReal_pow] using integrable_gaussian_coordinate_fourier b ha n
  rw [mFourierCoeff_eq_integral_of_periodization g H hper n hint]
  simpa only [mFourier_neg_coe, H, Complex.ofReal_exp, Complex.ofReal_neg,
    Complex.ofReal_mul, Complex.ofReal_pow] using hfourier n

end Rigidity.Smoothing
