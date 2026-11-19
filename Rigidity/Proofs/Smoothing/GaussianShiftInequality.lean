import Rigidity.Proofs.Smoothing.GaussianTorusCoefficients
import Rigidity.Proofs.Smoothing.GaussianTorusMaximum
import Rigidity.Proofs.Smoothing.GaussianCoefficients

/-!
# The lattice Gaussian shift inequality

The Gaussian mass of a translate of a lattice does not exceed the mass of the lattice itself.
This is Micciancio and Regev, *Worst-case to average-case reductions based on Gaussian measures*,
SIAM J. Comput. 37 (2007), Lemma 2.9, proved using the Gaussian Fourier transform.
-/

open MeasureTheory Module
open scoped FourierTransform

namespace Rigidity.Smoothing

/-- A shifted lattice Gaussian has no more mass than the unshifted Gaussian. -/
theorem gaussian_shift_le {E d : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype d]
    (b : Basis d ℝ E) {a : ℝ} (ha : 0 < a) (x : E) :
    Summable (fun z : Submodule.span ℤ (Set.range b) => Real.exp (-a * ‖(z : E) + x‖ ^ 2)) ∧
    Summable (fun z : Submodule.span ℤ (Set.range b) => Real.exp (-a * ‖(z : E)‖ ^ 2)) ∧
    (∑' z : Submodule.span ℤ (Set.range b), Real.exp (-a * ‖(z : E) + x‖ ^ 2)) ≤
      ∑' z : Submodule.span ℤ (Set.range b), Real.exp (-a * ‖(z : E)‖ ^ 2) := by
  obtain ⟨g, hg⟩ := exists_gaussian_torus b ha
  obtain ⟨C, hC, hcoeff⟩ := gaussian_torus_coefficients b ha g hg
  let L : Submodule ℤ E := Submodule.span ℤ (Set.range (frequencyBasis b))
  let v : (d → ℤ) → L := fun n => ⟨dualFrequency b n, dualFrequency_mem_span b n⟩
  have hv : Function.Injective v := by
    intro n m h
    apply dualFrequency_injective b
    exact congrArg Subtype.val h
  let A : ℝ := Real.pi ^ 2 / a
  let D : ℝ := C * (Real.pi / a) ^ (Module.finrank ℝ E / 2 : ℝ)
  have hA : 0 < A := by dsimp [A]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hformula (n : d → ℤ) : UnitAddTorus.mFourierCoeff g n =
      ((D * Real.exp (-A * ‖v n‖ ^ 2) : ℝ) : ℂ) := by
    rw [hcoeff n, fourier_gaussian_innerProductSpace (by simpa using ha)]
    dsimp only [D, A, v]
    simp only [Submodule.coe_norm]
    rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_cpow (by positivity),
      Complex.ofReal_exp, Complex.real_smul]
    push_cast
    ring_nf
  obtain ⟨hs, hn⟩ := summable_nonneg_of_gaussian_coefficients L v hv hA hD _ hformula
  exact gaussian_shift_le_of_fourier_nonneg b ha g hg hs hn x

end Rigidity.Smoothing
