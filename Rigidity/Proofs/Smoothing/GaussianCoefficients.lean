import Rigidity.Proofs.Smoothing.GaussianSummable
import Mathlib.Analysis.Complex.Basic

/-!
# Summability of Gaussian coefficient families

A positive constant times a Gaussian on a discrete lattice gives summable nonnegative Fourier
coefficients whenever the frequency vectors are distinct. This is the coefficient estimate used in
Micciancio and Regev, *Worst-case to average-case reductions based on Gaussian measures*, SIAM J.
Comput. 37 (2007), Lemma 2.9.
-/

namespace Rigidity.Smoothing

/-- A family with Gaussian lattice values is summable and nonnegative. -/
theorem summable_nonneg_of_gaussian_coefficients {E ι : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L]
    (v : ι → L) (hv : Function.Injective v) {a C : ℝ} (ha : 0 < a) (hC : 0 ≤ C)
    (c : ι → ℂ) (hc : ∀ i, c i = ((C * Real.exp (-a * ‖v i‖ ^ 2) : ℝ) : ℂ)) :
    Summable c ∧ ∀ i, ∃ r : ℝ, 0 ≤ r ∧ c i = r := by
  have hg : Summable (fun i => C * Real.exp (-a * ‖v i‖ ^ 2)) :=
    ((summable_gaussian L ha).comp_injective hv).mul_left C
  have hgc : Summable (fun i => ((C * Real.exp (-a * ‖v i‖ ^ 2) : ℝ) : ℂ)) :=
    Complex.summable_ofReal.mpr hg
  refine ⟨hgc.congr (fun i => (hc i).symm), ?_⟩
  intro i
  exact ⟨_, mul_nonneg hC (Real.exp_pos _).le, hc i⟩

end Rigidity.Smoothing
