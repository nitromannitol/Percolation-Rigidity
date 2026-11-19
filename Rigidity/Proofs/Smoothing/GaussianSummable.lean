import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Gaussian sums on discrete submodules

A Gaussian is summable on a discrete integer submodule of a finite-dimensional real normed space.
This provides convergence for lattice Gaussian sums in the argument of Micciancio and Regev,
*Worst-case to average-case reductions based on Gaussian measures*, SIAM J. Comput. 37 (2007),
Lemma 3.3.
-/

open Filter Asymptotics

namespace Rigidity.Smoothing

/-- Gaussian decay gives a summable function on a discrete integer submodule. -/
theorem summable_gaussian {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] {a : ℝ} (ha : 0 < a) :
    Summable (fun x : L => Real.exp (-a * ‖x‖ ^ 2)) := by
  let r : ℝ := -(Module.finrank ℤ L : ℝ) - 1
  have hr : r < -(Module.finrank ℤ L : ℝ) := by dsimp [r]; linarith
  have hclosed : IsClosed (L : Set E) :=
    @AddSubgroup.isClosed_of_discrete _ _ _ _ _ L.toAddSubgroup inferInstance
  have ht : Tendsto (fun x : L => ‖x‖) cofinite atTop :=
    tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding
      (e := fun x : L => (x : E)) hclosed.isClosedEmbedding_subtypeVal
  have hbound : ∀ᶠ x : L in cofinite, Real.exp (-a * ‖x‖ ^ 2) ≤ ‖x‖ ^ r := by
    have h₁ := ht.eventually ((isLittleO_exp_neg_mul_rpow_atTop ha r).bound (by norm_num : (0 : ℝ) < 1))
    filter_upwards [h₁, ht.eventually (eventually_ge_atTop (1 : ℝ))] with x hx hx1
    have hx' : Real.exp (-a * ‖x‖) ≤ ‖x‖ ^ r := by
      simpa only [one_mul, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le,
        abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)] using hx
    calc
      Real.exp (-a * ‖x‖ ^ 2) ≤ Real.exp (-a * ‖x‖) := by
        apply Real.exp_le_exp.mpr
        nlinarith [sq_nonneg (‖x‖ - 1)]
      _ ≤ ‖x‖ ^ r := hx'
  apply Summable.of_norm_bounded_eventually (ZLattice.summable_norm_rpow L r hr)
  filter_upwards [hbound] with x hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le] using hx

end Rigidity.Smoothing
