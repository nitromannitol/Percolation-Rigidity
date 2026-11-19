import Rigidity.Proofs.Smoothing.GaussianShift

/-!
# Periodicity of lattice Gaussian sums

The lattice Gaussian periodization is summable at every point and invariant under translations by
lattice vectors, as needed for the Gaussian shift argument of Micciancio and Regev, *Worst-case to
average-case reductions based on Gaussian measures*, SIAM J. Comput. 37 (2007), Lemma 2.9.
-/

namespace Rigidity.Smoothing

/-- A shifted lattice Gaussian is summable. -/
theorem summable_gaussian_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] {a : ℝ} (ha : 0 < a)
    (x : E) : Summable (fun z : L => Real.exp (-a * ‖(z : E) + x‖ ^ 2)) := by
  have hsum : Summable (fun z : L => Real.exp (a * ‖x‖ ^ 2) *
      Real.exp (-(a / 2) * ‖z‖ ^ 2)) :=
    (summable_gaussian L (show 0 < a / 2 by positivity)).mul_left _
  refine hsum.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) ?_
  intro z
  simpa only [Submodule.coe_norm] using
    exp_neg_norm_add_sq_le ha.le (norm_nonneg x) (z : E) x (le_refl _)

/-- Translating the argument by a lattice vector leaves the Gaussian periodization unchanged. -/
theorem tsum_gaussian_add_lattice {E : Type*} [NormedAddCommGroup E] (L : Submodule ℤ E)
    (a : ℝ) (x : E) (v : L) :
    (∑' z : L, Real.exp (-a * ‖(z : E) + (x + v)‖ ^ 2)) =
      ∑' z : L, Real.exp (-a * ‖(z : E) + x‖ ^ 2) := by
  simpa only [Equiv.coe_addRight, Submodule.coe_add, add_assoc, add_comm, add_left_comm] using
    (Equiv.addRight v).tsum_eq (fun z : L => Real.exp (-a * ‖(z : E) + x‖ ^ 2))

end Rigidity.Smoothing
