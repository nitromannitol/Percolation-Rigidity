import Mathlib.Tactic

/-!
# The final Gaussian mass estimate

The algebraic rearrangement in Micciancio and Regev, *Worst-case to average-case reductions
based on Gaussian measures*, SIAM J. Comput. 37 (2007), Lemma 3.3, converts a bound on the
fraction of mass outside the origin into the desired upper bound.
-/

namespace Rigidity.Smoothing

/-- A bound on the fraction of mass away from the origin controls that mass. -/
theorem le_of_le_fraction_mul_one_add {ε p u : ℝ} (hε : 0 < ε)
    (hp : p ≤ ε / (1 + ε)) (hu : u ≤ p * (1 + u)) : u ≤ ε := by
  have hden : 0 < 1 + ε := by linarith
  have hp' : p * (1 + ε) ≤ ε := (le_div_iff₀ hden).mp hp
  have hp1 : p < 1 := by
    by_contra h
    have hm : 0 ≤ (p - 1) * ε := mul_nonneg (by linarith) (le_of_lt hε)
    nlinarith
  by_contra h
  have hm : 0 < (1 - p) * (u - ε) := mul_pos (by linarith) (by linarith)
  nlinarith

end Rigidity.Smoothing
