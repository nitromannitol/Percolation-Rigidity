import Rigidity.Proofs.Smoothing.DualSummable
import Rigidity.Proofs.Smoothing.ZeroRank

/-!
# Convergence at the smoothing scale

The scale in Micciancio and Regev, *Worst-case to average-case reductions based on Gaussian
measures*, SIAM J. Comput. 37 (2007), Lemma 3.3, is positive in positive rank. Together with the
zero-rank case, this establishes convergence of the dual-lattice Gaussian at the stated scale.
-/

namespace Rigidity.Smoothing

/-- The stated smoothing scale is positive when the family has positive rank. -/
theorem scale_pos {N k : ℕ} (hk : 0 < k) (b : Fin k → EuclideanSpace ℝ (Fin N))
    (hb : LinearIndependent ℝ b) {r ε s : ℝ} (hr : ∀ i, ‖b i‖ ≤ r) (hε : 0 < ε)
    (hs : Real.sqrt (Real.log (2 * k * (1 + 1 / ε)) / Real.pi) * r ≤ s) : 0 < s := by
  let i : Fin k := ⟨0, hk⟩
  have hrpos : 0 < r := lt_of_lt_of_le (norm_pos_iff.mpr (hb.ne_zero i)) (hr i)
  have hkone : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hinv : 0 < 1 / ε := one_div_pos.mpr hε
  have harg : 1 < 2 * (k : ℝ) * (1 + 1 / ε) := by nlinarith
  have hroot : 0 < Real.sqrt (Real.log (2 * k * (1 + 1 / ε)) / Real.pi) :=
    Real.sqrt_pos.2 (div_pos (Real.log_pos harg) Real.pi_pos)
  exact lt_of_lt_of_le (mul_pos hroot hrpos) hs

/-- The nonzero dual-lattice Gaussian is summable at the stated smoothing scale. -/
theorem summable_dualLattice_of_scale_bound (N k : ℕ)
    (b : Fin k → EuclideanSpace ℝ (Fin N)) (hb : LinearIndependent ℝ b)
    (r : ℝ) (hr : ∀ i, ‖b i‖ ≤ r) (ε : ℝ) (hε : 0 < ε) (s : ℝ)
    (hs : Real.sqrt (Real.log (2 * k * (1 + 1 / ε)) / Real.pi) * r ≤ s) :
    Summable (fun y : {y // y ∈ Rigidity.External.dualLattice b ∧ y ≠ 0} =>
      Real.exp (-(Real.pi * s ^ 2 * ‖(y : EuclideanSpace ℝ (Fin N))‖ ^ 2))) := by
  by_cases hk : k = 0
  · subst k
    exact (Rigidity.External.smoothing_fin_zero N b ε s hε).1
  · have hspos : 0 < s := scale_pos (Nat.pos_of_ne_zero hk) b hb hr hε hs
    have ha : 0 < Real.pi * s ^ 2 := by positivity
    simpa only [neg_mul] using summable_dualLattice b hb ha

end Rigidity.Smoothing
