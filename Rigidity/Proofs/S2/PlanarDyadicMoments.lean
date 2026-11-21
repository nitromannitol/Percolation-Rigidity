import Rigidity.Proofs.S2.PlanarMomentRootBase

/-!
# Dyadic moment bounds for planar density

The additive moment-root recursion gives uniform polynomial growth in dyadic moment order.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory ProbabilityTheory LatticeProb.Percolation Rigidity.External

/-- Dyadic squared moment norms grow at most like the fourteenth power of the order. -/
theorem planar_density_dyadic_moment_roots (p : unitInterval)
    (hp : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j m : ℕ) (k : Vertex 2),
      planarDensityMomentRoot p m k (2 ^ (j + 1)) ≤
        C * (((2 ^ (j + 1) : ℕ) : ℝ) ^ 14) / (((3 ^ m : ℕ) : ℝ) ^ 2) := by
  obtain ⟨A, hA, hbase⟩ := planar_density_moment_root_two p hp
  obtain ⟨B, hB, hrec⟩ := planar_density_moment_root_recursion p hp
  let C := A + B
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, fun j m k => ?_⟩
  let v : ℝ := ((3 ^ m : ℕ) : ℝ)
  have hv : 0 < v ^ 2 := by dsimp [v]; positivity
  induction j with
  | zero =>
      have h := hbase m k
      change planarDensityMomentRoot p m k 2 ≤ C * (2 : ℝ) ^ 14 / v ^ 2
      have hscale : A / v ^ 2 ≤ C * (2 : ℝ) ^ 14 / v ^ 2 := by
        apply (div_le_div_iff_of_pos_right hv).2
        dsimp [C]
        nlinarith
      exact h.trans hscale
  | succ j ih =>
      let n : ℕ := 2 ^ (j + 1)
      have hn : 2 ≤ n := by
        dsimp [n]
        exact Nat.le_pow (by omega : 1 ≤ j + 1)
      have hstep := hrec n hn m k
      have hpow : (((2 ^ (j + 1 + 1) : ℕ) : ℝ) ^ 14) =
          (2 : ℝ) ^ 14 * ((n : ℝ) ^ 14) := by
        dsimp [n]
        rw [pow_succ]
        push_cast
        ring
      have hindex : 2 ^ (j + 1 + 1) = 2 * n := by
        dsimp [n]
        rw [pow_succ]
        omega
      change planarDensityMomentRoot p m k (2 ^ (j + 1 + 1)) ≤
        C * (((2 ^ (j + 1 + 1) : ℕ) : ℝ) ^ 14) / v ^ 2
      rw [hpow, hindex]
      have ih' : planarDensityMomentRoot p m k n ≤ C * ((n : ℝ) ^ 14) / v ^ 2 := ih
      calc
        _ ≤ planarDensityMomentRoot p m k n + B * (n : ℝ) ^ 14 / v ^ 2 := hstep
        _ ≤ C * (n : ℝ) ^ 14 / v ^ 2 + B * (n : ℝ) ^ 14 / v ^ 2 := add_le_add ih' le_rfl
        _ ≤ C * (2 ^ (14 : ℕ) * (n : ℝ) ^ 14) / v ^ 2 := by
          rw [← add_div]
          apply (div_le_div_iff_of_pos_right hv).2
          have hn0 : 0 ≤ (n : ℝ) ^ 14 := by positivity
          dsimp [C] at *
          nlinarith

end Rigidity.Proofs.S2
