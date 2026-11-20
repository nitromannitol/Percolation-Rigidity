import Rigidity.Percolation.TriadicWellConnectedUnion
import Rigidity.Percolation.PolynomialExponential

/-!
# Exponential estimates for well-connectedness

Exponential estimates for crossing failures and local test failures imply an
exponential estimate for failure of well-connectedness.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory Rigidity.External
open scoped ENNReal

/-- Exponential crossing and local-test bounds imply an exponential
well-connectedness bound, with half the original rate. -/
theorem TriadicCube.measure_not_wellConnectedIn_le_exp {d : ℕ}
    (Q : TriadicCube d) (interior : Set (Vertex d)) (hinterior : interior ⊆ Q.vertices)
    (μ : Measure (Configuration d)) (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c)
    (hcross : μ {ω | ¬ HasCrossingComponent ω Q.vertices
        (fun i => ↑(Q.toIntegerCube.lowerFace i))
        (fun i => ↑(Q.toIntegerCube.upperFace i))} ≤
      ENNReal.ofReal (C * Real.exp (-c * (3 : ℝ) ^ Q.scale)))
    (htest : ∀ R ∈ Q.testCubes interior,
      μ (Q.badCoalescenceTest R) ≤
        ENNReal.ofReal (C * Real.exp (-c * (3 : ℝ) ^ Q.scale))) :
    μ {ω | ¬ Q.wellConnectedIn interior ω} ≤
      ENNReal.ofReal ((C * (1 + 2 * 7 ^ d * ((d + 1).factorial : ℝ) /
        (c / 2) ^ (d + 1))) * Real.exp (-(c / 2) * (3 : ℝ) ^ Q.scale)) := by
  let x : ℝ := (3 : ℝ) ^ Q.scale
  let A : ℝ := 2 * 7 ^ d * ((d + 1).factorial : ℝ) / (c / 2) ^ (d + 1)
  let N : ℕ := (3 ^ Q.scale + 1) * (6 * 3 ^ Q.scale + 1) ^ d
  have hx : 0 ≤ x := by positivity
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hsmall : Real.exp (-c * x) ≤ Real.exp (-(c / 2) * x) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hN : (N : ℝ) * Real.exp (-c * x) ≤ A * Real.exp (-(c / 2) * x) := by
    dsimp only [N, A, x]
    push_cast
    exact testCube_count_mul_exp_neg_le d Q.scale hc
  have hreal : C * Real.exp (-c * x) + (N : ℝ) * (C * Real.exp (-c * x)) ≤
      C * (1 + A) * Real.exp (-(c / 2) * x) := by
    have h1 := mul_le_mul_of_nonneg_left hsmall hC
    have h2 := mul_le_mul_of_nonneg_left hN hC
    nlinarith
  calc
    _ ≤ μ {ω | ¬ HasCrossingComponent ω Q.vertices
          (fun i => ↑(Q.toIntegerCube.lowerFace i))
          (fun i => ↑(Q.toIntegerCube.upperFace i))} +
        (N : ℝ≥0∞) * ENNReal.ofReal (C * Real.exp (-c * x)) :=
      Q.measure_not_wellConnectedIn_le interior hinterior μ
        (ENNReal.ofReal (C * Real.exp (-c * x))) htest
    _ ≤ ENNReal.ofReal (C * Real.exp (-c * x)) +
        (N : ℝ≥0∞) * ENNReal.ofReal (C * Real.exp (-c * x)) :=
      add_le_add hcross (le_refl _)
    _ = ENNReal.ofReal (C * Real.exp (-c * x) +
        (N : ℝ) * (C * Real.exp (-c * x))) := by
      rw [ENNReal.ofReal_add (mul_nonneg hC (Real.exp_nonneg _))
        (mul_nonneg (by positivity) (mul_nonneg hC (Real.exp_nonneg _))),
        ENNReal.ofReal_mul (show 0 ≤ (N : ℝ) by positivity), ENNReal.ofReal_natCast]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

end Rigidity.Percolation
