import Rigidity.Percolation.TriadicOverlapProbability
import Rigidity.Percolation.IntegerCubeCoalescenceScales
import Rigidity.Percolation.PolynomialExponential

/-!
# Exponential decay from overlap estimates

Uniform exponential bounds for ambient, test, and overlap failures imply an
exponential well-connectedness bound after absorbing the polynomial counts.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory Rigidity.External
open scoped ENNReal

/-- Exponential ambient, test-cube, and overlap-crossing estimates give an
exponential well-connectedness estimate with half the original rate. -/
theorem TriadicCube.measure_not_wellConnectedIn_threeQuarter_le_exp {d : ℕ}
    (hd : 0 < d) (Q : TriadicCube d) (hside : 2 ≤ Q.side)
    (hk : 0 < 3 ^ Q.scale / 20) (μ : Measure (Configuration d))
    (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c)
    (hQ : μ {ω | ¬ HasCrossingComponent ω Q.vertices
        (fun i => ↑(Q.toIntegerCube.lowerFace i))
        (fun i => ↑(Q.toIntegerCube.upperFace i)) ∨
      ¬ LargePathsCoalesce ω Q.vertices
        (pathDiameterAtLeast (((3 ^ Q.scale / 20 : ℕ) : ℤ) - 1))} ≤
      ENNReal.ofReal (C * Real.exp (-c * (3 : ℝ) ^ Q.scale)))
    (htest : ∀ R ∈ Q.testCubes Q.threeQuarterCube.vertices,
      μ {ω | ¬ CrossableRegion ω (↑R.vertices) (fun i => ↑(R.lowerFace i))
          (fun i => ↑(R.upperFace i)) ∨
        ¬ LargePathsCoalesce ω (↑R.vertices)
          (pathDiameterAtLeast (((3 ^ Q.scale / 20 : ℕ) : ℤ) - 1))} ≤
        ENNReal.ofReal (C * Real.exp (-c * (3 : ℝ) ^ Q.scale)))
    (hoverlap : ∀ T : IntegerCube d, T.size = 3 ^ Q.scale / 20 →
      (↑T.vertices : Set (Vertex d)) ⊆ Q.vertices →
      μ {ω | ¬ HasCrossingComponent ω (↑T.vertices)
        (fun i => ↑(T.lowerFace i)) (fun i => ↑(T.upperFace i))} ≤
        ENNReal.ofReal (C * Real.exp (-c * (3 : ℝ) ^ Q.scale))) :
    μ {ω | ¬ Q.wellConnectedIn Q.threeQuarterCube.vertices ω} ≤
      ENNReal.ofReal ((C * (1 + 4 * 7 ^ d * ((d + 1).factorial : ℝ) /
        (c / 2) ^ (d + 1))) * Real.exp (-(c / 2) * (3 : ℝ) ^ Q.scale)) := by
  let x : ℝ := (3 : ℝ) ^ Q.scale
  let A : ℝ := 2 * 7 ^ d * ((d + 1).factorial : ℝ) / (c / 2) ^ (d + 1)
  let N : ℕ := (3 ^ Q.scale + 1) * (6 * 3 ^ Q.scale + 1) ^ d
  let M : ℕ := Q.toIntegerCube.vertices.card
  have hx : 0 ≤ x := by positivity
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hMN : M ≤ N := by
    dsimp only [M, N]
    rw [IntegerCube.card_vertices]
    change (3 ^ Q.scale) ^ d ≤ (3 ^ Q.scale + 1) * (6 * 3 ^ Q.scale + 1) ^ d
    calc
      (3 ^ Q.scale) ^ d ≤ (6 * 3 ^ Q.scale + 1) ^ d := by gcongr; omega
      _ ≤ (3 ^ Q.scale + 1) * (6 * 3 ^ Q.scale + 1) ^ d := by
        exact Nat.le_mul_of_pos_left _ (by omega)
  have hsmall : Real.exp (-c * x) ≤ Real.exp (-(c / 2) * x) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hN : (N : ℝ) * Real.exp (-c * x) ≤ A * Real.exp (-(c / 2) * x) := by
    dsimp only [N, A, x]
    push_cast
    exact testCube_count_mul_exp_neg_le d Q.scale hc
  have hM : (M : ℝ) * Real.exp (-c * x) ≤ A * Real.exp (-(c / 2) * x) := by
    exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hMN) (Real.exp_nonneg _)).trans hN
  have hreal : C * Real.exp (-c * x) + (N : ℝ) * (C * Real.exp (-c * x)) +
      (M : ℝ) * (C * Real.exp (-c * x)) ≤
        C * (1 + 2 * A) * Real.exp (-(c / 2) * x) := by
    have h1 := mul_le_mul_of_nonneg_left hsmall hC
    have h2 := mul_le_mul_of_nonneg_left hN hC
    have h3 := mul_le_mul_of_nonneg_left hM hC
    nlinarith
  have hnonneg : 0 ≤ C * Real.exp (-c * x) := mul_nonneg hC (Real.exp_nonneg _)
  calc
    _ ≤ ENNReal.ofReal (C * Real.exp (-c * x)) +
        (N : ℝ≥0∞) * ENNReal.ofReal (C * Real.exp (-c * x)) +
        (M : ℝ≥0∞) * ENNReal.ofReal (C * Real.exp (-c * x)) :=
      Q.measure_not_wellConnectedIn_threeQuarter_le hd hside hk μ _ _ _ hQ htest hoverlap
    _ = ENNReal.ofReal (C * Real.exp (-c * x) +
        (N : ℝ) * (C * Real.exp (-c * x)) + (M : ℝ) * (C * Real.exp (-c * x))) := by
      rw [ENNReal.ofReal_add (add_nonneg hnonneg (mul_nonneg (by positivity) hnonneg))
          (mul_nonneg (by positivity) hnonneg),
        ENNReal.ofReal_add hnonneg (mul_nonneg (by positivity) hnonneg),
        ENNReal.ofReal_mul (show 0 ≤ (N : ℝ) by positivity),
        ENNReal.ofReal_mul (show 0 ≤ (M : ℝ) by positivity), ENNReal.ofReal_natCast,
        ENNReal.ofReal_natCast]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      convert hreal using 1
      dsimp only [A, x]
      ring

end Rigidity.Percolation
