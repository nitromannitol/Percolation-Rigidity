import Rigidity.Proofs.S2.PlanarDensityMomentTail
import LatticeProb.Prob.StochasticO

/-!
# From geometric grid tails to a stretched-exponential tail

A geometric tail at seventh-power thresholds gives a stretched-exponential tail with exponent
one seventh.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory
open scoped ENNReal

/-- Geometric tails on a seventh-power grid imply an `O₁/₁₂` tail bound. -/
theorem osBound_one_seventh_of_geometric_tails {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (C : ℝ) (hC : 0 < C) (hX : ∀ ω, 0 ≤ X ω)
    (hgrid : ∀ n : ℕ, 1 ≤ n → μ {ω | C * (n : ℝ) ^ 7 ≤ X ω} ≤ (1 / 2 : ℝ≥0∞) ^ n) :
    LatticeProb.OsBound μ (1 / 7 : ℝ) (C * 4 ^ (7 : ℕ)) X := by
  intro t ht
  let u : ℝ := t ^ (1 / 7 : ℝ)
  let n : ℕ := ⌊4 * u⌋₊
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hu1 : 1 ≤ u := Real.one_le_rpow ht (by norm_num)
  have hu0 : 0 ≤ u := by linarith
  have hnUpper : (n : ℝ) ≤ 4 * u := Nat.floor_le (by positivity)
  have hnLower : 4 * u < (n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hn1 : 1 ≤ n := by
    have h : (1 : ℝ) ≤ n := by linarith
    exact_mod_cast h
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have huPow : u ^ 7 = t := by
    dsimp [u]
    simpa only [one_div, Nat.cast_ofNat] using
      Real.rpow_inv_natCast_pow ht0 (n := 7) (by norm_num)
  have hpow : (n : ℝ) ^ 7 ≤ 4 ^ (7 : ℕ) * t := by
    calc
      _ ≤ (4 * u) ^ 7 := pow_le_pow_left₀ hn0 hnUpper _
      _ = 4 ^ (7 : ℕ) * t := by rw [mul_pow, huPow]
  have hscale : C * (n : ℝ) ^ 7 ≤ t * (C * 4 ^ (7 : ℕ)) := by
    have h := mul_le_mul_of_nonneg_left hpow hC.le
    nlinarith
  have hsub : {ω | t * (C * 4 ^ (7 : ℕ)) < max (X ω) 0} ⊆
      {ω | C * (n : ℝ) ^ 7 ≤ X ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, max_eq_left (hX ω)] at hω
    exact hscale.trans hω.le
  have hlog : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (x := (2 : ℝ)) (by norm_num)
    norm_num at h ⊢
    exact h
  have harg : (n : ℝ) * (-Real.log 2) ≤ -u := by
    have h := mul_le_mul_of_nonneg_left hlog hn0
    nlinarith
  have hreal : (1 / 2 : ℝ) ^ n ≤ Real.exp (-u) := by
    calc
      _ = (Real.exp (-Real.log 2)) ^ n := by
        congr 1
        rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        norm_num
      _ = Real.exp ((n : ℝ) * (-Real.log 2)) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr harg
  have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  calc
    _ ≤ μ {ω | C * (n : ℝ) ^ 7 ≤ X ω} := measure_mono hsub
    _ ≤ (1 / 2 : ℝ≥0∞) ^ n := hgrid n hn1
    _ = ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := by rw [ENNReal.ofReal_pow (by norm_num), hhalf]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

end Rigidity.Proofs.S2
