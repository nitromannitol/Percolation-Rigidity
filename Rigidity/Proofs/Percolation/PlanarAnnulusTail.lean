import Rigidity.Proofs.Section5.AnnulusCrossings
import Rigidity.Proofs.Percolation.KestenCrossing

/-!
# Supercritical planar annulus crossings

The probability of a crossing failure at any scale beyond `R` decays exponentially in `R`.
-/

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Steps.Section5
open scoped ENNReal

namespace Rigidity.Percolation

/-- Supercritical annulus-crossing failures at any scale beyond `R` have an exponential tail. -/
theorem annulusCrossings_tail (p : unitInterval) (hp : criticalProbability 2 < (p : ℝ)) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ R : ℕ,
      latticeBondLaw 2 p {ω | ∃ n : ℕ, R ≤ n ∧ ¬ AnnulusCrossings ω n} ≤
        ENNReal.ofReal (C * Real.exp (-(c * R))) := by
  obtain ⟨C₀, c₀, hC₀, hc₀, hrect⟩ := kesten_rectangle_crossing p hp
  obtain ⟨C, c, hC, hc, hbound⟩ :=
    Rigidity.Proofs.Section5.crossingProbabilityStep p C₀ c₀ hC₀ hc₀ hrect
  have hhalf : 0 < c / 2 := by positivity
  let f : ℕ → ℝ := fun n => (n + 1) * Real.exp (-(c / 2 * n))
  have hf0 : ∀ n, 0 ≤ f n := fun n => by dsimp [f]; positivity
  have hfs : Summable f := by
    have h := (Real.summable_pow_mul_exp_neg_nat_mul 1 hhalf).add
      (Real.summable_pow_mul_exp_neg_nat_mul 0 hhalf)
    refine h.congr fun n => ?_
    simp only [f, pow_one, pow_zero, neg_mul]
    ring
  let A : ℝ := ∑' n, f n
  have hA : 0 ≤ A := tsum_nonneg hf0
  refine ⟨C * (A + 1), c / 2, by positivity, hhalf, fun R => ?_⟩
  let b : ℕ → ℝ := fun n => if R ≤ n then C * (n + 1) * Real.exp (-(c * n)) else 0
  let D : ℝ := C * Real.exp (-(c / 2 * R))
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hb0 : ∀ n, 0 ≤ b n := by
    intro n
    dsimp [b]
    split_ifs <;> positivity
  have hdom : ∀ n, b n ≤ D * f n := by
    intro n
    dsimp [b]
    split_ifs with hn
    · have hn' : (R : ℝ) ≤ n := by exact_mod_cast hn
      have he : Real.exp (-(c * n)) ≤
          Real.exp (-(c / 2 * R)) * Real.exp (-(c / 2 * n)) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by nlinarith)
      dsimp [D, f]
      calc
        _ ≤ C * (n + 1) * (Real.exp (-(c / 2 * R)) * Real.exp (-(c / 2 * n))) := by gcongr
        _ = _ := by ring
    · exact mul_nonneg hD (hf0 n)
  have hDs : Summable (fun n => D * f n) := hfs.mul_left D
  have hbs : Summable b := Summable.of_nonneg_of_le hb0 hdom hDs
  let bad : ℕ → Set (Configuration 2) := fun n =>
    if R ≤ n then {ω | ¬ AnnulusCrossings ω n} else ∅
  have hsub : {ω | ∃ n : ℕ, R ≤ n ∧ ¬ AnnulusCrossings ω n} ⊆ ⋃ n, bad n := by
    rintro ω ⟨n, hn, hω⟩
    exact Set.mem_iUnion.2 ⟨n, by simpa only [bad, if_pos hn, Set.mem_setOf_eq] using hω⟩
  have hbad : ∀ n, latticeBondLaw 2 p (bad n) ≤ ENNReal.ofReal (b n) := by
    intro n
    by_cases hn : R ≤ n
    · simpa only [bad, b, if_pos hn] using hbound n
    · simp only [bad, b, if_neg hn, measure_empty, ENNReal.ofReal_zero, le_refl]
  calc
    _ ≤ ∑' n, latticeBondLaw 2 p (bad n) := (measure_mono hsub).trans (measure_iUnion_le _)
    _ ≤ ∑' n, ENNReal.ofReal (b n) := ENNReal.tsum_le_tsum hbad
    _ = ENNReal.ofReal (∑' n, b n) := (ENNReal.ofReal_tsum_of_nonneg hb0 hbs).symm
    _ ≤ ENNReal.ofReal (C * (A + 1) * Real.exp (-(c / 2 * R))) := by
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ ∑' n, D * f n := hbs.tsum_le_tsum hdom hDs
        _ = D * A := by rw [tsum_mul_left]
        _ ≤ _ := by dsimp [D]; nlinarith [Real.exp_pos (-(c / 2 * R))]

end Rigidity.Percolation
