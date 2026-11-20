import Rigidity.Percolation.TriadicStoppingMeasurable
import Rigidity.Percolation.TriadicStretchedTail
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Good cubes from well-connected cubes

A cube is good when it has positive scale and it and all its children are
well-connected. A uniform exponential estimate for well-connected cubes then
implies the corresponding estimate for good cubes.
-/

namespace Rigidity.Percolation

open MeasureTheory
open scoped ENNReal

/-- A cube is good if it has positive scale and it and all its children belong
to the collection of well-connected cubes. -/
def TriadicCube.goodOfWellConnected {d : ℕ} (W : Set (TriadicCube d)) : Set (TriadicCube d) :=
  {Q | 0 < Q.scale ∧ Q ∈ W ∧ ∀ digits : Fin d → Fin 3, Q.child digits ∈ W}

/-- Goodness is measurable if well-connectedness is measurable. -/
theorem TriadicCube.measurableSet_mem_goodOfWellConnected {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (W : Ω → Set (TriadicCube d))
    (hW : ∀ Q : TriadicCube d, MeasurableSet {ω | Q ∈ W ω}) (Q : TriadicCube d) :
    MeasurableSet {ω | Q ∈ goodOfWellConnected (W ω)} := by
  classical
  by_cases hQ : 0 < Q.scale
  · have heq : {ω | Q ∈ goodOfWellConnected (W ω)} =
        {ω | Q ∈ W ω} ∩ ⋂ digits : Fin d → Fin 3, {ω | Q.child digits ∈ W ω} := by
      ext ω
      simp only [goodOfWellConnected, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter,
        hQ, true_and]
    rw [heq]
    exact (hW Q).inter (MeasurableSet.iInter (fun digits => hW (Q.child digits)))
  · have heq : {ω | Q ∈ goodOfWellConnected (W ω)} = ∅ := by
      ext ω
      simp only [goodOfWellConnected, Set.mem_setOf_eq, hQ, false_and, Set.mem_empty_iff_false]
    rw [heq]
    exact MeasurableSet.empty

/-- Exponential well-connectedness probabilities give exponential good-cube
probabilities, with constants independent of the cube. -/
theorem TriadicCube.measure_not_mem_goodOfWellConnected_le {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (W : Ω → Set (TriadicCube d))
    (C : ℝ≥0∞) (c : ℝ) (hc : 0 < c)
    (hW : ∀ Q : TriadicCube d,
      μ {ω | Q ∉ W ω} ≤ C * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ Q.scale))) :
    ∀ Q : TriadicCube d,
      μ {ω | Q ∉ goodOfWellConnected (W ω)} ≤
        max (ENNReal.ofReal (Real.exp (c / 3))) ((1 + 3 ^ d) * C) *
          ENNReal.ofReal (Real.exp (-(c / 3) * (3 : ℝ) ^ Q.scale)) := by
  classical
  intro Q
  let K : ℝ≥0∞ := max (ENNReal.ofReal (Real.exp (c / 3))) ((1 + 3 ^ d) * C)
  by_cases hQ : 0 < Q.scale
  · let z : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(c / 3) * (3 : ℝ) ^ Q.scale))
    have hparent : μ {ω | Q ∉ W ω} ≤ C * z := by
      calc
        _ ≤ C * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ Q.scale)) := hW Q
        _ ≤ C * z := by
          gcongr
          dsimp only [z]
          apply ENNReal.ofReal_le_ofReal
          apply Real.exp_le_exp.mpr
          have hp : 0 < (3 : ℝ) ^ Q.scale := by positivity
          nlinarith
    have hchild (digits : Fin d → Fin 3) : μ {ω | Q.child digits ∉ W ω} ≤ C * z := by
      calc
        _ ≤ C * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ (Q.child digits).scale)) :=
          hW (Q.child digits)
        _ = C * z := by
          dsimp only [z, child]
          have hscale : Q.scale = (Q.scale - 1) + 1 := by omega
          have heq : -c * (3 : ℝ) ^ (Q.scale - 1) =
              -(c / 3) * (3 : ℝ) ^ Q.scale := by
            conv_rhs => rw [hscale, pow_add]
            norm_num
            ring
          rw [heq]
    have hsubset : {ω | Q ∉ goodOfWellConnected (W ω)} ⊆
        {ω | Q ∉ W ω} ∪ ⋃ digits : Fin d → Fin 3, {ω | Q.child digits ∉ W ω} := by
      intro ω hω
      simp only [Set.mem_setOf_eq, goodOfWellConnected, hQ, true_and, not_and_or,
        not_forall, Set.mem_union, Set.mem_iUnion] at hω ⊢
      exact hω
    calc
      _ ≤ μ ({ω | Q ∉ W ω} ∪ ⋃ digits : Fin d → Fin 3, {ω | Q.child digits ∉ W ω}) :=
        measure_mono hsubset
      _ ≤ μ {ω | Q ∉ W ω} + μ (⋃ digits : Fin d → Fin 3, {ω | Q.child digits ∉ W ω}) :=
        measure_union_le _ _
      _ ≤ C * z + ∑ _digits : Fin d → Fin 3, C * z := by
        gcongr
        calc
          _ ≤ ∑ digits : Fin d → Fin 3, μ {ω | Q.child digits ∉ W ω} :=
            measure_iUnion_fintype_le μ _
          _ ≤ _ := Finset.sum_le_sum (fun digits _ => hchild digits)
      _ = ((1 + 3 ^ d) * C) * z := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          nsmul_eq_mul, Nat.cast_pow]
        ring
      _ ≤ K * z := by gcongr; exact le_max_right _ _
  · have hscale : Q.scale = 0 := by omega
    have he : (1 : ℝ≥0∞) = ENNReal.ofReal (Real.exp (c / 3)) *
        ENNReal.ofReal (Real.exp (-(c / 3) * (3 : ℝ) ^ Q.scale)) := by
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add, hscale]
      simp only [pow_zero, mul_one, add_neg_cancel, Real.exp_zero, ENNReal.ofReal_one]
    calc
      _ ≤ 1 := prob_le_one
      _ = ENNReal.ofReal (Real.exp (c / 3)) *
          ENNReal.ofReal (Real.exp (-(c / 3) * (3 : ℝ) ^ Q.scale)) := he
      _ ≤ K * ENNReal.ofReal (Real.exp (-(c / 3) * (3 : ℝ) ^ Q.scale)) := by
        gcongr
        exact le_max_left _ _

end Rigidity.Percolation
