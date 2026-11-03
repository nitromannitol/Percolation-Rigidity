import Rigidity.Steps.Section5.LoopsAroundAnnuli

/-!
# Lemma 5.14: the crossing probability and Borel-Cantelli steps

* `crossingProbabilityStep`: each of the five rectangles in `AnnulusCrossings ω R` has long side
  `m ≤ 4R` and short side `n ≥ R - 1`, so the failure of its crossing has probability at most
  `C (m + 1) e^{-cn} ≤ 4 C e^c (R + 1) e^{-cR}`; a union bound over the five gives `C' = 20 C e^c`
  and `c' = c`.
* `borelCantelliStep`: `(R + 1) e^{-cR}` is summable, and the Borel-Cantelli lemma applies.
-/

open MeasureTheory LatticeProb.Percolation Filter

namespace Rigidity.Proofs.Section5

open Rigidity.Section5 Rigidity.External Rigidity.Steps.Section5

/-- The crossing estimate of a rectangle with long side `m ≤ 4R + 3` and short side
`n ≥ R - 1`, in terms of `R`. -/
theorem crossing_bound_le {C c : ℝ} (hC : 0 < C) (hc : 0 < c) {m n R : ℕ}
    (hm : m + 1 ≤ 4 * (R + 1)) (hn : R ≤ n + 1) :
    C * (m + 1) * Real.exp (-(c * n)) ≤
      4 * C * Real.exp c * (R + 1) * Real.exp (-(c * R)) := by
  have hm' : (m : ℝ) + 1 ≤ 4 * ((R : ℝ) + 1) := by exact_mod_cast hm
  have hn' : (R : ℝ) ≤ n + 1 := by exact_mod_cast hn
  have hexp : Real.exp (-(c * n)) ≤ Real.exp c * Real.exp (-(c * R)) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    nlinarith
  calc C * (m + 1) * Real.exp (-(c * n))
      ≤ C * (4 * ((R : ℝ) + 1)) * (Real.exp c * Real.exp (-(c * R))) := by gcongr
    _ = 4 * C * Real.exp c * (R + 1) * Real.exp (-(c * R)) := by ring

/-- Step `step:5.14-union-bound`. -/
theorem crossingProbabilityStep : CrossingProbabilityStep := by
  intro p C c hC hc hbound
  refine ⟨20 * C * Real.exp c, c, by positivity, hc, fun R => ?_⟩
  set μ := latticeBondLaw 2 p
  set b := ENNReal.ofReal (4 * C * Real.exp c * (R + 1) * Real.exp (-(c * R)))
  have key : ∀ (x : Vertex 2) (m n : ℕ) (i : Fin 2), m + 1 ≤ 4 * (R + 1) → R ≤ n + 1 →
      μ {ω | ¬ HasOpenCrossing ω x m n i} ≤ b := fun x m n i hm hn =>
    (hbound x m n i).trans (ENNReal.ofReal_le_ofReal (crossing_bound_le hC hc hm hn))
  let bad : Vertex 2 → ℕ → ℕ → Fin 2 → Set (Configuration 2) := fun x m n i =>
    {ω | ¬ HasOpenCrossing ω x m n i}
  have hsub : {ω | ¬ AnnulusCrossings ω R} ⊆
      bad ![-(2 * R : ℤ), -(2 * R)] (4 * R) (R - 1) 0 ∪
        bad ![-(2 * R : ℤ), R + 1] (4 * R) (R - 1) 0 ∪
        bad ![-(2 * R : ℤ), -(2 * R)] (4 * R) (R - 1) 1 ∪
        bad ![(R : ℤ) + 1, -(2 * R)] (4 * R) (R - 1) 1 ∪
        bad ![(R : ℤ) + 1, 0] (3 * R - 1) R 0 := by
    intro ω hω
    simp only [Set.mem_setOf_eq, AnnulusCrossings] at hω
    simp only [bad, Set.mem_union, Set.mem_setOf_eq]
    tauto
  calc μ {ω | ¬ AnnulusCrossings ω R}
      ≤ μ (bad ![-(2 * R : ℤ), -(2 * R)] (4 * R) (R - 1) 0) +
          μ (bad ![-(2 * R : ℤ), R + 1] (4 * R) (R - 1) 0) +
          μ (bad ![-(2 * R : ℤ), -(2 * R)] (4 * R) (R - 1) 1) +
          μ (bad ![(R : ℤ) + 1, -(2 * R)] (4 * R) (R - 1) 1) +
          μ (bad ![(R : ℤ) + 1, 0] (3 * R - 1) R 0) :=
        (measure_mono hsub).trans <| (measure_union_le _ _).trans <| add_le_add_left
          ((measure_union_le _ _).trans <| add_le_add_left
            ((measure_union_le _ _).trans <| add_le_add_left (measure_union_le _ _) _) _) _
    _ ≤ b + b + b + b + b := by
        gcongr <;> exact key _ _ _ _ (by omega) (by omega)
    _ = ENNReal.ofReal (20 * C * Real.exp c * (R + 1) * Real.exp (-(c * R))) := by
        rw [show 20 * C * Real.exp c * (R + 1) * Real.exp (-(c * R)) =
            5 * (4 * C * Real.exp c * (R + 1) * Real.exp (-(c * R))) by ring,
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
        ring

/-- Step `step:5.14-borel-cantelli`. -/
theorem borelCantelliStep : BorelCantelliStep := by
  intro p C c hC hc hbound
  set f : ℕ → ℝ := fun R => C * (R + 1) * Real.exp (-(c * R))
  have hf0 : ∀ R, 0 ≤ f R := fun R => by positivity
  have hfs : Summable f := by
    have h := ((Real.summable_pow_mul_exp_neg_nat_mul 1 hc).add
      (Real.summable_pow_mul_exp_neg_nat_mul 0 hc)).mul_left C
    refine h.congr fun R => ?_
    simp only [f, pow_one, pow_zero, neg_mul]
    ring
  have hsum : ∑' R, latticeBondLaw 2 p {ω | ¬ AnnulusCrossings ω R} ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
    rw [← ENNReal.ofReal_tsum_of_nonneg hf0 hfs]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  obtain ⟨M, hM⟩ := eventually_atTop.mp hω
  exact ⟨M, fun R hR => not_not.mp (hM R hR)⟩

end Rigidity.Proofs.Section5
