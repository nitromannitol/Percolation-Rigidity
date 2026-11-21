import Rigidity.Proofs.Percolation.PlanarWellConnectedTail

/-!
# Planar well-connected cubes

The polynomial count of relevant subcubes is absorbed into the stretched-exponential tail.
-/

open MeasureTheory Filter Topology LatticeProb.Percolation Rigidity.External
open scoped ENNReal

namespace Rigidity.Percolation

/-- The deterministic radius condition for well-connectedness holds at all sufficiently large radii. -/
theorem eventually_planar_radius_condition :
    ∀ᶠ R : ℕ in atTop, (R : ℝ) ^ (1 / 400 : ℝ) ≤ R / 100 := by
  have hsmall : ∀ᶠ R : ℕ in atTop, (R : ℝ) ^ (-(399 / 400 : ℝ)) < 1 / 100 :=
    ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 399 / 400)).comp
      tendsto_natCast_atTop_atTop).eventually_lt_const (by norm_num)
  filter_upwards [hsmall, eventually_ge_atTop 1] with R hsmall hR
  have hRpos : (0 : ℝ) < R := by exact_mod_cast (show 0 < R by omega)
  have heq : (R : ℝ) ^ (1 / 400 : ℝ) = R * (R : ℝ) ^ (-(399 / 400 : ℝ)) := by
    calc
      _ = (R : ℝ) ^ ((1 : ℝ) + (-(399 / 400 : ℝ))) := by norm_num
      _ = (R : ℝ) ^ (1 : ℝ) * (R : ℝ) ^ (-(399 / 400 : ℝ)) :=
        Real.rpow_add hRpos _ _
      _ = _ := by rw [Real.rpow_one]
  rw [heq]
  have h := mul_le_mul_of_nonneg_left hsmall.le hRpos.le
  linarith

/-- A cubic count is eventually bounded by an exponential of the outer radius to power `1/800`. -/
theorem eventually_subcube_count_le_exp {c : ℝ} (hc : 0 < c) :
    ∀ᶠ R : ℕ in atTop,
      (((4 * R + 1) ^ 2 * (R + 1) + 1 : ℕ) : ℝ) ≤
        51 * Real.exp (c * (R : ℝ) ^ (1 / 800 : ℝ)) := by
  have htend : Tendsto (fun R : ℕ => (R : ℝ) ^ (1 / 800 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 800)).comp tendsto_natCast_atTop_atTop
  have hlittle := (isLittleO_pow_exp_pos_mul_atTop 2400 hc).bound (by norm_num : (0 : ℝ) < 1)
  filter_upwards [htend.eventually hlittle, eventually_ge_atTop 1] with R hlarge hR
  let t : ℝ := (R : ℝ) ^ (1 / 800 : ℝ)
  let r : ℝ := R
  have ht : 0 ≤ t := Real.rpow_nonneg (Nat.cast_nonneg R) _
  have hr : 1 ≤ r := by dsimp [r]; exact_mod_cast hR
  have hlarge' : t ^ 2400 ≤ Real.exp (c * t) := by
    change ‖t ^ 2400‖ ≤ (1 : ℝ) * ‖Real.exp (c * t)‖ at hlarge
    simpa only [one_mul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ht _),
      abs_of_pos (Real.exp_pos _)] using hlarge
  have hpower : t ^ 2400 = r ^ 3 := by
    dsimp [t, r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg R)]
    norm_num [Real.rpow_natCast]
  have hr2 : r ^ 2 ≤ r ^ 3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hr) (sq_nonneg r)]
  have hr1 : r ≤ r ^ 2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hr) (by linarith : 0 ≤ r)]
  have hr3 : 1 ≤ r ^ 3 := by linarith
  have hcount : (((4 * R + 1) ^ 2 * (R + 1) + 1 : ℕ) : ℝ) ≤ 51 * r ^ 3 := by
    dsimp [r]
    push_cast
    nlinarith
  calc
    _ ≤ 51 * r ^ 3 := hcount
    _ = 51 * t ^ 2400 := by rw [hpower]
    _ ≤ 51 * Real.exp (c * t) := by gcongr

/-- Planar supercritical bond percolation satisfies the well-connectedness estimate. -/
theorem wellConnected_input_two : WellConnectedInputTwo := by
  intro p hp _
  obtain ⟨C, c, hC, hc, hraw⟩ := wellConnected_failure_bound_raw p hp
  have hhalf : 0 < c / 2 := by positivity
  have hevent : ∀ᶠ R : ℕ in atTop,
      1 ≤ R ∧ (R : ℝ) ^ (1 / 400 : ℝ) ≤ R / 100 ∧
        (((4 * R + 1) ^ 2 * (R + 1) + 1 : ℕ) : ℝ) ≤
          51 * Real.exp (c / 2 * (R : ℝ) ^ (1 / 800 : ℝ)) :=
    (eventually_ge_atTop 1).and
      (eventually_planar_radius_condition.and (eventually_subcube_count_le_exp hhalf))
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.1 hevent
  let A := max (51 * C) (Real.exp (c / 2 * (R₀ : ℝ) ^ (1 / 800 : ℝ)))
  have hA : 0 < A := lt_of_lt_of_le (Real.exp_pos _) (le_max_right _ _)
  refine ⟨c / 2, A, 1 / 800, hhalf, hA, by norm_num, fun x R => ?_⟩
  by_cases hlarge : R₀ ≤ R
  · obtain ⟨hR, hpower, hcount⟩ := hR₀ R hlarge
    let t : ℝ := (R : ℝ) ^ (1 / 800 : ℝ)
    let P : ℕ := (4 * R + 1) ^ 2 * (R + 1) + 1
    have hcount' : (P : ℝ) ≤ 51 * Real.exp (c / 2 * t) := hcount
    have hexp : Real.exp (c / 2 * t) * Real.exp (-(c * t)) =
        Real.exp (-(c / 2 * t)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hreal : (P : ℝ) * (C * Real.exp (-(c * t))) ≤
        A * Real.exp (-(c / 2 * t)) := by
      calc
        _ ≤ (51 * Real.exp (c / 2 * t)) * (C * Real.exp (-(c * t))) := by gcongr
        _ = (51 * C) * Real.exp (-(c / 2 * t)) := by rw [← hexp]; ring
        _ ≤ _ := by gcongr; exact le_max_left _ _
    refine (hraw x R hR hpower).trans ?_
    rw [← ENNReal.ofReal_natCast P, ← ENNReal.ofReal_mul (Nat.cast_nonneg P)]
    exact ENNReal.ofReal_le_ofReal hreal
  · have hRle : R ≤ R₀ := by omega
    have hpow : (R : ℝ) ^ (1 / 800 : ℝ) ≤ (R₀ : ℝ) ^ (1 / 800 : ℝ) :=
      Real.rpow_le_rpow (Nat.cast_nonneg R) (by exact_mod_cast hRle) (by norm_num)
    have hone : (1 : ℝ≥0∞) ≤
        ENNReal.ofReal (A * Real.exp (-(c / 2 * (R : ℝ) ^ (1 / 800 : ℝ)))) := by
      rw [ENNReal.one_le_ofReal]
      calc
        1 = Real.exp (c / 2 * (R₀ : ℝ) ^ (1 / 800 : ℝ)) *
            Real.exp (-(c / 2 * (R₀ : ℝ) ^ (1 / 800 : ℝ))) := by
              rw [← Real.exp_add]
              simp
        _ ≤ A * Real.exp (-(c / 2 * (R : ℝ) ^ (1 / 800 : ℝ))) := by
          gcongr
          exact le_max_right _ _
    calc
      _ ≤ (latticeBondLaw 2 p) Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
      _ ≤ _ := hone

end Rigidity.Percolation
