import LatticeProb.Prob.StochasticO.Sums

/-!
# Sums of stretched exponential variables with exponent at most one

Armstrong and Dario, Section 1, recall (citing Armstrong, Kuusi and Mourrat, Lemma 2.3) that
averages of variables bounded by `𝒪_s(1)` are bounded by `𝒪_s(C)` for every `s > 0`. For
`s ≥ 1` this is `LatticeProb.osBound_sum`. For `0 < s ≤ 1` the function `y ↦ exp(y^s / 2)` is not
convex near `0`, but `y ↦ exp((y + b)^s / 2)` is convex on `[0, ∞)` once `b^s ≥ 2 (1 - s) / s`, and
Jensen's inequality applies to it.
-/

namespace Rigidity.Percolation

open MeasureTheory LatticeProb

/-- For `0 < s ≤ 1` and `b^s ≥ 2 (1 - s) / s`, the function `y ↦ exp ((y + b)^s / 2)` is convex
on `[0, ∞)`. -/
theorem convexOn_exp_add_rpow {s b : ℝ} (hs : 0 < s) (hb : 0 < b)
    (hbs : 2 * (1 - s) / s ≤ b ^ s) :
    ConvexOn ℝ (Set.Ici 0) (fun y : ℝ => Real.exp ((y + b) ^ s / 2)) := by
  have hderiv : ∀ y : ℝ, 0 ≤ y → HasDerivAt (fun y : ℝ => Real.exp ((y + b) ^ s / 2))
      (Real.exp ((y + b) ^ s / 2) * (s * (y + b) ^ (s - 1) / 2)) y := by
    intro y hy
    have hyb : 0 < y + b := by linarith
    have h1 : HasDerivAt (fun y : ℝ => y + b) 1 y := (hasDerivAt_id y).add_const b
    have h3 := ((h1.rpow_const (p := s) (Or.inl hyb.ne')).div_const 2).exp
    convert h3 using 1
    ring
  refine MonotoneOn.convexOn_of_deriv (convex_Ici 0) ?_ ?_ ?_
  · intro y hy
    exact (hderiv y hy).continuousAt.continuousWithinAt
  · intro y hy
    rw [interior_Ici] at hy
    exact (hderiv y (le_of_lt hy)).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]
    intro y hy z hz hyz
    rw [(hderiv y (le_of_lt hy)).deriv, (hderiv z (le_of_lt hz)).deriv]
    have hy0 : 0 < y := hy
    have hu : 0 < y + b := by linarith
    have hv : 0 < z + b := by linarith
    have huv : y + b ≤ z + b := by linarith
    have hL : 0 ≤ Real.log (z + b) - Real.log (y + b) :=
      sub_nonneg.2 (Real.log_le_log hu huv)
    have hvs : (z + b) ^ s =
        (y + b) ^ s * Real.exp (s * (Real.log (z + b) - Real.log (y + b))) := by
      rw [Real.rpow_def_of_pos hv, Real.rpow_def_of_pos hu, ← Real.exp_add]
      congr 1
      ring
    have hexp := Real.add_one_le_exp (s * (Real.log (z + b) - Real.log (y + b)))
    have hus : 2 * (1 - s) / s ≤ (y + b) ^ s :=
      hbs.trans (Real.rpow_le_rpow hb.le (by linarith) hs.le)
    have hus' : 2 * (1 - s) ≤ (y + b) ^ s * s := (div_le_iff₀ hs).1 hus
    have hupos : 0 ≤ (y + b) ^ s := Real.rpow_nonneg hu.le s
    have hgrow : (y + b) ^ s * (s * (Real.log (z + b) - Real.log (y + b)) + 1) ≤
        (z + b) ^ s := by
      rw [hvs]
      exact mul_le_mul_of_nonneg_left hexp hupos
    have key : (1 - s) * (Real.log (z + b) - Real.log (y + b)) ≤
        ((z + b) ^ s - (y + b) ^ s) / 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hus' hL]
    have hmain : Real.exp ((y + b) ^ s / 2) * (y + b) ^ (s - 1) ≤
        Real.exp ((z + b) ^ s / 2) * (z + b) ^ (s - 1) := by
      rw [Real.rpow_def_of_pos hu (s - 1), Real.rpow_def_of_pos hv (s - 1), ← Real.exp_add,
        ← Real.exp_add]
      apply Real.exp_le_exp.2
      linarith
    calc Real.exp ((y + b) ^ s / 2) * (s * (y + b) ^ (s - 1) / 2)
        = s / 2 * (Real.exp ((y + b) ^ s / 2) * (y + b) ^ (s - 1)) := by ring
      _ ≤ s / 2 * (Real.exp ((z + b) ^ s / 2) * (z + b) ^ (s - 1)) :=
          mul_le_mul_of_nonneg_left hmain (by positivity)
      _ = Real.exp ((z + b) ^ s / 2) * (s * (z + b) ^ (s - 1) / 2) := by ring

/-- **Markov's inequality for a stretched exponential moment.** If
`E[exp(Y^s / 2)] ≤ exp A` with `A ≥ 0`, then `Y ≤ 𝒪_s((2A + 2)^{1/s})`. -/
theorem osBound_of_lintegral_exp_half_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {s A : ℝ} {Y : Ω → ℝ} (hs : 0 < s) (hA : 0 ≤ A) (hm : Measurable Y) (hn : ∀ ω, 0 ≤ Y ω)
    (he : ∫⁻ ω, ENNReal.ofReal (Real.exp (Y ω ^ s / 2)) ∂P ≤ ENNReal.ofReal (Real.exp A)) :
    OsBound P s ((2 * A + 2) ^ s⁻¹) Y := by
  intro t ht
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have htp : 1 ≤ t ^ s := Real.one_le_rpow ht hs.le
  have hC : 0 ≤ (2 * A + 2) ^ s⁻¹ := Real.rpow_nonneg (by linarith) _
  have hmark := meas_le_lintegral₀ (μ := P)
    (f := fun ω => ENNReal.ofReal (Real.exp (-((A + 1) * t ^ s))) *
      ENNReal.ofReal (Real.exp (Y ω ^ s / 2)))
    (by fun_prop) (s := {ω | t * (2 * A + 2) ^ s⁻¹ < max (Y ω) 0}) (by
      intro ω hω
      change t * (2 * A + 2) ^ s⁻¹ < max (Y ω) 0 at hω
      rw [max_eq_left (hn ω)] at hω
      have hp := Real.rpow_le_rpow (mul_nonneg ht0 hC) hω.le hs.le
      rw [Real.mul_rpow ht0 hC, Real.rpow_inv_rpow (by linarith) hs.ne'] at hp
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal
        (Real.one_le_exp (by linarith : 0 ≤ -((A + 1) * t ^ s) + Y ω ^ s / 2)))
  calc
    _ ≤ _ := hmark
    _ = ENNReal.ofReal (Real.exp (-((A + 1) * t ^ s))) *
        ∫⁻ ω, ENNReal.ofReal (Real.exp (Y ω ^ s / 2)) ∂P :=
      lintegral_const_mul _ (by fun_prop)
    _ ≤ ENNReal.ofReal (Real.exp (-((A + 1) * t ^ s))) * ENNReal.ofReal (Real.exp A) :=
      mul_le_mul' le_rfl he
    _ ≤ ENNReal.ofReal (Real.exp (-(t ^ s))) := by
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
        (by nlinarith [mul_nonneg hA (sub_nonneg.2 htp)]))

end Rigidity.Percolation
