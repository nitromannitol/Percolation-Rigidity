import Rigidity.Proofs.Regularity.PlanarRestrictBadOs
import Rigidity.Proofs.Regularity.PlanarScaleMaxima

/-!
# The maximum of the local minimal scales over the triadic boxes, of class `O_s`

`exists_isOsBond_scale_le_three`: if the minimal scales `Y_z` at the vertices `z` have uniformly
bounded stretched-exponential moments, there is a minimal scale `X ≤ O_r(θ)` such that almost
surely `Y_z ≤ 3^{k γ}` on the box `triScaleBox k` of side `2 · 3^{k+2}` whenever `X < 3^k`: the
probability that some `Y_z` exceeds `3^{k γ}` on the box is at most `9^{k+3} · 2 exp(-(3^{kγ}/θ)^s)`
(a union bound), and `exists_isOsBond_of_events` collects the scales. This is the form `O_s` of
`ae_eventually_scale_le_three`.
-/

namespace Rigidity.Proofs.Regularity

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External Rigidity.Percolation
open scoped ENNReal

/-- **The local minimal scales on the triadic boxes, with a minimal scale of class `O_s`.** -/
theorem exists_isOsBond_scale_le_three {p : unitInterval} {Y : Vertex 2 → Configuration 2 → ℝ}
    {s θ γ : ℝ} (hs : 0 < s) (hθ : 0 < θ) (hγ : 0 < γ) (hYm : ∀ z, Measurable (Y z))
    (hYi : ∀ z, Integrable (fun ω => Real.exp (Real.rpow (Y z ω / θ) s)) (latticeBondLaw 2 p))
    (hYb : ∀ z, (∫ ω, Real.exp (Real.rpow (Y z ω / θ) s) ∂latticeBondLaw 2 p) ≤ 2) :
    ∃ r θ' : ℝ, 0 < r ∧ 0 < θ' ∧ ∃ X : Configuration 2 → ℝ, Measurable X ∧ (∀ ω, 0 ≤ X ω) ∧
      IsOsBond 2 p X r θ' ∧
      ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ k : ℕ, X ω < 3 ^ k → ∀ z ∈ triScaleBox k,
        Y z ω ≤ (3 : ℝ) ^ ((k : ℝ) * γ) := by
  set E : ℕ → Set (Configuration 2) := fun k =>
    ⋃ z ∈ triScaleBox k, {ω | (3 : ℝ) ^ ((k : ℝ) * γ) < Y z ω} with hE
  have hEm : ∀ k, MeasurableSet (E k) := fun k =>
    Finset.measurableSet_biUnion _ fun z _ => measurableSet_lt measurable_const (hYm z)
  set c : ℝ := θ⁻¹ ^ s with hc
  have hc0 : 0 < c := by positivity
  obtain ⟨K, hK, hKb⟩ := exists_rpow_mul_exp_le (a := (2 : ℝ)) hc0 (mul_pos hγ hs)
  have hP : ∀ k : ℕ, latticeBondLaw 2 p (E k) ≤ ENNReal.ofReal (1458 * K) *
      ENNReal.ofReal (Real.exp (-(c / 2) * ((3 : ℝ) ^ k) ^ (γ * s))) := by
    intro k
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine (measure_biUnion_le_card_mul _ _ (b := 2 * Real.exp (-c * ((3 : ℝ) ^ k) ^ (γ * s)))
      fun z _ => ?_).trans (ENNReal.ofReal_le_ofReal ?_)
    · refine (measure_lt_le_of_exp_rpow_moment (latticeBondLaw 2 p) hθ hs (hYi z) (hYb z)
        (by positivity)).trans (ENNReal.ofReal_le_ofReal ?_)
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (le_of_eq ?_)) (by norm_num)
      rw [Real.div_rpow (by positivity) hθ.le, ← Real.rpow_natCast (3 : ℝ) k,
        ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num), hc,
        Real.inv_rpow hθ.le]
      ring_nf
    · have hcard := card_triScaleBox_le k
      have h9 : (9 : ℝ) ^ k = ((3 : ℝ) ^ k) ^ (2 : ℝ) := by
        rw [show (9 : ℝ) = 3 ^ 2 by norm_num, ← pow_mul, Real.rpow_two, ← pow_mul, mul_comm]
      have hx1 : (1 : ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
      have h := hKb ((3 : ℝ) ^ k) hx1
      have hE0 : 0 ≤ Real.exp (-c * ((3 : ℝ) ^ k) ^ (γ * s)) := (Real.exp_pos _).le
      calc ((triScaleBox k).card : ℝ) * (2 * Real.exp (-c * ((3 : ℝ) ^ k) ^ (γ * s)))
          ≤ 9 ^ 3 * 9 ^ k * (2 * Real.exp (-c * ((3 : ℝ) ^ k) ^ (γ * s))) :=
            mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = 1458 * (((3 : ℝ) ^ k) ^ (2 : ℝ) * Real.exp (-c * ((3 : ℝ) ^ k) ^ (γ * s))) := by
            rw [h9]; ring
        _ ≤ 1458 * (K * Real.exp (-(c / 2) * ((3 : ℝ) ^ k) ^ (γ * s))) :=
            mul_le_mul_of_nonneg_left h (by norm_num)
        _ = 1458 * K * Real.exp (-(c / 2) * ((3 : ℝ) ^ k) ^ (γ * s)) := by ring
  obtain ⟨θ', hθ', X, hXm, hX0, hXos, hXae⟩ := exists_isOsBond_of_events E hEm
    ENNReal.ofReal_ne_top (mul_pos hγ hs) (by positivity) hP
  refine ⟨γ * s, θ', mul_pos hγ hs, hθ', X, hXm, hX0, hXos, ?_⟩
  filter_upwards [hXae] with ω hω k hk z hz
  have h := hω k hk
  simp only [hE, Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_lt] at h
  exact h z hz

end Rigidity.Proofs.Regularity
