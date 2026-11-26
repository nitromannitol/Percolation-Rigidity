import Rigidity.Proofs.Green.PointSourceTailsD

/-!
# The point source at one configuration and one time

For a final time `t`, the geometric times `s_j = 3^j s_0` with `s_0 = t/3^J ∈ [t^η, 3t^η)`
(`exists_nat_pow_near`) and the radii `l_j = √(s_j) L` with `L = t^{η/(d+2)}`, the passage from
smooth initial data to a point source (`l2norm_pointSource_le`) with the norms from Proposition A.7
and the whole-cluster estimate (`l2norm_gaussFlowDiff_le_of_inputs`, `l2norm_initialError_le`) and
the tails from the Carne–Varopoulos bound (`tsum_out_gaussFlowDiff_le_of_cv`,
`tsum_out_initialError_le_of_cv`) gives (`l2norm_pointSource_le_of_time`)

  `‖p_t(·, y) - G_t‖ ≤ psBound`,

an explicit bound in `t`, `L` and the constants of the inputs. The radii `√s t^{η/(d+2)}` replace
the radii `√s log(2 + t)` of the source of the route; the powers of `L` they produce are absorbed in
the same way.
-/

open scoped Classical
open LatticeProb.Percolation Rigidity.WeakPoincare

namespace Rigidity.Green

/-- `(2θ (2πσ)^{-d/2})^{1/2}`. -/
noncomputable def psGauss (d : ℕ) (σ θ : ℝ) : ℝ :=
  Real.sqrt (2 * θ * (2 * Real.pi * σ) ^ (-((d : ℝ) / 2)))

/-- The constant of the norms of the differences. -/
noncomputable def psCN (d : ℕ) (σ θ CA CG : ℝ) : ℝ :=
  2 * (2 * CA / θ ^ 2 * psGauss d σ θ) + CG

/-- The constant of the norm of the initial error. -/
noncomputable def psCE (d : ℕ) (σ θ CB : ℝ) : ℝ := Real.sqrt CB + 2 / θ * psGauss d σ θ

/-- The uniform bound of the tails. -/
noncomputable def psT0 (d : ℕ) (σ θ CV η t L : ℝ) : ℝ :=
  CV * (4 * Real.pi * CV * t) ^ ((d : ℝ) / 2) * gaussMassBoundD d CV *
      Real.exp (-(L ^ 2 / (16 * CV))) +
    CV * expMassBoundD d CV * Real.exp (-(t ^ η / (2 * CV))) +
    4 / θ * (2 ^ ((d : ℝ) / 2) * gaussMassBoundD d σ) * Real.exp (-(L ^ 2 / (16 * σ)))

/-- The bound of `‖p_t(·, y) - G_t‖`. -/
noncomputable def psBound (d : ℕ) (σ θ C₀ A CB CA CG CV η t : ℝ) : ℝ :=
  (5 ^ ((d : ℝ) / 2) * ((C₀ + (10 * C₀ + 32) * A) * (1 + Real.sqrt 8)) * Real.sqrt CB *
      psCE d σ θ CB * (t ^ (η / (d + 2))) ^ ((d : ℝ) / 2 + 1) * (3 * t ^ η) ^ ((1 : ℝ) / 2) *
      t ^ (-((d : ℝ) / 4) - 1 / 2) +
    (2 + (C₀ + (10 * C₀ + 32) * A) * (1 + Real.sqrt 8) * Real.sqrt CB) *
      psT0 d σ θ CV η t (t ^ (η / (d + 2)))) +
  Real.log t * (5 ^ ((d : ℝ) / 2) * ((C₀ + (10 * C₀ + 32) * A) * (1 + Real.sqrt 8)) *
      Real.sqrt CB * psCN d σ θ CA CG * (t ^ (η / (d + 2))) ^ ((d : ℝ) / 2 + 1) *
      t ^ (η - (d : ℝ) / 4 - 1 / 2) +
    psCN d σ θ CA CG * (4 * (t ^ (η / (d + 2))) ^ 2) ^ ((d : ℝ) / 4 + 1 / 2) *
      t ^ (η - (d : ℝ) / 4 - 1 / 2) +
    (2 + (C₀ + (10 * C₀ + 32) * A) * (1 + Real.sqrt 8) * Real.sqrt CB) *
      psT0 d σ θ CV η t (t ^ (η / (d + 2))))

variable {d : ℕ} [NeZero d] {ω : Configuration d}

theorem psGauss_nonneg (d : ℕ) (σ θ : ℝ) : 0 ≤ psGauss d σ θ := Real.sqrt_nonneg _

theorem exp_neg_div_le {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hbc : b ≤ c) :
    Real.exp (-(a / b)) ≤ Real.exp (-(a / c)) := by
  apply Real.exp_le_exp.2
  rw [neg_le_neg_iff]
  exact div_le_div_of_nonneg_left ha hb hbc

variable {K : OpenComponent ω} {σ θ : ℝ} {y : Vertex d}

omit [NeZero d] in
/-- The tails of the differences are at most `T₀`. -/
theorem tail_gaussFlowDiff_le_psT0 (hσ : 0 < σ) (hθ : 0 < θ) {s t η L CV : ℝ} (ht : 0 ≤ t)
    (hs : t ^ η ≤ s) (hst : s ≤ t) (hCV : 0 < CV) :
    CV * (4 * Real.pi * CV * s) ^ ((d : ℝ) / 2) * gaussMassBoundD d CV *
          Real.exp (-(L ^ 2 / (16 * CV))) + CV * expMassBoundD d CV * Real.exp (-(s / CV)) +
        2 / θ * (2 ^ ((d : ℝ) / 2) * gaussMassBoundD d σ) *
          (Real.exp (-(L ^ 2 / (16 * σ))) + Real.exp (-(L ^ 2 / (12 * σ)))) ≤
      psT0 d σ θ CV η t L := by
  have htη : 0 ≤ t ^ η := Real.rpow_nonneg ht _
  have hs0 : 0 ≤ s := htη.trans hs
  have hM : 0 ≤ gaussMassBoundD d CV := by linarith [one_le_gaussMassBoundD (d := d) hCV]
  have hMσ : 0 ≤ gaussMassBoundD d σ := by linarith [one_le_gaussMassBoundD (d := d) hσ]
  have hE := expMassBoundD_nonneg d CV
  unfold psT0
  have h1 : (4 * Real.pi * CV * s) ^ ((d : ℝ) / 2) ≤ (4 * Real.pi * CV * t) ^ ((d : ℝ) / 2) :=
    Real.rpow_le_rpow (by positivity) (by gcongr) (by positivity)
  have h2 : Real.exp (-(s / CV)) ≤ Real.exp (-(t ^ η / (2 * CV))) := by
    apply Real.exp_le_exp.2
    rw [neg_le_neg_iff, div_le_div_iff₀ (by positivity) hCV]
    nlinarith
  have h3 : Real.exp (-(L ^ 2 / (12 * σ))) ≤ Real.exp (-(L ^ 2 / (16 * σ))) :=
    exp_neg_div_le (sq_nonneg L) (by positivity) (by linarith)
  have hG : 0 ≤ 2 ^ ((d : ℝ) / 2) * gaussMassBoundD d σ := by positivity
  have hA : CV * (4 * Real.pi * CV * s) ^ ((d : ℝ) / 2) * gaussMassBoundD d CV *
      Real.exp (-(L ^ 2 / (16 * CV))) ≤ CV * (4 * Real.pi * CV * t) ^ ((d : ℝ) / 2) *
      gaussMassBoundD d CV * Real.exp (-(L ^ 2 / (16 * CV))) := by gcongr
  have hB : CV * expMassBoundD d CV * Real.exp (-(s / CV)) ≤
      CV * expMassBoundD d CV * Real.exp (-(t ^ η / (2 * CV))) := by gcongr
  have hC : 2 / θ * (2 ^ ((d : ℝ) / 2) * gaussMassBoundD d σ) *
      (Real.exp (-(L ^ 2 / (16 * σ))) + Real.exp (-(L ^ 2 / (12 * σ)))) ≤
      4 / θ * (2 ^ ((d : ℝ) / 2) * gaussMassBoundD d σ) * Real.exp (-(L ^ 2 / (16 * σ))) := by
    have : 2 / θ * (2 ^ ((d : ℝ) / 2) * gaussMassBoundD d σ) * (Real.exp (-(L ^ 2 / (16 * σ))) +
        Real.exp (-(L ^ 2 / (12 * σ)))) ≤ 2 / θ * (2 ^ ((d : ℝ) / 2) * gaussMassBoundD d σ) *
        (Real.exp (-(L ^ 2 / (16 * σ))) + Real.exp (-(L ^ 2 / (16 * σ)))) := by gcongr
    have e : 2 / θ * (2 ^ ((d : ℝ) / 2) * gaussMassBoundD d σ) * (Real.exp (-(L ^ 2 / (16 * σ))) +
        Real.exp (-(L ^ 2 / (16 * σ)))) = 4 / θ * (2 ^ ((d : ℝ) / 2) * gaussMassBoundD d σ) *
        Real.exp (-(L ^ 2 / (16 * σ))) := by ring
    linarith
  linarith

omit [NeZero d] in
/-- The tail of the initial error is at most `T₀`. -/
theorem tail_initialError_le_psT0 (hσ : 0 < σ) (hθ : 0 < θ) {s t η L CV : ℝ} (ht : 0 ≤ t)
    (hs : t ^ η ≤ s) (hst : s ≤ t) (hCV : 0 < CV) :
    CV * (2 * Real.pi * CV * s) ^ ((d : ℝ) / 2) * gaussMassBoundD d CV *
          Real.exp (-(L ^ 2 / (2 * CV))) + CV * expMassBoundD d CV * Real.exp (-(s / (2 * CV))) +
        2 / θ * (2 ^ ((d : ℝ) / 2) * gaussMassBoundD d σ) * Real.exp (-(L ^ 2 / (4 * σ))) ≤
      psT0 d σ θ CV η t L := by
  have htη : 0 ≤ t ^ η := Real.rpow_nonneg ht _
  have hs0 : 0 ≤ s := htη.trans hs
  have hM : 0 ≤ gaussMassBoundD d CV := by linarith [one_le_gaussMassBoundD (d := d) hCV]
  have hMσ : 0 ≤ gaussMassBoundD d σ := by linarith [one_le_gaussMassBoundD (d := d) hσ]
  have hE := expMassBoundD_nonneg d CV
  unfold psT0
  have h1 : (2 * Real.pi * CV * s) ^ ((d : ℝ) / 2) ≤ (4 * Real.pi * CV * t) ^ ((d : ℝ) / 2) :=
    Real.rpow_le_rpow (by positivity) (by
      calc 2 * Real.pi * CV * s ≤ 2 * Real.pi * CV * t := by gcongr
        _ ≤ 4 * Real.pi * CV * t := by
          have : 0 ≤ 2 * Real.pi * CV * t := by positivity
          linarith) (by positivity)
  have h1' : Real.exp (-(L ^ 2 / (2 * CV))) ≤ Real.exp (-(L ^ 2 / (16 * CV))) :=
    exp_neg_div_le (sq_nonneg L) (by positivity) (by linarith)
  have h2 : Real.exp (-(s / (2 * CV))) ≤ Real.exp (-(t ^ η / (2 * CV))) := by
    apply Real.exp_le_exp.2
    rw [neg_le_neg_iff]
    exact div_le_div_of_nonneg_right hs (by positivity)
  have h3 : Real.exp (-(L ^ 2 / (4 * σ))) ≤ Real.exp (-(L ^ 2 / (16 * σ))) :=
    exp_neg_div_le (sq_nonneg L) (by positivity) (by linarith)
  have hG : 0 ≤ 2 ^ ((d : ℝ) / 2) * gaussMassBoundD d σ := by positivity
  have hA : CV * (2 * Real.pi * CV * s) ^ ((d : ℝ) / 2) * gaussMassBoundD d CV *
      Real.exp (-(L ^ 2 / (2 * CV))) ≤ CV * (4 * Real.pi * CV * t) ^ ((d : ℝ) / 2) *
      gaussMassBoundD d CV * Real.exp (-(L ^ 2 / (16 * CV))) := by gcongr
  have hB : CV * expMassBoundD d CV * Real.exp (-(s / (2 * CV))) ≤
      CV * expMassBoundD d CV * Real.exp (-(t ^ η / (2 * CV))) := by gcongr
  have hC : 2 / θ * (2 ^ ((d : ℝ) / 2) * gaussMassBoundD d σ) * Real.exp (-(L ^ 2 / (4 * σ))) ≤
      4 / θ * (2 ^ ((d : ℝ) / 2) * gaussMassBoundD d σ) * Real.exp (-(L ^ 2 / (16 * σ))) := by
    have : 2 / θ * (2 ^ ((d : ℝ) / 2) * gaussMassBoundD d σ) * Real.exp (-(L ^ 2 / (4 * σ))) ≤
        2 / θ * (2 ^ ((d : ℝ) / 2) * gaussMassBoundD d σ) * Real.exp (-(L ^ 2 / (16 * σ))) := by
      gcongr
    have h4 : 0 ≤ 2 / θ * (2 ^ ((d : ℝ) / 2) * gaussMassBoundD d σ) *
        Real.exp (-(L ^ 2 / (16 * σ))) := by positivity
    have e : 4 / θ * (2 ^ ((d : ℝ) / 2) * gaussMassBoundD d σ) * Real.exp (-(L ^ 2 / (16 * σ))) =
        2 * (2 / θ * (2 ^ ((d : ℝ) / 2) * gaussMassBoundD d σ) *
          Real.exp (-(L ^ 2 / (16 * σ)))) := by ring
    linarith
  linarith

end Rigidity.Green
