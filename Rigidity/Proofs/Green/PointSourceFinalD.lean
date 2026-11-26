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
the radii `√s log(2 + t)` of the written proof; the powers of `L` they produce are absorbed in
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

omit [NeZero d] in
theorem psCN_nonneg {σ θ CA CG : ℝ} (hθ : 0 < θ) (hCA : 0 ≤ CA) (hCG : 0 ≤ CG) :
    0 ≤ psCN d σ θ CA CG := by
  unfold psCN
  have := psGauss_nonneg d σ θ
  positivity

omit [NeZero d] in
theorem psCE_nonneg {σ θ CB : ℝ} (hθ : 0 < θ) : 0 ≤ psCE d σ θ CB := by
  unfold psCE
  have := psGauss_nonneg d σ θ
  positivity

omit [NeZero d] in
theorem psT0_nonneg {σ θ CV η t L : ℝ} (hσ : 0 < σ) (hθ : 0 < θ) (hCV : 0 < CV) (ht : 0 ≤ t) :
    0 ≤ psT0 d σ θ CV η t L := by
  unfold psT0
  have hM : 0 ≤ gaussMassBoundD d CV := by linarith [one_le_gaussMassBoundD (d := d) hCV]
  have hMσ : 0 ≤ gaussMassBoundD d σ := by linarith [one_le_gaussMassBoundD (d := d) hσ]
  have hE := expMassBoundD_nonneg d CV
  positivity

theorem one_lt_log_three : 1 < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

/-- `J ≤ log t` for `3^J ≤ t`. -/
theorem natCast_le_log_of_three_pow_le {J : ℕ} {t : ℝ} (h : (3 : ℝ) ^ J ≤ t) :
    (J : ℝ) ≤ Real.log t := by
  have h1 : Real.log ((3 : ℝ) ^ J) ≤ Real.log t := Real.log_le_log (by positivity) h
  rw [Real.log_pow] at h1
  have h3 := one_lt_log_three
  nlinarith [Nat.cast_nonneg (α := ℝ) J]

/-- **The point source at one configuration and one time.** -/
theorem l2norm_pointSource_le_of_time {K : OpenComponent ω} {y : Vertex d} (hy : y ∈ K.supp)
    (hacc : ∀ ρ, LatticeProb.Network.BoundaryAccessible (openGraph ω)
      (interiorOf (openGraph ω) (clusterBall K y ρ)))
    {X C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hOZ : ∀ R', 2 * X ≤ R' → ∀ u : Vertex d → ℝ,
      (∀ x ∈ interiorOf (openGraph ω) (clusterBall K y R'),
        LatticeProb.Graph.laplacian (openGraph ω) u x = 0) →
      ∃ c : ℝ, ∀ r, X ≤ r → r ≤ R' / 2 →
        nL2 (clusterBall K y r) (fun x => u x - c) ≤ C₀ * (r / R') * nL2 (clusterBall K y R') u)
    {A ρ₀ : ℝ} (hA : 0 ≤ A)
    (hHK : ∀ ρ, ρ₀ ≤ ρ → ∀ z ∈ interiorOf (openGraph ω) (clusterBall K y ρ),
      ∑ w ∈ interiorOf (openGraph ω) (clusterBall K y ρ),
        vsrwHeat (openGraph ω) (2 * d) (A * ρ ^ 2) z w ≤ 1 / 2)
    {σ θ η CB CA CG CV : ℝ} (hσ : 0 < σ) (hθ : 0 < θ) (hη0 : 0 < η) (hη : η ≤ 1 / 8)
    (hCB : 0 ≤ CB) (hCA : 0 ≤ CA) (hCG : 0 ≤ CG) (hCV : 0 < CV)
    (hcv : ∀ w ∈ K.supp, ∀ u, 1 ≤ u → CVBranches ω CV u w)
    {t : ℝ} (ht : 1 ≤ t) (hL2 : 2 ≤ t ^ (η / (d + 2)))
    (hbig : 12 * (t ^ (η / (d + 2))) ^ 2 * t ^ η ≤ t)
    (hXl : X ≤ t ^ (η / 2) * t ^ (η / (d + 2)))
    (hρ₀ : ρ₀ ≤ 2 * (t ^ (η / 2) * t ^ (η / (d + 2))))
    (hdiag : ∀ z ∈ clusterBall K y (Real.sqrt t), ∀ r, t / 4 ≤ r → r ≤ 2 * t →
      vsrwHeat (openGraph ω) (2 * d) r z z ≤ CB * t ^ (-((d : ℝ) / 2)))
    (hdiagy : ∀ u, t ^ η ≤ u → u ≤ 3 * t ^ η →
      vsrwHeat (openGraph ω) (2 * d) (u + u) y y ≤ CB * u ^ (-((d : ℝ) / 2)))
    (hA7 : ∀ s, t ^ η ≤ s → s ≤ t → |clusterGaussMass K σ s y - θ| ≤ CA * s ^ (η - 1 / 2))
    (hsmall : CA * (t ^ η) ^ (η - 1 / 2) ≤ θ / 2)
    (hGF : ∀ s, t ^ η ≤ s → 3 * s ≤ t → l2norm (fun x => heatFlowG (openGraph ω) (2 * d) (2 * s)
        (fun z => θ⁻¹ * clusterInd K σ s y z) x - θ⁻¹ * clusterInd K σ (3 * s) y x) ≤
      CG * s ^ (η - (d : ℝ) / 4 - 1 / 2)) :
    l2norm (fun x => vsrwHeat (openGraph ω) (2 * d) t x y - clusterGaussNorm K σ t y x) ≤
      psBound d σ θ C₀ A CB CA CG CV η t := by
  set L := t ^ (η / (d + 2)) with hLdef
  have ht0 : 0 < t := by linarith
  have hL0 : 0 ≤ L := by linarith
  have htη1 : 1 ≤ t ^ η := Real.one_le_rpow ht hη0.le
  -- the geometric times
  have hx : 1 ≤ t ^ (1 - η) := Real.one_le_rpow ht (by linarith)
  obtain ⟨J, hJ1, hJ2⟩ := exists_nat_pow_near hx (by norm_num : (1 : ℝ) < 3)
  have h3J : (0 : ℝ) < 3 ^ J := by positivity
  have htsplit : t = t ^ (1 - η) * t ^ η := by rw [← Real.rpow_add ht0]; simp
  set s0 := t / 3 ^ J with hs0
  have hs0lo : t ^ η ≤ s0 := by
    rw [hs0, le_div_iff₀ h3J]
    calc t ^ η * 3 ^ J ≤ t ^ η * t ^ (1 - η) := mul_le_mul_of_nonneg_left hJ1 (by positivity)
      _ = t := by rw [mul_comm, ← htsplit]
  have hs0hi : s0 ≤ 3 * t ^ η := by
    rw [hs0, div_le_iff₀ h3J]
    calc t = t ^ (1 - η) * t ^ η := htsplit
      _ ≤ 3 ^ (J + 1) * t ^ η := mul_le_mul_of_nonneg_right hJ2.le (by positivity)
      _ = 3 * t ^ η * 3 ^ J := by ring
  set s : ℕ → ℝ := fun j => 3 ^ j * s0 with hsdef
  have hs : ∀ j, s (j + 1) = 3 * s j := fun j => by simp only [hsdef]; ring
  have hsJ : s J = t := by simp only [hsdef, hs0]; field_simp
  have hs00 : s 0 = s0 := by simp [hsdef]
  have hslo : ∀ j, t ^ η ≤ s j := fun j => by
    simp only [hsdef]
    have : (1 : ℝ) ≤ 3 ^ j := one_le_pow₀ (by norm_num)
    nlinarith
  have hshi : ∀ j, j ≤ J → s j ≤ t := fun j hj => by
    rw [← hsJ]; simp only [hsdef]
    have : (3 : ℝ) ^ j ≤ 3 ^ J := pow_le_pow_right₀ (by norm_num) hj
    nlinarith
  have hs1 : ∀ j, 1 ≤ s j := fun j => htη1.trans (hslo j)
  -- smallness and the masses
  have hsm : ∀ u, t ^ η ≤ u → CA * u ^ (η - 1 / 2) ≤ θ / 2 := fun u hu =>
    le_trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by positivity) hu
      (by linarith)) hCA) hsmall
  have hMlo : ∀ u, t ^ η ≤ u → u ≤ t → θ / 2 ≤ clusterGaussMass K σ u y := fun u hu hut => by
    have h1 := abs_le.1 (hA7 u hu hut)
    have h2 := hsm u hu
    linarith
  -- the radii
  have hsq0 : t ^ (η / 2) ≤ Real.sqrt (s 0) := by
    rw [show t ^ (η / 2) = Real.sqrt (t ^ η) by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht0.le]; ring_nf]
    exact Real.sqrt_le_sqrt (hs00 ▸ hs0lo)
  have hrad : t ^ (η / 2) * L ≤ Real.sqrt (s 0) * L := mul_le_mul_of_nonneg_right hsq0 hL0
  have hs0t : 4 * L ^ 2 * s 0 ≤ s J := by
    rw [hsJ, hs00]
    calc 4 * L ^ 2 * s0 ≤ 4 * L ^ 2 * (3 * t ^ η) :=
          mul_le_mul_of_nonneg_left hs0hi (by positivity)
      _ = 12 * L ^ 2 * t ^ η := by ring
      _ ≤ t := hbig
  have hdiag' : ∀ z ∈ clusterBall K y (Real.sqrt (s J)), ∀ r, s J / 4 ≤ r → r ≤ 2 * s J →
      vsrwHeat (openGraph ω) (2 * d) r z z ≤ CB * s J ^ (-((d : ℝ) / 2)) := by
    rw [hsJ]; exact hdiag
  have hCN := psCN_nonneg (d := d) (σ := σ) hθ hCA hCG
  have hT₀ := psT0_nonneg (d := d) (θ := θ) (η := η) (L := L) hσ hθ hCV ht0.le
  have h := l2norm_pointSource_le (CE := psCE d σ θ CB) (CN := psCN d σ θ CA CG)
    hy hacc hC₀ hOZ hA hHK hσ hη0.le (by linarith) (hs1 0) hs J
    (by linarith) (hXl.trans hrad) (hρ₀.trans (by linarith)) hs0t hCB hCN hT₀ hdiag'
    (fun j hj => by linarith [hMlo (s j) (hslo j) (hshi j hj), hθ])
    (fun j hj => by
      have hsj : 0 < s j := by linarith [hs1 j]
      have h3 : 3 * s j ≤ t := by rw [← hs j]; exact hshi (j + 1) hj
      have hb := l2norm_gaussFlowDiff_le_of_inputs (K := K) (y := y) hσ hθ hsj (by linarith)
        (hA7 (s j) (hslo j) (hshi j hj.le)) (hsm (s j) (hslo j))
        (hA7 (3 * s j) (by linarith [hslo j]) h3) (hsm (3 * s j) (by linarith [hslo j]))
        (hGF (s j) (hslo j) h3)
      exact hb)
    (fun j hj => by
      have h3 : 3 * s j ≤ t := by rw [← hs j]; exact hshi (j + 1) hj
      have hb := tsum_out_gaussFlowDiff_le_of_cv (K := K) (y := y) hσ hθ (hs1 j) hL0 hCV
        (fun w hw => hcv w hw (2 * s j) (by linarith [hs1 j]))
        (hMlo (s j) (hslo j) (hshi j hj.le)) (hMlo (3 * s j) (by linarith [hslo j]) h3)
      exact hb.trans (tail_gaussFlowDiff_le_psT0 hσ hθ ht0.le (hslo j) (hshi j hj.le) hCV))
    (by
      have hb := l2norm_initialError_le (K := K) (y := y) hσ hθ (by linarith [hs1 0])
        (hA7 (s 0) (hslo 0) (hshi 0 (Nat.zero_le J))) (hsm (s 0) (hslo 0))
        (hdiagy (s 0) (hslo 0) (hs00 ▸ hs0hi))
      exact hb)
    (by
      have hb := tsum_out_initialError_le_of_cv (K := K) (y := y) hσ hθ (hs1 0) hL0 hCV hy
        (hcv y hy (s 0) (hs1 0)) (hMlo (s 0) (hslo 0) (hshi 0 (Nat.zero_le J)))
      exact hb.trans (tail_initialError_le_psT0 hσ hθ ht0.le (hslo 0) (hshi 0 (Nat.zero_le J))
        hCV))
  rw [hsJ] at h
  refine h.trans ?_
  -- the factor `s_0^{1/2}` and the number of terms
  have hJlog : (J : ℝ) ≤ Real.log t :=
    natCast_le_log_of_three_pow_le (hJ1.trans (Real.rpow_le_self_of_one_le ht (by linarith)))
  have hsq : s 0 ^ ((1 : ℝ) / 2) ≤ (3 * t ^ η) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow (by linarith [hs1 0]) (hs00 ▸ hs0hi) (by norm_num)
  have hCE := psCE_nonneg (d := d) (σ := σ) (CB := CB) hθ
  unfold psBound
  rw [← hLdef]
  have hκ : 0 ≤ (C₀ + (10 * C₀ + 32) * A) * (1 + Real.sqrt 8) := by positivity
  have hQ : 0 ≤ 5 ^ ((d : ℝ) / 2) * ((C₀ + (10 * C₀ + 32) * A) * (1 + Real.sqrt 8)) *
      Real.sqrt CB * psCN d σ θ CA CG * L ^ ((d : ℝ) / 2 + 1) * t ^ (η - (d : ℝ) / 4 - 1 / 2) +
    psCN d σ θ CA CG * (4 * L ^ 2) ^ ((d : ℝ) / 4 + 1 / 2) * t ^ (η - (d : ℝ) / 4 - 1 / 2) +
    (2 + (C₀ + (10 * C₀ + 32) * A) * (1 + Real.sqrt 8) * Real.sqrt CB) *
      psT0 d σ θ CV η t L := by positivity
  have hfirst : 5 ^ ((d : ℝ) / 2) * ((C₀ + (10 * C₀ + 32) * A) * (1 + Real.sqrt 8)) *
      Real.sqrt CB * psCE d σ θ CB * L ^ ((d : ℝ) / 2 + 1) * s 0 ^ ((1 : ℝ) / 2) *
      t ^ (-((d : ℝ) / 4) - 1 / 2) ≤
      5 ^ ((d : ℝ) / 2) * ((C₀ + (10 * C₀ + 32) * A) * (1 + Real.sqrt 8)) *
      Real.sqrt CB * psCE d σ θ CB * L ^ ((d : ℝ) / 2 + 1) * (3 * t ^ η) ^ ((1 : ℝ) / 2) *
      t ^ (-((d : ℝ) / 4) - 1 / 2) := by
    have h0 : 0 ≤ 5 ^ ((d : ℝ) / 2) * ((C₀ + (10 * C₀ + 32) * A) * (1 + Real.sqrt 8)) *
        Real.sqrt CB * psCE d σ θ CB * L ^ ((d : ℝ) / 2 + 1) := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq h0) (by positivity)
  have hsecond := mul_le_mul_of_nonneg_right hJlog hQ
  linarith

end Rigidity.Green
