import Rigidity.Proofs.Green.PointSourceSumD

/-!
# The norms of the differences from Proposition A.7 and the whole-cluster estimate

With the concentration of the Gaussian mass of the cluster (Dario–Gu, Proposition A.7)
`|M_r - θ| ≤ C_A r^{η - 1/2} ≤ θ/2` at the times `r`:

* `l2norm_clusterGaussNorm_sub_le`: `‖G_r - θ^{-1} b_r‖ ≤ K₁ r^{η - d/4 - 1/2}` with
  `K₁ = (2C_A/θ²) (2θ (2πσ)^{-d/2})^{1/2}`;
* `l2norm_gaussFlowDiff_le_of_inputs`: with the whole-cluster estimate
  `‖P_{2s} H_s - H_{3s}‖ ≤ C_G s^{η - d/4 - 1/2}` (Dario–Gu (4.40) with Proposition 2.12),
  `‖D_s‖ ≤ (2K₁ + C_G) s^{η - d/4 - 1/2}`;
* `l2norm_initialError_le`: with `p_{2u}(y, y) ≤ C_B u^{-d/2}`,
  `‖p_u(·, y) - G_u‖ ≤ (C_B^{1/2} + (2/θ)(2θ (2πσ)^{-d/2})^{1/2}) u^{-d/4}`.
-/

open scoped Classical
open LatticeProb.Percolation

namespace Rigidity.Green

variable {d : ℕ} {ω : Configuration d} {K : OpenComponent ω} {σ θ : ℝ} {y : Vertex d}

/-- `‖b_r‖ ≤ (2θ (2πσ)^{-d/2})^{1/2} r^{-d/4}` for `M_r ≤ 2θ`. -/
theorem l2norm_clusterInd_le (hσ : 0 < σ) (hθ : 0 < θ) {r : ℝ} (hr : 0 < r)
    (hM : clusterGaussMass K σ r y ≤ 2 * θ) :
    l2norm (clusterInd K σ r y) ≤
      Real.sqrt (2 * θ * (2 * Real.pi * σ) ^ (-((d : ℝ) / 2))) * r ^ (-((d : ℝ) / 4)) := by
  have h1 := sq_l2norm_clusterInd_le (K := K) (y := y) hσ hr
  have h2 : (2 * Real.pi * σ * r) ^ (-((d : ℝ) / 2)) * clusterGaussMass K σ r y ≤
      2 * θ * (2 * Real.pi * σ) ^ (-((d : ℝ) / 2)) * r ^ (-((d : ℝ) / 2)) := by
    rw [Real.mul_rpow (by positivity) hr.le]
    have : 0 ≤ (2 * Real.pi * σ) ^ (-((d : ℝ) / 2)) * r ^ (-((d : ℝ) / 2)) := by positivity
    nlinarith
  have h3 : Real.sqrt (2 * θ * (2 * Real.pi * σ) ^ (-((d : ℝ) / 2)) * r ^ (-((d : ℝ) / 2))) =
      Real.sqrt (2 * θ * (2 * Real.pi * σ) ^ (-((d : ℝ) / 2))) * r ^ (-((d : ℝ) / 4)) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_eq_rpow (r ^ _), ← Real.rpow_mul hr.le]
    ring_nf
  rw [← h3, ← Real.sqrt_sq (l2norm_nonneg _)]
  exact Real.sqrt_le_sqrt (h1.trans h2)

/-- **The normalization error**: `‖G_r - θ^{-1} b_r‖ ≤ K₁ r^{η - d/4 - 1/2}`. -/
theorem l2norm_clusterGaussNorm_sub_le (hσ : 0 < σ) (hθ : 0 < θ) {r η CA : ℝ} (hr : 0 < r)
    (hA7 : |clusterGaussMass K σ r y - θ| ≤ CA * r ^ (η - 1 / 2))
    (hsmall : CA * r ^ (η - 1 / 2) ≤ θ / 2) :
    l2norm (fun z => clusterGaussNorm K σ r y z - θ⁻¹ * clusterInd K σ r y z) ≤
      2 * CA / θ ^ 2 * Real.sqrt (2 * θ * (2 * Real.pi * σ) ^ (-((d : ℝ) / 2))) *
        r ^ (η - (d : ℝ) / 4 - 1 / 2) := by
  set M := clusterGaussMass K σ r y with hMdef
  have hab := abs_le.1 hA7
  have hM1 : θ / 2 ≤ M := by linarith
  have hM2 : M ≤ 2 * θ := by linarith
  have hM0 : 0 < M := by linarith
  have hCA : 0 ≤ CA * r ^ (η - 1 / 2) := (abs_nonneg _).trans hA7
  rw [l2norm_clusterGaussNorm_sub]
  have hinv : |M⁻¹ - θ⁻¹| ≤ 2 * (CA * r ^ (η - 1 / 2)) / θ ^ 2 := by
    have e : M⁻¹ - θ⁻¹ = (θ - M) / (M * θ) := by field_simp
    rw [e, abs_div, abs_of_pos (by positivity : 0 < M * θ), abs_sub_comm]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : θ ^ 2 ≤ 2 * (M * θ) := by nlinarith
    nlinarith [abs_nonneg (M - θ)]
  have hb := l2norm_clusterInd_le (K := K) (y := y) hσ hθ hr hM2
  have hexp : r ^ (η - 1 / 2) * r ^ (-((d : ℝ) / 4)) = r ^ (η - (d : ℝ) / 4 - 1 / 2) := by
    rw [← Real.rpow_add hr]; ring_nf
  calc |M⁻¹ - θ⁻¹| * l2norm (clusterInd K σ r y)
      ≤ 2 * (CA * r ^ (η - 1 / 2)) / θ ^ 2 *
          (Real.sqrt (2 * θ * (2 * Real.pi * σ) ^ (-((d : ℝ) / 2))) * r ^ (-((d : ℝ) / 4))) :=
        mul_le_mul hinv hb (l2norm_nonneg _) (by positivity)
    _ = 2 * CA / θ ^ 2 * Real.sqrt (2 * θ * (2 * Real.pi * σ) ^ (-((d : ℝ) / 2))) *
          (r ^ (η - 1 / 2) * r ^ (-((d : ℝ) / 4))) := by ring
    _ = _ := by rw [hexp]

/-- **The norm of `D_s`** from Proposition A.7 at `s` and `3s` and the whole-cluster estimate. -/
theorem l2norm_gaussFlowDiff_le_of_inputs [NeZero d] (hσ : 0 < σ) (hθ : 0 < θ) {s η CA CG : ℝ}
    (hs : 0 < s) (hη : η ≤ 1 / 2)
    (hA7 : |clusterGaussMass K σ s y - θ| ≤ CA * s ^ (η - 1 / 2))
    (hsmall : CA * s ^ (η - 1 / 2) ≤ θ / 2)
    (hA7' : |clusterGaussMass K σ (3 * s) y - θ| ≤ CA * (3 * s) ^ (η - 1 / 2))
    (hsmall' : CA * (3 * s) ^ (η - 1 / 2) ≤ θ / 2)
    (hGF : l2norm (fun x => heatFlowG (openGraph ω) (2 * d) (2 * s)
        (fun z => θ⁻¹ * clusterInd K σ s y z) x - θ⁻¹ * clusterInd K σ (3 * s) y x) ≤
      CG * s ^ (η - (d : ℝ) / 4 - 1 / 2)) :
    l2norm (gaussFlowDiff K σ s y) ≤
      (2 * (2 * CA / θ ^ 2 * Real.sqrt (2 * θ * (2 * Real.pi * σ) ^ (-((d : ℝ) / 2)))) + CG) *
        s ^ (η - (d : ℝ) / 4 - 1 / 2) := by
  have h := l2norm_gaussFlowDiff_le (K := K) (y := y) hσ hs θ
  have h1 := l2norm_clusterGaussNorm_sub_le (K := K) (y := y) hσ hθ hs hA7 hsmall
  have h3 := l2norm_clusterGaussNorm_sub_le (K := K) (y := y) hσ hθ (by linarith : 0 < 3 * s)
    hA7' hsmall'
  have hCA : 0 ≤ CA := by
    have h0 : 0 ≤ CA * s ^ (η - 1 / 2) := (abs_nonneg _).trans hA7
    exact nonneg_of_mul_nonneg_left h0 (by positivity)
  have hmono : (3 * s) ^ (η - (d : ℝ) / 4 - 1 / 2) ≤ s ^ (η - (d : ℝ) / 4 - 1 / 2) :=
    Real.rpow_le_rpow_of_nonpos hs (by linarith) (by
      have : (0 : ℝ) ≤ d / 4 := by positivity
      linarith)
  have hK : 0 ≤ 2 * CA / θ ^ 2 * Real.sqrt (2 * θ * (2 * Real.pi * σ) ^ (-((d : ℝ) / 2))) := by
    positivity
  have h3' := h3.trans (mul_le_mul_of_nonneg_left hmono hK)
  calc _ ≤ _ := h
    _ ≤ _ := add_le_add (add_le_add h1 hGF) h3'
    _ = _ := by ring

/-- **The norm of the initial error.** -/
theorem l2norm_initialError_le [NeZero d] (hσ : 0 < σ) (hθ : 0 < θ) {u η CA CB : ℝ} (hu : 0 < u)
    (hA7 : |clusterGaussMass K σ u y - θ| ≤ CA * u ^ (η - 1 / 2))
    (hsmall : CA * u ^ (η - 1 / 2) ≤ θ / 2)
    (hdiag : vsrwHeat (openGraph ω) (2 * d) (u + u) y y ≤ CB * u ^ (-((d : ℝ) / 2))) :
    l2norm (fun x => vsrwHeat (openGraph ω) (2 * d) u x y - clusterGaussNorm K σ u y x) ≤
      (Real.sqrt CB + 2 / θ * Real.sqrt (2 * θ * (2 * Real.pi * σ) ^ (-((d : ℝ) / 2)))) *
        u ^ (-((d : ℝ) / 4)) := by
  have hD := two_mul_pos_d (d := d)
  have hdeg := openGraph_degree_le ω
  set M := clusterGaussMass K σ u y with hMdef
  have hab := abs_le.1 hA7
  have hM1 : θ / 2 ≤ M := by linarith
  have hM2 : M ≤ 2 * θ := by linarith
  have hM0 : 0 < M := by linarith
  -- the heat kernel
  have hp2 : HasSum (fun x => vsrwHeat (openGraph ω) (2 * d) u x y ^ 2)
      (vsrwHeat (openGraph ω) (2 * d) (u + u) y y) := by
    have h := hasSum_heatDeriv_sq hD hdeg 0 hu.le y
    refine h.congr_fun fun x => ?_
    rw [heatDeriv_zero, vsrwHeat_symm hD hdeg u x y]
  have hpn : l2norm (fun x => vsrwHeat (openGraph ω) (2 * d) u x y) ≤
      Real.sqrt CB * u ^ (-((d : ℝ) / 4)) := by
    unfold l2norm
    rw [hp2.tsum_eq]
    have hCB : 0 ≤ CB := by
      have h0 : 0 ≤ CB * u ^ (-((d : ℝ) / 2)) :=
        (vsrwHeat_nonneg hD hdeg (by linarith) y y).trans hdiag
      exact nonneg_of_mul_nonneg_left h0 (by positivity)
    calc Real.sqrt (vsrwHeat (openGraph ω) (2 * d) (u + u) y y)
        ≤ Real.sqrt (CB * u ^ (-((d : ℝ) / 2))) := Real.sqrt_le_sqrt hdiag
      _ = _ := by
        rw [Real.sqrt_mul hCB, Real.sqrt_eq_rpow (u ^ _), ← Real.rpow_mul hu.le]
        ring_nf
  -- the normalized Gaussian
  have hGn : l2norm (clusterGaussNorm K σ u y) ≤
      2 / θ * Real.sqrt (2 * θ * (2 * Real.pi * σ) ^ (-((d : ℝ) / 2))) * u ^ (-((d : ℝ) / 4)) := by
    have e : clusterGaussNorm K σ u y = fun z => M⁻¹ * clusterInd K σ u y z := by
      funext z; unfold clusterGaussNorm; rw [← hMdef]; ring
    rw [e, l2norm_const_mul, abs_of_pos (inv_pos.2 hM0)]
    have hb := l2norm_clusterInd_le (K := K) (y := y) hσ hθ hu hM2
    have hMi : M⁻¹ ≤ 2 / θ := by
      rw [inv_le_comm₀ hM0 (by positivity)]; field_simp; linarith
    calc M⁻¹ * l2norm (clusterInd K σ u y)
        ≤ 2 / θ * (Real.sqrt (2 * θ * (2 * Real.pi * σ) ^ (-((d : ℝ) / 2))) *
            u ^ (-((d : ℝ) / 4))) := mul_le_mul hMi hb (l2norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hGs : Summable fun z => (-clusterGaussNorm K σ u y z) ^ 2 := by
    simpa using summable_sq_clusterGaussNorm (K := K) (y := y) hσ hu
  obtain ⟨-, htri⟩ := l2norm_add_le hp2.summable hGs
  have hneg : l2norm (fun z => -clusterGaussNorm K σ u y z) =
      l2norm (clusterGaussNorm K σ u y) := by
    unfold l2norm; simp_rw [neg_sq]
  have heq : (fun x => vsrwHeat (openGraph ω) (2 * d) u x y - clusterGaussNorm K σ u y x) =
      fun x => vsrwHeat (openGraph ω) (2 * d) u x y + -clusterGaussNorm K σ u y x :=
    funext fun x => sub_eq_add_neg _ _
  rw [heq]
  calc _ ≤ _ := htri
    _ ≤ Real.sqrt CB * u ^ (-((d : ℝ) / 4)) +
        2 / θ * Real.sqrt (2 * θ * (2 * Real.pi * σ) ^ (-((d : ℝ) / 2))) *
          u ^ (-((d : ℝ) / 4)) := by
        rw [hneg]; exact add_le_add hpn hGn
    _ = _ := by ring

end Rigidity.Green
