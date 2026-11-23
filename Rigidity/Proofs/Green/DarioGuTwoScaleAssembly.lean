import Rigidity.Proofs.Green.DarioGuTwoScaleClusterBounds

/-!
# Proposition 4.3 of Dario–Gu from the estimate of the source term

The deterministic part of the proof of Proposition 4.3 of Dario–Gu (Steps 1, 2 and 5, lines
2241-2490 of the source), for one configuration: if the corrector grows at most linearly on the
cluster and the source term satisfies, at every time `s ∈ (τ, t)` and for every truncated weight
`ψ_R = dgWeightTrunc C s R y` (`ψ_0 = 1`), the estimate of Steps 3-4
`Σ_x ψ_R² u G ≤ E(ψ_R u) + (2s)^{-1} Σ_x (ψ_R u)² + Q s^{α - 3}`, then
`‖w(t, ·, τ, y) exp(dgExponent C t |· - y|)‖_{L²(𝒞_∞)} ≤ √K' (t/τ)^{1/2} τ^{-1 + α/2}`
(`dgW_weightedL2Le_of_sourceBound`).

* `clusterW_first_pass`: (4.40), `Σ_x u(t)² ≤ 2Q/(3 - α) (t/τ) τ^{α - 2}`;
* `clusterW_second_pass`: the bound with the truncated weight, uniform in `R`.
-/

open scoped Classical
open LatticeProb LatticeProb.Percolation

namespace Rigidity.Green

theorem dgWeightTrunc_zero (C s : ℝ) (y x : Vertex 2) : dgWeightTrunc C s 0 y x = 1 := by
  unfold dgWeightTrunc dgShape
  rw [min_eq_right (latticeDist_nonneg x y)]
  split_ifs <;> simp

/-- **(4.40) for `u = 1_K w`**: the first pass of Step 5. -/
theorem clusterW_first_pass {ω : Configuration 2} {K : OpenComponent ω} {σ θ τ t A Q α : ℝ}
    {χ : Fin 2 → Vertex 2 → ℝ} {y : Vertex 2} (hχK : IsDGCorrector K y χ) (hσ : 0 < σ)
    (hτ : 0 < τ) (hτt : τ ≤ t) (hA : 0 ≤ A)
    (hχ : ∀ x ∈ K.supp, ∀ k, |χ k x| ≤ A * (1 + latticeDist x y)) (hQ : 0 ≤ Q) (hα : α < 3)
    (hsrc : ∀ s ∈ Set.Ioo τ t,
      ∑' x, clusterW K σ θ χ τ y s x * clusterSource K σ θ χ y s x ≤
        openEnergy ω (clusterW K σ θ χ τ y s) +
          1 / (2 * s) * ∑' x, clusterW K σ θ χ τ y s x ^ 2 + Q * s ^ (α - 3)) :
    ∑' x, clusterW K σ θ χ τ y t x ^ 2 ≤ 2 * Q / (3 - α) * (t / τ) * τ ^ (α - 2) := by
  obtain ⟨D, hD, hDu⟩ := exists_clusterW_dom (θ := θ) hσ hτ hτt hA hχ
  obtain ⟨D', hD', hDu'⟩ := exists_clusterW_deriv_dom (θ := θ) hχK hσ hτ hτt hA hχ
  have hf := summable_sq_clusterInit (θ := θ) hσ hτ hA hχ
  have hcont : ContinuousOn (fun s => ∑' x, clusterW K σ θ χ τ y s x ^ 2) (Set.Icc τ t) := by
    have h := continuousOn_tsum_sq_mul (ψ := fun _ _ => (1 : ℝ)) (B := 1) hD hDu
      (fun _ _ _ => by simp) (fun x => continuousOn_clusterW hσ hτ hf x)
      (fun _ => continuousOn_const)
    simpa only [one_mul] using h
  exact energy_first_pass ω (u := clusterW K σ θ χ τ y) (G := clusterSource K σ θ χ y) hτ hτt hQ
    hα hD hD' (fun s hs x => hDu s ⟨hs.1.le, hs.2.le⟩ x)
    (fun s hs x => hDu' s ⟨hs.1, hs.2.le⟩ x)
    (fun s hs x => hasDerivAt_clusterW hχK hσ hf (T := t - τ + 1)
      ⟨by linarith [hs.1], by linarith [hs.2]⟩ (hτ.trans hs.1) x)
    hcont (fun x => clusterW_self K σ θ χ τ y x) hsrc

/-- **The weighted bound for `u = 1_K w`**: the second pass of Step 5, uniform in the truncation
radius `R`. -/
theorem clusterW_second_pass {ω : Configuration 2} {K : OpenComponent ω}
    {σ θ τ t A Q α C C₁ R : ℝ} {χ : Fin 2 → Vertex 2 → ℝ} {y : Vertex 2}
    (hχK : IsDGCorrector K y χ) (hσ : 0 < σ) (hτ1 : 1 ≤ τ) (hτt : τ ≤ t) (hA : 0 ≤ A)
    (hχ : ∀ x ∈ K.supp, ∀ k, |χ k x| ≤ A * (1 + latticeDist x y)) (hQ : 0 ≤ Q) (hα : α < 2)
    (hC : 0 < C) (hC₁ : 0 ≤ C₁)
    (hwtb : ∀ (s R : ℝ) (x : Vertex 2), 1 ≤ s → 0 ≤ R →
      dgWeightTrunc C s R y x ^ 2 *
          (dgShapeTimeDeriv s (min (latticeDist x y) R) / C + 1 / 2 / s) +
        1 * edgeKappa ω (dgWeightTrunc C s R y) x ≤ C₁ / s)
    (hsrc : ∀ s ∈ Set.Ioo τ t, ∀ R : ℝ, 0 ≤ R →
      ∑' x, dgWeightTrunc C s R y x ^ 2 * clusterW K σ θ χ τ y s x *
          clusterSource K σ θ χ y s x ≤
        openEnergy ω (fun x => dgWeightTrunc C s R y x * clusterW K σ θ χ τ y s x) +
          1 / (2 * s) * ∑' x, (dgWeightTrunc C s R y x * clusterW K σ θ χ τ y s x) ^ 2 +
            Q * s ^ (α - 3))
    (hR : 0 ≤ R) :
    ∑' x, (dgWeightTrunc C t R y x * clusterW K σ θ χ τ y t x) ^ 2 ≤
      2 * C₁ * (2 * Q / (3 - α)) * (t / τ) * τ ^ (α - 2) + 2 * Q / (2 - α) * τ ^ (α - 2) := by
  have hτ : 0 < τ := by linarith
  have hfirst : ∀ s ∈ Set.Ioo τ t, ∑' x, clusterW K σ θ χ τ y s x ^ 2 ≤
      2 * Q / (3 - α) * (s / τ) * τ ^ (α - 2) := by
    intro s hs
    refine clusterW_first_pass hχK hσ hτ hs.1.le hA hχ hQ (by linarith) fun r hr => ?_
    have h := hsrc r ⟨hr.1, hr.2.trans hs.2⟩ 0 le_rfl
    simpa only [dgWeightTrunc_zero, one_pow, one_mul] using h
  obtain ⟨D, hD, hDu⟩ := exists_clusterW_dom (θ := θ) hσ hτ hτt hA hχ
  obtain ⟨D', hD', hDu'⟩ := exists_clusterW_deriv_dom (θ := θ) hχK hσ hτ hτt hA hχ
  have hf := summable_sq_clusterInit (θ := θ) hσ hτ hA hχ
  set B := Real.exp (R ^ 2 / τ / C) with hB
  have hψS : ∀ s, τ ≤ s → ∀ x, |dgWeightTrunc C s R y x| ≤ B := by
    intro s hs x
    have hs0 : 0 < s := hτ.trans_le hs
    rw [abs_of_pos (dgWeightTrunc_pos C s R y x)]
    refine (dgWeightTrunc_le hC hs0 hR y x).trans (Real.exp_le_exp.2 ?_)
    exact div_le_div_of_nonneg_right (div_le_div_of_nonneg_left (sq_nonneg R) hτ hs) hC.le
  have hψ' : ∀ s ∈ Set.Ioo τ t, ∀ x,
      |dgWeightTrunc C s R y x * (dgShapeTimeDeriv s (min (latticeDist x y) R) / C)| ≤
        B * ((R ^ 2 / τ ^ 2 + R / τ) / C) := by
    intro s hs x
    have hs0 : 0 < s := hτ.trans hs.1
    have hm0 : 0 ≤ min (latticeDist x y) R := le_min (latticeDist_nonneg x y) hR
    have hmR : min (latticeDist x y) R ≤ R := min_le_right _ _
    have h1 := abs_dgShapeTimeDeriv_le hs0 hm0
    have h2 : min (latticeDist x y) R ^ 2 / s ^ 2 ≤ R ^ 2 / τ ^ 2 :=
      (div_le_div_of_nonneg_right (pow_le_pow_left₀ hm0 hmR 2) (sq_nonneg s)).trans
        (div_le_div_of_nonneg_left (sq_nonneg R) (by positivity)
          (pow_le_pow_left₀ hτ.le hs.1.le 2))
    have h3 : min (latticeDist x y) R / s ≤ R / τ :=
      (div_le_div_of_nonneg_right hmR hs0.le).trans
        (div_le_div_of_nonneg_left hR hτ hs.1.le)
    rw [abs_mul, abs_div, abs_of_pos hC]
    refine mul_le_mul (hψS s hs.1.le x) (div_le_div_of_nonneg_right ?_ hC.le) (by positivity)
      (Real.exp_pos _).le
    linarith
  have hcont : ContinuousOn
      (fun s => ∑' x, (dgWeightTrunc C s R y x * clusterW K σ θ χ τ y s x) ^ 2)
      (Set.Icc τ t) :=
    continuousOn_tsum_sq_mul hD hDu (fun s hs x => hψS s hs.1 x)
      (fun x => continuousOn_clusterW hσ hτ hf x)
      (fun x s hs => (hasDerivAt_dgWeightTrunc (C := C) (R := R) (hτ.trans_le hs.1) y x)
        |>.continuousAt.continuousWithinAt)
  refine energy_second_pass ω (u := clusterW K σ θ χ τ y) (G := clusterSource K σ θ χ y)
    (ψ := fun s => dgWeightTrunc C s R y)
    (ψ' := fun s x => dgWeightTrunc C s R y x * (dgShapeTimeDeriv s (min (latticeDist x y) R) / C))
    (c := C₁) (B := B) (B' := B * ((R ^ 2 / τ ^ 2 + R / τ) / C)) (B₀ := 2 * Q / (3 - α))
    hτ hτt hQ hα hC₁ (div_nonneg (by positivity) (by linarith)) hD hD'
    (fun s hs x => hDu s ⟨hs.1.le, hs.2.le⟩ x) (fun s hs x => hDu' s ⟨hs.1, hs.2.le⟩ x)
    (fun s hs x => hψS s hs.1.le x) hψ'
    (fun s hs x => hasDerivAt_clusterW hχK hσ hf (T := t - τ + 1)
      ⟨by linarith [hs.1], by linarith [hs.2]⟩ (hτ.trans hs.1) x)
    (fun s hs x => hasDerivAt_dgWeightTrunc (hτ.trans hs.1) y x) hcont
    (fun x => clusterW_self K σ θ χ τ y x) (fun s hs => hsrc s hs R hR) ?_ hfirst
  · intro s hs x
    have hs1 : 1 ≤ s := hτ1.trans hs.1.le
    have h := hwtb s R x hs1 hR
    have e : dgWeightTrunc C s R y x *
          (dgWeightTrunc C s R y x * (dgShapeTimeDeriv s (min (latticeDist x y) R) / C)) +
        edgeKappa ω (dgWeightTrunc C s R y) x + dgWeightTrunc C s R y x ^ 2 / (2 * s) =
        dgWeightTrunc C s R y x ^ 2 *
          (dgShapeTimeDeriv s (min (latticeDist x y) R) / C + 1 / 2 / s) +
        1 * edgeKappa ω (dgWeightTrunc C s R y) x := by
      ring
    rw [e]
    exact h

/-- **Proposition 4.3 of Dario–Gu for one configuration, from the estimate of Steps 3-4**:
`‖w(t, ·, τ, y) exp(dgExponent C t |· - y|)‖_{L²(𝒞_∞)} ≤ √K' (t/τ)^{1/2} τ^{-1 + α/2}` with
`K' = 2 C₁ (2Q/(3 - α)) + 2Q/(2 - α)`. -/
theorem dgW_weightedL2Le_of_sourceBound {ω : Configuration 2} {K : OpenComponent ω}
    {σ θ τ t A Q α C C₁ : ℝ} {χ : Fin 2 → Vertex 2 → ℝ} {y : Vertex 2}
    (hχK : IsDGCorrector K y χ) (hσ : 0 < σ) (hτ1 : 1 ≤ τ) (hτt : τ ≤ t) (hA : 0 ≤ A)
    (hχ : ∀ x ∈ K.supp, ∀ k, |χ k x| ≤ A * (1 + latticeDist x y)) (hQ : 0 ≤ Q) (hα : α < 2)
    (hC : 0 < C) (hC₁ : 0 ≤ C₁)
    (hwtb : ∀ (s R : ℝ) (x : Vertex 2), 1 ≤ s → 0 ≤ R →
      dgWeightTrunc C s R y x ^ 2 *
          (dgShapeTimeDeriv s (min (latticeDist x y) R) / C + 1 / 2 / s) +
        1 * edgeKappa ω (dgWeightTrunc C s R y) x ≤ C₁ / s)
    (hsrc : ∀ s ∈ Set.Ioo τ t, ∀ R : ℝ, 0 ≤ R →
      ∑' x, dgWeightTrunc C s R y x ^ 2 * clusterW K σ θ χ τ y s x *
          clusterSource K σ θ χ y s x ≤
        openEnergy ω (fun x => dgWeightTrunc C s R y x * clusterW K σ θ χ τ y s x) +
          1 / (2 * s) * ∑' x, (dgWeightTrunc C s R y x * clusterW K σ θ χ τ y s x) ^ 2 +
            Q * s ^ (α - 3)) :
    WeightedL2Le K.supp C t y (fun x => dgW ω σ θ χ t τ x y)
      (Real.sqrt (2 * C₁ * (2 * Q / (3 - α)) + 2 * Q / (2 - α)) * (t / τ) ^ (1 / 2 : ℝ) *
        τ ^ (-(1 : ℝ) + α / 2)) := by
  have hτ : 0 < τ := by linarith
  have ht0 : 0 < t := hτ.trans_le hτt
  set K' := 2 * C₁ * (2 * Q / (3 - α)) + 2 * Q / (2 - α) with hK'def
  have h3 : 0 ≤ 2 * Q / (3 - α) := div_nonneg (by linarith) (by linarith)
  have h2 : 0 ≤ 2 * Q / (2 - α) := div_nonneg (by linarith) (by linarith)
  have hK' : 0 ≤ K' := by positivity
  have hf := summable_sq_clusterInit (θ := θ) hσ hτ hA hχ
  obtain ⟨D, hD, hDu⟩ := exists_clusterW_dom (θ := θ) hσ hτ hτt hA hχ
  have hut : Summable fun x => clusterW K σ θ χ τ y t x ^ 2 :=
    Summable.of_nonneg_of_le (fun x => sq_nonneg _)
      (fun x => sq_le_sq_of_abs_le (hDu t ⟨hτt, le_rfl⟩ x)) hD
  refine weightedL2Le_of_trunc fun R hR S hS => ?_
  have hb := clusterW_second_pass hχK hσ hτ1 hτt hA hχ hQ hα hC hC₁ hwtb hsrc hR
  have e : ∑ x ∈ S, (dgW ω σ θ χ t τ x y * dgWeightTrunc C t R y x) ^ 2 =
      ∑ x ∈ S, (dgWeightTrunc C t R y x * clusterW K σ θ χ τ y t x) ^ 2 :=
    Finset.sum_congr rfl fun x hx => by
      rw [clusterW_eq_dgW hσ hτ hτt hf (hS x hx)]
      ring
  rw [e]
  have hsum : Summable fun x => (dgWeightTrunc C t R y x * clusterW K σ θ χ τ y t x) ^ 2 :=
    summable_sq_mul_of_abs_le (B := Real.exp (R ^ 2 / t / C)) (fun x => by
      rw [abs_of_pos (dgWeightTrunc_pos C t R y x)]
      exact dgWeightTrunc_le hC ht0 hR y x) hut
  refine (sum_le_of_tsum_le hsum hb).trans ?_
  have hsq : (Real.sqrt K' * (t / τ) ^ (1 / 2 : ℝ) * τ ^ (-(1 : ℝ) + α / 2)) ^ 2 =
      K' * (t / τ) * τ ^ (α - 2) := by
    rw [← Real.sqrt_eq_rpow, mul_pow, mul_pow, Real.sq_sqrt hK',
      Real.sq_sqrt (div_nonneg ht0.le hτ.le), sq (τ ^ _), ← Real.rpow_add hτ,
      show -(1 : ℝ) + α / 2 + (-(1 : ℝ) + α / 2) = α - 2 by ring]
  rw [hsq]
  have ht1 : 1 ≤ t / τ := (one_le_div hτ).2 hτt
  have hq : 0 ≤ 2 * Q / (2 - α) * τ ^ (α - 2) := mul_nonneg h2 (by positivity)
  have hm := mul_le_mul_of_nonneg_left ht1 hq
  have expand : K' * (t / τ) * τ ^ (α - 2) =
      2 * C₁ * (2 * Q / (3 - α)) * (t / τ) * τ ^ (α - 2) +
        2 * Q / (2 - α) * τ ^ (α - 2) * (t / τ) := by
    rw [hK'def]
    ring
  linarith

end Rigidity.Green
