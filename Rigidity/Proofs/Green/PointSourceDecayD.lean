import Rigidity.Proofs.Green.PointSourceFinalD

/-!
# The decay of the bound of the point source

`psBound ≤ C t^{3η - d/4 - 1/2}` for all large `t` (`eventually_psBound_le`): with `L = t^{η/(d+2)}`
the powers `L^{d/2+1}` and `(4L²)^{d/4+1/2}` are `t^{η/2}` up to constants, `log t ≤ (2/η) t^{η/2}`,
and the tails `t^k e^{-t^a/c}` (`a > 0`) decay faster than every power
(`tendsto_rpow_mul_exp_neg_rpow`).
-/

open Filter Topology

namespace Rigidity.Green

/-- `t^k e^{-t^a/c} → 0` for `a, c > 0`. -/
theorem tendsto_rpow_mul_exp_neg_rpow (k : ℝ) {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    Tendsto (fun t : ℝ => t ^ k * Real.exp (-(t ^ a / c))) atTop (𝓝 0) := by
  have h1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k / a) (1 / c) (by positivity)
  have h2 : Tendsto (fun t : ℝ => t ^ a) atTop atTop := tendsto_rpow_atTop ha
  refine (h1.comp h2).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  simp only [Function.comp_apply]
  have e : a * (k / a) = k := by field_simp
  rw [← Real.rpow_mul ht.le, e]
  congr 2
  ring

/-- Eventually `t^k e^{-t^a/c} ≤ ε` for `ε > 0`. -/
theorem eventually_rpow_mul_exp_neg_rpow_le (k : ℝ) {a c ε : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hε : 0 < ε) : ∀ᶠ t : ℝ in atTop, t ^ k * Real.exp (-(t ^ a / c)) ≤ ε :=
  (tendsto_rpow_mul_exp_neg_rpow k ha hc).eventually (ge_mem_nhds hε)

variable {d : ℕ}

/-- `t^k psT0(t, t^γ) → 0` for `γ, η > 0`. -/
theorem eventually_rpow_mul_psT0_le (k : ℝ) {σ θ CV η γ ε : ℝ} (hσ : 0 < σ) (hθ : 0 < θ)
    (hCV : 0 < CV) (hη : 0 < η) (hγ : 0 < γ) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, t ^ k * psT0 d σ θ CV η t (t ^ γ) ≤ ε := by
  set K1 := CV * (4 * Real.pi * CV) ^ ((d : ℝ) / 2) * gaussMassBoundD d CV with hK1
  set K2 := CV * expMassBoundD d CV with hK2
  set K3 := 4 / θ * (2 ^ ((d : ℝ) / 2) * gaussMassBoundD d σ) with hK3
  have hM : 0 ≤ gaussMassBoundD d CV := by linarith [one_le_gaussMassBoundD (d := d) hCV]
  have hMσ : 0 ≤ gaussMassBoundD d σ := by linarith [one_le_gaussMassBoundD (d := d) hσ]
  have hK10 : 0 ≤ K1 := by positivity
  have hK20 : 0 ≤ K2 := mul_nonneg hCV.le (expMassBoundD_nonneg d CV)
  have hK30 : 0 ≤ K3 := by positivity
  have e1 := eventually_rpow_mul_exp_neg_rpow_le (k + (d : ℝ) / 2) (a := 2 * γ) (c := 16 * CV)
    (ε := ε / (3 * (K1 + 1))) (by positivity) (by positivity) (by positivity)
  have e2 := eventually_rpow_mul_exp_neg_rpow_le k (a := η) (c := 2 * CV)
    (ε := ε / (3 * (K2 + 1))) hη (by positivity) (by positivity)
  have e3 := eventually_rpow_mul_exp_neg_rpow_le k (a := 2 * γ) (c := 16 * σ)
    (ε := ε / (3 * (K3 + 1))) (by positivity) (by positivity) (by positivity)
  filter_upwards [e1, e2, e3, eventually_gt_atTop (0 : ℝ)] with t h1 h2 h3 ht
  have hL : (t ^ γ) ^ 2 = t ^ (2 * γ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]; ring_nf
  unfold psT0
  rw [hL]
  have hp : t ^ k * ((4 * Real.pi * CV * t) ^ ((d : ℝ) / 2)) =
      (4 * Real.pi * CV) ^ ((d : ℝ) / 2) * t ^ (k + (d : ℝ) / 2) := by
    rw [Real.mul_rpow (by positivity) ht.le, Real.rpow_add ht]; ring
  have hsplit : t ^ k * (CV * (4 * Real.pi * CV * t) ^ ((d : ℝ) / 2) * gaussMassBoundD d CV *
        Real.exp (-(t ^ (2 * γ) / (16 * CV))) + CV * expMassBoundD d CV *
        Real.exp (-(t ^ η / (2 * CV))) + 4 / θ * (2 ^ ((d : ℝ) / 2) * gaussMassBoundD d σ) *
        Real.exp (-(t ^ (2 * γ) / (16 * σ)))) =
      K1 * (t ^ (k + (d : ℝ) / 2) * Real.exp (-(t ^ (2 * γ) / (16 * CV)))) +
        K2 * (t ^ k * Real.exp (-(t ^ η / (2 * CV)))) +
        K3 * (t ^ k * Real.exp (-(t ^ (2 * γ) / (16 * σ)))) := by
    rw [hK1, hK2, hK3]
    have := hp
    calc _ = CV * (t ^ k * (4 * Real.pi * CV * t) ^ ((d : ℝ) / 2)) * gaussMassBoundD d CV *
          Real.exp (-(t ^ (2 * γ) / (16 * CV))) + CV * expMassBoundD d CV *
          (t ^ k * Real.exp (-(t ^ η / (2 * CV)))) +
          4 / θ * (2 ^ ((d : ℝ) / 2) * gaussMassBoundD d σ) *
          (t ^ k * Real.exp (-(t ^ (2 * γ) / (16 * σ)))) := by ring
      _ = _ := by rw [hp]; ring
  rw [hsplit]
  have hb : ∀ K x : ℝ, 0 ≤ K → x ≤ ε / (3 * (K + 1)) → K * x ≤ ε / 3 := by
    intro K x hK hx
    have hK1' : 0 < K + 1 := by linarith
    calc K * x ≤ K * (ε / (3 * (K + 1))) := by
          rcases eq_or_lt_of_le hK with h | h
          · rw [← h]; simp
          · exact mul_le_mul_of_nonneg_left hx hK
      _ ≤ (K + 1) * (ε / (3 * (K + 1))) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = ε / 3 := by field_simp
  have := hb K1 _ hK10 h1
  have := hb K2 _ hK20 h2
  have := hb K3 _ hK30 h3
  linarith

/-- The tails of the bound of the point source. -/
theorem psTail_le {B T0 η t : ℝ} (d : ℕ) (hB0 : 0 < B) (hT00 : 0 ≤ T0) (hη : 0 < η) (ht : 1 ≤ t)
    (hT : t ^ ((d : ℝ) / 4 + 1 / 2 + η / 2) * T0 ≤ 1 / (B * (1 + 2 / η))) :
    B * T0 + Real.log t * (B * T0) ≤ t ^ (3 * η - (d : ℝ) / 4 - 1 / 2) := by
  have ht0 : 0 < t := by linarith
  have hlog : Real.log t ≤ 2 / η * t ^ (η / 2) := by
    have := Real.log_le_rpow_div ht0.le (by positivity : 0 < η / 2)
    calc Real.log t ≤ t ^ (η / 2) / (η / 2) := this
      _ = _ := by field_simp
  have hpow : ∀ a b : ℝ, a ≤ b → t ^ a ≤ t ^ b := fun a b hab =>
    Real.rpow_le_rpow_of_exponent_le ht hab
  have hmul : ∀ a b : ℝ, t ^ a * t ^ b = t ^ (a + b) := fun a b => (Real.rpow_add ht0 a b).symm
  have h1 : B * T0 + Real.log t * (B * T0) ≤ B * (1 + 2 / η) * t ^ (η / 2) * T0 := by
    have hη2 : 1 ≤ t ^ (η / 2) := Real.one_le_rpow ht (by positivity)
    have h5 : Real.log t * (B * T0) ≤ 2 / η * t ^ (η / 2) * (B * T0) :=
      mul_le_mul_of_nonneg_right hlog (by positivity)
    have hBT : 0 ≤ B * T0 := mul_nonneg hB0.le hT00
    have h4 : B * T0 ≤ t ^ (η / 2) * (B * T0) := le_mul_of_one_le_left hBT hη2
    calc B * T0 + Real.log t * (B * T0) ≤ t ^ (η / 2) * (B * T0) +
          2 / η * t ^ (η / 2) * (B * T0) := add_le_add h4 h5
      _ = B * (1 + 2 / η) * t ^ (η / 2) * T0 := by ring
  have h2 : t ^ (η / 2) * T0 ≤ t ^ (-((d : ℝ) / 4) - 1 / 2) * (1 / (B * (1 + 2 / η))) := by
    have hk : t ^ ((d : ℝ) / 4 + 1 / 2 + η / 2) =
        t ^ ((d : ℝ) / 4 + 1 / 2) * t ^ (η / 2) := by rw [hmul]
    have hinv : t ^ (-((d : ℝ) / 4) - 1 / 2) * t ^ ((d : ℝ) / 4 + 1 / 2) = 1 := by
      rw [hmul, show -((d : ℝ) / 4) - 1 / 2 + ((d : ℝ) / 4 + 1 / 2) = 0 by ring, Real.rpow_zero]
    calc t ^ (η / 2) * T0 = t ^ (-((d : ℝ) / 4) - 1 / 2) *
          (t ^ ((d : ℝ) / 4 + 1 / 2 + η / 2) * T0) := by
          rw [hk, ← mul_assoc, ← mul_assoc, hinv, one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hT (by positivity)
  have h3' : B * (1 + 2 / η) * t ^ (η / 2) * T0 ≤ t ^ (-((d : ℝ) / 4) - 1 / 2) := by
    calc B * (1 + 2 / η) * t ^ (η / 2) * T0 = B * (1 + 2 / η) * (t ^ (η / 2) * T0) := by ring
      _ ≤ B * (1 + 2 / η) * (t ^ (-((d : ℝ) / 4) - 1 / 2) * (1 / (B * (1 + 2 / η)))) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := by field_simp
  exact h1.trans (h3'.trans (hpow _ _ (by linarith)))

/-- **The decay of the bound of the point source.** -/
theorem eventually_psBound_le {σ θ C₀ A CB CA CG CV η : ℝ} (hσ : 0 < σ) (hθ : 0 < θ)
    (hC₀ : 0 ≤ C₀) (hA : 0 ≤ A) (hCA : 0 ≤ CA) (hCG : 0 ≤ CG) (hCV : 0 < CV)
    (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop,
      psBound d σ θ C₀ A CB CA CG CV η t ≤ C * t ^ (3 * η - (d : ℝ) / 4 - 1 / 2) := by
  set γ := η / ((d : ℝ) + 2) with hγ
  have hd2 : (0 : ℝ) < (d : ℝ) + 2 := by positivity
  have hγ0 : 0 < γ := div_pos hη hd2
  set κ := (C₀ + (10 * C₀ + 32) * A) * (1 + Real.sqrt 8) with hκ
  have hκ0 : 0 ≤ κ := by positivity
  set B := 2 + κ * Real.sqrt CB with hB
  have hB0 : 0 < B := by positivity
  set CE := psCE d σ θ CB with hCE
  set CN := psCN d σ θ CA CG with hCN
  have hCE0 : 0 ≤ CE := psCE_nonneg hθ
  have hCN0 : 0 ≤ CN := psCN_nonneg hθ hCA hCG
  set c1 := 5 ^ ((d : ℝ) / 2) * κ * Real.sqrt CB * CE * Real.sqrt 3 with hc1
  set c2 := 5 ^ ((d : ℝ) / 2) * κ * Real.sqrt CB * CN + CN * 4 ^ ((d : ℝ) / 4 + 1 / 2) with hc2
  have hc10 : 0 ≤ c1 := by positivity
  have hc20 : 0 ≤ c2 := by positivity
  refine ⟨c1 + 2 / η * c2 + 1, by positivity, ?_⟩
  have hT := eventually_rpow_mul_psT0_le (d := d) ((d : ℝ) / 4 + 1 / 2 + η / 2) hσ hθ hCV hη hγ0
    (ε := 1 / (B * (1 + 2 / η))) (by positivity)
  filter_upwards [hT, eventually_ge_atTop (1 : ℝ)] with t hT ht
  have ht0 : 0 < t := by linarith
  -- the powers of `L`
  have hL1 : (t ^ γ) ^ ((d : ℝ) / 2 + 1) = t ^ (η / 2) := by
    rw [← Real.rpow_mul ht0.le]; congr 1; rw [hγ]; field_simp; try ring
  have hL2 : (4 * (t ^ γ) ^ 2) ^ ((d : ℝ) / 4 + 1 / 2) =
      4 ^ ((d : ℝ) / 4 + 1 / 2) * t ^ (η / 2) := by
    rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul ht0.le,
      ← Real.rpow_mul ht0.le]
    congr 2; rw [hγ]; push_cast; field_simp; try ring
  have h3 : (3 * t ^ η) ^ ((1 : ℝ) / 2) = Real.sqrt 3 * t ^ (η / 2) := by
    rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul ht0.le, Real.sqrt_eq_rpow]
    congr 2; ring
  have hlog : Real.log t ≤ 2 / η * t ^ (η / 2) := by
    have := Real.log_le_rpow_div ht0.le (by positivity : 0 < η / 2)
    calc Real.log t ≤ t ^ (η / 2) / (η / 2) := this
      _ = _ := by field_simp
  have hlog0 : 0 ≤ Real.log t := Real.log_nonneg ht
  set T0 := psT0 d σ θ CV η t (t ^ γ) with hT0
  have hT00 : 0 ≤ T0 := psT0_nonneg hσ hθ hCV ht0.le
  -- the powers of `t`
  have hpow : ∀ a b : ℝ, a ≤ b → t ^ a ≤ t ^ b := fun a b hab =>
    Real.rpow_le_rpow_of_exponent_le ht hab
  have hmul : ∀ a b : ℝ, t ^ a * t ^ b = t ^ (a + b) := fun a b => (Real.rpow_add ht0 a b).symm
  have hfirst : 5 ^ ((d : ℝ) / 2) * κ * Real.sqrt CB * CE * (t ^ γ) ^ ((d : ℝ) / 2 + 1) *
      (3 * t ^ η) ^ ((1 : ℝ) / 2) * t ^ (-((d : ℝ) / 4) - 1 / 2) ≤
      c1 * t ^ (3 * η - (d : ℝ) / 4 - 1 / 2) := by
    rw [hL1, h3]
    have e : 5 ^ ((d : ℝ) / 2) * κ * Real.sqrt CB * CE * t ^ (η / 2) *
        (Real.sqrt 3 * t ^ (η / 2)) * t ^ (-((d : ℝ) / 4) - 1 / 2) =
        c1 * (t ^ (η / 2) * t ^ (η / 2) * t ^ (-((d : ℝ) / 4) - 1 / 2)) := by rw [hc1]; ring
    rw [e, hmul, hmul]
    exact mul_le_mul_of_nonneg_left (hpow _ _ (by linarith)) hc10
  have hsecond : 5 ^ ((d : ℝ) / 2) * κ * Real.sqrt CB * CN * (t ^ γ) ^ ((d : ℝ) / 2 + 1) *
      t ^ (η - (d : ℝ) / 4 - 1 / 2) + CN * (4 * (t ^ γ) ^ 2) ^ ((d : ℝ) / 4 + 1 / 2) *
      t ^ (η - (d : ℝ) / 4 - 1 / 2) = c2 * (t ^ (η / 2) * t ^ (η - (d : ℝ) / 4 - 1 / 2)) := by
    rw [hL1, hL2, hc2]; ring
  have htail := psTail_le d hB0 hT00 hη ht hT
  unfold psBound
  rw [← hκ, ← hγ, ← hT0, ← hCE, ← hCN, ← hB]
  have hlogQ : Real.log t * (c2 * (t ^ (η / 2) * t ^ (η - (d : ℝ) / 4 - 1 / 2))) ≤
      2 / η * c2 * t ^ (3 * η - (d : ℝ) / 4 - 1 / 2) := by
    have e : t ^ (η / 2) * (t ^ (η / 2) * t ^ (η - (d : ℝ) / 4 - 1 / 2)) =
        t ^ (2 * η - (d : ℝ) / 4 - 1 / 2) := by
      rw [hmul, hmul]; congr 1; ring
    calc _ ≤ 2 / η * t ^ (η / 2) * (c2 * (t ^ (η / 2) * t ^ (η - (d : ℝ) / 4 - 1 / 2))) :=
          mul_le_mul_of_nonneg_right hlog (by positivity)
      _ = 2 / η * c2 * (t ^ (η / 2) * (t ^ (η / 2) * t ^ (η - (d : ℝ) / 4 - 1 / 2))) := by ring
      _ ≤ _ := by
          rw [e]
          exact mul_le_mul_of_nonneg_left (hpow _ _ (by linarith)) (by positivity)
  have hexp : Real.log t * (5 ^ ((d : ℝ) / 2) * κ * Real.sqrt CB * CN *
      (t ^ γ) ^ ((d : ℝ) / 2 + 1) * t ^ (η - (d : ℝ) / 4 - 1 / 2) +
      CN * (4 * (t ^ γ) ^ 2) ^ ((d : ℝ) / 4 + 1 / 2) * t ^ (η - (d : ℝ) / 4 - 1 / 2) + B * T0) =
      Real.log t * (c2 * (t ^ (η / 2) * t ^ (η - (d : ℝ) / 4 - 1 / 2))) +
        Real.log t * (B * T0) := by
    rw [← hsecond]; ring
  rw [hexp]
  linarith [hfirst, hlogQ, htail]

end Rigidity.Green
