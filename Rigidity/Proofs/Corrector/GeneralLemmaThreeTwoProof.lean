import Rigidity.Proofs.Corrector.GeneralLemmaThreeTwoStepTwo

/-!
# Dario's Lemma 3.2 in every dimension

`darioMeanBound`: **Lemma 3.2** in every dimension `d ≥ 2`,
`|E[Φ_{r²} * ∇_j[χ_{e_i}]_𝒫(x)]| ≤ C/r^{d/2}` for `r ≥ 1`, following Dario's proof with
`3^k ≤ r^{1/2} < 3^{k+1}`:

* Step 1 (`exists_lintegral_abs_statDiscrepancy_le`): the coarsened gradients of `𝒫` and
  `𝒫_stat^k` differ by `χ(z̄_stat(y)) - χ(z̄(y)) - (χ(z̄_stat(y + e_j)) - χ(z̄(y + e_j)))`, of
  expectation at most `2 K (1 + θ₀ 3^{kd})^{2d} e^{-c 3^k/2}`;
* Step 2 (`sum_statMean_period_eq_zero`): the mean of `∇[χ]_{𝒫_stat^k}` is `3^k`-periodic with sum
  zero over a period, from (1.22);
* Step 3 (`abs_tsum_zdHeat_mul_periodic_le_exp`): its heat-kernel average is at most `e^{-16 r}`
  times its sum over a period.

The polynomial factors are absorbed by `e^{-c 3^k / 2}` with `r < 9^{k+1}`
(`exp_bound_lemmaThreeTwo`). Hence `darioMeanBoundThree_holds : DarioMeanBoundThree`, and Dario's
Theorem 1 in dimension `d ≥ 3` from Lemma 3.3 alone
(`darioOptimalCorrectorThree_of_varianceBound`).
-/

namespace Rigidity.Corrector.GeneralDim

open MeasureTheory Filter Set LatticeProb.Percolation Rigidity.Percolation Rigidity.External
open scoped Classical ENNReal

variable {d : ℕ}

theorem summable_zdHeat [NeZero d] {t : ℝ} (ht : 0 ≤ t) (x : Vertex d) :
    Summable fun y => Rigidity.Poincare.GeneralDim.zdHeat d t x y :=
  (ENNReal.summable_toReal (by
    rw [Rigidity.Poincare.GeneralDim.tsum_ofReal_zdHeat ht x]; exact ENNReal.one_ne_top)).congr
    fun y => ENNReal.toReal_ofReal (Rigidity.Poincare.GeneralDim.zdHeat_nonneg ht x y)

theorem tsum_zdHeat [NeZero d] {t : ℝ} (ht : 0 ≤ t) (x : Vertex d) :
    ∑' y, Rigidity.Poincare.GeneralDim.zdHeat d t x y = 1 := by
  have h := Rigidity.Poincare.GeneralDim.tsum_ofReal_zdHeat ht x
  rw [← ENNReal.ofReal_tsum_of_nonneg (Rigidity.Poincare.GeneralDim.zdHeat_nonneg ht x)
    (summable_zdHeat ht x)] at h
  have h0 : 0 ≤ ∑' y, Rigidity.Poincare.GeneralDim.zdHeat d t x y :=
    tsum_nonneg (Rigidity.Poincare.GeneralDim.zdHeat_nonneg ht x)
  rw [← ENNReal.ofReal_one] at h
  exact (ENNReal.ofReal_eq_ofReal_iff h0 zero_le_one).1 h

/-- **The final inequality of Lemma 3.2**: for `r ≥ 1` and `9^k ≤ r < 9^{k+1}`,
`e^{-16 r} 3^{kd} (2A + 2B) + 2B ≤ (2A d!/16^d + 4K')/r^{d/2}` with
`B = K (1 + θ₀ 3^{kd})^{2d} e^{-c 3^k/2}`. -/
theorem exp_bound_lemmaThreeTwo (d : ℕ) {A K c θ₀ r : ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hc : 0 < c) (hθ₀ : 0 ≤ θ₀) (hr : 1 ≤ r) {k : ℕ} (h9k : (9 : ℝ) ^ k ≤ r)
    (hr9 : r < 9 * 9 ^ k) :
    Real.exp (-(16 * r)) * ((3 : ℝ) ^ k) ^ d *
        (2 * A + 2 * (K * (1 + θ₀ * ((3 : ℝ) ^ k) ^ d) ^ (2 * d) *
          Real.exp (-(c * 3 ^ k / 2)))) +
        2 * (K * (1 + θ₀ * ((3 : ℝ) ^ k) ^ d) ^ (2 * d) * Real.exp (-(c * 3 ^ k / 2))) ≤
      (2 * A * (d.factorial / 16 ^ d) + 4 * (9 ^ d * K * (1 + θ₀) ^ (2 * d) *
        ((2 * d + 2 * d ^ 2).factorial / (c / 2) ^ (2 * d + 2 * d ^ 2)))) /
        r ^ ((d : ℝ) / 2) := by
  have hr0 : 0 < r := by linarith
  set L : ℝ := (3 : ℝ) ^ k with hL
  have hL1 : 1 ≤ L := one_le_pow₀ (by norm_num)
  have h9 : (9 : ℝ) ^ k = L ^ 2 := by rw [hL, ← pow_mul, mul_comm, pow_mul]; norm_num
  rw [h9] at h9k hr9
  set B := K * (1 + θ₀ * L ^ d) ^ (2 * d) * Real.exp (-(c * L / 2)) with hB
  have hB0 : 0 ≤ B := by positivity
  set ρ : ℝ := r ^ ((d : ℝ) / 2) with hρ
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos hr0 _
  have hρρ : ρ * ρ = r ^ d := by
    rw [hρ, ← Real.rpow_add hr0, add_halves, Real.rpow_natCast]
  have hLρ : L ^ d ≤ ρ := by
    have h1 : (L ^ 2) ^ ((d : ℝ) / 2) ≤ ρ := Real.rpow_le_rpow (by positivity) h9k (by positivity)
    have e : (L ^ 2) ^ ((d : ℝ) / 2) = L ^ d := by
      rw [← Real.rpow_natCast L 2, ← Real.rpow_mul (by positivity), ← Real.rpow_natCast]
      congr 1
      push_cast
      ring
    rw [e] at h1
    exact h1
  have hρr : ρ ≤ r ^ d := by
    have h1 : 1 ≤ ρ := Real.one_le_rpow hr (by positivity)
    nlinarith
  -- `r^d B ≤ K'`
  set n : ℕ := 2 * d + 2 * d ^ 2 with hn
  set K' : ℝ := 9 ^ d * K * (1 + θ₀) ^ (2 * d) * (n.factorial / (c / 2) ^ n) with hK'
  have hrB : r ^ d * B ≤ K' := by
    have hrd : r ^ d ≤ 9 ^ d * L ^ (2 * d) := by
      rw [pow_mul, ← mul_pow]
      exact pow_le_pow_left₀ hr0.le hr9.le d
    have hpoly : (1 + θ₀ * L ^ d) ^ (2 * d) ≤ (1 + θ₀) ^ (2 * d) * L ^ (2 * d ^ 2) := by
      have hLd : 1 ≤ L ^ d := one_le_pow₀ hL1
      have h1 : 1 + θ₀ * L ^ d ≤ (1 + θ₀) * L ^ d := by nlinarith
      calc (1 + θ₀ * L ^ d) ^ (2 * d) ≤ ((1 + θ₀) * L ^ d) ^ (2 * d) :=
            pow_le_pow_left₀ (by positivity) h1 _
        _ = (1 + θ₀) ^ (2 * d) * L ^ (2 * d ^ 2) := by
            rw [mul_pow, ← pow_mul]
            ring_nf
    have hf := pow_mul_exp_neg_le_factorial (a := c / 2) (y := L) (by positivity)
      (by positivity) n
    have he : Real.exp (-(c * L / 2)) = Real.exp (-(c / 2 * L)) := by ring_nf
    calc r ^ d * B ≤ (9 ^ d * L ^ (2 * d)) *
          (K * ((1 + θ₀) ^ (2 * d) * L ^ (2 * d ^ 2)) * Real.exp (-(c / 2 * L))) := by
          rw [hB, he]
          gcongr
      _ = 9 ^ d * K * (1 + θ₀) ^ (2 * d) * (L ^ n * Real.exp (-(c / 2 * L))) := by
          rw [hn, pow_add]
          ring
      _ ≤ K' := by
          rw [hK']
          gcongr
  -- `r^d e^{-16 r} ≤ d!/16^d`
  have hexp := pow_mul_exp_neg_le_factorial (a := 16) (y := r) (by norm_num) hr0.le d
  have hexp1 : Real.exp (-(16 * r)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have he0 := (Real.exp_pos (-(16 * r))).le
  rw [le_div_iff₀ hρ0]
  have t1 : Real.exp (-(16 * r)) * L ^ d * (2 * A) * ρ ≤ 2 * A * (d.factorial / 16 ^ d) := by
    have : Real.exp (-(16 * r)) * L ^ d * ρ ≤ Real.exp (-(16 * r)) * r ^ d := by
      rw [← hρρ, mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hLρ hρ0.le) he0
    calc Real.exp (-(16 * r)) * L ^ d * (2 * A) * ρ
        = 2 * A * (Real.exp (-(16 * r)) * L ^ d * ρ) := by ring
      _ ≤ 2 * A * (r ^ d * Real.exp (-(16 * r))) := by
          rw [mul_comm (r ^ d)]
          exact mul_le_mul_of_nonneg_left this (by positivity)
      _ ≤ 2 * A * (d.factorial / 16 ^ d) := mul_le_mul_of_nonneg_left hexp (by positivity)
  have t2 : Real.exp (-(16 * r)) * L ^ d * (2 * B) * ρ ≤ 2 * K' := by
    have : L ^ d * ρ ≤ r ^ d := by
      rw [← hρρ]
      exact mul_le_mul_of_nonneg_right hLρ hρ0.le
    calc Real.exp (-(16 * r)) * L ^ d * (2 * B) * ρ
        = Real.exp (-(16 * r)) * (2 * ((L ^ d * ρ) * B)) := by ring
      _ ≤ 1 * (2 * (r ^ d * B)) := by
          gcongr
      _ ≤ 2 * K' := by linarith
  have t3 : 2 * B * ρ ≤ 2 * K' := by
    have : B * ρ ≤ r ^ d * B := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right hρr hB0
    linarith
  calc (Real.exp (-(16 * r)) * L ^ d * (2 * A + 2 * B) + 2 * B) * ρ
      = Real.exp (-(16 * r)) * L ^ d * (2 * A) * ρ +
          Real.exp (-(16 * r)) * L ^ d * (2 * B) * ρ + 2 * B * ρ := by ring
    _ ≤ 2 * A * (d.factorial / 16 ^ d) + 2 * K' + 2 * K' := by linarith
    _ = 2 * A * (d.factorial / 16 ^ d) + 4 * K' := by ring

section Carrier

variable {G : Set (Configuration d)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent d)

/-- The coarse gradient of the partition in terms of the stationary one:
`∇[χ]_𝒫(y) = ∇[χ]_{𝒫_stat^k}(y) - ε(y + e_j) + ε(y)`. -/
theorem coarseField_step_eq (hd : 0 < d) {ω : Configuration d} (hω : ω ∈ G)
    (hP : PartitionEvent ω) (i : Fin d) (k : ℕ) (y : Vertex d) (j : Fin d) :
    coarseField hG hGv i 0 (y + LatticeProb.unit j) ω - coarseField hG hGv i 0 y ω =
      statGrad hG hGv i k y j ω - statDiscrepancy hG hGv i k (y + LatticeProb.unit j) ω +
        statDiscrepancy hG hGv i k y ω := by
  have h := correctorDiff_statAnchor_eq hG hGv hd hω hP i k (y + LatticeProb.unit j) y
  unfold statGrad
  rw [h]
  ring

/-- **Dario, Lemma 3.2, in every dimension `d ≥ 2`**:
`|E[Φ_{r²} * ∇_j[χ_{e_i}]_𝒫(x)]| ≤ C/r^{d/2}` for `r ≥ 1`. -/
theorem darioMeanBound [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) :
    ∃ C : ℝ, 0 < C ∧ ∀ (i j : Fin d) (r : ℝ), 1 ≤ r → ∀ x : Vertex d,
      |∫ ω, heatComp (fun z => coarseField hG hGv i 0 z ω) r x j ∂latticeBondLaw d p| ≤
        C / r ^ ((d : ℝ) / 2) := by
  have hd0 : 0 < d := by omega
  obtain ⟨Λ, A, κ, hA0, -, hΛm, hΛ0, hlip, hmom6⟩ := stepSix_data hG hGv hd hpc hp1 hGae
  obtain ⟨K, c, θ₀, hK, hc, hθ₀, hεb⟩ :=
    exists_lintegral_abs_statDiscrepancy_le hG hGv hd hpc hp1 hGae
  set K' : ℝ := 9 ^ d * K * (1 + θ₀) ^ (2 * d) *
    ((2 * d + 2 * d ^ 2).factorial / (c / 2) ^ (2 * d + 2 * d ^ 2)) with hK'
  have hK'0 : 0 ≤ K' := by positivity
  set C₀ : ℝ := 2 * A * (d.factorial / 16 ^ d) + 4 * K' with hC₀
  have hC₀0 : 0 ≤ C₀ := by positivity
  refine ⟨C₀ + 1, by positivity, fun i j r hr x => ?_⟩
  have hr0 : 0 < r := by linarith
  set k := Nat.log 9 ⌊r⌋₊ with hk
  have hfl : ⌊r⌋₊ ≠ 0 := (Nat.floor_pos.2 hr).ne'
  have h9k : (9 : ℝ) ^ k ≤ r := by
    have h := Nat.pow_log_le_self 9 hfl
    calc (9 : ℝ) ^ k = ((9 ^ k : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (⌊r⌋₊ : ℝ) := by exact_mod_cast h
      _ ≤ r := Nat.floor_le hr0.le
  have hr9 : r < 9 * 9 ^ k := by
    have h := Nat.succ_le_of_lt (Nat.lt_pow_succ_log_self (by norm_num : 1 < 9) ⌊r⌋₊)
    have h' : (⌊r⌋₊ : ℝ) + 1 ≤ (9 : ℝ) ^ (k + 1) := by exact_mod_cast h
    have := Nat.lt_floor_add_one r
    rw [pow_succ] at h'
    linarith
  set B : ℝ := K * (1 + θ₀ * ((3 : ℝ) ^ k) ^ d) ^ (2 * d) * Real.exp (-(c * 3 ^ k / 2)) with hB
  have hB0 : 0 ≤ B := by positivity
  have hall : ∀ᵐ ω ∂latticeBondLaw d p, ∀ x, ω ∈ infiniteComponentEvent x → ∀ y,
      (openGraph ω).Adj x y → |correctorDiff hG hGv (Pi.single i 1) ω x y| ≤ Λ i x ω :=
    ae_all_iff.2 fun x => hlip i x
  have hεi : ∀ z, Integrable (statDiscrepancy hG hGv i k z) (latticeBondLaw d p) := by
    intro z
    refine ⟨(measurable_statDiscrepancy hG hGv i k z).aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    simp_rw [Real.enorm_eq_ofReal_abs]
    exact lt_of_le_of_lt (hεb i k z) ENNReal.ofReal_lt_top
  have hεB : ∀ z, |∫ ω, statDiscrepancy hG hGv i k z ω ∂latticeBondLaw d p| ≤ B := by
    intro z
    have h := norm_integral_le_lintegral_norm (μ := latticeBondLaw d p)
      (statDiscrepancy hG hGv i k z)
    simp only [Real.norm_eq_abs] at h
    exact h.trans (ENNReal.toReal_le_of_le_ofReal hB0 (hεb i k z))
  have hS1 : ∀ v, ∫⁻ ω, stepSixSum (Λ i) v ω ∂latticeBondLaw d p ≤ ENNReal.ofReal A := by
    intro v
    have := hmom6 i v 1 le_rfl
    simpa only [ENNReal.rpow_one, Real.one_rpow, mul_one, Real.rpow_one] using this
  set dF : Vertex d → Configuration d → ℝ := fun y ω =>
    coarseField hG hGv i 0 (y + LatticeProb.unit j) ω - coarseField hG hGv i 0 y ω with hdF
  have hdFm : ∀ y, Measurable (dF y) := fun y =>
    (measurable_coarseField hG hGv i 0 _).sub (measurable_coarseField hG hGv i 0 y)
  have hdFl : ∀ y, ∫⁻ ω, ENNReal.ofReal |dF y ω| ∂latticeBondLaw d p ≤
      ENNReal.ofReal (2 * A) := by
    intro y
    calc ∫⁻ ω, ENNReal.ofReal |dF y ω| ∂latticeBondLaw d p
        ≤ ∫⁻ ω, (stepSixSum (Λ i) (y + LatticeProb.unit j) ω + stepSixSum (Λ i) y ω)
            ∂latticeBondLaw d p := by
          refine lintegral_mono_ae ?_
          filter_upwards [hGae, ae_partitionEvent hd hpc, hall] with ω hω hP hl
          exact ofReal_abs_coarseField_step_le hG hGv hd0 hω hP (fun x => hΛ0 i x ω) hl y j
      _ = ∫⁻ ω, stepSixSum (Λ i) (y + LatticeProb.unit j) ω ∂latticeBondLaw d p +
            ∫⁻ ω, stepSixSum (Λ i) y ω ∂latticeBondLaw d p :=
          lintegral_add_left (measurable_stepSixSum (hΛm i) _) _
      _ ≤ ENNReal.ofReal A + ENNReal.ofReal A := add_le_add (hS1 _) (hS1 _)
      _ = ENNReal.ofReal (2 * A) := by rw [← ENNReal.ofReal_add hA0.le hA0.le, two_mul]
  have hdFA : ∀ y, |∫ ω, dF y ω ∂latticeBondLaw d p| ≤ 2 * A := by
    intro y
    have h := norm_integral_le_lintegral_norm (μ := latticeBondLaw d p) (dF y)
    simp only [Real.norm_eq_abs] at h
    exact h.trans (ENNReal.toReal_le_of_le_ofReal (by positivity) (hdFl y))
  set g : Vertex d → ℝ := fun y => statMean hG hGv p i k y j with hg
  have hdec : ∀ y, ∫ ω, dF y ω ∂latticeBondLaw d p = g y -
      ∫ ω, statDiscrepancy hG hGv i k (y + LatticeProb.unit j) ω ∂latticeBondLaw d p +
      ∫ ω, statDiscrepancy hG hGv i k y ω ∂latticeBondLaw d p := by
    intro y
    have hsi := integrable_statGrad hG hGv hd hpc hp1 hGae i k y j
    have hcongr : ∫ ω, dF y ω ∂latticeBondLaw d p = ∫ ω, (statGrad hG hGv i k y j ω -
        statDiscrepancy hG hGv i k (y + LatticeProb.unit j) ω + statDiscrepancy hG hGv i k y ω)
        ∂latticeBondLaw d p := by
      refine integral_congr_ae ?_
      filter_upwards [hGae, ae_partitionEvent hd hpc] with ω hω hP
      exact coarseField_step_eq hG hGv hd0 hω hP i k y j
    rw [hcongr, integral_add (f := fun ω => statGrad hG hGv i k y j ω -
      statDiscrepancy hG hGv i k (y + LatticeProb.unit j) ω) (hsi.sub (hεi _)) (hεi _),
      integral_sub hsi (hεi _)]
    rfl
  have hgb : ∀ y, |g y| ≤ 2 * A + 2 * B := by
    intro y
    have a1 := abs_le.1 (hdFA y)
    have a2 := abs_le.1 (hεB (y + LatticeProb.unit j))
    have a3 := abs_le.1 (hεB y)
    rw [hdec y] at a1
    rw [abs_le]
    constructor <;> linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2]
  have hΦs := summable_zdHeat (sq_nonneg r) x
  have hΦ1 := tsum_zdHeat (sq_nonneg r) x
  have hΦ0 := Rigidity.Poincare.GeneralDim.zdHeat_nonneg (d := d) (sq_nonneg r) x
  have hX : ∫ ω, heatComp (fun z => coarseField hG hGv i 0 z ω) r x j ∂latticeBondLaw d p =
      ∑' y, Rigidity.Poincare.GeneralDim.zdHeat d (r ^ 2) x y *
        ∫ ω, dF y ω ∂latticeBondLaw d p := by
    unfold heatComp
    rw [integral_tsum (fun y => ((hdFm y).const_mul _).aestronglyMeasurable) ?_]
    · exact tsum_congr fun y => integral_const_mul _ _
    · refine ne_top_of_le_ne_top (b := ∑' y, ENNReal.ofReal
        (Rigidity.Poincare.GeneralDim.zdHeat d (r ^ 2) x y) * ENNReal.ofReal (2 * A)) ?_
        (ENNReal.tsum_le_tsum fun y => ?_)
      · rw [ENNReal.tsum_mul_right, Rigidity.Poincare.GeneralDim.tsum_ofReal_zdHeat (sq_nonneg r) x,
          one_mul]
        exact ENNReal.ofReal_ne_top
      · simp_rw [enorm_mul, Real.enorm_eq_ofReal_abs, abs_of_nonneg (hΦ0 y)]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact mul_le_mul_right (hdFl y) _
  have hs1 : Summable fun y => Rigidity.Poincare.GeneralDim.zdHeat d (r ^ 2) x y * g y :=
    (hΦs.mul_right (2 * A + 2 * B)).of_norm_bounded fun y => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hΦ0 y)]
      exact mul_le_mul_of_nonneg_left (hgb y) (hΦ0 y)
  set ε' : Vertex d → ℝ := fun y => ∫ ω, statDiscrepancy hG hGv i k y ω ∂latticeBondLaw d p -
    ∫ ω, statDiscrepancy hG hGv i k (y + LatticeProb.unit j) ω ∂latticeBondLaw d p with hε'
  have hε'b : ∀ y, |ε' y| ≤ 2 * B := by
    intro y
    have := abs_sub (∫ ω, statDiscrepancy hG hGv i k y ω ∂latticeBondLaw d p)
      (∫ ω, statDiscrepancy hG hGv i k (y + LatticeProb.unit j) ω ∂latticeBondLaw d p)
    have := hεB y
    have := hεB (y + LatticeProb.unit j)
    simp only [hε']
    linarith
  have hs2 : Summable fun y => Rigidity.Poincare.GeneralDim.zdHeat d (r ^ 2) x y * ε' y :=
    (hΦs.mul_right (2 * B)).of_norm_bounded fun y => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hΦ0 y)]
      exact mul_le_mul_of_nonneg_left (hε'b y) (hΦ0 y)
  have hsplit : ∑' y, Rigidity.Poincare.GeneralDim.zdHeat d (r ^ 2) x y *
        ∫ ω, dF y ω ∂latticeBondLaw d p =
      ∑' y, Rigidity.Poincare.GeneralDim.zdHeat d (r ^ 2) x y * g y +
        ∑' y, Rigidity.Poincare.GeneralDim.zdHeat d (r ^ 2) x y * ε' y := by
    rw [← hs1.tsum_add hs2]
    refine tsum_congr fun y => ?_
    rw [hdec y, hε']
    ring
  -- Step 3 for the mean
  haveI : NeZero (3 ^ k) := ⟨pow_ne_zero k (by norm_num)⟩
  have hper : ∀ y z : Vertex d, (∀ i', ((3 ^ k : ℕ) : ℤ) ∣ y i' - z i') → g y = g z := by
    intro y z h
    have h' := statMean_add hG hGv hd hpc hGae i (k := k) (c := y - z)
      (fun i' => by have := h i'; push_cast at this; exact this) z j
    have e : z + (y - z) = y := by abel
    rw [e] at h'
    exact h'
  have h0 : ∑ w : Fin d → ZMod (3 ^ k), g (zdResidueRep w) = 0 :=
    sum_statMean_period_eq_zero hG hGv hd hpc hp1 hGae i k j
  have h3 := abs_tsum_zdHeat_mul_periodic_le_exp hper h0 hr0 h9k x
  have h3' : |∑' y, Rigidity.Poincare.GeneralDim.zdHeat d (r ^ 2) x y * g y| ≤
      Real.exp (-(16 * r)) * (((3 : ℝ) ^ k) ^ d * (2 * A + 2 * B)) := by
    refine h3.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
    calc ∑ w : Fin d → ZMod (3 ^ k), |g (zdResidueRep w)|
        ≤ ∑ _w : Fin d → ZMod (3 ^ k), (2 * A + 2 * B) :=
          Finset.sum_le_sum fun w _ => hgb _
      _ = ((3 : ℝ) ^ k) ^ d * (2 * A + 2 * B) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin,
            nsmul_eq_mul]
          push_cast
          ring
  -- the discrepancy part
  have h4 : |∑' y, Rigidity.Poincare.GeneralDim.zdHeat d (r ^ 2) x y * ε' y| ≤ 2 * B := by
    have hn : Summable fun y => ‖Rigidity.Poincare.GeneralDim.zdHeat d (r ^ 2) x y * ε' y‖ :=
      hs2.norm
    calc |∑' y, Rigidity.Poincare.GeneralDim.zdHeat d (r ^ 2) x y * ε' y|
        ≤ ∑' y, ‖Rigidity.Poincare.GeneralDim.zdHeat d (r ^ 2) x y * ε' y‖ := by
          rw [← Real.norm_eq_abs]
          exact norm_tsum_le_tsum_norm hn
      _ ≤ ∑' y, Rigidity.Poincare.GeneralDim.zdHeat d (r ^ 2) x y * (2 * B) := by
          refine hn.tsum_le_tsum (fun y => ?_) (hΦs.mul_right _)
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hΦ0 y)]
          exact mul_le_mul_of_nonneg_left (hε'b y) (hΦ0 y)
      _ = 2 * B := by rw [tsum_mul_right, hΦ1, one_mul]
  -- the conclusion
  rw [hX, hsplit]
  have hfin := exp_bound_lemmaThreeTwo d hA0.le hK.le hc hθ₀.le hr h9k hr9
  rw [← hB, ← hK'] at hfin
  have hρ0 : 0 < r ^ ((d : ℝ) / 2) := Real.rpow_pos_of_pos hr0 _
  calc |∑' y, Rigidity.Poincare.GeneralDim.zdHeat d (r ^ 2) x y * g y +
        ∑' y, Rigidity.Poincare.GeneralDim.zdHeat d (r ^ 2) x y * ε' y|
      ≤ |∑' y, Rigidity.Poincare.GeneralDim.zdHeat d (r ^ 2) x y * g y| +
          |∑' y, Rigidity.Poincare.GeneralDim.zdHeat d (r ^ 2) x y * ε' y| := abs_add_le _ _
    _ ≤ Real.exp (-(16 * r)) * (((3 : ℝ) ^ k) ^ d * (2 * A + 2 * B)) + 2 * B :=
        add_le_add h3' h4
    _ = Real.exp (-(16 * r)) * ((3 : ℝ) ^ k) ^ d * (2 * A + 2 * B) + 2 * B := by ring
    _ ≤ C₀ / r ^ ((d : ℝ) / 2) := hfin
    _ ≤ (C₀ + 1) / r ^ ((d : ℝ) / 2) := div_le_div_of_nonneg_right (by linarith) hρ0.le

end Carrier

/-- **Dario, Lemma 3.2, in dimension `d ≥ 3`**, with no hypothesis. -/
theorem darioMeanBoundThree_holds : DarioMeanBoundThree := by
  intro d _ hd3 p hpc hp1 G hG hGv hGae
  exact darioMeanBound hG hGv (by omega) hpc hp1 hGae

/-- **Dario, Theorem 1, in dimension `d ≥ 3`**, from Lemma 3.3 alone. -/
theorem darioOptimalCorrectorThree_of_varianceBound (h33 : DarioVarianceBoundThree) :
    DarioOptimalCorrectorThree :=
  darioOptimalCorrectorThree_of_lemmas darioMeanBoundThree_holds h33

end Rigidity.Corrector.GeneralDim
