import Rigidity.Proofs.Corrector.DarioLemmaThreeTwoMean
import Rigidity.Proofs.Corrector.DarioPropThreeOne

/-!
# Dario's Lemma 3.2 from the quantitative sublinearity (1.22)

`darioLemmaThreeTwo_of_osc`: **Lemma 3.2** (`DarioLemmaThreeTwo`,
`|E[Φ_{r²} * ∇_j[χ_{e_i}]_𝒫(x)]| ≤ C/r`) from the order-zero regularity (R3) and (1.22)
(`CorrectorOscSublinearTwo`), following Dario's proof with `3^k ≤ r^{1/2} < 3^{k+1}`:

* Step 1 (`exists_lintegral_abs_statDiscrepancy_le`): the coarsened gradients of `𝒫` and
  `𝒫_stat^k` differ by `χ(z̄_stat(y)) - χ(z̄(y)) - (χ(z̄_stat(y + e_j)) - χ(z̄(y + e_j)))`, of
  expectation at most `2 K (1 + θ₀ 9^k)^4 e^{-c 3^k/2}`;
* Step 2 (`sum_statMean_period_eq_zero`): the mean of `∇[χ]_{𝒫_stat^k}` is `3^k`-periodic with sum
  zero over a period;
* Step 3 (`abs_tsum_openHeat_mul_periodic_le_exp`): its heat-kernel average is at most
  `e^{-16 r}` times its sum over a period.

The polynomial factors are absorbed by `e^{-c √r / 6}` (`exp_bound_lemmaThreeTwo`).
`darioOptimalCorrectorTwo_of_osc` composes Dario's Theorem 1 in dimension two with Lemma 3.2
replaced by (1.22).
-/

namespace Rigidity.Corrector

open MeasureTheory Filter Set LatticeProb.Percolation Rigidity.Percolation Rigidity.External
open scoped Classical ENNReal

theorem summable_latticeHeat {t : ℝ} (ht : 0 ≤ t) (x : Vertex 2) :
    Summable fun y => latticeHeat t x y :=
  (ENNReal.summable_toReal (by rw [tsum_ofReal_latticeHeat ht x]; exact ENNReal.one_ne_top)).congr
    fun y => ENNReal.toReal_ofReal (latticeHeat_nonneg ht x y)

theorem tsum_latticeHeat {t : ℝ} (ht : 0 ≤ t) (x : Vertex 2) : ∑' y, latticeHeat t x y = 1 := by
  have h := tsum_ofReal_latticeHeat ht x
  rw [← ENNReal.ofReal_tsum_of_nonneg (latticeHeat_nonneg ht x) (summable_latticeHeat ht x)] at h
  have h0 : 0 ≤ ∑' y, latticeHeat t x y := tsum_nonneg (latticeHeat_nonneg ht x)
  rw [← ENNReal.ofReal_one] at h
  exact (ENNReal.ofReal_eq_ofReal_iff h0 zero_le_one).1 h

/-- `y^n e^{-a y} ≤ n! / a^n` for `y ≥ 0` and `a > 0`. -/
theorem pow_mul_exp_neg_le {a y : ℝ} (ha : 0 < a) (hy : 0 ≤ y) (n : ℕ) :
    y ^ n * Real.exp (-(a * y)) ≤ n.factorial / a ^ n := by
  have h := Real.pow_div_factorial_le_exp (a * y) (by positivity) n
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have han : 0 < a ^ n := pow_pos ha n
  rw [div_le_iff₀ hf, mul_pow] at h
  rw [le_div_iff₀ han]
  have he : Real.exp (-(a * y)) * Real.exp (a * y) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hpos := Real.exp_pos (-(a * y))
  calc y ^ n * Real.exp (-(a * y)) * a ^ n = (a ^ n * y ^ n) * Real.exp (-(a * y)) := by ring
    _ ≤ (Real.exp (a * y) * n.factorial) * Real.exp (-(a * y)) :=
        mul_le_mul_of_nonneg_right h hpos.le
    _ = n.factorial * (Real.exp (-(a * y)) * Real.exp (a * y)) := by ring
    _ = n.factorial := by rw [he, mul_one]

/-- **The final inequality of Lemma 3.2**: for `r ≥ 1` and `9^k ≤ r < 9^{k+1}`,
`e^{-16 r} 9^k (2A + 2B) + 2B ≤ (A/64 + 4K')/r` with `B = K (1 + θ₀ 9^k)^4 e^{-c 3^k/2}`. -/
theorem exp_bound_lemmaThreeTwo {A K c θ₀ r : ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K) (hc : 0 < c)
    (hθ₀ : 0 ≤ θ₀) (hr : 1 ≤ r) {k : ℕ} (h9k : (9 : ℝ) ^ k ≤ r) (hr9 : r < 9 * 9 ^ k) :
    Real.exp (-(16 * r)) * 9 ^ k * (2 * A + 2 * (K * (1 + θ₀ * 9 ^ k) ^ 4 *
        Real.exp (-(c * 3 ^ k / 2)))) + 2 * (K * (1 + θ₀ * 9 ^ k) ^ 4 *
        Real.exp (-(c * 3 ^ k / 2))) ≤
      (A / 64 + 4 * (K * (1 + θ₀) ^ 4 * (Nat.factorial 12 / (c / 6) ^ 12))) / r := by
  have hr0 : 0 < r := by linarith
  set B := K * (1 + θ₀ * 9 ^ k) ^ 4 * Real.exp (-(c * 3 ^ k / 2)) with hB
  have hB0 : 0 ≤ B := by positivity
  set x := Real.sqrt r with hx
  have hx1 : 1 ≤ x := by rw [hx]; exact Real.one_le_sqrt.2 hr
  have hxr : x ^ 2 = r := Real.sq_sqrt hr0.le
  -- `3^k ≥ √r / 3`
  have h3k : x / 3 ≤ (3 : ℝ) ^ k := by
    have h9 : (9 : ℝ) ^ k = ((3 : ℝ) ^ k) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have h1 : (x / 3) ^ 2 ≤ ((3 : ℝ) ^ k) ^ 2 := by
      rw [div_pow, hxr, ← h9]
      linarith
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 h1
  -- the bound on `r B`
  have hrB : r * B ≤ K * (1 + θ₀) ^ 4 * (Nat.factorial 12 / (c / 6) ^ 12) / r := by
    have hpoly : (1 + θ₀ * 9 ^ k) ^ 4 ≤ (1 + θ₀) ^ 4 * x ^ 8 := by
      have h1 : 1 + θ₀ * 9 ^ k ≤ (1 + θ₀) * x ^ 2 := by
        rw [hxr]
        nlinarith
      calc (1 + θ₀ * 9 ^ k) ^ 4 ≤ ((1 + θ₀) * x ^ 2) ^ 4 :=
            pow_le_pow_left₀ (by positivity) h1 4
        _ = (1 + θ₀) ^ 4 * x ^ 8 := by ring
    have hexp : Real.exp (-(c * 3 ^ k / 2)) ≤ Real.exp (-(c / 6 * x)) :=
      Real.exp_le_exp.2 (by nlinarith)
    have hf := pow_mul_exp_neg_le (a := c / 6) (y := x) (by positivity) (by positivity) 12
    have hr2 : r * r = x ^ 4 := by rw [← hxr]; ring
    rw [le_div_iff₀ hr0, hB]
    calc r * (K * (1 + θ₀ * 9 ^ k) ^ 4 * Real.exp (-(c * 3 ^ k / 2))) * r
        ≤ r * (K * ((1 + θ₀) ^ 4 * x ^ 8) * Real.exp (-(c / 6 * x))) * r := by gcongr
      _ = K * (1 + θ₀) ^ 4 * (x ^ 12 * Real.exp (-(c / 6 * x))) := by
          rw [← hxr]
          ring
      _ ≤ K * (1 + θ₀) ^ 4 * (Nat.factorial 12 / (c / 6) ^ 12) := by gcongr
  -- the bound on `e^{-16 r} r`
  have hexpr : Real.exp (-(16 * r)) * r ≤ 1 / (128 * r) := by
    have h := pow_mul_exp_neg_le (a := 16) (y := r) (by norm_num) hr0.le 2
    rw [le_div_iff₀ (by positivity)]
    have : (Nat.factorial 2 : ℝ) / 16 ^ 2 = 1 / 128 := by norm_num [Nat.factorial]
    rw [this] at h
    nlinarith
  have hexp1 : Real.exp (-(16 * r)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  set K' := K * (1 + θ₀) ^ 4 * (Nat.factorial 12 / (c / 6) ^ 12) with hK'
  have hB' : B ≤ K' / r := by
    have : B ≤ r * B := le_mul_of_one_le_left hB0 hr
    linarith
  calc Real.exp (-(16 * r)) * 9 ^ k * (2 * A + 2 * B) + 2 * B
      ≤ Real.exp (-(16 * r)) * r * (2 * A) + r * (2 * B) + 2 * B := by
        have h1 : Real.exp (-(16 * r)) * 9 ^ k ≤ Real.exp (-(16 * r)) * r :=
          mul_le_mul_of_nonneg_left h9k (Real.exp_pos _).le
        have h2 : Real.exp (-(16 * r)) * r ≤ r := by nlinarith [Real.exp_pos (-(16 * r))]
        nlinarith [Real.exp_pos (-(16 * r))]
    _ ≤ 1 / (128 * r) * (2 * A) + 2 * (K' / r) + 2 * (K' / r) := by
        have t1 : Real.exp (-(16 * r)) * r * (2 * A) ≤ 1 / (128 * r) * (2 * A) :=
          mul_le_mul_of_nonneg_right hexpr (by positivity)
        have t2 : r * (2 * B) ≤ 2 * (K' / r) := by linarith [hrB]
        have t3 : 2 * B ≤ 2 * (K' / r) := by linarith [hB']
        linarith [t1, t2, t3]
    _ = (A / 64 + 4 * K') / r := by
        field_simp
        ring

section Carrier

variable {G : Set (Configuration 2)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2)

/-- The coarse gradient of the planar partition in terms of the stationary one:
`∇[χ]_𝒫(y) = ∇[χ]_{𝒫_stat^k}(y) - (χ(z̄_stat(y + e_j)) - χ(z̄(y + e_j))) + (χ(z̄_stat(y)) - χ(z̄(y)))`. -/
theorem coarseField_step_eq {ω : Configuration 2} (hω : ω ∈ G) (hP : PlanarPartitionEvent ω)
    (i : Fin 2) (k : ℕ) (y : Vertex 2) (j : Fin 2) :
    coarseField hG hGv i 0 (y + LatticeProb.unit j) ω - coarseField hG hGv i 0 y ω =
      statGrad hG hGv i k y j ω - statDiscrepancy hG hGv i k (y + LatticeProb.unit j) ω +
        statDiscrepancy hG hGv i k y ω := by
  have e0 : ∀ u, shiftedAnchor 0 ω u = planarCoarseAnchor ω u := fun u => by
    rw [shiftedAnchor_zero, guardAnchor_of_event hP]
  simp only [coarseField, statGrad, statDiscrepancy, e0, guardAnchor_of_event hP]
  have hb := infinite_planarCoarseAnchor hP 0
  have ha := infinite_planarCoarseAnchor hP y
  have ha' := infinite_planarCoarseAnchor hP (y + LatticeProb.unit j)
  have hs := statAnchor_mem_inf k y hb
  have hs' := statAnchor_mem_inf k (y + LatticeProb.unit j) hb
  rw [correctorDiff_sub_eq hG hGv hω ha' ha hb, correctorDiff_add' hG hGv hω hs' ha' hs,
    correctorDiff_add' hG hGv hω ha' ha hs, correctorDiff_swap' hG hGv hω hs ha]
  ring

end Carrier

/-- **Dario, Lemma 3.2 in dimension two**, from the order-zero regularity (R3) and the
quantitative sublinearity (1.22): `|E[Φ_{r²} * ∇_j[χ_{e_i}]_𝒫(x)]| ≤ C/r` for `r ≥ 1`. -/
theorem darioLemmaThreeTwo_of_osc (hR3 : ArmstrongDarioOrderZeroTwo)
    (h122 : CorrectorOscSublinearTwo) : DarioLemmaThreeTwo := by
  intro p hpc hp1 G hG hGv hGae
  obtain ⟨Λ, A, κ, hA0, -, hΛm, hΛ0, hlip, hmom6⟩ := stepSix_data hG hGv hR3 hpc hp1 hGae
  obtain ⟨K, c, θ₀, hK, hc, hθ₀, hεb⟩ :=
    exists_lintegral_abs_statDiscrepancy_le hG hGv hR3 hpc hp1 hGae
  set K' : ℝ := K * (1 + θ₀) ^ 4 * (Nat.factorial 12 / (c / 6) ^ 12) with hK'
  have hK'0 : 0 ≤ K' := by positivity
  refine ⟨A / 64 + 4 * K' + 1, by positivity, fun i j r hr x => ?_⟩
  have hr0 : 0 < r := by linarith
  -- the scale `k` with `9^k ≤ r < 9^{k+1}`
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
  set B : ℝ := K * (1 + θ₀ * 9 ^ k) ^ 4 * Real.exp (-(c * 3 ^ k / 2)) with hB
  have hB0 : 0 ≤ B := by positivity
  have hall : ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ x, ω ∈ infiniteComponentEvent x → ∀ y,
      (openGraph ω).Adj x y → |correctorDiff hG hGv (Pi.single i 1) ω x y| ≤ Λ i x ω :=
    ae_all_iff.2 fun x => hlip i x
  -- the discrepancies
  have hεi : ∀ z, Integrable (statDiscrepancy hG hGv i k z) (latticeBondLaw 2 p) := by
    intro z
    refine ⟨(measurable_statDiscrepancy hG hGv i k z).aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    simp_rw [Real.enorm_eq_ofReal_abs]
    exact lt_of_le_of_lt (hεb i k z) ENNReal.ofReal_lt_top
  have hεB : ∀ z, |∫ ω, statDiscrepancy hG hGv i k z ω ∂latticeBondLaw 2 p| ≤ B := by
    intro z
    have h := norm_integral_le_lintegral_norm (μ := latticeBondLaw 2 p)
      (statDiscrepancy hG hGv i k z)
    simp only [Real.norm_eq_abs] at h
    exact h.trans (ENNReal.toReal_le_of_le_ofReal hB0 (hεb i k z))
  -- the coarse gradients of the planar partition
  have hS1 : ∀ v, ∫⁻ ω, stepSixSum (Λ i) v ω ∂latticeBondLaw 2 p ≤ ENNReal.ofReal A := by
    intro v
    have := hmom6 i v 1 le_rfl
    simpa only [ENNReal.rpow_one, Real.one_rpow, mul_one, Real.rpow_one] using this
  set dF : Vertex 2 → Configuration 2 → ℝ := fun y ω =>
    coarseField hG hGv i 0 (y + LatticeProb.unit j) ω - coarseField hG hGv i 0 y ω with hdF
  have hdFm : ∀ y, Measurable (dF y) := fun y =>
    (measurable_coarseField hG hGv i 0 _).sub (measurable_coarseField hG hGv i 0 y)
  have hdFl : ∀ y, ∫⁻ ω, ENNReal.ofReal |dF y ω| ∂latticeBondLaw 2 p ≤ ENNReal.ofReal (2 * A) := by
    intro y
    calc ∫⁻ ω, ENNReal.ofReal |dF y ω| ∂latticeBondLaw 2 p
        ≤ ∫⁻ ω, (stepSixSum (Λ i) (y + LatticeProb.unit j) ω + stepSixSum (Λ i) y ω)
            ∂latticeBondLaw 2 p := by
          refine lintegral_mono_ae ?_
          filter_upwards [hGae, ae_planarPartitionEvent hpc, hall] with ω hω hP hl
          exact ofReal_abs_coarseField_step_le hG hGv hω hP (fun x => hΛ0 i x ω) hl y j
      _ = ∫⁻ ω, stepSixSum (Λ i) (y + LatticeProb.unit j) ω ∂latticeBondLaw 2 p +
            ∫⁻ ω, stepSixSum (Λ i) y ω ∂latticeBondLaw 2 p :=
          lintegral_add_left (measurable_stepSixSum (hΛm i) _) _
      _ ≤ ENNReal.ofReal A + ENNReal.ofReal A := add_le_add (hS1 _) (hS1 _)
      _ = ENNReal.ofReal (2 * A) := by rw [← ENNReal.ofReal_add hA0.le hA0.le, two_mul]
  have hdFi : ∀ y, Integrable (dF y) (latticeBondLaw 2 p) := by
    intro y
    refine ⟨(hdFm y).aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    simp_rw [Real.enorm_eq_ofReal_abs]
    exact lt_of_le_of_lt (hdFl y) ENNReal.ofReal_lt_top
  have hdFA : ∀ y, |∫ ω, dF y ω ∂latticeBondLaw 2 p| ≤ 2 * A := by
    intro y
    have h := norm_integral_le_lintegral_norm (μ := latticeBondLaw 2 p) (dF y)
    simp only [Real.norm_eq_abs] at h
    exact h.trans (ENNReal.toReal_le_of_le_ofReal (by positivity) (hdFl y))
  -- the decomposition of the mean
  set g : Vertex 2 → ℝ := fun y => statMean hG hGv p i k y j with hg
  have hdec : ∀ y, ∫ ω, dF y ω ∂latticeBondLaw 2 p = g y -
      ∫ ω, statDiscrepancy hG hGv i k (y + LatticeProb.unit j) ω ∂latticeBondLaw 2 p +
      ∫ ω, statDiscrepancy hG hGv i k y ω ∂latticeBondLaw 2 p := by
    intro y
    have hsi := integrable_statGrad hG hGv hR3 h122 hpc hp1 hGae i k y j
    have hcongr : ∫ ω, dF y ω ∂latticeBondLaw 2 p = ∫ ω, (statGrad hG hGv i k y j ω -
        statDiscrepancy hG hGv i k (y + LatticeProb.unit j) ω + statDiscrepancy hG hGv i k y ω)
        ∂latticeBondLaw 2 p := by
      refine integral_congr_ae ?_
      filter_upwards [hGae, ae_planarPartitionEvent hpc] with ω hω hP
      exact coarseField_step_eq hG hGv hω hP i k y j
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
  -- the heat-kernel average as a series of means
  have hΦs := summable_latticeHeat (sq_nonneg r) x
  have hΦ1 := tsum_latticeHeat (sq_nonneg r) x
  have hΦ0 := latticeHeat_nonneg (sq_nonneg r) x
  have hX : ∫ ω, heatComp (fun z => coarseField hG hGv i 0 z ω) r x j ∂latticeBondLaw 2 p =
      ∑' y, latticeHeat (r ^ 2) x y * ∫ ω, dF y ω ∂latticeBondLaw 2 p := by
    unfold heatComp
    rw [integral_tsum (fun y => ((hdFm y).const_mul _).aestronglyMeasurable) ?_]
    · exact tsum_congr fun y => integral_const_mul _ _
    · refine ne_top_of_le_ne_top (b := ∑' y, ENNReal.ofReal (latticeHeat (r ^ 2) x y) *
        ENNReal.ofReal (2 * A)) ?_ (ENNReal.tsum_le_tsum fun y => ?_)
      · rw [ENNReal.tsum_mul_right, tsum_ofReal_latticeHeat (sq_nonneg r) x, one_mul]
        exact ENNReal.ofReal_ne_top
      · simp_rw [enorm_mul, Real.enorm_eq_ofReal_abs, abs_of_nonneg (hΦ0 y)]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact mul_le_mul_right (hdFl y) _
  -- the two parts
  have hs1 : Summable fun y => latticeHeat (r ^ 2) x y * g y :=
    (hΦs.mul_right (2 * A + 2 * B)).of_norm_bounded fun y => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hΦ0 y)]
      exact mul_le_mul_of_nonneg_left (hgb y) (hΦ0 y)
  set ε' : Vertex 2 → ℝ := fun y => ∫ ω, statDiscrepancy hG hGv i k y ω ∂latticeBondLaw 2 p -
    ∫ ω, statDiscrepancy hG hGv i k (y + LatticeProb.unit j) ω ∂latticeBondLaw 2 p with hε'
  have hε'b : ∀ y, |ε' y| ≤ 2 * B := by
    intro y
    have := abs_sub (∫ ω, statDiscrepancy hG hGv i k y ω ∂latticeBondLaw 2 p)
      (∫ ω, statDiscrepancy hG hGv i k (y + LatticeProb.unit j) ω ∂latticeBondLaw 2 p)
    have := hεB y
    have := hεB (y + LatticeProb.unit j)
    simp only [hε']
    linarith
  have hs2 : Summable fun y => latticeHeat (r ^ 2) x y * ε' y :=
    (hΦs.mul_right (2 * B)).of_norm_bounded fun y => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hΦ0 y)]
      exact mul_le_mul_of_nonneg_left (hε'b y) (hΦ0 y)
  have hsplit : ∑' y, latticeHeat (r ^ 2) x y * ∫ ω, dF y ω ∂latticeBondLaw 2 p =
      ∑' y, latticeHeat (r ^ 2) x y * g y + ∑' y, latticeHeat (r ^ 2) x y * ε' y := by
    rw [← hs1.tsum_add hs2]
    refine tsum_congr fun y => ?_
    rw [hdec y, hε']
    ring
  -- Step 3 for the mean
  haveI : NeZero (3 ^ k) := ⟨pow_ne_zero k (by norm_num)⟩
  have hper : ∀ y z : Vertex 2, (∀ i', ((3 ^ k : ℕ) : ℤ) ∣ y i' - z i') → g y = g z := by
    intro y z h
    have h' := statMean_add hG hGv hpc hGae i (k := k) (c := y - z)
      (fun i' => by have := h i'; push_cast at this; exact this) z j
    have e : z + (y - z) = y := by abel
    rw [e] at h'
    exact h'
  have h0 : ∑ w : ZMod (3 ^ k) × ZMod (3 ^ k), g (residueRep w) = 0 :=
    sum_statMean_period_eq_zero hG hGv hR3 h122 hpc hp1 hGae i k j
  have h3 := abs_tsum_openHeat_mul_periodic_le_exp hper h0 hr0 h9k x
  have h3' : |∑' y, latticeHeat (r ^ 2) x y * g y| ≤
      Real.exp (-(16 * r)) * (9 ^ k * (2 * A + 2 * B)) := by
    refine h3.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
    calc ∑ w : ZMod (3 ^ k) × ZMod (3 ^ k), |g (residueRep w)|
        ≤ ∑ _w : ZMod (3 ^ k) × ZMod (3 ^ k), (2 * A + 2 * B) :=
          Finset.sum_le_sum fun w _ => hgb _
      _ = 9 ^ k * (2 * A + 2 * B) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, ZMod.card, nsmul_eq_mul]
          push_cast
          rw [← mul_pow]
          norm_num
  -- the discrepancy part
  have h4 : |∑' y, latticeHeat (r ^ 2) x y * ε' y| ≤ 2 * B := by
    have hn : Summable fun y => ‖latticeHeat (r ^ 2) x y * ε' y‖ := hs2.norm
    calc |∑' y, latticeHeat (r ^ 2) x y * ε' y|
        ≤ ∑' y, ‖latticeHeat (r ^ 2) x y * ε' y‖ := by
          rw [← Real.norm_eq_abs]
          exact norm_tsum_le_tsum_norm hn
      _ ≤ ∑' y, latticeHeat (r ^ 2) x y * (2 * B) := by
          refine hn.tsum_le_tsum (fun y => ?_) (hΦs.mul_right _)
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hΦ0 y)]
          exact mul_le_mul_of_nonneg_left (hε'b y) (hΦ0 y)
      _ = 2 * B := by rw [tsum_mul_right, hΦ1, one_mul]
  -- the conclusion
  rw [hX, hsplit]
  have hfin := exp_bound_lemmaThreeTwo hA0.le hK.le hc hθ₀.le hr h9k hr9
  rw [← hB] at hfin
  calc |∑' y, latticeHeat (r ^ 2) x y * g y + ∑' y, latticeHeat (r ^ 2) x y * ε' y|
      ≤ |∑' y, latticeHeat (r ^ 2) x y * g y| + |∑' y, latticeHeat (r ^ 2) x y * ε' y| :=
        abs_add_le _ _
    _ ≤ Real.exp (-(16 * r)) * (9 ^ k * (2 * A + 2 * B)) + 2 * B := add_le_add h3' h4
    _ = Real.exp (-(16 * r)) * 9 ^ k * (2 * A + 2 * B) + 2 * B := by ring
    _ ≤ (A / 64 + 4 * K') / r := hfin
    _ ≤ (A / 64 + 4 * K' + 1) / r := div_le_div_of_nonneg_right (by linarith) hr0.le

/-- **Dario's Theorem 1 in dimension two** from R2, R3, the multiscale Poincaré inequality, the
concentration inequality, the quantitative sublinearity (1.22) and Lemma 3.3. -/
theorem darioOptimalCorrectorTwo_of_osc (hR2 : SupercriticalBondCorrectorInputTwo)
    (hR3 : ArmstrongDarioOrderZeroTwo) {A₀ : ℝ} (hA₀ : 0 < A₀) (hMSP : MultiscalePoincareTwo A₀)
    (hconc : ConcentrationTwo) (h122 : CorrectorOscSublinearTwo) (h33 : DarioLemmaThreeThree) :
    DarioOptimalCorrectorTwo :=
  darioOptimalCorrectorTwo_of_lemmas hR2 hR3 hA₀ hMSP hconc (darioLemmaThreeTwo_of_osc hR3 h122) h33

end Rigidity.Corrector
