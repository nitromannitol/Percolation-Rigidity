import Rigidity.Proofs.Corrector.GeneralFlipTerms

/-!
# Lemma 3.3 of Dario in dimension `d ≥ 3` from the sums of Steps 1 and 2

Dario reduces Lemma 3.3, `𝕍[X] ≤ O_s(C r^{-d})` for `X = Φ_{r²} * ∇[χ_p]_𝒫(0)`, to the estimate
(3.13) `Σ_e |Φ_{r²} * (∇[χ_p]_𝒫 - ∇[χ_p^e]_{𝒫^e})(0)|² ≤ O_s'(C r^{-d})` on the doubled
probability space, by Jensen's inequality and the argument of Armstrong, Kuusi and Mourrat,
Lemma 2.3, and proves (3.13) from the split (3.15) into the change of partition (Step 1) and the
change of corrector (Step 2). For the Bernoulli bond law, `𝕍[X] ≤ Σ_e (D_e X)²` almost surely with
the flip difference `D_e X(ω) = X(ω^{e,1}) - X(ω^{e,0})` (`ae_resampleVar_le_tsum_bondFlipDiff`),
so (3.13) takes the flip form `DarioFlipSumBoundThree`. Here, for the partition into good cubes of
`ℤᵈ`, every direction, component, radius `r ≥ 1` and point:

* `darioVarianceBoundThree_of_flipSum`: Lemma 3.3 (`DarioVarianceBoundThree`) from
  `DarioFlipSumBoundThree`, the integrability of `X` coming from
  `heatGradient_coarseField_isOsBond`;
* `darioFlipSumBoundThree_of_sums`: `DarioFlipSumBoundThree` from the almost sure convergence of the
  heat series of `T₁(e)` and the bounds `Σ_e T₁(e)² ≤ O_s(C r^{-d})`, `Σ_e T₂(e)² ≤ O_s(C r^{-d})`,
  through `D_e X = T₁(e) + T₂(e)`, `(a + b)² ≤ 2a² + 2b²` and the `O_s` bound of a maximum;
* `DarioStepOneSumBoundThree`, `DarioStepTwoSumBoundThree`: the bounds of the sums of Step 1 (with
  the convergence of the heat series of `T₁`) and of Step 2;
* `darioVarianceBoundThree_of_sums`: Lemma 3.3 in dimension `d ≥ 3` from these two bounds.
-/

namespace Rigidity.Corrector.GeneralDim

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.External
open scoped ENNReal

/-- **Dario, (3.13) in flip form, in dimension `d ≥ 3`**: for the conull sets `G` of the
measurable corrector there are `s, C > 0` such that for all `i, j`, `r ≥ 1` and `x`, the flip sum
`Σ_e (D_e X)²` of `X = Φ_{r²} * ∇_j[χ_{e_i}]_𝒫(x)` is almost surely finite and `≤ O_s(C r^{-d})`. -/
def DarioFlipSumBoundThree : Prop :=
  ∀ (d : ℕ) [NeZero d], 3 ≤ d → ∀ p : unitInterval, criticalProbability d < (p : ℝ) →
    (p : ℝ) < 1 → ∀ (G : Set (Configuration d)) (hG : MeasurableSet G)
      (hGv : G ⊆ correctorValidEvent d), (∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) →
      ∃ s C : ℝ, 0 < s ∧ 0 < C ∧ ∀ (i j : Fin d) (r : ℝ), 1 ≤ r → ∀ x : Vertex d,
        (∀ᵐ ω ∂latticeBondLaw d p, heatFlipSum hG hGv i j r x ω < ∞) ∧
        IsOsBond d p (fun ω => (heatFlipSum hG hGv i j r x ω).toReal) s (C / r ^ (d : ℝ))

/-- **Dario, Lemma 3.3 in dimension `d ≥ 3`, from the flip form of (3.13)**: the resampling
variance is almost surely at most the flip sum, which is `O_s(C r^{-d})`. -/
theorem darioVarianceBoundThree_of_flipSum (h : DarioFlipSumBoundThree) :
    DarioVarianceBoundThree := by
  intro d _ hd3 p hpc hp1 G hG hGv hGae
  obtain ⟨s, C, hs, hC, hflip⟩ := h d hd3 p hpc hp1 G hG hGv hGae
  obtain ⟨s₀, C₀, hs₀, hC₀, h0⟩ :=
    heatGradient_coarseField_isOsBond hG hGv (by omega) hpc hp1 hGae
  refine ⟨s, C, hs, hC, fun i j r hr x => ?_⟩
  have hF : ∀ z, Measurable (coarseField hG hGv i 0 z) := fun z =>
    measurable_coarseField hG hGv i 0 z
  have hHm := measurable_heatGradient_const hF r x
  have hXm : Measurable (heatCoarseComp hG hGv i j r x) := measurable_heatCoarseComp hG hGv i j r x
  have hHi : Integrable (fun ω => Rigidity.Poincare.GeneralDim.heatGradient
      (fun z => coarseField hG hGv i 0 z ω) r x) (latticeBondLaw d p) := by
    have := (IsOsBond.integral_rpow_le hs₀ hC₀ one_pos hHm (fun ω => heatGradient_nonneg' _ _ _)
      (h0 i r x)).1
    simpa only [Real.rpow_one] using this
  have hXi : Integrable (heatCoarseComp hG hGv i j r x) (latticeBondLaw d p) :=
    hHi.mono' hXm.aestronglyMeasurable (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]
      exact abs_heatComp_le_heatGradient _ _ _ _)
  obtain ⟨hfin, hOs⟩ := hflip i j r hr x
  have hle := ae_resampleVar_le_tsum_bondFlipDiff p hXm hXi
  have hfinV : ∀ᵐ ω ∂latticeBondLaw d p,
      resampleVar p (fun ω => heatComp (fun z => coarseField hG hGv i 0 z ω) r x j) ω < ∞ := by
    filter_upwards [hle, hfin] with ω h1 h2
    exact lt_of_le_of_lt h1 h2
  refine ⟨hfinV, ?_⟩
  have hr0 : 0 < r := by linarith
  refine isOsBond_of_ae_le hs (by positivity) (measurable_resampleVar p hXm).ennreal_toReal ?_ hOs
  filter_upwards [hle, hfin] with ω h1 h2
  exact ENNReal.toReal_mono h2.ne h1

theorem ofReal_sq_add_le (a b : ℝ) :
    ENNReal.ofReal ((a + b) ^ 2) ≤ 2 * ENNReal.ofReal (a ^ 2) + 2 * ENNReal.ofReal (b ^ 2) := by
  have h : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by nlinarith [sq_nonneg (a - b)]
  calc ENNReal.ofReal ((a + b) ^ 2) ≤ ENNReal.ofReal (2 * a ^ 2 + 2 * b ^ 2) :=
        ENNReal.ofReal_le_ofReal h
    _ = 2 * ENNReal.ofReal (a ^ 2) + 2 * ENNReal.ofReal (b ^ 2) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]

/-- **(3.13) in flip form from the two terms of (3.15)**: `DarioFlipSumBoundThree` holds if, for
the conull sets `G` of the measurable corrector, there are `s, C > 0` such that for all `i, j`,
`r ≥ 1` and `x`, almost surely the heat series of `T₁(e)` converges for every bond, and the sums
`Σ_e T₁(e)²` (Step 1) and `Σ_e T₂(e)²` (Step 2) are almost surely finite and `≤ O_s(C r^{-d})`. -/
theorem darioFlipSumBoundThree_of_sums
    (h : ∀ (d : ℕ) [NeZero d], 3 ≤ d → ∀ p : unitInterval, criticalProbability d < (p : ℝ) →
      (p : ℝ) < 1 → ∀ (G : Set (Configuration d)) (hG : MeasurableSet G)
        (hGv : G ⊆ correctorValidEvent d), (∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) →
        ∃ s C : ℝ, 0 < s ∧ 0 < C ∧ ∀ (i j : Fin d) (r : ℝ), 1 ≤ r → ∀ x : Vertex d,
          (∀ᵐ ω ∂latticeBondLaw d p, ∀ e, FlipTermOneSummable hG hGv i j r x e ω) ∧
          (∀ᵐ ω ∂latticeBondLaw d p, flipSumOne hG hGv i j r x ω < ∞) ∧
          (∀ᵐ ω ∂latticeBondLaw d p, flipSumTwo hG hGv i j r x ω < ∞) ∧
          IsOsBond d p (fun ω => (flipSumOne hG hGv i j r x ω).toReal) s (C / r ^ (d : ℝ)) ∧
          IsOsBond d p (fun ω => (flipSumTwo hG hGv i j r x ω).toReal) s (C / r ^ (d : ℝ))) :
    DarioFlipSumBoundThree := by
  intro d _ hd3 p hpc hp1 G hG hGv hGae
  have hd : 2 ≤ d := by omega
  obtain ⟨s, C, hs, hC, hb⟩ := h d hd3 p hpc hp1 G hG hGv hGae
  have hp0 : 0 < (p : ℝ) := (criticalProbability_nonneg d).trans_lt hpc
  refine ⟨s, 4 * C * 4 ^ (1 / s), hs, by positivity, fun i j r hr x => ?_⟩
  obtain ⟨hsum, hf1, hf2, h1, h2⟩ := hb i j r hr x
  have hflipG := ae_setBond hp0 hp1 hGae
  have hflipP := ae_setBond hp0 hp1 (ae_partitionEvent hd hpc)
  have hser := ae_flipSeries_summable hG hGv hd hpc hp1 hGae i
  have hr0 : 0 < r := by linarith
  have hle : ∀ᵐ ω ∂latticeBondLaw d p, heatFlipSum hG hGv i j r x ω ≤
      2 * flipSumOne hG hGv i j r x ω + 2 * flipSumTwo hG hGv i j r x ω := by
    filter_upwards [hflipG, hflipP, hsum, hser] with ω hG' hP' hS hser'
    unfold heatFlipSum flipSumOne flipSumTwo
    calc ∑' e, ENNReal.ofReal (bondFlipDiff (heatCoarseComp hG hGv i j r x) e ω ^ 2)
        ≤ ∑' e, (2 * ENNReal.ofReal (flipTermOne hG hGv i j r x e ω ^ 2) +
            2 * ENNReal.ofReal (flipTermTwo hG hGv i j r x e ω ^ 2)) :=
          ENNReal.tsum_le_tsum fun e => by
            rw [bondFlipDiff_eq_flipTermOne_add_flipTermTwo hG hGv (hG' e true) (hG' e false)
              (hP' e true) (hP' e false) i j r x (fun b => hser' e b x j r hr0) (hS e)]
            exact ofReal_sq_add_le _ _
      _ = 2 * ∑' e, ENNReal.ofReal (flipTermOne hG hGv i j r x e ω ^ 2) +
          2 * ∑' e, ENNReal.ofReal (flipTermTwo hG hGv i j r x e ω ^ 2) := by
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
  have hfin : ∀ᵐ ω ∂latticeBondLaw d p, heatFlipSum hG hGv i j r x ω < ∞ := by
    filter_upwards [hle, hf1, hf2] with ω h0 h1' h2'
    exact h0.trans_lt (ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by norm_num) h1',
      ENNReal.mul_lt_top (by norm_num) h2'⟩)
  refine ⟨hfin, ?_⟩
  have hθ : 0 < C / r ^ (d : ℝ) := by positivity
  have hm1 := (measurable_flipSumOne hG hGv i j r x).ennreal_toReal
  have hm2 := (measurable_flipSumTwo hG hGv i j r x).ennreal_toReal
  have hmax := Rigidity.Proofs.S2.IsOsBond.const_mul (c := 4) (by norm_num)
    (Rigidity.Proofs.S2.IsOsBond.max hs hθ hθ hm1 hm2 h1 h2)
  have e' : 4 * (max (C / r ^ (d : ℝ)) (C / r ^ (d : ℝ)) * 4 ^ (1 / s)) =
      4 * C * 4 ^ (1 / s) / r ^ (d : ℝ) := by
    rw [max_self]
    ring
  rw [e'] at hmax
  refine isOsBond_of_ae_le hs (by positivity)
    (measurable_heatFlipSum hG hGv i j r x).ennreal_toReal ?_ hmax
  filter_upwards [hle, hf1, hf2] with ω h0 h1' h2'
  have hsum_lt : 2 * flipSumOne hG hGv i j r x ω + 2 * flipSumTwo hG hGv i j r x ω < ∞ :=
    ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by norm_num) h1', ENNReal.mul_lt_top (by norm_num) h2'⟩
  calc (heatFlipSum hG hGv i j r x ω).toReal
      ≤ (2 * flipSumOne hG hGv i j r x ω + 2 * flipSumTwo hG hGv i j r x ω).toReal :=
        ENNReal.toReal_mono hsum_lt.ne h0
    _ = 2 * (flipSumOne hG hGv i j r x ω).toReal + 2 * (flipSumTwo hG hGv i j r x ω).toReal := by
        rw [ENNReal.toReal_add (ENNReal.mul_lt_top (by norm_num) h1').ne
          (ENNReal.mul_lt_top (by norm_num) h2').ne, ENNReal.toReal_mul, ENNReal.toReal_mul]
        norm_num
    _ ≤ 4 * max (flipSumOne hG hGv i j r x ω).toReal (flipSumTwo hG hGv i j r x ω).toReal := by
        have := le_max_left (flipSumOne hG hGv i j r x ω).toReal
          (flipSumTwo hG hGv i j r x ω).toReal
        have := le_max_right (flipSumOne hG hGv i j r x ω).toReal
          (flipSumTwo hG hGv i j r x ω).toReal
        linarith

/-- **The bound of the Step 1 sum of the proof of Lemma 3.3 of Dario in dimension `d ≥ 3`**: for
every supercritical `p < 1` and every almost sure event `G` of valid correctors, almost surely the
heat series of `T₁(e)` converges for every bond, and `Σ_e T₁(e)²` is almost surely finite and
`O_s(C r^{-d})`. -/
def DarioStepOneSumBoundThree : Prop :=
  ∀ (d : ℕ) [NeZero d], 3 ≤ d → ∀ p : unitInterval, criticalProbability d < (p : ℝ) →
    (p : ℝ) < 1 → ∀ (G : Set (Configuration d)) (hG : MeasurableSet G)
      (hGv : G ⊆ correctorValidEvent d), (∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) →
      ∃ s C : ℝ, 0 < s ∧ 0 < C ∧ ∀ (i j : Fin d) (r : ℝ), 1 ≤ r → ∀ x : Vertex d,
        (∀ᵐ ω ∂latticeBondLaw d p, ∀ e, FlipTermOneSummable hG hGv i j r x e ω) ∧
        (∀ᵐ ω ∂latticeBondLaw d p, flipSumOne hG hGv i j r x ω < ∞) ∧
        IsOsBond d p (fun ω => (flipSumOne hG hGv i j r x ω).toReal) s (C / r ^ (d : ℝ))

/-- **The bound of the Step 2 sum of the proof of Lemma 3.3 of Dario in dimension `d ≥ 3`**: for
every supercritical `p < 1` and every almost sure event `G` of valid correctors, `Σ_e T₂(e)²` is
almost surely finite and `O_s(C r^{-d})`. The form in dimension two is
`Rigidity.Poincare.DarioStepTwoSumBound`. -/
def DarioStepTwoSumBoundThree : Prop :=
  ∀ (d : ℕ) [NeZero d], 3 ≤ d → ∀ p : unitInterval, criticalProbability d < (p : ℝ) →
    (p : ℝ) < 1 → ∀ (G : Set (Configuration d)) (hG : MeasurableSet G)
      (hGv : G ⊆ correctorValidEvent d), (∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) →
      ∃ s C : ℝ, 0 < s ∧ 0 < C ∧ ∀ (i j : Fin d) (r : ℝ), 1 ≤ r → ∀ x : Vertex d,
        (∀ᵐ ω ∂latticeBondLaw d p, flipSumTwo hG hGv i j r x ω < ∞) ∧
        IsOsBond d p (fun ω => (flipSumTwo hG hGv i j r x ω).toReal) s (C / r ^ (d : ℝ))

/-- **Dario, Lemma 3.3 in dimension `d ≥ 3`, from the bounds of the sums of Steps 1 and 2.** -/
theorem darioVarianceBoundThree_of_sums (h1 : DarioStepOneSumBoundThree)
    (h2 : DarioStepTwoSumBoundThree) : DarioVarianceBoundThree := by
  refine darioVarianceBoundThree_of_flipSum (darioFlipSumBoundThree_of_sums ?_)
  intro d _ hd3 p hpc hp1 G hG hGv hGae
  obtain ⟨s₁, C₁, hs₁, hC₁, hb1⟩ := h1 d hd3 p hpc hp1 G hG hGv hGae
  obtain ⟨s₂, C₂, hs₂, hC₂, hb2⟩ := h2 d hd3 p hpc hp1 G hG hGv hGae
  set s := min s₁ s₂
  have hs : 0 < s := lt_min hs₁ hs₂
  refine ⟨s, max C₁ C₂ * 6 ^ (1 / s), hs, by positivity, fun i j r hr x => ?_⟩
  have hr0 : 0 < r ^ (d : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  obtain ⟨hsum, hf1, hO1⟩ := hb1 i j r hr x
  obtain ⟨hf2, hO2⟩ := hb2 i j r hr x
  have hm1 : Measurable fun ω => (flipSumOne hG hGv i j r x ω).toReal :=
    (measurable_flipSumOne hG hGv i j r x).ennreal_toReal
  have hm2 : Measurable fun ω => (flipSumTwo hG hGv i j r x ω).toReal :=
    (measurable_flipSumTwo hG hGv i j r x).ennreal_toReal
  have hfin : ∀ {C'' : ℝ}, C'' ≤ max C₁ C₂ →
      C'' / r ^ (d : ℝ) * 6 ^ (1 / s) ≤ max C₁ C₂ * 6 ^ (1 / s) / r ^ (d : ℝ) := fun h => by
    rw [div_mul_eq_mul_div]
    gcongr
  refine ⟨hsum, hf1, hf2, ?_, ?_⟩
  · exact Rigidity.Proofs.S2.IsOsBond.mono_scale hs (by positivity) (hfin (le_max_left _ _)) hm1
      (Rigidity.Proofs.S2.IsOsBond.mono_exponent hs (min_le_left _ _) hm1 hO1)
  · exact Rigidity.Proofs.S2.IsOsBond.mono_scale hs (by positivity) (hfin (le_max_right _ _)) hm2
      (Rigidity.Proofs.S2.IsOsBond.mono_exponent hs (min_le_right _ _) hm2 hO2)

end Rigidity.Corrector.GeneralDim
