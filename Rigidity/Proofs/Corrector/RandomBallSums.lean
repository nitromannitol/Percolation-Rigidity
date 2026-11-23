import Rigidity.Proofs.Corrector.DarioPoincareMoments

/-!
# Moments of sums over random balls

Dario's estimates (2.23)–(2.24), (5.7) and (5.10) bound sums of `O_s` variables over balls of
random radius `C size(□_𝒫(x))`. With (2.24) and the `O_s` calculus (1.12), (1.14), the paper
bounds `1{x' ∈ B(x, ρ)} ≤ O_s(C) / (|x - x'| ∨ 1)^{d+1}`. Here this is replaced by moments
(`lintegral_randomBallSum_le`): if the radius `ρ` has an exponential tail
`P[ρ ≥ t] ≤ 2 e^{-t/θ}` and the summands have uniform moments `E[Y_x^{2q}] ≤ M²`, then

`E[(Σ_{x : |x - v| ≤ ρ} Y_x)^q] ≤ (4 (1 + 8qθ)²)^{q-1} · 4√2 (1 + 8θ)² · M`,

by Jensen's inequality for the weights `e^{-|x - v|/(4qθ)}`, the Cauchy–Schwarz inequality and
the lattice sum `Σ_x e^{-|x - v|/κ} ≤ 4 (1 + 2κ)²` (`tsum_exp_neg_norm_sub_le`).
-/

namespace Rigidity.Corrector

open MeasureTheory Filter Set LatticeProb.Percolation Rigidity.External
open scoped ENNReal

/-- `Σ_{x ∈ ℤ²} e^{-|x - v|/κ} ≤ 4 (1 + 2κ)²`. -/
theorem tsum_exp_neg_norm_sub_le (v : Vertex 2) {κ : ℝ} (hκ : 0 < κ) :
    ∑' x : Vertex 2, ENNReal.ofReal (Real.exp (-‖latticeEuclideanEmbedding (x - v)‖ / κ)) ≤
      ENNReal.ofReal (4 * (1 + 2 * κ) ^ 2) := by
  rw [← (Equiv.addRight v).tsum_eq]
  simp only [Equiv.coe_addRight, add_sub_cancel_right]
  set c : ℝ := 1 / (2 * κ) with hc
  have hc0 : 0 < c := by positivity
  set f : ℤ → ℝ≥0∞ := fun n => ENNReal.ofReal (Real.exp (-(c * |(n : ℝ)|))) with hf
  have hpt : ∀ x : Vertex 2, ENNReal.ofReal (Real.exp (-‖latticeEuclideanEmbedding x‖ / κ)) ≤
      f (x 0) * f (x 1) := by
    intro x
    have h0 := PiLp.norm_apply_le (latticeEuclideanEmbedding x) 0
    have h1 := PiLp.norm_apply_le (latticeEuclideanEmbedding x) 1
    change ‖((x 0 : ℤ) : ℝ)‖ ≤ _ at h0
    change ‖((x 1 : ℤ) : ℝ)‖ ≤ _ at h1
    rw [Real.norm_eq_abs] at h0 h1
    simp only [hf]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    set e := ‖latticeEuclideanEmbedding x‖
    have key : c * |((x 0 : ℤ) : ℝ)| + c * |((x 1 : ℤ) : ℝ)| ≤ e / κ := by
      rw [hc, div_mul_eq_mul_div, div_mul_eq_mul_div, one_mul, one_mul, ← add_div,
        div_le_div_iff₀ (by positivity) hκ]
      nlinarith
    have : -e / κ = -(e / κ) := neg_div _ _
    rw [this]
    linarith
  have hsum : ∑' n : ℤ, f n ≤ ENNReal.ofReal (2 * (1 + 2 * κ)) := by
    have := tsum_int_exp_neg_le hc0
    rwa [hc, one_div_one_div] at this
  have hprod : ∑' x : Vertex 2, f (x 0) * f (x 1) = (∑' n : ℤ, f n) * ∑' n : ℤ, f n := by
    rw [← ENNReal.tsum_mul_right]
    simp_rw [← ENNReal.tsum_mul_left]
    rw [← ENNReal.tsum_prod]
    exact (finTwoArrowEquiv ℤ).tsum_eq (fun ab => f ab.1 * f ab.2)
  calc ∑' x : Vertex 2, ENNReal.ofReal (Real.exp (-‖latticeEuclideanEmbedding x‖ / κ))
      ≤ ∑' x : Vertex 2, f (x 0) * f (x 1) := ENNReal.tsum_le_tsum hpt
    _ = (∑' n : ℤ, f n) * ∑' n : ℤ, f n := hprod
    _ ≤ ENNReal.ofReal (2 * (1 + 2 * κ)) * ENNReal.ofReal (2 * (1 + 2 * κ)) := by gcongr
    _ = ENNReal.ofReal (4 * (1 + 2 * κ) ^ 2) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        ring_nf

/-- **Moments of a sum over a ball of random radius.** -/
theorem lintegral_randomBallSum_le {p : unitInterval} (v : Vertex 2) {ρ : Configuration 2 → ℝ}
    {θ : ℝ} (hθ : 0 < θ)
    (htail : ∀ t : ℝ, 0 ≤ t →
      latticeBondLaw 2 p {ω | t ≤ ρ ω} ≤ ENNReal.ofReal (2 * Real.exp (-(t / θ))))
    (hρ : Measurable ρ) {Y : Vertex 2 → Configuration 2 → ℝ≥0∞} (hY : ∀ x, Measurable (Y x))
    {q M : ℝ} (hq : 1 ≤ q) (hM : 0 ≤ M)
    (hYm : ∀ x, ∫⁻ ω, Y x ω ^ (2 * q) ∂latticeBondLaw 2 p ≤ ENNReal.ofReal (M ^ 2)) :
    ∫⁻ ω, (∑' x, if ‖latticeEuclideanEmbedding (x - v)‖ ≤ ρ ω then Y x ω else 0) ^ q
        ∂latticeBondLaw 2 p ≤
      ENNReal.ofReal ((4 * (1 + 8 * q * θ) ^ 2) ^ (q - 1) *
        (Real.sqrt 2 * 4 * (1 + 8 * θ) ^ 2 * M)) := by
  classical
  have hq0 : 0 < q := by linarith
  set κ : ℝ := 4 * q * θ with hκ
  have hκ0 : 0 < κ := by positivity
  set a : Vertex 2 → ℝ := fun x => ‖latticeEuclideanEmbedding (x - v)‖ with ha
  have ha0 : ∀ x, 0 ≤ a x := fun x => norm_nonneg _
  set w : Vertex 2 → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (-a x / κ)) with hw
  set I : Vertex 2 → Configuration 2 → ℝ≥0∞ := fun x ω =>
    if a x ≤ ρ ω then Y x ω else 0 with hI
  have hIm : ∀ x, Measurable (I x) := fun x =>
    Measurable.ite (measurableSet_le measurable_const hρ) (hY x) measurable_const
  set W := ∑' x, w x with hW
  have hWle : W ≤ ENNReal.ofReal (4 * (1 + 8 * q * θ) ^ 2) := by
    have := tsum_exp_neg_norm_sub_le v hκ0
    rw [show 2 * κ = 8 * q * θ by rw [hκ]; ring] at this
    exact this
  -- Jensen for the weights `w`, pointwise in `ω`
  set g : Vertex 2 → Configuration 2 → ℝ≥0∞ := fun x ω =>
    I x ω * ENNReal.ofReal (Real.exp (a x / κ)) with hg
  have hgw : ∀ x ω, g x ω * w x = I x ω := by
    intro x ω
    simp only [hg, hw]
    rw [mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
      show a x / κ + -a x / κ = 0 by ring, Real.exp_zero, ENNReal.ofReal_one, mul_one]
  have hgq : ∀ x ω, g x ω ^ q * w x =
      I x ω ^ q * ENNReal.ofReal (Real.exp ((q - 1) * (a x / κ))) := by
    intro x ω
    simp only [hg, hw]
    rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le,
      ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hq0.le, ← Real.exp_mul, mul_assoc,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 3
    ring
  have hJ : ∀ ω, (∑' x, I x ω) ^ q ≤
      (∑' x, I x ω ^ q * ENNReal.ofReal (Real.exp ((q - 1) * (a x / κ)))) * W ^ (q - 1) := by
    intro ω
    have h := lintegral_mul_rpow_le (μ := Measure.count) (g := fun x => g x ω) (w := w)
      (measurable_of_countable _).aemeasurable (measurable_of_countable _).aemeasurable
      (fun x => ENNReal.ofReal_ne_top) hq
    simp only [lintegral_count, hgw, hgq] at h
    exact h
  -- the moments of the summands on their events
  have hCS : ∀ x, ∫⁻ ω, I x ω ^ q ∂latticeBondLaw 2 p ≤
      ENNReal.ofReal (Real.sqrt 2 * Real.exp (-(a x / (2 * θ))) * M) := by
    intro x
    set A := {ω : Configuration 2 | a x ≤ ρ ω}
    have hA : MeasurableSet A := measurableSet_le measurable_const hρ
    have hpt : ∀ ω, I x ω ^ q = A.indicator 1 ω * Y x ω ^ q := by
      intro ω
      simp only [hI, Set.indicator_apply, A, Set.mem_setOf_eq, Pi.one_apply]
      split_ifs <;> simp [ENNReal.zero_rpow_of_pos hq0]
    simp only [hpt]
    have hcs := ENNReal.lintegral_mul_le_Lp_mul_Lq (latticeBondLaw 2 p)
      (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩ : (2 : ℝ).HolderConjugate 2)
      ((measurable_one.indicator hA).aemeasurable) (((hY x).pow_const q).aemeasurable)
    have h1 : ∫⁻ ω, A.indicator 1 ω ^ (2 : ℝ) ∂latticeBondLaw 2 p = latticeBondLaw 2 p A := by
      have : ∀ ω, A.indicator (1 : Configuration 2 → ℝ≥0∞) ω ^ (2 : ℝ) = A.indicator 1 ω := by
        intro ω
        simp only [Set.indicator_apply, Pi.one_apply]
        split_ifs <;> simp
      simp only [this]
      rw [lintegral_indicator_one hA]
    have h2 : ∫⁻ ω, (Y x ω ^ q) ^ (2 : ℝ) ∂latticeBondLaw 2 p ≤ ENNReal.ofReal (M ^ 2) := by
      have : ∀ ω, (Y x ω ^ q) ^ (2 : ℝ) = Y x ω ^ (2 * q) := by
        intro ω
        rw [← ENNReal.rpow_mul, mul_comm]
      simp only [this]
      exact hYm x
    have htx : latticeBondLaw 2 p A ≤ ENNReal.ofReal (2 * Real.exp (-(a x / θ))) :=
      htail (a x) (ha0 x)
    have hfin : ENNReal.ofReal (2 * Real.exp (-(a x / θ))) ^ (1 / (2 : ℝ)) *
        ENNReal.ofReal (M ^ 2) ^ (1 / (2 : ℝ)) =
          ENNReal.ofReal (Real.sqrt 2 * Real.exp (-(a x / (2 * θ))) * M) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
        ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [Real.mul_rpow (by norm_num) (Real.exp_pos _).le, ← Real.sqrt_eq_rpow 2,
        ← Real.exp_mul, ← Real.rpow_two M, ← Real.rpow_mul hM,
        show (2 : ℝ) * (1 / 2) = 1 by norm_num, Real.rpow_one,
        show -(a x / θ) * (1 / 2) = -(a x / (2 * θ)) by field_simp]
    calc ∫⁻ ω, A.indicator 1 ω * Y x ω ^ q ∂latticeBondLaw 2 p
        ≤ (∫⁻ ω, A.indicator 1 ω ^ (2 : ℝ) ∂latticeBondLaw 2 p) ^ (1 / (2 : ℝ)) *
            (∫⁻ ω, (Y x ω ^ q) ^ (2 : ℝ) ∂latticeBondLaw 2 p) ^ (1 / (2 : ℝ)) := hcs
      _ ≤ ENNReal.ofReal (2 * Real.exp (-(a x / θ))) ^ (1 / (2 : ℝ)) *
            ENNReal.ofReal (M ^ 2) ^ (1 / (2 : ℝ)) :=
          mul_le_mul' (ENNReal.rpow_le_rpow (h1.le.trans htx) (by norm_num))
            (ENNReal.rpow_le_rpow h2 (by norm_num))
      _ = _ := hfin
  -- assembling
  have hterm : ∀ x, ENNReal.ofReal (Real.exp ((q - 1) * (a x / κ))) *
      ENNReal.ofReal (Real.sqrt 2 * Real.exp (-(a x / (2 * θ))) * M) ≤
        ENNReal.ofReal (Real.sqrt 2 * M) *
          ENNReal.ofReal (Real.exp (-‖latticeEuclideanEmbedding (x - v)‖ / (4 * θ))) := by
    intro x
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hexp : Real.exp ((q - 1) * (a x / κ)) * Real.exp (-(a x / (2 * θ))) ≤
        Real.exp (-‖latticeEuclideanEmbedding (x - v)‖ / (4 * θ)) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have hax := ha0 x
      change (q - 1) * (a x / κ) + -(a x / (2 * θ)) ≤ -a x / (4 * θ)
      rw [hκ]
      have : (q - 1) * (a x / (4 * q * θ)) ≤ a x / (4 * θ) := by
        rw [div_eq_mul_inv, div_eq_mul_inv, show (4 * q * θ)⁻¹ = q⁻¹ * (4 * θ)⁻¹ by
          rw [mul_comm 4 q, mul_assoc, mul_inv]]
        have hqi : (q - 1) * q⁻¹ ≤ 1 := by
          rw [sub_mul, mul_inv_cancel₀ hq0.ne', one_mul]
          have : 0 < q⁻¹ := inv_pos.2 hq0
          linarith
        have h4 : 0 ≤ a x * (4 * θ)⁻¹ := by positivity
        nlinarith
      have e1 : -a x / (4 * θ) = a x / (4 * θ) - a x / (2 * θ) := by field_simp; ring
      rw [e1]
      linarith
    calc Real.exp ((q - 1) * (a x / κ)) * (Real.sqrt 2 * Real.exp (-(a x / (2 * θ))) * M)
        = Real.sqrt 2 * M * (Real.exp ((q - 1) * (a x / κ)) * Real.exp (-(a x / (2 * θ)))) := by
          ring
      _ ≤ Real.sqrt 2 * M * Real.exp (-‖latticeEuclideanEmbedding (x - v)‖ / (4 * θ)) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
  have hsumW := tsum_exp_neg_norm_sub_le v (show 0 < 4 * θ by positivity)
  calc ∫⁻ ω, (∑' x, if ‖latticeEuclideanEmbedding (x - v)‖ ≤ ρ ω then Y x ω else 0) ^ q
        ∂latticeBondLaw 2 p
      = ∫⁻ ω, (∑' x, I x ω) ^ q ∂latticeBondLaw 2 p := rfl
    _ ≤ ∫⁻ ω, (∑' x, I x ω ^ q * ENNReal.ofReal (Real.exp ((q - 1) * (a x / κ)))) * W ^ (q - 1)
          ∂latticeBondLaw 2 p := lintegral_mono hJ
    _ = (∑' x, ENNReal.ofReal (Real.exp ((q - 1) * (a x / κ))) *
          ∫⁻ ω, I x ω ^ q ∂latticeBondLaw 2 p) * W ^ (q - 1) := by
        rw [lintegral_mul_const' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith)
          (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hWle))]
        congr 1
        rw [lintegral_tsum fun x => (((hIm x).pow_const q).mul_const _).aemeasurable]
        refine tsum_congr fun x => ?_
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, mul_comm]
    _ ≤ (∑' x, ENNReal.ofReal (Real.sqrt 2 * M) *
          ENNReal.ofReal (Real.exp (-‖latticeEuclideanEmbedding (x - v)‖ / (4 * θ)))) *
          ENNReal.ofReal (4 * (1 + 8 * q * θ) ^ 2) ^ (q - 1) := by
        exact mul_le_mul' (ENNReal.tsum_le_tsum fun x => (mul_le_mul_right (hCS x) _).trans (hterm x))
          (ENNReal.rpow_le_rpow hWle (by linarith))
    _ ≤ (ENNReal.ofReal (Real.sqrt 2 * M) * ENNReal.ofReal (4 * (1 + 2 * (4 * θ)) ^ 2)) *
          ENNReal.ofReal (4 * (1 + 8 * q * θ) ^ 2) ^ (q - 1) := by
        rw [ENNReal.tsum_mul_left]
        gcongr
    _ = ENNReal.ofReal ((4 * (1 + 8 * q * θ) ^ 2) ^ (q - 1) *
          (Real.sqrt 2 * 4 * (1 + 8 * θ) ^ 2 * M)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by linarith),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

end Rigidity.Corrector
