import Rigidity.Proofs.Corrector.GeneralPartitionComparison
import Rigidity.Proofs.Corrector.DarioPoincareMoments

/-!
# Step 1 of the proof of Dario's Theorem 2 in dimension `d ≥ 3`

Step 1 of the proof of Theorem 2 bounds the box oscillations of the coarsened corrector by the
multiscale Poincaré inequality (2.26) and Proposition 3.1,
`|Φ_{r²} * ∇[χ]_𝒫(x)| ≤ O_s(C r^{-d/2})`. In dimension `d ≥ 3` the heat-kernel square function
`∫_0^T r |Φ_{r²} * ∇[χ]_𝒫|² dr` has moments bounded uniformly in `T`, since
`∫_1^∞ r · r^{-d} dr < ∞` (`lintegral_rpow_heatSquare_le_three`); hence (5.5) holds with box
oscillations bounded uniformly in the scale (`lintegral_boxOsc_le_of_poincare_three`), and with
the comparison (5.7) and the coarsening error (5.10), Dario's Theorem 1 in dimension `d ≥ 3`
follows from the multiscale Poincaré inequality in cube form, Proposition 3.1 and the Lipschitz
bound of the smoothed gradients (`darioOptimalCorrectorThree_of_poincareInputs`).
-/

namespace Rigidity.Corrector.GeneralDim

open MeasureTheory Filter Set LatticeProb.Percolation Rigidity.External
open scoped ENNReal

variable {d : ℕ} {p : unitInterval}

/-- Jensen's inequality `E[Y^a] ≤ E[Y]^a` for `0 ≤ a ≤ 1`. -/
theorem lintegral_rpow_le_rpow_lintegral {Y : Configuration d → ℝ≥0∞}
    (hY : AEMeasurable Y (latticeBondLaw d p)) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∫⁻ ω, Y ω ^ a ∂latticeBondLaw d p ≤ (∫⁻ ω, Y ω ∂latticeBondLaw d p) ^ a := by
  have h := ENNReal.lintegral_mul_norm_pow_le hY (aemeasurable_const (b := (1 : ℝ≥0∞))) ha0
    (sub_nonneg.2 ha1) (by ring : a + (1 - a) = 1)
  simpa [ENNReal.one_rpow, lintegral_const, measure_univ] using h

theorem lintegral_le_of_isOsBond_rpow_inv {S : Configuration d → ℝ} {s θ q : ℝ} (hs : 0 < s)
    (hθ : 0 < θ) (hq : 1 ≤ q) (hS : Measurable S) (hS0 : ∀ ω, 0 ≤ S ω)
    (h : IsOsBond d p (fun ω => S ω ^ (1 / q)) s θ) :
    ∫⁻ ω, ENNReal.ofReal (S ω) ∂latticeBondLaw d p ≤
      ENNReal.ofReal ((2 * θ * (1 / s) ^ (1 / s) * q ^ (1 / s)) ^ q) := by
  have hq0 : 0 < q := by linarith
  obtain ⟨hint, hle⟩ := IsOsBond.integral_rpow_le hs hθ hq0 (hS.pow_const (1 / q))
    (fun ω => Real.rpow_nonneg (hS0 ω) _) h
  have hpow : ∀ ω, (S ω ^ (1 / q)) ^ q = S ω := fun ω => by
    rw [← Real.rpow_mul (hS0 ω), one_div_mul_cancel hq0.ne', Real.rpow_one]
  simp only [hpow] at hint hle
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hS0)]
  refine ENNReal.ofReal_le_ofReal (hle.trans ?_)
  have he : Real.exp (-(q / s)) ≤ 1 :=
    Real.exp_le_one_iff.2 (by have := div_pos hq0 hs; linarith)
  have he0 : 0 ≤ Real.exp (-(q / s)) := (Real.exp_pos _).le
  have hqs : (q / s) ^ (q / s) = ((1 / s) ^ (1 / s) * q ^ (1 / s)) ^ q := by
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by positivity),
      ← Real.rpow_mul hq0.le, show 1 / s * q = q / s by ring, ← Real.mul_rpow (by positivity)
      hq0.le]
    congr 1
    ring
  have h2 : (2 : ℝ) ≤ 2 ^ q := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hq
  have hexp : (2 * θ * (1 / s) ^ (1 / s) * q ^ (1 / s)) ^ q =
      2 ^ q * θ ^ q * ((1 / s) ^ (1 / s) * q ^ (1 / s)) ^ q := by
    rw [mul_assoc (2 * θ), Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by norm_num) hθ.le]
  rw [hexp, hqs]
  have hT : 0 ≤ θ ^ q := by positivity
  have hX : 0 ≤ ((1 / s) ^ (1 / s) * q ^ (1 / s)) ^ q := by positivity
  have hTX := mul_nonneg hT hX
  nlinarith [mul_nonneg hTX (sub_nonneg.2 he), mul_nonneg hTX (sub_nonneg.2 h2),
    mul_nonneg hTX he0]

/-- If `|f| ≤ O_s(θ)`, then `E|f|^q ≤ (2 θ (1/s)^{1/s} q^{1/s})^q`. -/
theorem mom_le_of_isOsBond {f : Configuration d → ℝ} {s θ q : ℝ} (hs : 0 < s) (hθ : 0 < θ)
    (hq : 1 ≤ q) (hf : Measurable f) (h : IsOsBond d p (fun ω => |f ω|) s θ) :
    mom p f q ≤ ENNReal.ofReal ((2 * θ * (1 / s) ^ (1 / s) * q ^ (1 / s)) ^ q) := by
  have hq0 : 0 < q := by linarith
  refine lintegral_le_of_isOsBond_rpow_inv hs hθ hq (hf.abs.pow_const q)
    (fun ω => by positivity) ?_
  have : (fun ω => (|f ω| ^ q) ^ (1 / q)) = fun ω => |f ω| := funext fun ω => by
    rw [← Real.rpow_mul (abs_nonneg _), mul_one_div_cancel hq0.ne', Real.rpow_one]
  rw [this]
  exact h

/-- The mass of the weight `min(r, r^{-2})` on `(0, T]`: at most `3/2`. -/
theorem lintegral_Ioc_min_rpow_le {T : ℝ} (hT : 1 ≤ T) :
    ∫⁻ r in Ioc 0 T, ENNReal.ofReal (min r (r ^ (-2 : ℝ))) ≤ ENNReal.ofReal (3 / 2) := by
  rw [← Ioc_union_Ioc_eq_Ioc zero_le_one hT,
    lintegral_union measurableSet_Ioc (Ioc_disjoint_Ioc_of_le le_rfl)]
  have h1 : ∫⁻ r in Ioc 0 1, ENNReal.ofReal (min r (r ^ (-2 : ℝ))) ≤ ENNReal.ofReal (1 / 2) := by
    calc ∫⁻ r in Ioc 0 1, ENNReal.ofReal (min r (r ^ (-2 : ℝ)))
        ≤ ∫⁻ r in Ioc 0 1, ENNReal.ofReal r :=
          lintegral_mono fun r => ENNReal.ofReal_le_ofReal (min_le_left _ _)
      _ = ENNReal.ofReal (∫ r in Ioc 0 1, r) :=
          (ofReal_integral_eq_lintegral_ofReal
            ((continuous_id.integrableOn_Icc).mono_set Ioc_subset_Icc_self)
            (ae_restrict_of_forall_mem measurableSet_Ioc fun r hr => hr.1.le)).symm
      _ = ENNReal.ofReal (1 / 2) := by
          rw [← intervalIntegral.integral_of_le zero_le_one, integral_id]
          norm_num
  have h2 : ∫⁻ r in Ioc 1 T, ENNReal.ofReal (min r (r ^ (-2 : ℝ))) ≤ ENNReal.ofReal 1 := by
    calc ∫⁻ r in Ioc 1 T, ENNReal.ofReal (min r (r ^ (-2 : ℝ)))
        ≤ ∫⁻ r in Ioc 1 T, ENNReal.ofReal (r ^ (-2 : ℝ)) :=
          lintegral_mono fun r => ENNReal.ofReal_le_ofReal (min_le_right _ _)
      _ ≤ ∫⁻ r in Ioi 1, ENNReal.ofReal (r ^ (-2 : ℝ)) := lintegral_mono_set Ioc_subset_Ioi_self
      _ = ENNReal.ofReal (∫ r in Ioi 1, r ^ (-2 : ℝ)) :=
          (ofReal_integral_eq_lintegral_ofReal
            (integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one)
            (ae_restrict_of_forall_mem measurableSet_Ioi fun r hr =>
              Real.rpow_nonneg (zero_le_one.trans (mem_Ioi.1 hr).le) _)).symm
      _ = ENNReal.ofReal 1 := by
          rw [integral_Ioi_rpow_of_lt (by norm_num) zero_lt_one]
          norm_num
  calc _ ≤ ENNReal.ofReal (1 / 2) + ENNReal.ofReal 1 := add_le_add h1 h2
    _ = ENNReal.ofReal (3 / 2) := by
        rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
        norm_num

/-- The lattice sum of the weights of the multiscale Poincaré inequality at `R = 3^m`:
`Σ_{x ∈ ℤᵈ} R^{-d} e^{-|x|/2R} ≤ (2 (1 + 2d))^d`. -/
theorem tsum_poincareWeight_le (m : ℕ) :
    ∑' x : Vertex d, ENNReal.ofReal
      (Real.exp (-‖latticeEuclideanEmbedding x‖ / (2 * 3 ^ m)) / (3 ^ m) ^ d) ≤
        ENNReal.ofReal ((2 * (1 + 2 * d)) ^ d) := by
  have hR1 : (1 : ℝ) ≤ 3 ^ m := one_le_pow₀ (by norm_num)
  have hR0 : (0 : ℝ) < 3 ^ m := by linarith
  have hpt : ∀ x : Vertex d, ENNReal.ofReal
      (Real.exp (-‖latticeEuclideanEmbedding x‖ / (2 * 3 ^ m)) / (3 ^ m) ^ d) =
        ENNReal.ofReal (1 / ((3 : ℝ) ^ m) ^ d) * ENNReal.ofReal
          (Real.exp (-‖latticeEuclideanEmbedding (x - 0)‖ / (2 * 3 ^ m))) := by
    intro x
    rw [← ENNReal.ofReal_mul (by positivity), sub_zero]
    congr 1
    ring
  rw [tsum_congr hpt, ENNReal.tsum_mul_left]
  calc ENNReal.ofReal (1 / ((3 : ℝ) ^ m) ^ d) * ∑' x : Vertex d, ENNReal.ofReal
        (Real.exp (-‖latticeEuclideanEmbedding (x - 0)‖ / (2 * 3 ^ m)))
      ≤ ENNReal.ofReal (1 / ((3 : ℝ) ^ m) ^ d) *
          ENNReal.ofReal ((2 * (1 + d * (2 * 3 ^ m))) ^ d) :=
        mul_le_mul_right (tsum_exp_neg_norm_sub_le 0 (by positivity)) _
    _ = ENNReal.ofReal ((2 * (1 + d * (2 * 3 ^ m)) / 3 ^ m) ^ d) := by
        rw [← ENNReal.ofReal_mul (by positivity), div_pow]
        congr 1
        ring
    _ ≤ ENNReal.ofReal ((2 * (1 + 2 * d)) ^ d) := by
        refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) ?_ d)
        rw [div_le_iff₀ hR0]
        nlinarith

/-- **The moment of the heat-kernel square function at one point, `d ≥ 3`**: under the bounds of
Proposition 3.1 (`S r x ≤ O_s(C r^{-d/2})` for `r ≥ 1`) and of the Lipschitz bound (`r ≤ 1`) on
`S r x = |Φ_{r²} * ∇u(x)|`,
`E[(∫_0^T r S(r, x)² dr)^{q/2}] ≤ (2 C (1/s)^{1/s} q^{1/s})^q (3/2)^{q/2}`, uniformly in `T`. -/
theorem lintegral_rpow_heatSquare_le_three {S : ℝ → Vertex d → Configuration d → ℝ} {C s : ℝ}
    (hd : 3 ≤ d) (hC : 0 < C) (hs : 0 < s)
    (hSm : ∀ x, Measurable fun rω : ℝ × Configuration d => S rω.1 x rω.2)
    (hS0 : ∀ r x ω, 0 ≤ S r x ω)
    (hlarge : ∀ r : ℝ, 1 ≤ r → ∀ x, IsOsBond d p (S r x) s (C / r ^ ((d : ℝ) / 2)))
    (hsmall : ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ x, IsOsBond d p (S r x) s C)
    {T q : ℝ} (hT : 1 ≤ T) (hq : 2 ≤ q) (x : Vertex d) :
    ∫⁻ ω, (∫⁻ r in Ioc 0 T, ENNReal.ofReal (r * S r x ω ^ 2)) ^ (q / 2) ∂latticeBondLaw d p ≤
      ENNReal.ofReal ((2 * C * (1 / s) ^ (1 / s) * q ^ (1 / s)) ^ q) *
        ENNReal.ofReal (3 / 2) ^ (q / 2) := by
  set a := q / 2 with ha
  have ha1 : 1 ≤ a := by rw [ha]; linarith
  have hq1 : 1 ≤ q := by linarith
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  set σ := (1 / s) ^ (1 / s) with hσ
  have hσ0 : 0 < σ := by positivity
  set K := (2 * C * σ * q ^ (1 / s)) ^ q with hK
  set W := ENNReal.ofReal (3 / 2) with hW
  have hW0 : W ≠ 0 := by
    rw [hW, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    norm_num
  have hWt : W ≠ ⊤ := ENNReal.ofReal_ne_top
  set w : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (r / max 1 r ^ (d : ℝ)) with hw
  have hwm : Measurable w :=
    (measurable_id.div ((measurable_const.max measurable_id).pow_const _)).ennreal_ofReal
  set g : ℝ → Configuration d → ℝ≥0∞ := fun r ω =>
    ENNReal.ofReal (max 1 r ^ (d : ℝ) * S r x ω ^ 2) with hg
  have hgm : Measurable fun rω : ℝ × Configuration d => g rω.1 rω.2 :=
    (((measurable_const.max measurable_fst).pow_const _).mul
      ((hSm x).pow_const 2)).ennreal_ofReal
  have hMpos : ∀ r : ℝ, 0 < max 1 r ^ (d : ℝ) := fun r =>
    Real.rpow_pos_of_pos (lt_max_of_lt_left zero_lt_one) _
  have hid : ∀ ω, EqOn (fun r => ENNReal.ofReal (r * S r x ω ^ 2)) (fun r => g r ω * w r)
      (Ioc 0 T) := by
    intro ω r hr
    simp only [hg, hw]
    have hr0 : 0 < r := hr.1
    rw [← ENNReal.ofReal_mul (by have := hMpos r; positivity)]
    congr 1
    have := (hMpos r).ne'
    field_simp
  have hwle : ∀ r ∈ Ioc (0 : ℝ) T, w r ≤ ENNReal.ofReal (min r (r ^ (-2 : ℝ))) := by
    intro r hr
    have hr0 : 0 < r := hr.1
    refine ENNReal.ofReal_le_ofReal ?_
    rcases le_or_gt r 1 with h1 | h1
    · rw [max_eq_left h1, Real.one_rpow, div_one]
      have : 1 ≤ r ^ (-2 : ℝ) :=
        Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr0 h1 (by norm_num)
      exact le_min le_rfl (h1.trans this)
    · rw [max_eq_right h1.le]
      have e : r / r ^ (d : ℝ) = r ^ (1 - (d : ℝ)) := by
        rw [Real.rpow_sub hr0, Real.rpow_one]
      rw [e]
      refine le_min ?_ ?_
      · calc r ^ (1 - (d : ℝ)) ≤ r ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le h1.le (by linarith)
          _ = r := Real.rpow_one r
      · exact Real.rpow_le_rpow_of_exponent_le h1.le (by linarith)
  have hwint : ∫⁻ r in Ioc 0 T, w r ≤ W :=
    (setLIntegral_mono' measurableSet_Ioc hwle).trans (lintegral_Ioc_min_rpow_le hT)
  -- Jensen in `r`, pointwise in `ω`
  have hpt : ∀ ω, (∫⁻ r in Ioc 0 T, ENNReal.ofReal (r * S r x ω ^ 2)) ^ a ≤
      (∫⁻ r in Ioc 0 T, g r ω ^ a * w r) * W ^ (a - 1) := by
    intro ω
    rw [setLIntegral_congr_fun measurableSet_Ioc (hid ω)]
    refine (lintegral_mul_rpow_le (hgm.comp (measurable_id.prodMk measurable_const)).aemeasurable
      hwm.aemeasurable (fun r => ENNReal.ofReal_ne_top) ha1).trans ?_
    exact mul_le_mul_right (ENNReal.rpow_le_rpow hwint (by linarith)) _
  -- the moment at each `r`
  have hmomr : ∀ r ∈ Ioc (0 : ℝ) T, ∫⁻ ω, g r ω ^ a ∂latticeBondLaw d p ≤ ENNReal.ofReal K := by
    intro r hr
    have hr0 : 0 < r := hr.1
    have hM : 0 ≤ max 1 r := le_max_of_le_left zero_le_one
    obtain ⟨θ, hθ, hO, hMθ⟩ : ∃ θ : ℝ, 0 < θ ∧ IsOsBond d p (S r x) s θ ∧
        max 1 r ^ ((d : ℝ) / 2) * θ = C := by
      rcases le_or_gt r 1 with h1 | h1
      · exact ⟨C, hC, hsmall r hr0 h1 x, by rw [max_eq_left h1, Real.one_rpow, one_mul]⟩
      · refine ⟨C / r ^ ((d : ℝ) / 2), by positivity, hlarge r h1.le x, ?_⟩
        rw [max_eq_right h1.le]
        have : (0 : ℝ) < r ^ ((d : ℝ) / 2) := Real.rpow_pos_of_pos hr0 _
        field_simp
    have hO' : IsOsBond d p (fun ω => |S r x ω|) s θ := by
      have : (fun ω => |S r x ω|) = S r x := funext fun ω => abs_of_nonneg (hS0 r x ω)
      rw [this]
      exact hO
    have hSmr : Measurable (S r x) :=
      (hSm x).comp (measurable_const.prodMk measurable_id)
    have hmom := mom_le_of_isOsBond hs hθ hq1 hSmr hO'
    have hga : ∀ ω, g r ω ^ a = ENNReal.ofReal ((max 1 r ^ ((d : ℝ) / 2)) ^ q) *
        ENNReal.ofReal (|S r x ω| ^ q) := by
      intro ω
      simp only [hg]
      rw [ENNReal.ofReal_rpow_of_nonneg (by have := hMpos r; positivity) (by linarith),
        ← ENNReal.ofReal_mul (by have := Real.rpow_nonneg hM ((d : ℝ) / 2); positivity)]
      congr 1
      have hMd : max 1 r ^ (d : ℝ) = (max 1 r ^ ((d : ℝ) / 2)) ^ (2 : ℕ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hM]
        congr 1
        push_cast
        ring
      rw [hMd, abs_of_nonneg (hS0 r x ω), ← mul_pow, ← Real.rpow_natCast,
        ← Real.rpow_mul (mul_nonneg (Real.rpow_nonneg hM _) (hS0 r x ω)),
        Real.mul_rpow (Real.rpow_nonneg hM _) (hS0 r x ω)]
      rw [show ((2 : ℕ) : ℝ) * a = q by rw [ha]; push_cast; ring]
    simp only [hga]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc ENNReal.ofReal ((max 1 r ^ ((d : ℝ) / 2)) ^ q) * mom p (S r x) q
        ≤ ENNReal.ofReal ((max 1 r ^ ((d : ℝ) / 2)) ^ q) *
            ENNReal.ofReal ((2 * θ * (1 / s) ^ (1 / s) * q ^ (1 / s)) ^ q) := by
          gcongr
      _ = ENNReal.ofReal K := by
          rw [← ENNReal.ofReal_mul (by have := Real.rpow_nonneg hM ((d : ℝ) / 2); positivity),
            ← Real.mul_rpow (Real.rpow_nonneg hM _) (by positivity), hK]
          congr 2
          rw [← hMθ, hσ]
          ring
  -- Tonelli and the mass of the weight
  have hswap : ∫⁻ ω, ∫⁻ r in Ioc 0 T, g r ω ^ a * w r ∂volume ∂latticeBondLaw d p =
      ∫⁻ r in Ioc 0 T, ∫⁻ ω, g r ω ^ a * w r ∂latticeBondLaw d p := by
    refine lintegral_lintegral_swap ?_
    exact (((hgm.comp measurable_swap).pow_const a).mul (hwm.comp measurable_snd)).aemeasurable
  have hinner : ∫⁻ r in Ioc 0 T, ∫⁻ ω, g r ω ^ a * w r ∂latticeBondLaw d p ≤
      ENNReal.ofReal K * W := by
    calc ∫⁻ r in Ioc 0 T, ∫⁻ ω, g r ω ^ a * w r ∂latticeBondLaw d p
        ≤ ∫⁻ r in Ioc 0 T, ENNReal.ofReal K * w r := by
          refine setLIntegral_mono' measurableSet_Ioc fun r hr => ?_
          rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
          exact mul_le_mul_left (hmomr r hr) _
      _ = ENNReal.ofReal K * ∫⁻ r in Ioc 0 T, w r := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal K * W := mul_le_mul_right hwint _
  calc ∫⁻ ω, (∫⁻ r in Ioc 0 T, ENNReal.ofReal (r * S r x ω ^ 2)) ^ a ∂latticeBondLaw d p
      ≤ ∫⁻ ω, (∫⁻ r in Ioc 0 T, g r ω ^ a * w r) * W ^ (a - 1) ∂latticeBondLaw d p :=
        lintegral_mono hpt
    _ = (∫⁻ ω, ∫⁻ r in Ioc 0 T, g r ω ^ a * w r ∂volume ∂latticeBondLaw d p) * W ^ (a - 1) :=
        lintegral_mul_const' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith) hWt)
    _ ≤ ENNReal.ofReal K * W * W ^ (a - 1) := by
        rw [hswap]
        exact mul_le_mul_left hinner _
    _ = ENNReal.ofReal K * W ^ a := by
        rw [mul_assoc]
        congr 1
        conv_rhs => rw [show a = 1 + (a - 1) by ring, ENNReal.rpow_add _ _ hW0 hWt,
          ENNReal.rpow_one]

theorem boxOsc_nonneg (u : Vertex d → Configuration d → ℝ) (m : ℕ) (q : ℝ)
    (ω : Configuration d) : 0 ≤ boxOsc u m q ω :=
  div_nonneg (Finset.sum_nonneg fun _ _ => by positivity) (by positivity)

/-- **The multiscale Poincaré inequality (2.26) in cube form at `R = 3^m`** in `ℤᵈ`, for `q ≥ 2`
with the constant `A₀ q^{3/2}` of Proposition 2.19, `S r x` standing for `|Φ_{r²} * ∇u(x)|`. -/
def PoincareCube (p : unitInterval) (u : Vertex d → Configuration d → ℝ)
    (S : ℝ → Vertex d → Configuration d → ℝ) (A₀ : ℝ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∀ q : ℝ, 2 ≤ q → ∀ᵐ ω ∂latticeBondLaw d p,
    ENNReal.ofReal (boxOsc u m q ω) ≤
      ENNReal.ofReal ((A₀ * q ^ (3 / 2 : ℝ)) ^ q) *
        ∑' x : Vertex d, ENNReal.ofReal
          (Real.exp (-‖latticeEuclideanEmbedding x‖ / (2 * 3 ^ m)) / (3 ^ m) ^ d) *
          (∫⁻ r in Ioc 0 (2 * 3 ^ m), ENNReal.ofReal (r * S r x ω ^ 2)) ^ (q / 2)

/-- The constant of `lintegral_boxOsc_le_of_poincare_three`. -/
noncomputable def poincareStepConstThree (d : ℕ) (A₀ C s : ℝ) : ℝ :=
  4 * (2 * (1 + 2 * d)) ^ d * A₀ * C * (1 / s) ^ (1 / s) * 2 ^ (3 / 2 + 1 / s)

/-- **Dario, Theorem 2, Step 1, in dimension `d ≥ 3`, moment form**: from the multiscale Poincaré
inequality (`PoincareCube`), Proposition 3.1 (`S r x ≤ O_s(C r^{-d/2})` for `r ≥ 1`) and the
Lipschitz bound (`S r x ≤ O_s(C)` for `r ≤ 1`), (5.5) with box oscillations bounded uniformly in
the scale and `k = 3/2 + 1/s`. -/
theorem lintegral_boxOsc_le_of_poincare_three (hd : 3 ≤ d) {u : Vertex d → Configuration d → ℝ}
    {S : ℝ → Vertex d → Configuration d → ℝ} {A₀ C s : ℝ} (hA₀ : 0 < A₀) (hC : 0 < C)
    (hs : 0 < s) (hu : ∀ z, Measurable (u z))
    (hSm : ∀ x, Measurable fun rω : ℝ × Configuration d => S rω.1 x rω.2)
    (hS0 : ∀ r x ω, 0 ≤ S r x ω) (hmsp : PoincareCube p u S A₀)
    (hlarge : ∀ r : ℝ, 1 ≤ r → ∀ x, IsOsBond d p (S r x) s (C / r ^ ((d : ℝ) / 2)))
    (hsmall : ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ x, IsOsBond d p (S r x) s C)
    {m : ℕ} (hm : 1 ≤ m) {q : ℝ} (hq : 1 ≤ q) :
    ∫⁻ ω, ENNReal.ofReal (boxOsc u m q ω) ∂latticeBondLaw d p ≤
      ENNReal.ofReal ((poincareStepConstThree d A₀ C s * q ^ (3 / 2 + 1 / s)) ^ q) := by
  set k : ℝ := 3 / 2 + 1 / s with hk
  have hk0 : 0 ≤ k := by positivity
  set σ := (1 / s) ^ (1 / s) with hσ
  have hσ0 : 0 < σ := by positivity
  set Wd : ℝ := (2 * (1 + 2 * d)) ^ d with hWd
  have hWd1 : 1 ≤ Wd := one_le_pow₀ (by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith)
  set A₁ : ℝ := 4 * Wd * A₀ * C * σ with hA₁
  have hA₁0 : 0 < A₁ := by positivity
  -- the case `q ≥ 2`
  have h2 : ∀ q : ℝ, 2 ≤ q → ∫⁻ ω, ENNReal.ofReal (boxOsc u m q ω) ∂latticeBondLaw d p ≤
      ENNReal.ofReal ((A₁ * q ^ k) ^ q) := by
    intro q hq2
    have hq0 : 0 < q := by linarith
    set T : ℝ := 2 * 3 ^ m with hT
    have hT1 : 1 ≤ T := by
      have : (1 : ℝ) ≤ 3 ^ m := one_le_pow₀ (by norm_num)
      linarith
    set ψ : Vertex d → ℝ≥0∞ := fun x => ENNReal.ofReal
      (Real.exp (-‖latticeEuclideanEmbedding x‖ / (2 * 3 ^ m)) / (3 ^ m) ^ d) with hψ
    set I : Vertex d → Configuration d → ℝ≥0∞ := fun x ω =>
      ∫⁻ r in Ioc 0 T, ENNReal.ofReal (r * S r x ω ^ 2) with hI
    have hIm : ∀ x, Measurable (I x) := fun x =>
      Measurable.lintegral_prod_left' (μ := volume.restrict (Ioc 0 T))
        ((measurable_fst.mul ((hSm x).pow_const 2)).ennreal_ofReal)
    set K := (2 * C * σ * q ^ (1 / s)) ^ q with hK
    have hmomx : ∀ x, ∫⁻ ω, I x ω ^ (q / 2) ∂latticeBondLaw d p ≤
        ENNReal.ofReal K * ENNReal.ofReal (3 / 2) ^ (q / 2) :=
      fun x => lintegral_rpow_heatSquare_le_three hd hC hs hSm hS0 hlarge hsmall hT1 hq2 x
    have hW : ENNReal.ofReal (3 / 2) ^ (q / 2) ≤ ENNReal.ofReal (2 ^ q) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by linarith)]
      refine ENNReal.ofReal_le_ofReal ?_
      calc (3 / 2 : ℝ) ^ (q / 2) ≤ (3 / 2) ^ q :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ ≤ 2 ^ q := Real.rpow_le_rpow (by norm_num) (by norm_num) (by linarith)
    calc ∫⁻ ω, ENNReal.ofReal (boxOsc u m q ω) ∂latticeBondLaw d p
        ≤ ∫⁻ ω, ENNReal.ofReal ((A₀ * q ^ (3 / 2 : ℝ)) ^ q) *
            ∑' x, ψ x * I x ω ^ (q / 2) ∂latticeBondLaw d p :=
          lintegral_mono_ae (hmsp m hm q hq2)
      _ = ENNReal.ofReal ((A₀ * q ^ (3 / 2 : ℝ)) ^ q) *
            ∑' x, ψ x * ∫⁻ ω, I x ω ^ (q / 2) ∂latticeBondLaw d p := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_tsum fun x => (((hIm x).pow_const _).const_mul _).aemeasurable]
          congr 1
          exact tsum_congr fun x => lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal ((A₀ * q ^ (3 / 2 : ℝ)) ^ q) *
            ∑' x, ψ x * (ENNReal.ofReal K * ENNReal.ofReal (2 ^ q)) := by
          refine mul_le_mul_right (ENNReal.tsum_le_tsum fun x => mul_le_mul_right ?_ _) _
          exact (hmomx x).trans (mul_le_mul_right hW _)
      _ = ENNReal.ofReal ((A₀ * q ^ (3 / 2 : ℝ)) ^ q) *
            ((∑' x, ψ x) * (ENNReal.ofReal K * ENNReal.ofReal (2 ^ q))) := by
          rw [ENNReal.tsum_mul_right]
      _ ≤ ENNReal.ofReal ((A₀ * q ^ (3 / 2 : ℝ)) ^ q) *
            (ENNReal.ofReal Wd * (ENNReal.ofReal K * ENNReal.ofReal (2 ^ q))) :=
          mul_le_mul_right (mul_le_mul_left (tsum_poincareWeight_le m) _) _
      _ = ENNReal.ofReal ((A₀ * q ^ (3 / 2 : ℝ)) ^ q * (Wd * (K * 2 ^ q))) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal ((A₁ * q ^ k) ^ q) := by
          refine ENNReal.ofReal_le_ofReal ?_
          set B := 4 * A₀ * C * σ * q ^ k with hB
          have hqk : q ^ k = q ^ (3 / 2 : ℝ) * q ^ (1 / s) := by rw [hk, Real.rpow_add hq0]
          have hq32 : 0 ≤ q ^ (3 / 2 : ℝ) := Real.rpow_nonneg hq0.le _
          have hX1 : 0 ≤ A₀ * q ^ (3 / 2 : ℝ) := mul_nonneg hA₀.le hq32
          have hX2 : 0 ≤ 2 * C * σ * q ^ (1 / s) := by positivity
          have hB0 : 0 ≤ B := by rw [hB]; positivity
          have hBeq : B = (A₀ * q ^ (3 / 2 : ℝ)) * (2 * C * σ * q ^ (1 / s)) * 2 := by
            rw [hB, hqk]
            ring
          have hBq : B ^ q = (A₀ * q ^ (3 / 2 : ℝ)) ^ q * K * 2 ^ q := by
            rw [hBeq, Real.mul_rpow (mul_nonneg hX1 hX2) (by norm_num), Real.mul_rpow hX1 hX2, hK]
          have hL : (A₀ * q ^ (3 / 2 : ℝ)) ^ q * (Wd * (K * 2 ^ q)) = Wd * B ^ q := by
            rw [hBq]
            ring
          have hR : (A₁ * q ^ k) ^ q = Wd ^ q * B ^ q := by
            rw [← Real.mul_rpow (by positivity) hB0]
            congr 1
            rw [hA₁, hB]
            ring
          rw [hL, hR]
          have hWq : Wd ≤ Wd ^ q := by
            simpa using Real.rpow_le_rpow_of_exponent_le hWd1 (by linarith : 1 ≤ q)
          exact mul_le_mul_of_nonneg_right hWq (by positivity)
  have hfin : (A₁ * 2 ^ k) * q ^ k = poincareStepConstThree d A₀ C s * q ^ k := by
    rw [poincareStepConstThree, hA₁, hσ, hk, hWd]
  rcases le_or_gt 2 q with hq2 | hq2
  · refine (h2 q hq2).trans (ENNReal.ofReal_le_ofReal ?_)
    refine Real.rpow_le_rpow (by positivity) ?_ (by linarith)
    have h2k : (1 : ℝ) ≤ 2 ^ k := Real.one_le_rpow (by norm_num) hk0
    have : 0 ≤ A₁ * q ^ k := by positivity
    rw [← hfin]
    calc A₁ * q ^ k = A₁ * q ^ k * 1 := by ring
      _ ≤ A₁ * q ^ k * 2 ^ k := mul_le_mul_of_nonneg_left h2k this
      _ = A₁ * 2 ^ k * q ^ k := by ring
  · have hq0 : 0 < q := by linarith
    have hpm : ∀ ω, boxOsc u m q ω ≤ boxOsc u m 2 ω ^ (q / 2) := by
      intro ω
      have h := abs_sum_div_rpow_le (boxAt 0 m) (fun z => |u z ω - boxAvg u 0 m ω| ^ q)
        (card_boxAt_real 0 m) (by positivity)
        (show 1 ≤ 2 / q by rw [le_div_iff₀ hq0]; linarith)
      beta_reduce at h
      have hpt : ∀ z, |(|u z ω - boxAvg u 0 m ω| ^ q)| ^ (2 / q) =
          |u z ω - boxAvg u 0 m ω| ^ (2 : ℝ) := by
        intro z
        rw [abs_of_nonneg (by positivity), ← Real.rpow_mul (abs_nonneg _),
          mul_div_cancel₀ _ hq0.ne']
      have h' : boxOsc u m q ω ^ (2 / q) ≤ boxOsc u m 2 ω := by
        have e1 : |(∑ z ∈ boxAt 0 m, |u z ω - boxAvg u 0 m ω| ^ q) / (3 ^ m) ^ d| =
            boxOsc u m q ω := abs_of_nonneg (boxOsc_nonneg u m q ω)
        rw [e1] at h
        refine h.trans_eq ?_
        unfold boxOsc
        congr 1
        exact Finset.sum_congr rfl fun z _ => hpt z
      calc boxOsc u m q ω = (boxOsc u m q ω ^ (2 / q)) ^ (q / 2) := by
            rw [← Real.rpow_mul (boxOsc_nonneg u m q ω), show 2 / q * (q / 2) = 1 by
              field_simp, Real.rpow_one]
        _ ≤ boxOsc u m 2 ω ^ (q / 2) :=
            Real.rpow_le_rpow (by have := boxOsc_nonneg u m q ω; positivity) h' (by linarith)
    calc ∫⁻ ω, ENNReal.ofReal (boxOsc u m q ω) ∂latticeBondLaw d p
        ≤ ∫⁻ ω, ENNReal.ofReal (boxOsc u m 2 ω) ^ (q / 2) ∂latticeBondLaw d p := by
          refine lintegral_mono fun ω => ?_
          rw [ENNReal.ofReal_rpow_of_nonneg (boxOsc_nonneg u m 2 ω) (by linarith)]
          exact ENNReal.ofReal_le_ofReal (hpm ω)
      _ ≤ (∫⁻ ω, ENNReal.ofReal (boxOsc u m 2 ω) ∂latticeBondLaw d p) ^ (q / 2) :=
          lintegral_rpow_le_rpow_lintegral (measurable_boxOsc hu m 2).ennreal_ofReal.aemeasurable
            (by linarith) (by linarith)
      _ ≤ (ENNReal.ofReal ((A₁ * 2 ^ k) ^ (2 : ℝ))) ^ (q / 2) :=
          ENNReal.rpow_le_rpow (h2 2 le_rfl) (by linarith)
      _ = ENNReal.ofReal ((A₁ * 2 ^ k) ^ q) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by linarith : (0 : ℝ) ≤ q / 2),
            ← Real.rpow_mul (by positivity)]
          congr 2
          ring
      _ ≤ ENNReal.ofReal ((poincareStepConstThree d A₀ C s * q ^ k) ^ q) := by
          refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (by positivity) ?_ hq0.le)
          rw [← hfin]
          have hqk : 1 ≤ q ^ k := Real.one_le_rpow hq hk0
          have : 0 ≤ A₁ * 2 ^ k := by positivity
          calc A₁ * 2 ^ k = A₁ * 2 ^ k * 1 := by ring
            _ ≤ A₁ * 2 ^ k * q ^ k := mul_le_mul_of_nonneg_left hqk this

/-- **The inputs of Step 1 of the proof of Theorem 2 in dimension `d ≥ 3`** for the coarsened
correctors: smoothed gradients `S i r x` (standing for `|Φ_{r²} * ∇[χ_{e_i}]_𝒫(x)|`) satisfying
the multiscale Poincaré inequality (Proposition 2.19 in cube form), Proposition 3.1
(`S i r x ≤ O_s(C r^{-d/2})` for `r ≥ 1`) and the Lipschitz bound (2.22) for `r ≤ 1`. They are
established from Proposition 3.1 in `darioOptimalCorrectorThree_of_prop31`. -/
def DarioPoincareInputsThree : Prop :=
  ∀ (d : ℕ) [NeZero d], 3 ≤ d → ∀ p : unitInterval, criticalProbability d < (p : ℝ) →
    (p : ℝ) < 1 → ∀ (G : Set (Configuration d)) (hG : MeasurableSet G)
      (hGv : G ⊆ correctorValidEvent d), (∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) →
      ∃ (S : Fin d → ℝ → Vertex d → Configuration d → ℝ) (A₀ C s : ℝ), 0 < A₀ ∧ 0 < C ∧
        0 < s ∧ (∀ i x, Measurable fun rω : ℝ × Configuration d => S i rω.1 x rω.2) ∧
        (∀ i r x ω, 0 ≤ S i r x ω) ∧
        (∀ i, PoincareCube p (coarseField hG hGv i 0) (S i) A₀) ∧
        (∀ i (r : ℝ), 1 ≤ r → ∀ x, IsOsBond d p (S i r x) s (C / r ^ ((d : ℝ) / 2))) ∧
        (∀ i (r : ℝ), 0 < r → r ≤ 1 → ∀ x, IsOsBond d p (S i r x) s C)

/-- **Dario's Theorem 1 in dimension `d ≥ 3`** (`DarioOptimalCorrectorThree`) from the inputs of
Step 1 of the proof of Theorem 2: the multiscale Poincaré inequality in cube form, Proposition 3.1
and the Lipschitz bound of the smoothed gradients. -/
theorem darioOptimalCorrectorThree_of_poincareInputs (h : DarioPoincareInputsThree) :
    DarioOptimalCorrectorThree := by
  refine darioOptimalCorrectorThree_of_baseTheorem fun d _ hd3 p hpc hp1 G hG hGv hGae => ?_
  obtain ⟨S, A₀, C, s, hA₀, hC, hs, hSm, hS0, hmsp, h31, hlip⟩ :=
    h d hd3 p hpc hp1 G hG hGv hGae
  have hP0 : 0 ≤ poincareStepConstThree d A₀ C s := by
    unfold poincareStepConstThree
    positivity
  refine ⟨poincareStepConstThree d A₀ C s, 3 / 2 + 1 / s, hP0, fun i m hm q hq => ?_⟩
  rw [mul_zero, Real.rpow_zero, mul_one]
  exact lintegral_boxOsc_le_of_poincare_three hd3 hA₀ hC hs
    (fun z => measurable_coarseField hG hGv i 0 z) (hSm i) (hS0 i) (hmsp i) (h31 i) (hlip i) hm hq

end Rigidity.Corrector.GeneralDim
