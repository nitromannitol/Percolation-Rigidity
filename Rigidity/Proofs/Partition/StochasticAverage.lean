import LatticeProb.Prob.StochasticO.Sums

/-!
# Sums of stretched exponential variables with exponent at most one

Armstrong and Dario, Section 1, recall (citing Armstrong, Kuusi and Mourrat, Lemma 2.3) that
averages of variables bounded by `𝒪_s(1)` are bounded by `𝒪_s(C)` for every `s > 0`. For
`s ≥ 1` this is `LatticeProb.osBound_sum`. For `0 < s ≤ 1` the function `y ↦ exp(y^s / 2)` is not
convex near `0`, but `y ↦ exp((y + b)^s / 2)` is convex on `[0, ∞)` once `b^s ≥ 2 (1 - s) / s`, and
Jensen's inequality applies to it.
-/

namespace Rigidity.Percolation

open MeasureTheory LatticeProb

/-- For `0 < s ≤ 1` and `b^s ≥ 2 (1 - s) / s`, the function `y ↦ exp ((y + b)^s / 2)` is convex
on `[0, ∞)`. -/
theorem convexOn_exp_add_rpow {s b : ℝ} (hs : 0 < s) (hb : 0 < b)
    (hbs : 2 * (1 - s) / s ≤ b ^ s) :
    ConvexOn ℝ (Set.Ici 0) (fun y : ℝ => Real.exp ((y + b) ^ s / 2)) := by
  have hderiv : ∀ y : ℝ, 0 ≤ y → HasDerivAt (fun y : ℝ => Real.exp ((y + b) ^ s / 2))
      (Real.exp ((y + b) ^ s / 2) * (s * (y + b) ^ (s - 1) / 2)) y := by
    intro y hy
    have hyb : 0 < y + b := by linarith
    have h1 : HasDerivAt (fun y : ℝ => y + b) 1 y := (hasDerivAt_id y).add_const b
    have h3 := ((h1.rpow_const (p := s) (Or.inl hyb.ne')).div_const 2).exp
    convert h3 using 1
    ring
  refine MonotoneOn.convexOn_of_deriv (convex_Ici 0) ?_ ?_ ?_
  · intro y hy
    exact (hderiv y hy).continuousAt.continuousWithinAt
  · intro y hy
    rw [interior_Ici] at hy
    exact (hderiv y (le_of_lt hy)).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]
    intro y hy z hz hyz
    rw [(hderiv y (le_of_lt hy)).deriv, (hderiv z (le_of_lt hz)).deriv]
    have hy0 : 0 < y := hy
    have hu : 0 < y + b := by linarith
    have hv : 0 < z + b := by linarith
    have huv : y + b ≤ z + b := by linarith
    have hL : 0 ≤ Real.log (z + b) - Real.log (y + b) :=
      sub_nonneg.2 (Real.log_le_log hu huv)
    have hvs : (z + b) ^ s =
        (y + b) ^ s * Real.exp (s * (Real.log (z + b) - Real.log (y + b))) := by
      rw [Real.rpow_def_of_pos hv, Real.rpow_def_of_pos hu, ← Real.exp_add]
      congr 1
      ring
    have hexp := Real.add_one_le_exp (s * (Real.log (z + b) - Real.log (y + b)))
    have hus : 2 * (1 - s) / s ≤ (y + b) ^ s :=
      hbs.trans (Real.rpow_le_rpow hb.le (by linarith) hs.le)
    have hus' : 2 * (1 - s) ≤ (y + b) ^ s * s := (div_le_iff₀ hs).1 hus
    have hupos : 0 ≤ (y + b) ^ s := Real.rpow_nonneg hu.le s
    have hgrow : (y + b) ^ s * (s * (Real.log (z + b) - Real.log (y + b)) + 1) ≤
        (z + b) ^ s := by
      rw [hvs]
      exact mul_le_mul_of_nonneg_left hexp hupos
    have key : (1 - s) * (Real.log (z + b) - Real.log (y + b)) ≤
        ((z + b) ^ s - (y + b) ^ s) / 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hus' hL]
    have hmain : Real.exp ((y + b) ^ s / 2) * (y + b) ^ (s - 1) ≤
        Real.exp ((z + b) ^ s / 2) * (z + b) ^ (s - 1) := by
      rw [Real.rpow_def_of_pos hu (s - 1), Real.rpow_def_of_pos hv (s - 1), ← Real.exp_add,
        ← Real.exp_add]
      apply Real.exp_le_exp.2
      linarith
    calc Real.exp ((y + b) ^ s / 2) * (s * (y + b) ^ (s - 1) / 2)
        = s / 2 * (Real.exp ((y + b) ^ s / 2) * (y + b) ^ (s - 1)) := by ring
      _ ≤ s / 2 * (Real.exp ((z + b) ^ s / 2) * (z + b) ^ (s - 1)) :=
          mul_le_mul_of_nonneg_left hmain (by positivity)
      _ = Real.exp ((z + b) ^ s / 2) * (s * (z + b) ^ (s - 1) / 2) := by ring

/-- **Markov's inequality for a stretched exponential moment.** If
`E[exp(Y^s / 2)] ≤ exp A` with `A ≥ 0`, then `Y ≤ 𝒪_s((2A + 2)^{1/s})`. -/
theorem osBound_of_lintegral_exp_half_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {s A : ℝ} {Y : Ω → ℝ} (hs : 0 < s) (hA : 0 ≤ A) (hm : Measurable Y) (hn : ∀ ω, 0 ≤ Y ω)
    (he : ∫⁻ ω, ENNReal.ofReal (Real.exp (Y ω ^ s / 2)) ∂P ≤ ENNReal.ofReal (Real.exp A)) :
    OsBound P s ((2 * A + 2) ^ s⁻¹) Y := by
  intro t ht
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have htp : 1 ≤ t ^ s := Real.one_le_rpow ht hs.le
  have hC : 0 ≤ (2 * A + 2) ^ s⁻¹ := Real.rpow_nonneg (by linarith) _
  have hmark := meas_le_lintegral₀ (μ := P)
    (f := fun ω => ENNReal.ofReal (Real.exp (-((A + 1) * t ^ s))) *
      ENNReal.ofReal (Real.exp (Y ω ^ s / 2)))
    (by fun_prop) (s := {ω | t * (2 * A + 2) ^ s⁻¹ < max (Y ω) 0}) (by
      intro ω hω
      change t * (2 * A + 2) ^ s⁻¹ < max (Y ω) 0 at hω
      rw [max_eq_left (hn ω)] at hω
      have hp := Real.rpow_le_rpow (mul_nonneg ht0 hC) hω.le hs.le
      rw [Real.mul_rpow ht0 hC, Real.rpow_inv_rpow (by linarith) hs.ne'] at hp
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal
        (Real.one_le_exp (by linarith : 0 ≤ -((A + 1) * t ^ s) + Y ω ^ s / 2)))
  calc
    _ ≤ _ := hmark
    _ = ENNReal.ofReal (Real.exp (-((A + 1) * t ^ s))) *
        ∫⁻ ω, ENNReal.ofReal (Real.exp (Y ω ^ s / 2)) ∂P :=
      lintegral_const_mul _ (by fun_prop)
    _ ≤ ENNReal.ofReal (Real.exp (-((A + 1) * t ^ s))) * ENNReal.ofReal (Real.exp A) :=
      mul_le_mul' le_rfl he
    _ ≤ ENNReal.ofReal (Real.exp (-(t ^ s))) := by
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
        (by nlinarith [mul_nonneg hA (sub_nonneg.2 htp)]))

/-- Powers: if `0 ≤ X ≤ 𝒪_s(θ)`, then `X^n ≤ 𝒪_{s/n}(θ^n)`. -/
theorem osBound_pow_of_nonneg {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {s θ : ℝ}
    {X : Ω → ℝ} (hX : OsBound P s θ X) (hX0 : ∀ ω, 0 ≤ X ω) {n : ℕ} (hn : 0 < n) :
    OsBound P (s / n) (θ ^ n) (fun ω => X ω ^ n) := by
  intro t ht
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hu1 : 1 ≤ t ^ ((n : ℝ)⁻¹) := Real.one_le_rpow ht (by positivity)
  have hun : (t ^ ((n : ℝ)⁻¹)) ^ n = t := Real.rpow_inv_natCast_pow ht0 hn.ne'
  refine le_trans (measure_mono ?_) ((hX _ hu1).trans ?_)
  · intro ω hω
    change t * θ ^ n < max (X ω ^ n) 0 at hω
    change t ^ ((n : ℝ)⁻¹) * θ < max (X ω) 0
    rw [max_eq_left (pow_nonneg (hX0 ω) n)] at hω
    rw [max_eq_left (hX0 ω)]
    by_contra hle
    have h := pow_le_pow_left₀ (hX0 ω) (not_lt.1 hle) n
    rw [mul_pow, hun] at h
    linarith
  · apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.2
    rw [← Real.rpow_mul ht0, div_eq_inv_mul]

/-- **Finite sums of `𝒪_s` variables for `0 < s ≤ 1`.** There is `C(s)` such that for every
probability measure and finite family with positive scales `θ i`, `X i ≤ 𝒪_s(θ i)` for all `i`
implies `∑ i, X i ≤ 𝒪_s(C ∑ i, θ i)`, independently of the number of summands. -/
theorem osBound_sum_of_le_one {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    ∃ C > 0, ∀ {Ω : Type*} [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] (ι : Type*) [Fintype ι]
      (X : ι → Ω → ℝ) (θ : ι → ℝ), (∀ i, Measurable (X i)) →
      (∀ i, 0 < θ i) → (∀ i, OsBound P s (θ i) (X i)) →
      OsBound P s (C * ∑ i, θ i) (fun ω => ∑ i, X i ω) := by
  set b : ℝ := (2 / s) ^ s⁻¹ with hbdef
  have hb : 0 < b := Real.rpow_pos_of_pos (by positivity) _
  have hbs' : b ^ s = 2 / s := Real.rpow_inv_rpow (by positivity) hs.ne'
  have hbs : 2 * (1 - s) / s ≤ b ^ s := by
    rw [hbs']
    exact div_le_div_of_nonneg_right (by linarith) hs.le
  set A : ℝ := b ^ s / 2 + 2 with hAdef
  have hA : 0 ≤ A := by positivity
  refine ⟨(2 * A + 2) ^ s⁻¹, Real.rpow_pos_of_pos (by linarith) _, ?_⟩
  intro Ω _ P _ ι _ X θ hm hθ hX
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · intro t _
    simp
  let W := ∑ i, θ i
  have hWpos : 0 < W := Finset.sum_pos (fun i _ => hθ i) Finset.univ_nonempty
  have hW0 : W ≠ 0 := hWpos.ne'
  let w (i : ι) := θ i / W
  let Z (i : ι) (ω : Ω) := max (X i ω) 0 / θ i
  let Y (ω : Ω) := ∑ i, w i * Z i ω
  have hw (i : ι) : 0 ≤ w i := div_nonneg (hθ i).le hWpos.le
  have hw_sum : ∑ i, w i = 1 := by
    dsimp [w]
    rw [← Finset.sum_div, div_self hW0]
  have hZ (i : ι) (ω : Ω) : 0 ≤ Z i ω := div_nonneg (le_max_right _ _) (hθ i).le
  have hY (ω : Ω) : 0 ≤ Y ω := Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (hZ i ω))
  have hmoment (i : ι) :
      ∫⁻ ω, ENNReal.ofReal (Real.exp (Z i ω ^ s / 2)) ∂P ≤
        ENNReal.ofReal (Real.exp 2) :=
    ((hX i).normalized_rpow hs (hθ i)).lintegral_exp_half
      (by fun_prop) (fun ω => Real.rpow_nonneg (hZ i ω) _)
  have hshift (i : ι) :
      ∫⁻ ω, ENNReal.ofReal (Real.exp ((Z i ω + b) ^ s / 2)) ∂P ≤
        ENNReal.ofReal (Real.exp A) := by
    calc ∫⁻ ω, ENNReal.ofReal (Real.exp ((Z i ω + b) ^ s / 2)) ∂P
        ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (b ^ s / 2)) *
            ENNReal.ofReal (Real.exp (Z i ω ^ s / 2)) ∂P := by
          apply lintegral_mono
          intro ω
          dsimp only
          rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
          apply ENNReal.ofReal_le_ofReal
          apply Real.exp_le_exp.2
          have := Real.rpow_add_le_add_rpow (hZ i ω) hb.le hs.le hs1
          linarith
      _ = ENNReal.ofReal (Real.exp (b ^ s / 2)) *
            ∫⁻ ω, ENNReal.ofReal (Real.exp (Z i ω ^ s / 2)) ∂P :=
          lintegral_const_mul _ (by fun_prop)
      _ ≤ ENNReal.ofReal (Real.exp (b ^ s / 2)) * ENNReal.ofReal (Real.exp 2) :=
          mul_le_mul' le_rfl (hmoment i)
      _ = ENNReal.ofReal (Real.exp A) := by
          rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
  have hconv := convexOn_exp_add_rpow hs hb hbs
  have hmomentY : ∫⁻ ω, ENNReal.ofReal (Real.exp (Y ω ^ s / 2)) ∂P ≤
      ENNReal.ofReal (Real.exp A) := by
    calc
      _ ≤ ∫⁻ ω, ∑ i, ENNReal.ofReal (w i) *
          ENNReal.ofReal (Real.exp ((Z i ω + b) ^ s / 2)) ∂P := by
        apply lintegral_mono
        intro ω
        have hj := hconv.map_sum_le (t := Finset.univ) (fun i _ => hw i) hw_sum
          (fun i _ => hZ i ω)
        have hjreal : Real.exp ((Y ω + b) ^ s / 2) ≤
            ∑ i, w i * Real.exp ((Z i ω + b) ^ s / 2) := by
          simpa only [smul_eq_mul] using hj
        have hYb : Real.exp (Y ω ^ s / 2) ≤ Real.exp ((Y ω + b) ^ s / 2) := by
          apply Real.exp_le_exp.2
          have := Real.rpow_le_rpow (hY ω) (by linarith : Y ω ≤ Y ω + b) hs.le
          linarith
        calc
          _ ≤ ENNReal.ofReal (∑ i, w i * Real.exp ((Z i ω + b) ^ s / 2)) :=
            ENNReal.ofReal_le_ofReal (hYb.trans hjreal)
          _ = _ := by
            rw [ENNReal.ofReal_sum_of_nonneg
              (fun i _ => mul_nonneg (hw i) (Real.exp_nonneg _))]
            apply Finset.sum_congr rfl
            intro i _
            exact ENNReal.ofReal_mul (hw i)
      _ = ∑ i, ENNReal.ofReal (w i) *
          ∫⁻ ω, ENNReal.ofReal (Real.exp ((Z i ω + b) ^ s / 2)) ∂P := by
        rw [lintegral_finsetSum _ (fun i _ => by fun_prop)]
        congr 1
        ext i
        exact lintegral_const_mul _ (by fun_prop)
      _ ≤ ∑ i, ENNReal.ofReal (w i) * ENNReal.ofReal (Real.exp A) :=
        Finset.sum_le_sum (fun i _ => mul_le_mul' le_rfl (hshift i))
      _ = ENNReal.ofReal (Real.exp A) := by
        rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => hw i), hw_sum]
        simp only [ENNReal.ofReal_one, one_mul]
  have hbound := osBound_of_lintegral_exp_half_le hs hA (by fun_prop) hY hmomentY
  intro t ht
  apply le_trans (measure_mono ?_) (hbound t ht)
  intro ω hωtail
  have hsum : ∑ i, X i ω ≤ W * Y ω := by
    dsimp [Y]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have heq : W * (w i * Z i ω) = max (X i ω) 0 := by
      dsimp [w, Z]
      field_simp [hW0, (hθ i).ne']
    rw [heq]
    exact le_max_left _ _
  change t * ((2 * A + 2) ^ s⁻¹ * W) < max (∑ i, X i ω) 0 at hωtail
  change t * (2 * A + 2) ^ s⁻¹ < max (Y ω) 0
  rw [max_eq_left (hY ω)]
  have hmax := max_le hsum (mul_nonneg hWpos.le (hY ω))
  exact (mul_lt_mul_iff_right₀ hWpos).mp (by
    simpa only [mul_assoc, mul_comm W] using hωtail.trans_le hmax)

end Rigidity.Percolation
