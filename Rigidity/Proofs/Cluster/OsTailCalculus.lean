import Rigidity.Proofs.Partition.StochasticAverage
import Rigidity.Proofs.S2.StochasticBoundExponentialMoment
import Rigidity.Proofs.S2.ScaleInputsFaithful
import Rigidity.Proofs.Partition.GeneralPartition

/-!
# Elementary calculus of the stochastic bounds `O_s`

For the tail form `LatticeProb.OsBound P s θ X` (`P[max(X, 0) > tθ] ≤ exp(-t^s)` for `t ≥ 1`):
indicators of events of small probability are `O_1` (`osBound_indicator`), sums
(`OsBound.add`), products of nonnegative variables (`OsBound.mul`, the rule
`O_s(a) · O_q(b) ≤ O_{sq/(s+q)}(C a b)` of Armstrong and Dario, (2.5)), maxima of finitely many
variables (`osBound_finset_sup'`), and variables with an exponential moment
(`osBound_of_exp_moment`).
A tail bound gives the exponential-moment form `IsOsBond` used in the statements of the inputs
(`isOsBond_of_osBound`).
-/

namespace Rigidity.Proofs.Cluster

open MeasureTheory LatticeProb
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

theorem exp_neg_le_half {t : ℝ} (ht : 1 ≤ t) : Real.exp (-t) ≤ 1 / 2 := by
  have h1 : Real.exp (-t) ≤ Real.exp (-1) := Real.exp_le_exp.2 (by linarith)
  have h2 : Real.exp (-1) < 1 / 2 := by
    rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]
    have := Real.exp_one_gt_d9
    norm_num at this ⊢
    linarith
  linarith

/-- Two tails `exp(-u)`, `u ≥ 2 t^r`, sum to at most `exp(-t^r)`. -/
theorem two_mul_exp_le {t r : ℝ} (ht : 1 ≤ t) (hr : 0 < r) :
    2 * Real.exp (-(2 * t ^ r)) ≤ Real.exp (-(t ^ r)) := by
  have htr : 1 ≤ t ^ r := Real.one_le_rpow ht hr.le
  have h := exp_neg_le_half htr
  have e : Real.exp (-(2 * t ^ r)) = Real.exp (-(t ^ r)) * Real.exp (-(t ^ r)) := by
    rw [← Real.exp_add]; ring_nf
  rw [e]
  have h0 := Real.exp_pos (-(t ^ r))
  nlinarith

/-- **Indicators of rare events are `O_1`.** -/
theorem osBound_indicator (P : Measure Ω) {E : Set Ω} {θ : ℝ} (hθ : 0 < θ)
    (hE : P E ≤ ENNReal.ofReal (Real.exp (-(1 / θ)))) :
    OsBound P 1 θ (E.indicator fun _ => (1 : ℝ)) := by
  intro t ht
  rw [Real.rpow_one]
  by_cases htθ : 1 ≤ t * θ
  · have : {ω | t * θ < max (E.indicator (fun _ => (1 : ℝ)) ω) 0} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      refine max_le ?_ (by positivity)
      exact (Set.indicator_le_self' (fun _ _ => zero_le_one) ω).trans htθ
    rw [this, measure_empty]
    exact zero_le
  · push Not at htθ
    refine (measure_mono fun ω hω => ?_).trans (hE.trans (ENNReal.ofReal_le_ofReal
      (Real.exp_le_exp.2 ?_)))
    · by_contra hωE
      simp only [Set.mem_setOf_eq, Set.indicator_of_notMem hωE, max_self] at hω
      exact absurd hω (not_lt.2 (by positivity))
    · rw [neg_le_neg_iff, le_div_iff₀ hθ]
      linarith

/-- **Sums.** -/
theorem OsBound.add {P : Measure Ω} {s a b : ℝ} {X Y : Ω → ℝ} (hs : 0 < s)
    (hX : OsBound P s a X) (hY : OsBound P s b Y) :
    OsBound P s (2 ^ (1 / s) * (a + b)) (fun ω => X ω + Y ω) := by
  intro t ht
  have h2 : (1 : ℝ) ≤ 2 ^ (1 / s) := Real.one_le_rpow (by norm_num) (by positivity)
  have ht' : 1 ≤ 2 ^ (1 / s) * t := by nlinarith
  have hpow : (2 ^ (1 / s) * t) ^ s = 2 * t ^ s := by
    rw [Real.mul_rpow (by positivity) (by linarith), ← Real.rpow_mul (by norm_num),
      one_div_mul_cancel hs.ne', Real.rpow_one]
  have hsub : {ω | t * (2 ^ (1 / s) * (a + b)) < max (X ω + Y ω) 0} ⊆
      {ω | 2 ^ (1 / s) * t * a < max (X ω) 0} ∪ {ω | 2 ^ (1 / s) * t * b < max (Y ω) 0} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, Set.mem_union] at hω ⊢
    by_contra hne
    push Not at hne
    have : max (X ω + Y ω) 0 ≤ max (X ω) 0 + max (Y ω) 0 :=
      max_le (add_le_add (le_max_left _ _) (le_max_left _ _)) (by positivity)
    nlinarith
  calc P {ω | t * (2 ^ (1 / s) * (a + b)) < max (X ω + Y ω) 0}
      ≤ P {ω | 2 ^ (1 / s) * t * a < max (X ω) 0} +
          P {ω | 2 ^ (1 / s) * t * b < max (Y ω) 0} := (measure_mono hsub).trans
        (measure_union_le _ _)
    _ ≤ ENNReal.ofReal (Real.exp (-((2 ^ (1 / s) * t) ^ s))) +
          ENNReal.ofReal (Real.exp (-((2 ^ (1 / s) * t) ^ s))) :=
        add_le_add (hX _ ht') (hY _ ht')
    _ ≤ ENNReal.ofReal (Real.exp (-(t ^ s))) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), hpow]
        apply ENNReal.ofReal_le_ofReal
        have := two_mul_exp_le ht hs
        linarith

/-- **Products** of nonnegative variables (Armstrong and Dario, (2.5)). -/
theorem OsBound.mul {P : Measure Ω} {s q a b : ℝ} {X Y : Ω → ℝ} (hs : 0 < s) (hq : 0 < q)
    (ha : 0 ≤ a) (hX0 : ∀ ω, 0 ≤ X ω) (hY0 : ∀ ω, 0 ≤ Y ω)
    (hX : OsBound P s a X) (hY : OsBound P q b Y) :
    OsBound P (s * q / (s + q)) (2 ^ ((s + q) / (s * q)) * (a * b)) (fun ω => X ω * Y ω) := by
  set r := s * q / (s + q) with hr
  have hr0 : 0 < r := by positivity
  have hrs : r / s + r / q = 1 := by rw [hr]; field_simp; ring
  intro t ht
  set u : ℝ := 2 ^ ((s + q) / (s * q)) * t with hu
  have h2 : (1 : ℝ) ≤ 2 ^ ((s + q) / (s * q)) := Real.one_le_rpow (by norm_num) (by positivity)
  have hu1 : 1 ≤ u := by rw [hu]; nlinarith
  have hu0 : 0 ≤ u := by linarith
  have hur : u ^ r = 2 * t ^ r := by
    rw [hu, Real.mul_rpow (by positivity) (by linarith), ← Real.rpow_mul (by norm_num)]
    rw [show (s + q) / (s * q) * r = 1 by rw [hr]; field_simp, Real.rpow_one]
  have hX1 : 1 ≤ u ^ (r / s) := Real.one_le_rpow hu1 (by positivity)
  have hY1 : 1 ≤ u ^ (r / q) := Real.one_le_rpow hu1 (by positivity)
  have hsplit : u ^ (r / s) * u ^ (r / q) = u := by
    rw [← Real.rpow_add (by linarith), hrs, Real.rpow_one]
  have hsub : {ω | t * (2 ^ ((s + q) / (s * q)) * (a * b)) < max (X ω * Y ω) 0} ⊆
      {ω | u ^ (r / s) * a < max (X ω) 0} ∪ {ω | u ^ (r / q) * b < max (Y ω) 0} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, Set.mem_union, max_eq_left (mul_nonneg (hX0 ω) (hY0 ω)),
      max_eq_left (hX0 ω), max_eq_left (hY0 ω)] at hω ⊢
    by_contra hne
    push Not at hne
    have h3 := mul_le_mul hne.1 hne.2 (hY0 ω) (by positivity)
    have e : u ^ (r / s) * a * (u ^ (r / q) * b) = t * (2 ^ ((s + q) / (s * q)) * (a * b)) := by
      calc u ^ (r / s) * a * (u ^ (r / q) * b) = (u ^ (r / s) * u ^ (r / q)) * (a * b) := by ring
        _ = _ := by rw [hsplit, hu]; ring
    linarith
  have hpX : (u ^ (r / s)) ^ s = u ^ r := by
    rw [← Real.rpow_mul hu0, div_mul_cancel₀ _ hs.ne']
  have hpY : (u ^ (r / q)) ^ q = u ^ r := by
    rw [← Real.rpow_mul hu0, div_mul_cancel₀ _ hq.ne']
  calc P {ω | t * (2 ^ ((s + q) / (s * q)) * (a * b)) < max (X ω * Y ω) 0}
      ≤ P {ω | u ^ (r / s) * a < max (X ω) 0} + P {ω | u ^ (r / q) * b < max (Y ω) 0} :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal (Real.exp (-((u ^ (r / s)) ^ s))) +
          ENNReal.ofReal (Real.exp (-((u ^ (r / q)) ^ q))) := add_le_add (hX _ hX1) (hY _ hY1)
    _ ≤ ENNReal.ofReal (Real.exp (-(t ^ r))) := by
        rw [hpX, hpY, hur, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have := two_mul_exp_le ht hr0
        linarith

/-- **Maxima of finitely many variables.** -/
theorem osBound_finset_sup' {ι : Type*} {P : Measure Ω} {s θ : ℝ} (hs : 0 < s) (hθ : 0 ≤ θ)
    (T : Finset ι) (hT : T.Nonempty) (X : ι → Ω → ℝ) (hX : ∀ i ∈ T, OsBound P s θ (X i)) :
    OsBound P s ((2 * (1 + Real.log T.card)) ^ (1 / s) * θ)
      (fun ω => T.sup' hT fun i => X i ω) := by
  intro t ht
  set L : ℝ := 2 * (1 + Real.log T.card) with hL
  have hcard : (1 : ℝ) ≤ T.card := by exact_mod_cast hT.card_pos
  have hlog : 0 ≤ Real.log T.card := Real.log_nonneg hcard
  have hL1 : 1 ≤ L := by rw [hL]; linarith
  have hL0 : 0 ≤ L := by linarith
  have h1 : (1 : ℝ) ≤ L ^ (1 / s) := Real.one_le_rpow hL1 (by positivity)
  have ht' : 1 ≤ L ^ (1 / s) * t := by nlinarith
  have hpow : (L ^ (1 / s) * t) ^ s = L * t ^ s := by
    rw [Real.mul_rpow (by positivity) (by linarith), ← Real.rpow_mul hL0,
      one_div_mul_cancel hs.ne', Real.rpow_one]
  have hsub : {ω | t * (L ^ (1 / s) * θ) < max (T.sup' hT fun i => X i ω) 0} ⊆
      ⋃ i ∈ T, {ω | L ^ (1 / s) * t * θ < max (X i ω) 0} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion] at hω ⊢
    by_contra hne
    push Not at hne
    have : max (T.sup' hT fun i => X i ω) 0 ≤ L ^ (1 / s) * t * θ := by
      refine max_le ((Finset.sup'_le_iff hT _).2 fun i hi => (le_max_left _ _).trans
        (hne i hi)) (by positivity)
    nlinarith
  have htr : 1 ≤ t ^ s := Real.one_le_rpow ht hs.le
  calc P {ω | t * (L ^ (1 / s) * θ) < max (T.sup' hT fun i => X i ω) 0}
      ≤ ∑ i ∈ T, P {ω | L ^ (1 / s) * t * θ < max (X i ω) 0} :=
        (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
    _ ≤ ∑ _i ∈ T, ENNReal.ofReal (Real.exp (-((L ^ (1 / s) * t) ^ s))) :=
        Finset.sum_le_sum fun i hi => hX i hi _ ht'
    _ = ENNReal.ofReal (T.card * Real.exp (-(L * t ^ s))) := by
        rw [Finset.sum_const, nsmul_eq_mul, hpow, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (Real.exp (-(t ^ s))) := by
        apply ENNReal.ofReal_le_ofReal
        rw [← Real.exp_log (by linarith : (0 : ℝ) < T.card), ← Real.exp_add]
        apply Real.exp_le_exp.2
        rw [hL]
        nlinarith

/-- **An exponential moment gives an `O_1` tail.** -/
theorem osBound_of_exp_moment {P : Measure Ω} [IsFiniteMeasure P] {S : Ω → ℝ} {θ : ℝ}
    (hθ : 0 < θ) (hint : Integrable (fun ω => Real.exp ((S ω / θ) ^ (1 : ℝ))) P)
    (hle : (∫ ω, Real.exp ((S ω / θ) ^ (1 : ℝ)) ∂P) ≤ 2) :
    OsBound P 1 (2 * θ) S := by
  intro t ht
  have h := Rigidity.Percolation.measure_lt_le_of_exp_rpow_moment P hθ one_pos hint hle
    (t := t * (2 * θ)) (by positivity)
  refine (measure_mono fun ω hω => ?_).trans (h.trans (ENNReal.ofReal_le_ofReal ?_))
  · simp only [Set.mem_setOf_eq] at hω ⊢
    rcases lt_max_iff.1 hω with h1 | h1
    · exact h1
    · exact absurd h1 (not_lt.2 (by positivity))
  · rw [Real.rpow_one, Real.rpow_one,
      show t * (2 * θ) / θ = 2 * t by field_simp]
    have := two_mul_exp_le ht one_pos
    rw [Real.rpow_one] at this
    linarith

/-- **Scaling.** -/
theorem OsBound.const_mul {P : Measure Ω} {s θ c : ℝ} {X : Ω → ℝ} (hc : 0 < c)
    (hX : OsBound P s θ X) : OsBound P s (c * θ) (fun ω => c * X ω) := by
  intro t ht
  refine le_trans (measure_mono fun ω hω => ?_) (hX t ht)
  simp only [Set.mem_setOf_eq] at hω ⊢
  have e : max (c * X ω) 0 = c * max (X ω) 0 := by
    rw [mul_max_of_nonneg _ _ hc.le, mul_zero]
  rw [e] at hω
  nlinarith

/-- **Almost-everywhere domination.** -/
theorem OsBound.mono_ae {P : Measure Ω} {s θ θ' : ℝ} {X Y : Ω → ℝ} (hθθ' : θ ≤ θ')
    (hXY : ∀ᵐ ω ∂P, X ω ≤ Y ω) (hY : OsBound P s θ Y) : OsBound P s θ' X := by
  intro t ht
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  set N := {ω | ¬ X ω ≤ Y ω} with hN
  have hN0 : P N = 0 := ae_iff.1 hXY
  have hsub : {ω | t * θ' < max (X ω) 0} ⊆ {ω | t * θ < max (Y ω) 0} ∪ N := by
    intro ω hω
    by_cases h : X ω ≤ Y ω
    · left
      simp only [Set.mem_setOf_eq] at hω ⊢
      have h1 : t * θ ≤ t * θ' := mul_le_mul_of_nonneg_left hθθ' ht0
      have h2 : max (X ω) 0 ≤ max (Y ω) 0 := max_le_max h le_rfl
      linarith
    · right; exact h
  calc P {ω | t * θ' < max (X ω) 0} ≤ P ({ω | t * θ < max (Y ω) 0} ∪ N) := measure_mono hsub
    _ ≤ P {ω | t * θ < max (Y ω) 0} + P N := measure_union_le _ _
    _ ≤ _ := by rw [hN0, add_zero]; exact hY t ht

/-- **From the tail form to the exponential-moment form `IsOsBond`.** -/
theorem isOsBond_of_osBound {d : ℕ} {p : unitInterval}
    {X : LatticeProb.Percolation.Configuration d → ℝ} {s θ : ℝ} (hs : 0 < s) (hθ : 0 < θ)
    (hXm : Measurable X)
    (hX : OsBound (LatticeProb.Percolation.latticeBondLaw d p) s θ X) :
    Rigidity.External.IsOsBond d p X s (θ * 2 ^ (1 / s) * Real.exp 2 ^ (1 / s)) := by
  obtain ⟨hint, hle⟩ := Rigidity.Proofs.S2.integrable_half_exponential_of_osBound _ X s θ hs hθ
    hXm hX
  have h2 : (0 : ℝ) < 2 ^ (1 / s) := by positivity
  have e : ∀ ω, Real.exp ((max (X ω) 0 / θ) ^ s / 2) =
      Real.exp (Real.rpow (max (X ω / (θ * 2 ^ (1 / s))) 0) s) := by
    intro ω
    congr 1
    have hm : max (X ω / (θ * 2 ^ (1 / s))) 0 = max (X ω) 0 / θ / 2 ^ (1 / s) := by
      rw [div_div, ← max_div_div_right (by positivity), zero_div]
    change _ = (max (X ω / (θ * 2 ^ (1 / s))) 0) ^ s
    rw [hm, Real.div_rpow (by positivity) h2.le, ← Real.rpow_mul (by norm_num),
      one_div_mul_cancel hs.ne', Real.rpow_one]
  simp only [e] at hint hle
  exact Rigidity.Proofs.S2.isOsBond_of_integral_le hs (Real.one_le_exp (by norm_num)) hint hle

end Rigidity.Proofs.Cluster
