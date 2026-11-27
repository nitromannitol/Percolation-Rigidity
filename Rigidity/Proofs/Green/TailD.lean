import Rigidity.Proofs.Green.DarioGuTail

/-!
# Stretched exponential tails on `ℤ^d`

The `d`-dimensional form of `DarioGuTail.lean`: `HasTailD p X C s` is `P[X ≥ u] ≤ C exp(-u^s/C)` for
every `u ≥ 0`; an `O_s(θ)` bound gives such a tail by Markov's inequality
(`hasTailD_of_isOsBond`), and tails are stable under maxima, powers, multiples and lowering the
exponent.
-/

open MeasureTheory Finset LatticeProb.Percolation Rigidity.External
open scoped ENNReal

namespace Rigidity.Green

variable {d : ℕ} {p : unitInterval}

/-- `P[X ≥ u] ≤ C exp(-u^s / C)` for every `u ≥ 0`, on `ℤ^d`. -/
def HasTailD (p : unitInterval) (X : Configuration d → ℝ) (C s : ℝ) : Prop :=
  ∀ u : ℝ, 0 ≤ u →
    latticeBondLaw d p {ω | u ≤ X ω} ≤ ENNReal.ofReal (C * Real.exp (-Real.rpow u s / C))

theorem HasTailD.mono {X : Configuration d → ℝ} {C C' s : ℝ} (h : HasTailD p X C s) (hC : 0 < C)
    (hCC : C ≤ C') : HasTailD p X C' s := by
  intro u hu
  refine (h u hu).trans (ENNReal.ofReal_le_ofReal ?_)
  have hv : 0 ≤ Real.rpow u s := Real.rpow_nonneg hu s
  have : Real.exp (-Real.rpow u s / C) ≤ Real.exp (-Real.rpow u s / C') := by
    apply Real.exp_le_exp.2
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left hv hC hCC
  exact mul_le_mul hCC this (Real.exp_pos _).le (by linarith)

theorem HasTailD.mono_exponent {X : Configuration d → ℝ} {C s s' : ℝ} (h : HasTailD p X C s)
    (hC : 2 ≤ C) (hs' : 0 < s') (hss : s' ≤ s) : HasTailD p X C s' := by
  intro u hu
  rcases le_or_gt 1 u with h1 | h1
  · refine (h u hu).trans (ENNReal.ofReal_le_ofReal ?_)
    have : Real.rpow u s' ≤ Real.rpow u s := Real.rpow_le_rpow_of_exponent_le h1 hss
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    apply Real.exp_le_exp.2
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_right this (by linarith)
  · calc latticeBondLaw d p {ω | u ≤ X ω} ≤ 1 := prob_le_one
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (one_le_mul_exp_neg hC
          (Real.rpow_le_one hu h1.le hs'.le))

theorem HasTailD.max {X Y : Configuration d → ℝ} {C s : ℝ} (hX : HasTailD p X C s)
    (hY : HasTailD p Y C s) (hC : 0 < C) :
    HasTailD p (fun ω => Max.max (X ω) (Y ω)) (2 * C) s := by
  intro u hu
  have hset : {ω | u ≤ Max.max (X ω) (Y ω)} = {ω | u ≤ X ω} ∪ {ω | u ≤ Y ω} := by
    ext ω; simp
  rw [hset]
  refine (measure_union_le _ _).trans ?_
  refine (add_le_add (hX u hu) (hY u hu)).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hv : 0 ≤ Real.rpow u s := Real.rpow_nonneg hu s
  have : Real.exp (-Real.rpow u s / C) ≤ Real.exp (-Real.rpow u s / (2 * C)) := by
    apply Real.exp_le_exp.2
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left hv hC (by linarith)
  nlinarith

theorem HasTailD.rpow {X : Configuration d → ℝ} {C s a : ℝ} (h : HasTailD p X C s) (ha : 0 < a)
    (hX : ∀ ω, 0 ≤ X ω) : HasTailD p (fun ω => X ω ^ a) C (s / a) := by
  intro u hu
  have hsub : {ω | u ≤ X ω ^ a} ⊆ {ω | u ^ (1 / a) ≤ X ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    have := Real.rpow_le_rpow hu hω (by positivity : (0 : ℝ) ≤ 1 / a)
    rwa [← Real.rpow_mul (hX ω), mul_one_div_cancel ha.ne', Real.rpow_one] at this
  have e : Real.rpow (u ^ (1 / a)) s = Real.rpow u (s / a) := by
    change (u ^ (1 / a)) ^ s = u ^ (s / a)
    rw [← Real.rpow_mul hu]
    ring_nf
  refine (measure_mono hsub).trans ((h _ (Real.rpow_nonneg hu _)).trans (le_of_eq ?_))
  rw [e]

theorem HasTailD.const_mul {X : Configuration d → ℝ} {C s c : ℝ} (h : HasTailD p X C s) (hC : 0 < C)
    (hc : 0 < c) : HasTailD p (fun ω => c * X ω) (Max.max C (c ^ s * C)) s := by
  intro u hu
  have hsub : {ω | u ≤ c * X ω} = {ω | u / c ≤ X ω} := by
    ext ω; simp only [Set.mem_setOf_eq]; rw [div_le_iff₀ hc, mul_comm]
  rw [hsub]
  refine (h _ (div_nonneg hu hc.le)).trans (ENNReal.ofReal_le_ofReal ?_)
  have hv : Real.rpow (u / c) s = Real.rpow u s / c ^ s := Real.div_rpow hu hc.le s
  rw [hv]
  have hcs : 0 < c ^ s := Real.rpow_pos_of_pos hc s
  have hw : 0 ≤ Real.rpow u s := Real.rpow_nonneg hu s
  apply mul_le_mul (le_max_left _ _) _ (Real.exp_pos _).le (by positivity)
  apply Real.exp_le_exp.2
  rw [neg_div, neg_div, neg_le_neg_iff, div_div]
  apply div_le_div_of_nonneg_left hw (by positivity)
  rw [mul_comm]
  exact le_max_right _ _

theorem HasTailD.max_const {X : Configuration d → ℝ} {C s a : ℝ} (h : HasTailD p X C s)
    (hC : 0 < C) (hs : 0 < s) :
    HasTailD p (fun ω => Max.max (X ω) a) (Max.max C (Max.max 3 (Real.rpow a s))) s := by
  intro u hu
  set C' := Max.max C (Max.max 3 (Real.rpow a s))
  have hC' : 3 ≤ C' := (le_max_left _ _).trans (le_max_right _ _)
  rcases le_or_gt u a with h1 | h1
  · calc latticeBondLaw d p {ω | u ≤ Max.max (X ω) a} ≤ 1 := prob_le_one
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          have hua : Real.rpow u s ≤ C' :=
            (Real.rpow_le_rpow hu h1 hs.le).trans ((le_max_right _ _).trans (le_max_right _ _))
          have hv : -(1 : ℝ) ≤ -Real.rpow u s / C' := by
            rw [neg_div, neg_le_neg_iff, div_le_one (by linarith)]
            exact hua
          have h2 : Real.exp (-1) ≤ Real.exp (-Real.rpow u s / C') := Real.exp_le_exp.2 hv
          have h3 : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; simp
          have h4 : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
          nlinarith [Real.exp_pos (-1)]
  · have hsub : {ω | u ≤ Max.max (X ω) a} = {ω | u ≤ X ω} := by
      ext ω; simp only [Set.mem_setOf_eq, le_max_iff]
      constructor
      · rintro (h' | h')
        · exact h'
        · exact absurd h' (not_le.2 h1)
      · exact Or.inl
    rw [hsub]
    exact HasTailD.mono h hC (le_max_left _ _) u hu

/-- `O_s(θ)` gives a tail (Markov's inequality). -/
theorem hasTailD_of_isOsBond {X : Configuration d → ℝ} {s θ : ℝ} (hs : 0 < s) (hθ : 0 < θ)
    (hX : IsOsBond d p X s θ) : HasTailD p X (max 2 (θ ^ s)) s := by
  intro u hu
  obtain ⟨hint, hle⟩ := hX
  set F := fun ω => Real.exp (Real.rpow (max (X ω / θ) 0) s)
  set a := Real.rpow (u / θ) s
  have hsub : {ω | u ≤ X ω} ⊆ {ω | Real.exp a ≤ F ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    apply Real.exp_le_exp.2
    apply Real.rpow_le_rpow (div_nonneg hu hθ.le) _ hs.le
    exact (div_le_div_of_nonneg_right hω hθ.le).trans (le_max_left _ _)
  have hmk := mul_meas_ge_le_integral_of_nonneg (μ := latticeBondLaw d p)
    (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le) hint (Real.exp a)
  have hreal : (latticeBondLaw d p).real {ω | Real.exp a ≤ F ω} ≤ 2 * Real.exp (-a) := by
    rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos a), mul_comm]
    exact hmk.trans hle
  calc latticeBondLaw d p {ω | u ≤ X ω} ≤ latticeBondLaw d p {ω | Real.exp a ≤ F ω} :=
        measure_mono hsub
    _ = ENNReal.ofReal ((latticeBondLaw d p).real {ω | Real.exp a ≤ F ω}) := by
        rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    _ ≤ ENNReal.ofReal (2 * Real.exp (-a)) := ENNReal.ofReal_le_ofReal hreal
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have ha : a = Real.rpow u s / θ ^ s := Real.div_rpow hu hθ.le s
        rw [ha]
        have hθs : 0 < θ ^ s := Real.rpow_pos_of_pos hθ s
        have hw : 0 ≤ Real.rpow u s := Real.rpow_nonneg hu s
        apply mul_le_mul (le_max_left _ _) _ (Real.exp_pos _).le (by positivity)
        apply Real.exp_le_exp.2
        rw [neg_div, neg_le_neg_iff]
        exact div_le_div_of_nonneg_left hw hθs (le_max_right _ _)

end Rigidity.Green
