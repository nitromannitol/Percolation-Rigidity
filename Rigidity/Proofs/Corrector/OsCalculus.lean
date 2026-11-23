import Rigidity.Proofs.S2.ClusterDensityFromDarioGu
import Rigidity.Proofs.S2.ClusterDensityBounds
import Rigidity.Percolation.TriadicExceptionalSupremum

/-!
# Triadic minimal scales (Dario–Gu, Lemma 1.6)

For the bond law, `X ≤ O_s(θ)` (`IsOsBond`) means `E[exp((X/θ ∨ 0)^s)] ≤ 2` (Dario–Gu, §1.6.2).

**Dario–Gu, Lemma 1.6** (Armstrong–Dario, Lemma 2.3): for `K ≥ 1` and `s, β > 0` there is
`C(s, β, K) < ∞` such that, if `X_n ≤ O_s(K 3^{-nβ})` for every `n`, the random scale
`M = sup {3^n : X_n ≥ 1}` satisfies `M ≤ O_{βs}(C)`.

The proof follows the printed one: by Chebyshev's inequality (`measure_le_le_of_isOsBond`)
`P[X_n ≥ 1] ≤ 2 exp(-(3^{nβ}/K)^s)`, and the triadic exceptional-scale estimate
`Rigidity.Percolation.uniform_exceptionalScale_exp_moment` bounds the stretched-exponential moment
of the supremum of the triadic lengths `3^n` of the events `{X_n ≥ 1}`. By the Borel–Cantelli
lemma (`Rigidity.Percolation.ae_exceptionalScale_ne_top`) this supremum is almost surely finite, so
that almost surely `3^n ≤ M` whenever `X_n ≥ 1`. The source proof prints `3^{-nβ}` for `3^{nβ}` in
the tail of `X_n` (Armstrong–Dario, proof of Lemma 2.3).

**Dario, Lemma C.3** (`lemmafromperc.0`): if `X_n ≤ K + O_s(K 3^{-nβ})`, the random scale
`sup {3^n : X_n ≥ K + 1}` is `O_{βs}(C)`; as printed, this is Lemma 1.6 applied to
`max(X_n - K, 0)`.
-/

namespace Rigidity.Corrector

open MeasureTheory Filter Set LatticeProb.Percolation Rigidity.External Rigidity.Proofs.S2
  Rigidity.Percolation
open scoped ENNReal

variable {d : ℕ} {p : unitInterval}

/-- The triadic random scale `sup {3^n : 1 ≤ X_n}` of Dario–Gu, Lemma 1.6, as a real number (`0`
when the supremum is infinite). -/
noncomputable def triadicScale (X : ℕ → Configuration d → ℝ) (ω : Configuration d) : ℝ :=
  (exceptionalScale (fun n => {ω' | 1 ≤ X n ω'}) ω).toReal

theorem triadicScale_nonneg (X : ℕ → Configuration d → ℝ) (ω : Configuration d) :
    0 ≤ triadicScale X ω :=
  ENNReal.toReal_nonneg

theorem measurable_triadicScale {X : ℕ → Configuration d → ℝ} (hX : ∀ n, Measurable (X n)) :
    Measurable (triadicScale X) :=
  ENNReal.measurable_toReal.comp
    (measurable_exceptionalScale _ fun n => measurableSet_le measurable_const (hX n))

/-- A finite exceptional scale dominates the triadic length of each exceptional index. -/
theorem le_triadicScale {X : ℕ → Configuration d → ℝ} {ω : Configuration d}
    (hfin : exceptionalScale (fun n => {ω' | 1 ≤ X n ω'}) ω ≠ ∞) {n : ℕ} (hn : 1 ≤ X n ω) :
    (3 : ℝ) ^ n ≤ triadicScale X ω := by
  classical
  have hle : (3 : ℝ≥0∞) ^ n ≤ exceptionalScale (fun n => {ω' | 1 ≤ X n ω'}) ω := by
    unfold exceptionalScale
    refine le_iSup_of_le n ?_
    simp only [Set.mem_setOf_eq, hn, if_true, le_refl]
  have h3 : ((3 : ℝ≥0∞) ^ n).toReal = (3 : ℝ) ^ n := by
    rw [ENNReal.toReal_pow]
    norm_num
  rw [← h3]
  exact ENNReal.toReal_mono hfin hle

/-- **Minimal scale from tails.** If `P[X_n ≥ 1] ≤ C exp(-c (3^n)^γ)` for every `n`, then
`triadicScale X ≤ O_γ(θ)` with `θ` depending only on `C, c, γ`, and almost surely
`3^n ≤ triadicScale X` whenever `X_n ≥ 1`. -/
theorem isOsBond_triadicScale_of_tail {C : ℝ≥0∞} (hC : C ≠ ∞) {c γ : ℝ} (hc : 0 < c)
    (hγ : 0 < γ) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ X : ℕ → Configuration d → ℝ, (∀ n, Measurable (X n)) →
      (∀ n : ℕ, latticeBondLaw d p {ω | 1 ≤ X n ω} ≤
        C * ENNReal.ofReal (Real.exp (-c * ((3 : ℝ) ^ n) ^ γ))) →
      IsOsBond d p (triadicScale X) γ θ ∧
        ∀ᵐ ω ∂latticeBondLaw d p, ∀ n, 1 ≤ X n ω → (3 : ℝ) ^ n ≤ triadicScale X ω := by
  obtain ⟨θ, hθ, hmom⟩ := uniform_exceptionalScale_exp_moment (Ω := Configuration d) C hC γ c hγ hc
  refine ⟨θ, hθ, fun X hX htail => ⟨?_, ?_⟩⟩
  · obtain ⟨hi, hb⟩ := hmom (latticeBondLaw d p) (fun n => {ω' | 1 ≤ X n ω'})
      (fun n => measurableSet_le measurable_const (hX n)) htail
    have heq : (fun ω => Real.exp (Real.rpow (max (triadicScale X ω / θ) 0) γ)) =
        fun ω => Real.exp (((exceptionalScale (fun n => {ω' | 1 ≤ X n ω'}) ω).toReal / θ) ^ γ) := by
      funext ω
      rw [max_eq_left (div_nonneg (triadicScale_nonneg X ω) hθ.le)]
      rfl
    unfold IsOsBond
    rw [heq]
    exact ⟨hi, hb⟩
  · have hb : (1 : ℝ) < (3 : ℝ) ^ γ := Real.one_lt_rpow (by norm_num) hγ
    have hE : ∀ n : ℕ, latticeBondLaw d p {ω | 1 ≤ X n ω} ≤
        C * ENNReal.ofReal (Real.exp (-c * ((3 : ℝ) ^ γ) ^ n)) := by
      intro n
      have h3 : ((3 : ℝ) ^ n) ^ γ = ((3 : ℝ) ^ γ) ^ n := by
        rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
          ← Real.rpow_mul (by norm_num), mul_comm]
      rw [← h3]
      exact htail n
    filter_upwards [ae_exceptionalScale_ne_top (latticeBondLaw d p)
      (fun n => {ω' | 1 ≤ X n ω'}) C hC _ c hb hc hE] with ω hω n hn
    exact le_triadicScale hω hn

/-- **Dario–Gu, Lemma 1.6** (Armstrong–Dario, Lemma 2.3). For `K ≥ 1` and `s, β > 0` there is
`C(s, β, K) < ∞` such that, for random variables `X_n ≤ O_s(K 3^{-nβ})`, the random scale
`M = sup {3^n : X_n ≥ 1}` satisfies `M ≤ O_{βs}(C)`; almost surely `3^n ≤ M` whenever `X_n ≥ 1`. -/
theorem isOsBond_triadicScale {K s β : ℝ} (hK : 1 ≤ K) (hs : 0 < s) (hβ : 0 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ → Configuration d → ℝ, (∀ n, Measurable (X n)) →
      (∀ n : ℕ, IsOsBond d p (X n) s (K / ((3 : ℝ) ^ n) ^ β)) →
      IsOsBond d p (triadicScale X) (β * s) C ∧
        ∀ᵐ ω ∂latticeBondLaw d p, ∀ n, 1 ≤ X n ω → (3 : ℝ) ^ n ≤ triadicScale X ω := by
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK
  have hc : 0 < 1 / K ^ s := by positivity
  obtain ⟨C, hC, h⟩ := isOsBond_triadicScale_of_tail (d := d) (p := p) (C := ENNReal.ofReal 2)
    ENNReal.ofReal_ne_top hc
    (mul_pos hβ hs)
  refine ⟨C, hC, fun X hX hO => h X hX fun n => ?_⟩
  have h3 : (0 : ℝ) < ((3 : ℝ) ^ n) ^ β := by positivity
  have hm := measure_le_le_of_isOsBond (div_pos hK0 h3) hs zero_le_one (hO n)
  refine hm.trans ?_
  rw [← ENNReal.ofReal_mul (by norm_num)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  congr 2
  rw [one_div_div, Real.div_rpow h3.le hK0.le, ← Real.rpow_mul (by positivity)]
  ring


/-- `X ≤ O_s(θ)` if and only if its positive part is. -/
theorem isOsBond_max_zero_iff {X : Configuration d → ℝ} {s θ : ℝ} (hθ : 0 < θ) :
    IsOsBond d p (fun ω => max (X ω) 0) s θ ↔ IsOsBond d p X s θ := by
  have heq : ∀ ω, max (max (X ω) 0 / θ) 0 = max (X ω / θ) 0 := by
    intro ω
    rcases le_total (X ω) 0 with h | h
    · rw [max_eq_right h, zero_div, max_self, max_eq_right (div_nonpos_of_nonpos_of_nonneg h hθ.le)]
    · rw [max_eq_left h]
  unfold IsOsBond
  simp only [heq]

/-- **Dario, Lemma C.3** (`lemmafromperc.0` of *Optimal corrector estimates on percolation
clusters*). For `K ≥ 1` and `s, β > 0` there is `C(s, β, K)` such that, if `X_n ≤ K + Y_n` with
`Y_n ≤ O_s(K 3^{-nβ})`, the random scale `sup {3^n : X_n ≥ K + 1}`, that is the triadic scale of
`max(X_n - K, 0)`, satisfies `≤ O_{βs}(C)`, and almost surely `3^n` is at most this scale whenever
`X_n ≥ K + 1`. -/
theorem isOsBond_triadicScale_shift {K s β : ℝ} (hK : 1 ≤ K) (hs : 0 < s) (hβ : 0 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ X Y : ℕ → Configuration d → ℝ, (∀ n, Measurable (X n)) →
      (∀ n ω, X n ω ≤ K + Y n ω) → (∀ n : ℕ, IsOsBond d p (Y n) s (K / ((3 : ℝ) ^ n) ^ β)) →
      IsOsBond d p (triadicScale fun n ω => max (X n ω - K) 0) (β * s) C ∧
        ∀ᵐ ω ∂latticeBondLaw d p, ∀ n, K + 1 ≤ X n ω →
          (3 : ℝ) ^ n ≤ triadicScale (fun n ω => max (X n ω - K) 0) ω := by
  obtain ⟨C, hC, h⟩ := isOsBond_triadicScale (d := d) (p := p) hK hs hβ
  refine ⟨C, hC, fun X Y hX hXY hO => ?_⟩
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK
  have hO' : ∀ n : ℕ, IsOsBond d p (fun ω => max (X n ω - K) 0) s (K / ((3 : ℝ) ^ n) ^ β) := by
    intro n
    have hθ : 0 < K / ((3 : ℝ) ^ n) ^ β := by positivity
    have hY := (isOsBond_max_zero_iff (X := Y n) (p := p) (s := s) hθ).2 (hO n)
    refine IsOsBond.mono_variable hs hθ (((hX n).sub_const K).max measurable_const)
      (fun ω => ?_) hY
    exact max_le_max (by linarith [hXY n ω]) le_rfl
  obtain ⟨h1, h2⟩ := h (fun n ω => max (X n ω - K) 0)
    (fun n => ((hX n).sub_const K).max measurable_const) hO'
  refine ⟨h1, ?_⟩
  filter_upwards [h2] with ω hω n hn
  exact hω n (le_max_of_le_left (by linarith))

end Rigidity.Corrector
