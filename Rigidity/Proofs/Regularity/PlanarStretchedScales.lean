import Rigidity.Proofs.Partition.GeneralPartition
import Rigidity.Percolation.TriadicExceptionalSupremum
import Rigidity.Percolation.PolynomialExponential
import Rigidity.External.CorrectorQuantitative

/-!
# Minimal scales from events with stretched-exponential probabilities

* `exp_neg_rpow_anti`, `exists_rpow_mul_exp_le`: comparisons of stretched exponentials in `x ≥ 1`;
  a power of `x` is absorbed by halving the rate;
* `measure_lt_le_of_isOsBond`: the tail `P(X > t) ≤ 2 exp(-(t/θ)^s)` of `X ≤ O_s(θ)`;
* `exists_isOsBond_of_events`: if `P(E_n) ≤ C exp(-c 3^{n s})` for every `n`, the supremum of the
  `3^n` over the `n` with `ω ∈ E_n` is a minimal scale `Y ≤ O_s(θ)`: almost surely `ω ∉ E_n` as soon as
  `Y(ω) < 3^n`. This is the union bound over the scales and the Borel–Cantelli argument of the
  proof of Proposition 2.4 of Armstrong and Dario (arXiv:1609.09431v2), through
  `Rigidity.Percolation.exceptionalScale`.
-/

namespace Rigidity.Proofs.Regularity

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External Rigidity.Percolation
open scoped ENNReal

theorem exp_neg_rpow_anti {x c c' σ σ' : ℝ} (hx : 1 ≤ x) (hc' : 0 ≤ c') (hcc : c' ≤ c)
    (hσσ : σ' ≤ σ) : Real.exp (-c * x ^ σ) ≤ Real.exp (-c' * x ^ σ') := by
  apply Real.exp_le_exp.2
  have h1 : x ^ σ' ≤ x ^ σ := Real.rpow_le_rpow_of_exponent_le hx hσσ
  have h2 : (0 : ℝ) ≤ x ^ σ' := by positivity
  nlinarith

/-- A power of `x` is absorbed by a stretched exponential with half the rate. -/
theorem exists_rpow_mul_exp_le {a c σ : ℝ} (hc : 0 < c) (hσ : 0 < σ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 1 ≤ x →
      x ^ a * Real.exp (-c * x ^ σ) ≤ K * Real.exp (-(c / 2) * x ^ σ) := by
  set N : ℕ := ⌈a / σ⌉₊ with hN
  refine ⟨(N.factorial : ℝ) / (c / 2) ^ N, by positivity, fun x hx => ?_⟩
  set y : ℝ := x ^ σ with hy
  have hy1 : 1 ≤ y := Real.one_le_rpow hx hσ.le
  have hxa : x ^ a ≤ y ^ N := by
    rw [hy, ← Real.rpow_natCast (x ^ σ), ← Real.rpow_mul (by linarith)]
    refine Real.rpow_le_rpow_of_exponent_le hx ?_
    have h1 : a / σ ≤ N := Nat.le_ceil _
    rw [div_le_iff₀ hσ] at h1
    linarith
  calc x ^ a * Real.exp (-c * y) ≤ y ^ N * Real.exp (-c * y) :=
        mul_le_mul_of_nonneg_right hxa (Real.exp_pos _).le
    _ ≤ _ := pow_mul_exp_neg_le N hc (by linarith)

/-- **The tail of `X ≤ O_s(θ)`.** -/
theorem measure_lt_le_of_isOsBond {p : unitInterval} {X : Configuration 2 → ℝ} {s θ t : ℝ}
    (hs : 0 < s) (hθ : 0 < θ) (ht : 0 ≤ t) (h : IsOsBond 2 p X s θ) :
    latticeBondLaw 2 p {ω | t < X ω} ≤ ENNReal.ofReal (2 * Real.exp (-((t / θ) ^ s))) := by
  obtain ⟨hi, hb⟩ := h
  have e : ∀ ω, Real.exp (Real.rpow (max (X ω / θ) 0) s) =
      Real.exp ((max (X ω) 0 / θ) ^ s) := fun ω => by
    rw [← max_div_div_right hθ.le, zero_div]
    rfl
  simp only [e] at hi hb
  refine le_trans (measure_mono fun ω (hω : t < X ω) => ?_)
    (measure_lt_le_of_exp_rpow_moment (latticeBondLaw 2 p) hθ hs hi hb ht)
  exact lt_of_lt_of_le hω (le_max_left _ _)

/-- **A minimal scale from events with stretched-exponential probabilities.** -/
theorem exists_isOsBond_of_events {p : unitInterval} (E : ℕ → Set (Configuration 2))
    (hEm : ∀ n, MeasurableSet (E n)) {C : ℝ≥0∞} (hC : C ≠ ∞) {s c : ℝ} (hs : 0 < s)
    (hc : 0 < c)
    (hE : ∀ n : ℕ, latticeBondLaw 2 p (E n) ≤
      C * ENNReal.ofReal (Real.exp (-c * ((3 : ℝ) ^ n) ^ s))) :
    ∃ θ : ℝ, 0 < θ ∧ ∃ Y : Configuration 2 → ℝ, Measurable Y ∧ (∀ ω, 0 ≤ Y ω) ∧
      IsOsBond 2 p Y s θ ∧
      ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ n : ℕ, Y ω < 3 ^ n → ω ∉ E n := by
  obtain ⟨θ, hθ, hint, hle⟩ := exceptionalScale_exp_moment (latticeBondLaw 2 p) E hEm C hC s c
    hs hc hE
  have hfin : ∀ᵐ ω ∂latticeBondLaw 2 p, exceptionalScale E ω ≠ ∞ :=
    ae_exceptionalScale_ne_top (latticeBondLaw 2 p) E C hC ((3 : ℝ) ^ s) c
      (Real.one_lt_rpow (by norm_num) hs) hc (fun n => by
        rw [Real.rpow_pow_comm (show (0 : ℝ) ≤ 3 by norm_num) s n]
        exact hE n)
  have e : ∀ ω, Real.exp (Real.rpow (max ((exceptionalScale E ω).toReal / θ) 0) s) =
      Real.exp (((exceptionalScale E ω).toReal / θ) ^ s) := fun ω => by
    rw [max_eq_left (div_nonneg ENNReal.toReal_nonneg hθ.le)]
    rfl
  refine ⟨θ, hθ, fun ω => (exceptionalScale E ω).toReal,
    (measurable_exceptionalScale E hEm).ennreal_toReal, fun ω => ENNReal.toReal_nonneg, ?_, ?_⟩
  · unfold IsOsBond
    simp only [e]
    exact ⟨hint, hle⟩
  · filter_upwards [hfin] with ω hω n hn hωE
    have h3 : (3 : ℝ≥0∞) ^ n ≤ exceptionalScale E ω := by
      unfold exceptionalScale
      exact le_iSup_of_le n (by rw [if_pos hωE])
    have h3' : (3 : ℝ) ^ n ≤ (exceptionalScale E ω).toReal := by
      have := ENNReal.toReal_mono hω h3
      simpa using this
    linarith

end Rigidity.Proofs.Regularity
