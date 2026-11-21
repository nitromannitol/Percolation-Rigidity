import Rigidity.Proofs.Percolation.PlanarOmegaDBounds
import Rigidity.Proofs.Percolation.PlanarOmegaIteration
import Rigidity.Proofs.Percolation.PlanarTauSummable

/-!
# Geometric decay of `D_n` from the decay of `ω`

Lemma 5.9 of Armstrong and Dario bounds `D_n` by the geometric error plus the weighted past of
`τ`: `D_n ≤ C (σⁿ + ∑_{l ≤ n} ρ^{n-l} τ_l)`. Combined with the decrease of `D_n` along `τ_n` (Step 1
of the proof of Lemma 5.10) and the lower bound `D_n ≥ -C 3^(-n/2)`, the iteration for real sequences
gives `D_n ≤ K λⁿ` with `λ < 1` (Steps 2 and 3 of the proof of Lemma 5.10, in dimension two). This
file proves this implication, with the bound of Lemma 5.9 as a hypothesis.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped ENNReal Classical Matrix

namespace Rigidity.Percolation

/-- The errors `3^(-n/2) + exp (-c 3ⁿ)` are geometric. -/
theorem planarError_le_two_mul_pow {c σ : ℝ} (hc : 0 < c) (hr : 1 / Real.sqrt 3 ≤ σ)
    (he : Real.exp (-c) ≤ σ) (n : ℕ) :
    1 / Real.sqrt ((3 : ℝ) ^ n) + Real.exp (-c * (3 : ℝ) ^ n) ≤ 2 * σ ^ n := by
  have h1 : 1 / Real.sqrt ((3 : ℝ) ^ n) ≤ σ ^ n := by
    rw [sqrt_three_pow, ← one_div_pow]
    exact pow_le_pow_left₀ (by positivity) hr n
  have h2 : Real.exp (-c * (3 : ℝ) ^ n) ≤ σ ^ n := by
    refine le_trans ?_ (pow_le_pow_left₀ (Real.exp_pos _).le he n)
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    have hk : (n : ℝ) ≤ 3 ^ n := by exact_mod_cast (Nat.lt_pow_self (by norm_num)).le
    nlinarith
  linarith

/-- **Geometric decay of `D_n` from the bound of Lemma 5.9** (Armstrong and Dario, Steps 2 and 3
of the proof of Lemma 5.10, in dimension two). -/
theorem exists_planarOmegaD_le_pow_of_decay {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) {C₉ σ₉ ρ₉ : ℝ} {N₉ : ℕ} (hC₉ : 0 ≤ C₉) (hσ₉ : 0 ≤ σ₉)
    (hσ₉1 : σ₉ < 1) (hρ₉ : 0 ≤ ρ₉) (hρ₉1 : ρ₉ < 1)
    (h59 : ∀ n, N₉ ≤ n → planarOmegaD p n ≤
      C₉ * σ₉ ^ n + C₉ * ∑ l ∈ Finset.range (n + 1), ρ₉ ^ (n - l) * planarTau p l) :
    ∃ K l : ℝ, 0 < l ∧ l < 1 ∧ ∃ N : ℕ, ∀ n, N ≤ n → planarOmegaD p n ≤ K * l ^ n := by
  obtain ⟨c, hc, C₁, hC₁, c', hc', N₁, h1⟩ := exists_planarOmegaD_succ_le hpc
  obtain ⟨C₂, hC₂, N₂, h2⟩ := exists_neg_le_planarOmegaD hpc
  have hsq3 : 1 < Real.sqrt 3 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hr1 : 1 / Real.sqrt 3 < 1 := (div_lt_one (by positivity)).2 hsq3
  have he1 : Real.exp (-c') < 1 := by simpa using Real.exp_lt_exp.2 (neg_lt_zero.2 hc')
  have hρs : Real.sqrt ρ₉ < 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_lt_sqrt hρ₉ hρ₉1
  set σ := max (max σ₉ (1 / Real.sqrt 3)) (max (Real.exp (-c')) (Real.sqrt ρ₉)) with hσdef
  have hσ1 : σ < 1 := max_lt (max_lt hσ₉1 hr1) (max_lt he1 hρs)
  have hσ0 : 0 ≤ σ := le_max_of_le_left (le_max_of_le_left hσ₉)
  have hσ₉σ : σ₉ ≤ σ := le_max_of_le_left (le_max_left _ _)
  have hrσ : 1 / Real.sqrt 3 ≤ σ := le_max_of_le_left (le_max_right _ _)
  have heσ : Real.exp (-c') ≤ σ := le_max_of_le_right (le_max_left _ _)
  have hρσ : Real.sqrt ρ₉ ≤ σ := le_max_of_le_right (le_max_right _ _)
  set μ := (1 + σ) / 2 with hμdef
  have hσμ : σ < μ := by rw [hμdef]; linarith
  have hμ1 : μ < 1 := by rw [hμdef]; linarith
  have hρμ : ρ₉ ≤ μ ^ 2 := by
    rw [← Real.sq_sqrt hρ₉]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (hρσ.trans hσμ.le) 2
  set C := 2 * C₁ + C₂ + C₉ with hCdef
  have hC : 0 ≤ C := by positivity
  set N := max N₁ (max N₂ N₉) with hNdef
  have hσn : ∀ n, 0 ≤ σ ^ n := fun n => pow_nonneg hσ0 n
  have h1' : ∀ n, N ≤ n → planarOmegaD p (n + 1) ≤ planarOmegaD p n - c * planarTau p n +
      C * σ ^ n := fun n hn => by
    have h := h1 n (le_trans (le_max_left _ _) hn)
    have he := planarError_le_two_mul_pow hc' hrσ heσ n
    have := mul_le_mul_of_nonneg_left he hC₁
    have : C₁ * (2 * σ ^ n) ≤ C * σ ^ n := by
      rw [hCdef]
      nlinarith [hσn n]
    linarith
  have h2' : ∀ n, N ≤ n → -(C * σ ^ n) ≤ planarOmegaD p n := fun n hn => by
    have h := h2 n (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn)
    have hr : 1 / Real.sqrt ((3 : ℝ) ^ n) ≤ σ ^ n := by
      rw [sqrt_three_pow, ← one_div_pow]
      exact pow_le_pow_left₀ (by positivity) hrσ n
    have := mul_le_mul_of_nonneg_left hr hC₂
    have : C₂ * σ ^ n ≤ C * σ ^ n := by
      rw [hCdef]
      nlinarith [hσn n]
    linarith
  have h3' : ∀ n, N ≤ n → planarOmegaD p n ≤ C * σ ^ n +
      C * ∑ l ∈ Finset.range (n + 1), ρ₉ ^ (n - l) * planarTau p l := fun n hn => by
    have h := h59 n (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn)
    have hS : 0 ≤ ∑ l ∈ Finset.range (n + 1), ρ₉ ^ (n - l) * planarTau p l :=
      Finset.sum_nonneg fun l _ => mul_nonneg (pow_nonneg hρ₉ _) (planarTau_nonneg p l)
    have a1 : σ₉ ^ n ≤ σ ^ n := pow_le_pow_left₀ hσ₉ hσ₉σ n
    have a2 : C₉ * σ₉ ^ n ≤ C * σ ^ n := by
      have := mul_le_mul_of_nonneg_left a1 hC₉
      rw [hCdef]
      nlinarith [hσn n]
    have a3 : C₉ * ∑ l ∈ Finset.range (n + 1), ρ₉ ^ (n - l) * planarTau p l ≤
        C * ∑ l ∈ Finset.range (n + 1), ρ₉ ^ (n - l) * planarTau p l :=
      mul_le_mul_of_nonneg_right (by rw [hCdef]; linarith) hS
    linarith
  obtain ⟨K, l, hl0, hl1, hK⟩ := exists_le_mul_pow_of_omega_iteration_of_ge N hc hC hσ0 hσμ hμ1
    hρ₉ hρμ (planarTau_nonneg p) h1' h2' h3'
  exact ⟨K, l, hl0, hl1, N, hK⟩

end Rigidity.Percolation
