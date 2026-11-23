import Rigidity.Proofs.Cluster.GeneralOmegaStepOne
import Rigidity.Proofs.Percolation.PlanarOmegaIteration

/-!
# Geometric decay of `D_n` from the decay of `ω`, in every dimension

By the duality inequality in expectation, `eᵢ · ā_{□_n} eᵢ ≤ E[-μ(□_n, ā_{□_n} eᵢ)] +
E[ν(□_n, eᵢ)] + C 3^{-n/2}`, so that `D_n ≥ -C 3^{-n/2}` from some scale on
(`exists_neg_le_cubeOmegaD`, the lower bound of display (5.43) of Armstrong and Dario).

Lemma 5.9 of Armstrong and Dario bounds `D_n` by a geometric error plus the weighted past of `τ`:
`D_n ≤ C (σⁿ + ∑_{l ≤ n} ρ^{n-l} τ_l)`. Combined with the decrease `D_{n+1} ≤ D_n - c τ_n +
C 3^{-n/4}` of display (5.45) and the lower bound (5.43), the iteration for real sequences
`exists_le_mul_pow_of_omega_iteration_of_ge` gives `D_n ≤ K λⁿ` and `τ_n ≤ K λⁿ` with `λ < 1`
(Steps 2 and 3 of the proof of Lemma 5.10 of Armstrong and Dario, in every dimension `d ≥ 2`).
This file proves this implication, with the bound of Lemma 5.9 as a hypothesis.
-/

open MeasureTheory Filter Topology LatticeProb LatticeProb.Percolation Rigidity.External
open scoped ENNReal Classical Matrix

namespace Rigidity.Percolation

variable {d : ℕ}

/-- `exp(-c y) ≤ 1 / (c y)` for `c, y > 0`. -/
theorem exp_neg_mul_le_one_div_mul {c y : ℝ} (hc : 0 < c) (hy : 0 < y) :
    Real.exp (-c * y) ≤ 1 / (c * y) := by
  have hcy : 0 < c * y := mul_pos hc hy
  have h2 : c * y + 1 ≤ Real.exp (c * y) := Real.add_one_le_exp _
  have h3 : Real.exp (-c * y) = 1 / Real.exp (c * y) := by
    rw [neg_mul, Real.exp_neg, one_div]
  rw [h3]
  exact one_div_le_one_div_of_le hcy (by linarith)

/-- `exp(-c 3ⁿ) ≤ c⁻¹ 3^{-n/2}`. -/
theorem exp_neg_mul_three_pow_le_one_div_sqrt {c : ℝ} (hc : 0 < c) (n : ℕ) :
    Real.exp (-c * (3 : ℝ) ^ n) ≤ 1 / c * (1 / √((3 : ℝ) ^ n)) := by
  have h3 : (1 : ℝ) ≤ 3 ^ n := one_le_pow₀ (by norm_num)
  have hs : √((3 : ℝ) ^ n) ≤ 3 ^ n := Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith⟩
  have hs0 : 0 < √((3 : ℝ) ^ n) := Real.sqrt_pos.2 (by positivity)
  calc Real.exp (-c * (3 : ℝ) ^ n) ≤ 1 / (c * 3 ^ n) :=
        exp_neg_mul_le_one_div_mul hc (by positivity)
    _ ≤ 1 / (c * √((3 : ℝ) ^ n)) :=
        one_div_le_one_div_of_le (mul_pos hc hs0) (mul_le_mul_of_nonneg_left hs hc.le)
    _ = 1 / c * (1 / √((3 : ℝ) ^ n)) := by rw [one_div_mul_one_div]

/-- **The lower bound of display (5.43)** (Armstrong and Dario, proof of Lemma 5.10, every
dimension `d ≥ 2`): from some scale on, `D_n ≥ -C 3^{-n/2}`. -/
theorem exists_neg_le_cubeOmegaD [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      -(C * (1 / √((3 : ℝ) ^ n))) ≤ cubeOmegaD (d := d) p n := by
  obtain ⟨c₀, C₀, hc₀, -, N₁, hN₁⟩ := exists_cubeAhomInvFinite_bounds hd hpc
  obtain ⟨N₂, hN₂⟩ := exists_cubeAhomInvFinite_mul_cubeAhomFinite hd hpc
  obtain ⟨C, c, hC, hc, hdual⟩ := exists_sum_mul_le_cubeMuMean_add_cubeNuMean hd hpc
  set R := √(d * (1 / (4 * c₀ ^ 2))) with hR
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  set K₀ := R * C + 2 * d * 3 ^ d * R * C + R + 3 ^ d * R / 2 with hK₀
  set K := K₀ + R * C * (1 / c) with hK
  have hK₀0 : 0 ≤ K₀ := by positivity
  have hK0 : 0 ≤ K := by positivity
  refine ⟨d * K, by positivity, max N₁ N₂, fun n hn => ?_⟩
  obtain ⟨hinv, -⟩ := hN₂ n (le_of_max_le_right hn)
  have hb := hN₁ n (le_of_max_le_left hn)
  set s := 1 / √((3 : ℝ) ^ n) with hs
  have hs0 : 0 ≤ s := by positivity
  have hterm : ∀ i : Fin d, -(K * s) ≤ cubeNuMean p n (Pi.single i 1) +
      cubeMuMean p n (cubeAhomFinite p n *ᵥ Pi.single i 1) -
      (cubeAhomFinite p n *ᵥ Pi.single i 1) i := by
    intro i
    set x := cubeAhomFinite (d := d) p n *ᵥ Pi.single i 1 with hx
    have hsq : ∑ j, x j ^ 2 ≤ 1 / (4 * c₀ ^ 2) :=
      sum_sq_mulVec_single_le_of_le hc₀ (fun q => (hb q).1) hinv i
    have hx1 : ∑ j, |x j| ≤ R := by
      refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
      have h1 := sq_sum_abs_le_card_mul x
      have h2 := mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg (α := ℝ) d)
      linarith
    have hxi : |x i| ≤ R :=
      (Finset.single_le_sum (f := fun j => |x j|) (fun j _ => abs_nonneg _)
        (Finset.mem_univ i)).trans hx1
    have hξ1 : ∑ j, |(Pi.single i 1 : Fin d → ℝ) j| = 1 := by
      rw [Finset.sum_eq_single i (fun k _ hk => by simp [hk]) (by simp)]
      simp
    have hsum : ∑ j, x j * (Pi.single i 1 : Fin d → ℝ) j = x i := by
      rw [Finset.sum_eq_single i (fun k _ hk => by simp [hk]) (by simp)]
      simp
    have h := hdual x (Pi.single i 1) n
    rw [hsum, hξ1] at h
    simp only [mul_one, one_pow] at h
    have hA : (∑ j, |x j|) * C + 2 * d * 3 ^ d * (∑ j, |x j|) * C + |x i| +
        3 ^ d * (∑ j, |x j|) / 2 ≤ K₀ := by
      rw [hK₀]
      gcongr
    have hB : ((∑ j, |x j|) * C + 2 * d * 3 ^ d * (∑ j, |x j|) * C + |x i| +
        3 ^ d * (∑ j, |x j|) / 2) / √((3 : ℝ) ^ n) ≤ K₀ * s := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_right hA hs0
    have he := exp_neg_mul_three_pow_le_one_div_sqrt hc n
    have hE : |x i| * C * Real.exp (-c * (3 : ℝ) ^ n) ≤ R * C * (1 / c * s) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hxi hC) he (Real.exp_pos _).le (by positivity)
    have hKs : K * s = K₀ * s + R * C * (1 / c * s) := by
      rw [hK]
      ring
    linarith
  unfold cubeOmegaD
  have hsumK : -(d * K * s) = ∑ _i : Fin d, -(K * s) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [hsumK]
  exact Finset.sum_le_sum fun i _ => hterm i

/-- **Geometric decay of `D_n` from the bound of Lemma 5.9** (Armstrong and Dario, Steps 2 and 3
of the proof of Lemma 5.10, every dimension `d ≥ 2`). -/
theorem exists_cubeOmegaD_le_pow_of_decay [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) {C₉ σ₉ ρ₉ : ℝ} {N₉ : ℕ} (hC₉ : 0 ≤ C₉)
    (hσ₉ : 0 ≤ σ₉) (hσ₉1 : σ₉ < 1) (hρ₉ : 0 ≤ ρ₉) (hρ₉1 : ρ₉ < 1)
    (h59 : ∀ n, N₉ ≤ n → cubeOmegaD (d := d) p n ≤
      C₉ * σ₉ ^ n + C₉ * ∑ l ∈ Finset.range (n + 1), ρ₉ ^ (n - l) * cubeTau (d := d) p l) :
    ∃ K l : ℝ, 0 < l ∧ l < 1 ∧ ∃ N : ℕ, ∀ n, N ≤ n → cubeOmegaD (d := d) p n ≤ K * l ^ n := by
  obtain ⟨c, hc, C₁, hC₁, N₁, h1⟩ := exists_cubeOmegaD_succ_le hd hpc
  obtain ⟨C₂, hC₂, N₂, h2⟩ := exists_neg_le_cubeOmegaD hd hpc
  set r := 1 / √(√(3 : ℝ)) with hrdef
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := one_div_sqrt_sqrt_three_lt_one
  have hρs : √ρ₉ < 1 := by
    rw [show (1 : ℝ) = √1 from Real.sqrt_one.symm]
    exact Real.sqrt_lt_sqrt hρ₉ hρ₉1
  set σ := max (max σ₉ r) √ρ₉ with hσdef
  have hσ1 : σ < 1 := max_lt (max_lt hσ₉1 hr1) hρs
  have hσ0 : 0 ≤ σ := le_max_of_le_left (le_max_of_le_left hσ₉)
  have hσ₉σ : σ₉ ≤ σ := le_max_of_le_left (le_max_left _ _)
  have hrσ : r ≤ σ := le_max_of_le_left (le_max_right _ _)
  have hρσ : √ρ₉ ≤ σ := le_max_right _ _
  set μ := (1 + σ) / 2 with hμdef
  have hσμ : σ < μ := by rw [hμdef]; linarith
  have hμ1 : μ < 1 := by rw [hμdef]; linarith
  have hρμ : ρ₉ ≤ μ ^ 2 := by
    rw [← Real.sq_sqrt hρ₉]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (hρσ.trans hσμ.le) 2
  set C := C₁ + C₂ + C₉ with hCdef
  have hC : 0 ≤ C := by positivity
  set N := max N₁ (max N₂ N₉) with hNdef
  have hσn : ∀ n, 0 ≤ σ ^ n := fun n => pow_nonneg hσ0 n
  have hq : ∀ n, 1 / √(√((3 : ℝ) ^ n)) ≤ σ ^ n := fun n => by
    rw [one_div_sqrt_sqrt_three_pow]
    exact pow_le_pow_left₀ hr0 hrσ n
  have hh : ∀ n, 1 / √((3 : ℝ) ^ n) ≤ σ ^ n := fun n =>
    (le_of_eq_of_le (by rw [sqrt_pow_eq_pow_sqrt (by norm_num)])
      (one_div_sqrt_three_pow_le n)).trans (hq n)
  have h1' : ∀ n, N ≤ n → cubeOmegaD (d := d) p (n + 1) ≤
      cubeOmegaD (d := d) p n - c * cubeTau (d := d) p n + C * σ ^ n := fun n hn => by
    have h := h1 n (le_trans (le_max_left _ _) hn)
    have := mul_le_mul_of_nonneg_left (hq n) hC₁
    have : C₁ * σ ^ n ≤ C * σ ^ n := by
      rw [hCdef]
      nlinarith [hσn n]
    linarith
  have h2' : ∀ n, N ≤ n → -(C * σ ^ n) ≤ cubeOmegaD (d := d) p n := fun n hn => by
    have h := h2 n (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn)
    have := mul_le_mul_of_nonneg_left (hh n) hC₂
    have : C₂ * σ ^ n ≤ C * σ ^ n := by
      rw [hCdef]
      nlinarith [hσn n]
    linarith
  have h3' : ∀ n, N ≤ n → cubeOmegaD (d := d) p n ≤ C * σ ^ n +
      C * ∑ l ∈ Finset.range (n + 1), ρ₉ ^ (n - l) * cubeTau (d := d) p l := fun n hn => by
    have h := h59 n (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn)
    have hS : 0 ≤ ∑ l ∈ Finset.range (n + 1), ρ₉ ^ (n - l) * cubeTau (d := d) p l :=
      Finset.sum_nonneg fun l _ => mul_nonneg (pow_nonneg hρ₉ _) (cubeTau_nonneg p l)
    have a1 : σ₉ ^ n ≤ σ ^ n := pow_le_pow_left₀ hσ₉ hσ₉σ n
    have a2 : C₉ * σ₉ ^ n ≤ C * σ ^ n := by
      have := mul_le_mul_of_nonneg_left a1 hC₉
      rw [hCdef]
      nlinarith [hσn n]
    have a3 : C₉ * ∑ l ∈ Finset.range (n + 1), ρ₉ ^ (n - l) * cubeTau (d := d) p l ≤
        C * ∑ l ∈ Finset.range (n + 1), ρ₉ ^ (n - l) * cubeTau (d := d) p l :=
      mul_le_mul_of_nonneg_right (by rw [hCdef]; linarith) hS
    linarith
  obtain ⟨K, l, hl0, hl1, hK⟩ := exists_le_mul_pow_of_omega_iteration_of_ge N hc hC hσ0 hσμ hμ1
    hρ₉ hρμ (cubeTau_nonneg (d := d) p) h1' h2' h3'
  exact ⟨K, l, hl0, hl1, N, hK⟩

/-- **Geometric decay of `τ_n` from the bound of Lemma 5.9** (Armstrong and Dario, proof of
Lemma 5.10, every dimension `d ≥ 2`): `c τ_n ≤ D_n - D_{n+1} + C 3^{-n/4}`. -/
theorem exists_cubeTau_le_pow_of_decay [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) {C₉ σ₉ ρ₉ : ℝ} {N₉ : ℕ} (hC₉ : 0 ≤ C₉)
    (hσ₉ : 0 ≤ σ₉) (hσ₉1 : σ₉ < 1) (hρ₉ : 0 ≤ ρ₉) (hρ₉1 : ρ₉ < 1)
    (h59 : ∀ n, N₉ ≤ n → cubeOmegaD (d := d) p n ≤
      C₉ * σ₉ ^ n + C₉ * ∑ l ∈ Finset.range (n + 1), ρ₉ ^ (n - l) * cubeTau (d := d) p l) :
    ∃ K l : ℝ, 0 < l ∧ l < 1 ∧ ∃ N : ℕ, ∀ n, N ≤ n → cubeTau (d := d) p n ≤ K * l ^ n := by
  obtain ⟨K₁, l₁, hl₁0, hl₁1, N₁, hD⟩ :=
    exists_cubeOmegaD_le_pow_of_decay hd hpc hC₉ hσ₉ hσ₉1 hρ₉ hρ₉1 h59
  obtain ⟨c, hc, C₁, hC₁, N₂, h1⟩ := exists_cubeOmegaD_succ_le hd hpc
  obtain ⟨C₂, hC₂, N₃, h2⟩ := exists_neg_le_cubeOmegaD hd hpc
  set r := 1 / √(√(3 : ℝ)) with hrdef
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := one_div_sqrt_sqrt_three_lt_one
  set σ := max l₁ r with hσdef
  have hσ1 : σ < 1 := max_lt hl₁1 hr1
  have hσ0 : 0 < σ := lt_of_lt_of_le hl₁0 (le_max_left _ _)
  have hlσ : l₁ ≤ σ := le_max_left _ _
  have hrσ : r ≤ σ := le_max_right _ _
  have hq : ∀ n, 1 / √(√((3 : ℝ) ^ n)) ≤ σ ^ n := fun n => by
    rw [one_div_sqrt_sqrt_three_pow]
    exact pow_le_pow_left₀ hr0 hrσ n
  have hh : ∀ n, 1 / √((3 : ℝ) ^ n) ≤ σ ^ n := fun n =>
    (le_of_eq_of_le (by rw [sqrt_pow_eq_pow_sqrt (by norm_num)])
      (one_div_sqrt_three_pow_le n)).trans (hq n)
  refine ⟨(max K₁ 0 + C₂ + C₁) / c, σ, hσ0, hσ1, max N₁ (max N₂ N₃), fun n hn => ?_⟩
  have hn1 : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : N₂ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn3 : N₃ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have a1 := h1 n hn2
  have a2 := hD n hn1
  have a3 := h2 (n + 1) (by omega)
  have hσn : 0 ≤ σ ^ n := pow_nonneg hσ0.le n
  have b1 : K₁ * l₁ ^ n ≤ max K₁ 0 * σ ^ n := by
    have : l₁ ^ n ≤ σ ^ n := pow_le_pow_left₀ hl₁0.le hlσ n
    have hl : 0 ≤ l₁ ^ n := pow_nonneg hl₁0.le n
    calc K₁ * l₁ ^ n ≤ max K₁ 0 * l₁ ^ n := mul_le_mul_of_nonneg_right (le_max_left _ _) hl
      _ ≤ max K₁ 0 * σ ^ n := mul_le_mul_of_nonneg_left this (le_max_right _ _)
  have b2 : C₂ * (1 / √((3 : ℝ) ^ (n + 1))) ≤ C₂ * σ ^ n := by
    refine mul_le_mul_of_nonneg_left ((hh (n + 1)).trans ?_) hC₂
    exact pow_le_pow_of_le_one hσ0.le hσ1.le (Nat.le_succ n)
  have b3 : C₁ * (1 / √(√((3 : ℝ) ^ n))) ≤ C₁ * σ ^ n := mul_le_mul_of_nonneg_left (hq n) hC₁
  have key : c * cubeTau (d := d) p n ≤ (max K₁ 0 + C₂ + C₁) * σ ^ n := by
    have : (max K₁ 0 + C₂ + C₁) * σ ^ n = max K₁ 0 * σ ^ n + C₂ * σ ^ n + C₁ * σ ^ n := by
      ring
    linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hc]
  linarith

end Rigidity.Percolation
