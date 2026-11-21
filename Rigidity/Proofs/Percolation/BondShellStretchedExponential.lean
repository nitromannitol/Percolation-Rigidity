import Rigidity.Proofs.Percolation.BondShellSummation
import LatticeProb.Analysis.StretchedExponentialSummability

/-!
# Stretched-exponential summation over planar bond shells

Polynomially growing planar shells are summable against stretched-exponential weights, with a
bound proportional to the volume of the inner cube.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation

/-- The planar shell volume is bounded by the product of inner volume and a quadratic shell weight. -/
theorem planar_shell_card_factor_le (R n : ℕ) :
    ((2 * 2 * (2 * (R + n + 1) + 1) ^ 2 : ℕ) : ℝ) ≤
      36 * ((R : ℝ) + 1) ^ 2 * ((n : ℝ) + 1) ^ 2 := by
  have hR : 0 ≤ (R : ℝ) := Nat.cast_nonneg _
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hprod : 0 ≤ (R : ℝ) * n := mul_nonneg hR hn
  have h : 2 * ((R : ℝ) + n + 1) + 1 ≤ 3 * ((R : ℝ) + 1) * ((n : ℝ) + 1) := by
    nlinarith
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * ((R : ℝ) + n + 1) + 1) h 2
  push_cast
  nlinarith

/-- Quadratic weights times stretched-exponential decay form a summable sequence. -/
theorem summable_shift_square_exp_sqrt (c : ℝ) (hc : 0 < c) :
    Summable fun n : ℕ => ((n : ℝ) + 1) ^ 2 * Real.exp (-c * Real.sqrt n) := by
  have h0 := LatticeProb.summable_pow_mul_exp_neg_sqrt c hc 0
  have h1 := LatticeProb.summable_pow_mul_exp_neg_sqrt c hc 1
  have h2 := LatticeProb.summable_pow_mul_exp_neg_sqrt c hc 2
  have h := h2.add ((h1.mul_left 2).add h0)
  apply h.congr
  intro n
  simp only [pow_zero, pow_one, one_mul]
  ring

/-- A planar bond function with stretched-exponential shell decay is summable at volume scale. -/
theorem summable_planar_bond_shells (z : Vertex 2) (R : ℕ) (f : Bond 2 → ℝ)
    (K c : ℝ) (hK : 0 ≤ K) (hc : 0 < c) (hf : ∀ e, 0 ≤ f e)
    (hglobal : ∀ e, f e ≤ K)
    (hdecay : ∀ n, 1 ≤ n → ∀ e ∈ bondShell 2 z R n,
      f e ≤ K * Real.exp (-c * Real.sqrt n)) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ 2 * Real.exp (-c * Real.sqrt n)) ∧
    Summable f ∧
      (∑' e, f e) ≤ 36 * ((R : ℝ) + 1) ^ 2 * K *
        (1 + ∑' n : ℕ, ((n : ℝ) + 1) ^ 2 * Real.exp (-c * Real.sqrt n)) := by
  classical
  let q : ℕ → ℝ := fun n => ((n : ℝ) + 1) ^ 2 * Real.exp (-c * Real.sqrt n)
  let g : ℕ → ℝ := fun n => K * Real.exp (-c * Real.sqrt n)
  let H : ℕ → ℝ := fun n =>
    ((2 * 2 * (2 * (R + n + 1) + 1) ^ 2 : ℕ) : ℝ) * g n
  let C : ℝ := 36 * ((R : ℝ) + 1) ^ 2 * K
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hq (n : ℕ) : 0 ≤ q n := by dsimp [q]; positivity
  have hqsum : Summable q := summable_shift_square_exp_sqrt c hc
  have hH (n : ℕ) : 0 ≤ H n := by dsimp [H, g]; positivity
  have hHbound (n : ℕ) : H n ≤ C * q n := by
    have h := planar_shell_card_factor_le R n
    dsimp only [H, g, C, q]
    calc
      _ ≤ (36 * ((R : ℝ) + 1) ^ 2 * ((n : ℝ) + 1) ^ 2) *
          (K * Real.exp (-c * Real.sqrt n)) :=
        mul_le_mul_of_nonneg_right h (mul_nonneg hK (Real.exp_pos _).le)
      _ = _ := by ring
  have hHsum : Summable H := Summable.of_nonneg_of_le hH hHbound (hqsum.mul_left C)
  have hbound : ∀ n e, e ∈ bondShell 2 z R n → f e ≤ g n := by
    intro n e he
    by_cases hn : n = 0
    · subst n
      simpa [g] using hglobal e
    · exact hdecay n (Nat.pos_of_ne_zero hn) e he
  have ⟨hfs, hsum⟩ := summable_of_bondShell_bound 2 z R f g hf
    (fun n => mul_nonneg hK (Real.exp_pos _).le) hHsum hbound
  have hbase : (∑ e ∈ bondBox 2 z R, f e) ≤ C := by
    have hcard := card_bondsIncidentTo_le 2 (Rigidity.Proofs.S3.cubeFinset z R)
    have hvolume : ((bondBox 2 z R).card : ℝ) ≤ 36 * ((R : ℝ) + 1) ^ 2 := by
      have h := planar_shell_card_factor_le R 0
      have h' : ((bondBox 2 z R).card : ℝ) ≤
          ((2 * 2 * (2 * (R + 0 + 1) + 1) ^ 2 : ℕ) : ℝ) := by
        have hn : (bondBox 2 z R).card ≤ 2 * 2 * (2 * (R + 0 + 1) + 1) ^ 2 := by
          change (bondsIncidentTo 2 (Rigidity.Proofs.S3.cubeFinset z R)).card ≤ _
          rw [Rigidity.Proofs.S3.card_cubeFinset] at hcard
          exact hcard.trans (by gcongr; omega)
        exact_mod_cast hn
      exact h'.trans (by simpa using h)
    calc
      _ ≤ ∑ _e ∈ bondBox 2 z R, K := Finset.sum_le_sum fun e _ => hglobal e
      _ = ((bondBox 2 z R).card : ℝ) * K := by simp
      _ ≤ C := mul_le_mul_of_nonneg_right hvolume hK
  have hsumH : (∑' n, H n) ≤ C * ∑' n, q n := by
    calc
      _ ≤ ∑' n, C * q n := hHsum.tsum_le_tsum hHbound (hqsum.mul_left C)
      _ = _ := tsum_mul_left
  refine ⟨hqsum, hfs, hsum.trans ?_⟩
  calc
    _ ≤ C + C * ∑' n, q n := add_le_add hbase hsumH
    _ = _ := by dsimp only [C, q]; ring

end Rigidity.Percolation
