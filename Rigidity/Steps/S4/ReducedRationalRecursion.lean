import Rigidity.Draft.Section4Statements
import Rigidity.Frozen.GadgetNumDenomRecsV1
import Rigidity.Support.GadgetArithmeticConsumer

/-!
# Lemma 4.3 from Lemma 4.2

Lemma 4.3 (paper L1204-1275 of the corrected draft) follows from Lemma 4.2 by `step:4.3-induction`:
induction on `n`, with the recursion of Lemma 4.2 and the paired identities of Lemma 4.4
(`Rigidity.Gadget.numDenomRecs`). The denominators stay positive by `Gadget.arithmetic_data`.
-/

namespace Rigidity.Steps.S4

open Rigidity.Section4 Rigidity.Gadget

/-- Step `step:4.3-induction`: the effective resistances of Lemma 4.2 are the fractions
`R_n = A_{n+1}/B_n`. -/
theorem effectiveResistance_eq_A_div_B {R : ℕ → ℝ} (h1 : R 1 = 3)
    (hrec : ∀ n : ℕ, 1 ≤ n → R (n + 1) = (3 * R n + 2) / (R n + 1)) :
    ∀ n : ℕ, 1 ≤ n → R n = (A (n + 1) : ℝ) / (B n : ℝ) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    obtain ⟨hA2, hB1, -⟩ := arithmetic_one
    rw [h1, hA2, hB1]
    norm_num
  | succ n hn ih =>
    obtain ⟨hBn, -⟩ := arithmetic_data n hn
    have hA := (A_succ_pos_and_B_nonneg n).1
    obtain ⟨hBs, hAs⟩ := numDenomRecs n
    have hBn' : (0 : ℝ) < B n := by exact_mod_cast hBn
    have hA' : (0 : ℝ) < A (n + 1) := by exact_mod_cast hA
    have hBs' : (B (n + 1) : ℝ) = A (n + 1) + B n := by exact_mod_cast hBs.symm
    have hAs' : (A (n + 1 + 1) : ℝ) = 3 * A (n + 1) + 2 * B n := by exact_mod_cast hAs.symm
    rw [hrec n hn, ih, hBs', hAs']
    field_simp

/-- Lemma 4.3 follows from Lemma 4.2. -/
theorem reducedRationalRecursion_of_effectiveResistanceRecurrence
    (h42 : Section4.EffectiveResistanceRecurrenceStmt) : Section4.ReducedRationalRecursionStmt := by
  obtain ⟨-, R, hR, h1, hrec⟩ := h42
  intro n hn h hh
  rw [← hR n hn h hh]
  exact effectiveResistance_eq_A_div_B h1 hrec n hn

end Rigidity.Steps.S4
