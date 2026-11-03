import Rigidity.Proofs.S4.UnitVoltage
import Rigidity.Support.OpenGadgetTransfer
import Rigidity.Support.GadgetArithmeticConsumer

/-!
# The recursion of the effective resistance of the gadget network

Step `step:4.2-recursion` (paper L1162-1200 of the corrected draft, Figures elec1-elec4). Write
`D` for the top rung difference of a function harmonic off the two terminals of the gadget of
height `n`. Kirchhoff's equations on the rungs, eliminated from the top down, give the rung
difference at height `n - k` as `A_{k+1} D` and the terminal gap as `A_{n+1} D`
(`OpenGadget.terminal_gap_real`). Kirchhoff's equations on the left rail, eliminated from the top
down, give the voltage drop along each left rail edge as the sum of the rung currents above it,
`B_{k+1} D`, and the unit current out of the source as `B_n D`. For the unit voltage this is
`h(a) = B_n / A_{n+1}`, so the effective resistance is `R_n = A_{n+1} / B_n`, and the paired
recursions `B_{n+1} = A_{n+1} + B_n`, `A_{n+2} = 3 A_{n+1} + 2 B_n` give
`R_{n+1} = (3 R_n + 2)/(R_n + 1)`.
-/

namespace Rigidity.Proofs.S4

open LatticeProb.Network LatticeProb.Network.OpenLadder Rigidity.Section4

/-- The real form of the denominator recursion `B_{k+1} = A_{k+1} + B_k`. -/
theorem B_real_succ (k : ℕ) :
    (Gadget.B (k + 1) : ℝ) = (Gadget.A (k + 1) : ℝ) + (Gadget.B k : ℝ) := by
  exact_mod_cast (Gadget.numDenomRecs k).1.symm

/-- The rung difference at height `n - k` is `A_{k+1}` times the top rung difference. -/
theorem rungDifference_eq_A {n : ℕ} {u : Vertex (n : ℤ) → ℝ} (hu : Harmonic u) (k : ℕ)
    (hk : k < n) :
    rungDifference u ((n : ℤ) - (k : ℤ)) ⟨by omega, by omega⟩ =
      (Gadget.A (k + 1) : ℝ) * rungDifference u n ⟨by omega, by omega⟩ :=
  rung_difference_transfer (fun k => (Gadget.A k : ℝ))
    (by rw [Gadget.A_zero]; norm_num) (by rw [Gadget.A_one]; norm_num)
    OpenGadget.A_real_recurrence hu k hk

/-- Kirchhoff's equations on the left rail, from the top down: the voltage drop along the left
rail edge from height `n - k - 1` to height `n - k` is `B_{k+1}` times the top rung
difference. -/
theorem left_rail_difference_transfer {n : ℕ} {u : Vertex (n : ℤ) → ℝ} (hu : Harmonic u)
    (k : ℕ) (hk : k + 1 < n) :
    u (left n ((n : ℤ) - (k : ℤ)) ⟨by omega, by omega⟩) -
        u (left n ((n : ℤ) - ((k + 1 : ℕ) : ℤ)) ⟨by omega, by omega⟩) =
      (Gadget.B (k + 1) : ℝ) * rungDifference u n ⟨by omega, by omega⟩ := by
  induction k with
  | zero =>
    have ht := kirchhoff_left_top hu (n := n) (by omega)
    simp only [Nat.cast_zero, sub_zero, Nat.zero_add, Nat.cast_one, Gadget.B_one,
      Int.cast_one, one_mul]
    unfold rungDifference
    linarith
  | succ k ih =>
    have hm := kirchhoff_left_middle (j := (n : ℤ) - ((k + 1 : ℕ) : ℤ)) hu (by omega)
      (by omega)
    have hlo : (n : ℤ) - ((k + 1 : ℕ) : ℤ) - 1 = (n : ℤ) - ((k + 1 + 1 : ℕ) : ℤ) := by omega
    have hhi : (n : ℤ) - ((k + 1 : ℕ) : ℤ) + 1 = (n : ℤ) - (k : ℤ) := by omega
    simp only [hlo, hhi] at hm
    have hr := rungDifference_eq_A hu (k + 1) (by omega)
    have ih' := ih (by omega)
    rw [B_real_succ (k + 1)]
    unfold rungDifference at hr ih' ⊢
    linear_combination hm + hr + ih'

/-- Kirchhoff's equation at the left bottom site: the unit current out of the source is
`B_n` times the top rung difference. -/
theorem left_one_sub_source {n : ℕ} (hn : 1 ≤ n) {u : Vertex (n : ℤ) → ℝ} (hu : Harmonic u) :
    u (left n 1 ⟨le_rfl, by exact_mod_cast hn⟩) - u (source n) =
      (Gadget.B n : ℝ) * rungDifference u n ⟨by omega, by omega⟩ := by
  by_cases hn1 : n = 1
  · subst n
    have hl : 2 * u (left ((1 : ℕ) : ℤ) 1 ⟨le_rfl, le_rfl⟩) =
        u (source ((1 : ℕ) : ℤ)) + u (right ((1 : ℕ) : ℤ) 1 ⟨le_rfl, le_rfl⟩) :=
      kirchhoff_left_one hu
    have hD : rungDifference u ((1 : ℕ) : ℤ) ⟨le_rfl, le_rfl⟩ =
        u (right ((1 : ℕ) : ℤ) 1 ⟨le_rfl, le_rfl⟩) - u (left ((1 : ℕ) : ℤ) 1 ⟨le_rfl, le_rfl⟩) :=
      rfl
    rw [Gadget.B_one, Int.cast_one, one_mul, hD]
    linarith
  have hb := kirchhoff_left_bottom hu (n := n) (by omega)
  have hv := left_rail_difference_transfer hu (n - 2) (by omega)
  have hr := rungDifference_eq_A hu (n - 1) (by omega)
  have hi2 : (n : ℤ) - ((n - 2 : ℕ) : ℤ) = 2 := by omega
  have hi1' : (n : ℤ) - ((n - 1 : ℕ) : ℤ) = 1 := by omega
  have hn2 : n - 2 + 1 = n - 1 := by omega
  have hn1' : n - 1 + 1 = n := by omega
  simp only [hi2, hn2, hi1'] at hv
  simp only [hi1', hn1'] at hr
  have hB := B_real_succ (n - 1)
  rw [hn1'] at hB
  rw [hB]
  unfold rungDifference at hr hv ⊢
  linear_combination hb + hr + hv

/-- The unit current of the gadget of height `n ≥ 1` is `h(a) = B_n / A_{n+1}`. -/
theorem unitVoltage_siteA {n : ℕ} (hn : 1 ≤ n) {h : Vertex (n : ℤ) → ℝ}
    (hh : IsUnitVoltage n h) :
    h (siteA n hn) = (Gadget.B n : ℝ) / (Gadget.A (n + 1) : ℝ) := by
  obtain ⟨hs, ht, hharm⟩ := (isUnitVoltage_iff h).1 hh
  have hg := OpenGadget.terminal_gap_real hn hharm
  have hc := left_one_sub_source hn hharm
  rw [hs, ht] at hg
  rw [hs] at hc
  have hA : (0 : ℝ) < Gadget.A (n + 1) := by
    exact_mod_cast (Gadget.A_succ_pos_and_B_nonneg n).1
  rw [eq_div_iff hA.ne', siteA]
  linear_combination hc * (Gadget.A (n + 1) : ℝ) - (Gadget.B n : ℝ) * hg

/-- Step `step:4.2-recursion`: `R_{n+1} = (3 R_n + 2)/(R_n + 1)` for the effective resistances
`R_n = 1/h_n(a)`. -/
theorem resistanceRecursion : Steps.S4.ResistanceRecursionStep := by
  intro n hn h h' hh hh'
  rw [unitVoltage_siteA hn hh, unitVoltage_siteA (Nat.le_add_left 1 n) hh']
  have hB : (0 : ℝ) < Gadget.B n := by exact_mod_cast (Gadget.arithmetic_data n hn).1
  have hA : (0 : ℝ) < Gadget.A (n + 1) := by
    exact_mod_cast (Gadget.A_succ_pos_and_B_nonneg n).1
  have hB' : (Gadget.B (n + 1) : ℝ) = Gadget.A (n + 1) + Gadget.B n := B_real_succ n
  have hA' : (Gadget.A (n + 1 + 1) : ℝ) = 3 * Gadget.A (n + 1) + 2 * Gadget.B n := by
    exact_mod_cast (Gadget.numDenomRecs n).2.symm
  rw [hB', hA']
  field_simp

end Rigidity.Proofs.S4
