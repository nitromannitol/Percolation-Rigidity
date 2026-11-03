import Rigidity.Draft.Section4Statements

/-!
# Lemma 4.2: the steps of the effective resistance recurrence

Lemma 4.2 (paper L1162-1200 of the corrected draft) is carved into three steps: the unit voltage of
the gadget network exists and is unique, the effective resistance `R_1 = 1/h_1(a)` of the gadget of
height one is three, and the series-parallel recursion `R_{n+1} = (3 R_n + 2)/(R_n + 1)`. The
reduction defines `R_n = 1/h_n(a)` from the unique unit voltage `h_n` and checks the three clauses
of the lemma.
-/

namespace Rigidity.Steps.S4

open Rigidity.Section4

/-- Step `step:4.2-unique-voltage`: on the finite connected gadget network of every height
`n ≥ 1` there is exactly one unit voltage. -/
def UnitVoltageExistsUniqueStep : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃! h : LatticeProb.Network.OpenLadder.Vertex n → ℝ, Section4.IsUnitVoltage n h

/-- Step `step:4.2-current` at height one (paper L1170-1175): the effective resistance of the
gadget of height one, the reciprocal of the unit current `h(a)`, is `R_1 = 3`. -/
def ResistanceBaseStep : Prop :=
  ∀ h : LatticeProb.Network.OpenLadder.Vertex ((1 : ℕ) : ℤ) → ℝ,
    Section4.IsUnitVoltage ((1 : ℕ) : ℤ) h → 1 / h (Section4.siteA 1 le_rfl) = 3

/-- Step `step:4.2-recursion` (Figures elec1-elec4): the series and parallel laws give
`R_{n+1} = (3 R_n + 2)/(R_n + 1)` for the effective resistances `R_n = 1/h_n(a)`. -/
def ResistanceRecursionStep : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n) (h : LatticeProb.Network.OpenLadder.Vertex (n : ℤ) → ℝ)
    (h' : LatticeProb.Network.OpenLadder.Vertex ((n + 1 : ℕ) : ℤ) → ℝ),
    Section4.IsUnitVoltage (n : ℤ) h → Section4.IsUnitVoltage ((n + 1 : ℕ) : ℤ) h' →
      1 / h' (Section4.siteA (n + 1) (Nat.le_add_left 1 n)) =
        (3 * (1 / h (Section4.siteA n hn)) + 2) / (1 / h (Section4.siteA n hn) + 1)

/-- The effective resistance `R_n = 1/h_n(a)` of the gadget of height `n ≥ 1`, where `h_n` is the
unit voltage chosen by `UnitVoltageExistsUniqueStep`; it is set to zero at `n = 0`. -/
noncomputable def effectiveResistance (hU : UnitVoltageExistsUniqueStep) (n : ℕ) : ℝ :=
  if hn : 1 ≤ n then 1 / (hU n hn).exists.choose (siteA n hn) else 0

/-- Every unit voltage computes the effective resistance. -/
theorem effectiveResistance_eq (hU : UnitVoltageExistsUniqueStep) (n : ℕ) (hn : 1 ≤ n)
    (h : LatticeProb.Network.OpenLadder.Vertex n → ℝ) (hh : IsUnitVoltage n h) :
    effectiveResistance hU n = 1 / h (siteA n hn) := by
  rw [effectiveResistance, dif_pos hn, (hU n hn).unique hh (hU n hn).exists.choose_spec]

/-- Lemma 4.2 follows from its three steps, with `R_n = 1/h_n(a)`. -/
theorem effectiveResistanceRecurrence_of_steps (hU : UnitVoltageExistsUniqueStep)
    (hB : ResistanceBaseStep) (hR : ResistanceRecursionStep) :
    Section4.EffectiveResistanceRecurrenceStmt := by
  refine ⟨hU, effectiveResistance hU, effectiveResistance_eq hU, ?_, fun n hn => ?_⟩
  · have hspec := (hU 1 le_rfl).exists.choose_spec
    rw [effectiveResistance_eq hU 1 le_rfl _ hspec]
    exact hB _ hspec
  · have hspec := (hU n hn).exists.choose_spec
    have hspec' := (hU (n + 1) (Nat.le_add_left 1 n)).exists.choose_spec
    rw [effectiveResistance_eq hU n hn _ hspec,
      effectiveResistance_eq hU (n + 1) (Nat.le_add_left 1 n) _ hspec']
    exact hR n hn _ _ hspec hspec'

end Rigidity.Steps.S4
