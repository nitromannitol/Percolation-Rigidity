import LatticeProb.Site
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic

/-!
# A discrete Sobolev inequality with mixed differences

For a function `g` on `ℤ^d`, the mixed forward difference in the directions of a set `S` of
coordinates is `D_S g(y) = ∑_{U ⊆ S} (-1)^{|S| - |U|} g(y + ∑_{j ∈ U} e_j)` (`mixedDiff`); it is
the composition of the forward differences `D_j g(y) = g(y + e_j) - g(y)`, `j ∈ S`
(`mixedDiff_insert`). The discrete Sobolev inequality bounds the value of `g` at a corner `x₀` of
the box `x₀ + [0, n]^T` (the coordinates outside `T` fixed) by
`|g(x₀)| ≤ ∑_{S ⊆ T} (n + 1)^{-(|T| - |S|)} ∑_{y ∈ box} |D_S g(y)|`
(`abs_le_sum_mixedDiff`): in one direction, `g(x₀)` is the average over `k ≤ n` of
`g(x₀ + k e_i) - ∑_{j < k} D_i g(x₀ + j e_i)`, and the general case follows by induction on `T`.

With `T` all the coordinates, the mixed differences of order at most `d` of a discrete harmonic
function are bounded in `ℓ²` by iterated Caccioppoli inequalities, and the inequality gives the
interior `L^∞` bound of discrete harmonic functions by their normalized `ℓ²` norm, an ingredient
of the excess decay (`HarmonicRegularity`) of discrete harmonic functions on lattice balls.
-/

namespace Rigidity.Proofs.Regularity

open Finset LatticeProb

variable {d : ℕ}

/-- The vertex `∑_{j ∈ U} e_j`. -/
def shiftSum (U : Finset (Fin d)) : Fin d → ℤ := ∑ j ∈ U, unit j

/-- The mixed forward difference `D_S g(y) = ∑_{U ⊆ S} (-1)^{|S| - |U|} g(y + ∑_{j ∈ U} e_j)`. -/
def mixedDiff (S : Finset (Fin d)) (g : (Fin d → ℤ) → ℝ) (y : Fin d → ℤ) : ℝ :=
  ∑ U ∈ S.powerset, (-1 : ℝ) ^ (S.card - U.card) * g (y + shiftSum U)

theorem mixedDiff_empty (g : (Fin d → ℤ) → ℝ) (y : Fin d → ℤ) : mixedDiff ∅ g y = g y := by
  simp [mixedDiff, shiftSum]

theorem shiftSum_insert {U : Finset (Fin d)} {i : Fin d} (hi : i ∉ U) :
    shiftSum (insert i U) = unit i + shiftSum U :=
  Finset.sum_insert hi

/-- Adding a direction to a mixed difference takes one more forward difference. -/
theorem mixedDiff_insert {S : Finset (Fin d)} {i : Fin d} (hi : i ∉ S) (g : (Fin d → ℤ) → ℝ)
    (y : Fin d → ℤ) :
    mixedDiff (insert i S) g y = mixedDiff S g (y + unit i) - mixedDiff S g y := by
  rw [mixedDiff, Finset.sum_powerset_insert hi]
  have h1 : ∀ U ∈ S.powerset, (-1 : ℝ) ^ ((insert i S).card - U.card) * g (y + shiftSum U) =
      -((-1 : ℝ) ^ (S.card - U.card) * g (y + shiftSum U)) := by
    intro U hU
    have hUS := card_le_card (mem_powerset.1 hU)
    rw [card_insert_of_notMem hi, Nat.succ_sub hUS, pow_succ]
    ring
  have h2 : ∀ U ∈ S.powerset, (-1 : ℝ) ^ ((insert i S).card - (insert i U).card) *
      g (y + shiftSum (insert i U)) =
        (-1 : ℝ) ^ (S.card - U.card) * g ((y + unit i) + shiftSum U) := by
    intro U hU
    have hiU : i ∉ U := fun h => hi (mem_powerset.1 hU h)
    rw [card_insert_of_notMem hi, card_insert_of_notMem hiU, Nat.add_sub_add_right,
      shiftSum_insert hiU, add_assoc]
  rw [sum_congr rfl h1, sum_congr rfl h2, sum_neg_distrib, mixedDiff, mixedDiff]
  ring

/-- Mixed differences commute with translations. -/
theorem mixedDiff_comp_add (S : Finset (Fin d)) (g : (Fin d → ℤ) → ℝ) (v y : Fin d → ℤ) :
    mixedDiff S (fun x => g (x + v)) y = mixedDiff S g (y + v) := by
  simp only [mixedDiff]
  refine sum_congr rfl fun U _ => ?_
  rw [add_right_comm]

/-- Mixed differences are linear. -/
theorem mixedDiff_sub (S : Finset (Fin d)) (g₁ g₂ : (Fin d → ℤ) → ℝ) (y : Fin d → ℤ) :
    mixedDiff S (fun x => g₁ x - g₂ x) y = mixedDiff S g₁ y - mixedDiff S g₂ y := by
  simp only [mixedDiff, mul_sub, sum_sub_distrib]

/-- The mixed difference of the forward difference `D_i g` in the directions `S ∌ i`. -/
theorem mixedDiff_forwardDiff {S : Finset (Fin d)} {i : Fin d} (hi : i ∉ S)
    (g : (Fin d → ℤ) → ℝ) (y : Fin d → ℤ) :
    mixedDiff S (fun x => g (x + unit i) - g x) y = mixedDiff (insert i S) g y := by
  rw [mixedDiff_sub, mixedDiff_comp_add, mixedDiff_insert hi]

end Rigidity.Proofs.Regularity
