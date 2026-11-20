import LatticeProb.Network.Flow

/-!
# Series composition of flows

Adding flows composes their divergences, and its energy is bounded by twice the sum of
their energies.
-/

open LatticeProb.Network
open scoped Classical

namespace Rigidity.Proofs.Section5

variable {V : Type*} (G : SimpleGraph V) [G.LocallyFinite]

omit [G.LocallyFinite] in
/-- The sum of two flows is a flow. -/
theorem isFlow_add (θ η : V → V → ℝ) (hθ : IsFlow G θ) (hη : IsFlow G η) :
    IsFlow G (fun x y => θ x y + η x y) := by
  refine ⟨fun x y => ?_, fun x y hxy => ?_⟩
  · rw [hθ.antisymm x y, hη.antisymm x y, neg_add]
  · rw [hθ.zero_of_not_adj hxy, hη.zero_of_not_adj hxy, add_zero]

/-- Divergence distributes over sums of flows. -/
theorem divergence_add (θ η : V → V → ℝ) (x : V) :
    divergence G (fun x y => θ x y + η x y) x =
      divergence G θ x + divergence G η x := by
  simp only [divergence, Finset.sum_add_distrib]

/-- The energy of a sum is at most twice the sum of its energies. -/
theorem flowEnergyOn_add_le (c : V → V → ℝ) (hc : IsCond G c)
    (S : Finset V) (θ η : V → V → ℝ) :
    flowEnergyOn G c S (fun x y => θ x y + η x y) ≤
      2 * (flowEnergyOn G c S θ + flowEnergyOn G c S η) := by
  unfold flowEnergyOn
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x hx
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y hy
  have hsq : (θ x y + η x y) ^ 2 ≤ 2 * (θ x y ^ 2 + η x y ^ 2) := by
    nlinarith [sq_nonneg (θ x y - η x y)]
  calc
    _ ≤ (2 * (θ x y ^ 2 + η x y ^ 2)) / c x y :=
      div_le_div_of_nonneg_right hsq (hc.nonneg x y)
    _ = _ := by ring

/-- Flows from `a` to `b` and from `b` to `c` compose to a flow from `a` to `c`. -/
theorem isFlow_add_unit_divergence (θ η : V → V → ℝ) (hθ : IsFlow G θ) (hη : IsFlow G η)
    (a b c : V)
    (hθdiv : ∀ z, divergence G θ z = (if z = a then 1 else 0) - (if z = b then 1 else 0))
    (hηdiv : ∀ z, divergence G η z = (if z = b then 1 else 0) - (if z = c then 1 else 0)) :
    IsFlow G (fun x y => θ x y + η x y) ∧
      ∀ z, divergence G (fun x y => θ x y + η x y) z =
        (if z = a then 1 else 0) - (if z = c then 1 else 0) := by
  refine ⟨isFlow_add G θ η hθ hη, fun z => ?_⟩
  rw [divergence_add, hθdiv, hηdiv]
  ring

end Rigidity.Proofs.Section5
