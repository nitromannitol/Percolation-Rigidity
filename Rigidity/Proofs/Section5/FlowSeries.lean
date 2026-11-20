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

/-- The average of a nonempty finite family of unit flows is a unit flow. -/
theorem isFlow_average_unit_divergence {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (θ : ι → V → V → ℝ) (a b : V)
    (hflow : ∀ i ∈ s, IsFlow G (θ i))
    (hdiv : ∀ i ∈ s, ∀ z, divergence G (θ i) z =
      (if z = a then 1 else 0) - (if z = b then 1 else 0)) :
    IsFlow G (fun x y => (∑ i ∈ s, θ i x y) / s.card) ∧
      ∀ z, divergence G (fun x y => (∑ i ∈ s, θ i x y) / s.card) z =
        (if z = a then 1 else 0) - (if z = b then 1 else 0) := by
  have hs0 : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_ne_zero
  constructor
  · refine ⟨fun x y => ?_, fun x y hxy => ?_⟩
    · simp only [← Finset.sum_neg_distrib, ← neg_div]
      congr 1
      exact Finset.sum_congr rfl fun i hi => (hflow i hi).antisymm x y
    · have hzero : ∑ i ∈ s, θ i x y = 0 :=
        Finset.sum_eq_zero fun i hi => (hflow i hi).zero_of_not_adj hxy
      rw [hzero, zero_div]
  · intro z
    unfold divergence
    rw [← Finset.sum_div, Finset.sum_comm]
    have hsum : ∑ i ∈ s, ∑ y ∈ G.neighborFinset z, θ i z y =
        ∑ _i ∈ s, ((if z = a then 1 else 0) - (if z = b then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hdiv i hi z
    rw [hsum]
    simp only [Finset.sum_const, nsmul_eq_mul]
    exact mul_div_cancel_left₀ _ hs0

/-- The energy of an averaged flow is bounded by the squared average absolute edge load. -/
theorem flowEnergyOn_average_le {ι : Type*} (s : Finset ι) (θ : ι → V → V → ℝ)
    (S : Finset V) :
    flowEnergyOn G (unitCond G) S (fun x y => (∑ i ∈ s, θ i x y) / s.card) ≤
      ∑ x ∈ S, ∑ y ∈ G.neighborFinset x, ((∑ i ∈ s, |θ i x y|) / s.card) ^ 2 := by
  unfold flowEnergyOn
  apply Finset.sum_le_sum
  intro x hx
  apply Finset.sum_le_sum
  intro y hy
  have hadj : G.Adj x y := (SimpleGraph.mem_neighborFinset _ _ _).mp hy
  have hcard : (0 : ℝ) ≤ s.card := Nat.cast_nonneg _
  have habs : |(∑ i ∈ s, θ i x y) / s.card| ≤ (∑ i ∈ s, |θ i x y|) / s.card := by
    rw [abs_div, abs_of_nonneg hcard]
    exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hcard
  have hnonneg : 0 ≤ (∑ i ∈ s, |θ i x y|) / s.card := by positivity
  have hsquare : ((∑ i ∈ s, θ i x y) / s.card) ^ 2 ≤
      ((∑ i ∈ s, |θ i x y|) / s.card) ^ 2 := by
    nlinarith [sq_abs ((∑ i ∈ s, θ i x y) / s.card), abs_nonneg
      ((∑ i ∈ s, θ i x y) / s.card)]
  simpa [unitCond, hadj] using hsquare

end Rigidity.Proofs.Section5
