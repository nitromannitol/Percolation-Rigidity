import Rigidity.Steps.Section5.DirectionFree

/-!
# The large-gradient estimate from a planar minimal scale

A dimension-two cone comparison suffices for the large-gradient argument.
-/

open MeasureTheory Filter Topology LatticeProb.Percolation

namespace Rigidity.Steps.Section5

open Rigidity.Section5

/-- The large-gradient estimate from the dimension-two minimal scale. -/
theorem largeGradientSensitive_of_planar_scale {p : unitInterval} {f : Vertex 2 → ℤ}
    (h520 : BoundarySizeStmt p f) (h524 : LongPathRenormalizedStmt p)
    (h525 : GoodEventLowerBoundStmt p) (h528 : FiniteBranchesStmt p f)
    (hM : ∀ r : ℕ, ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω,
      ∃ M : ℝ, ∀ ℓ, IsCorrectedPlane (uniqueInfiniteComponent h) (Pi.single 0 1) ℓ →
        ∀ x y : uniqueInfiniteComponent h, |x.val 1| ≤ x.val 0 → M ≤ x.val 0 →
          (y.val ∈ cube r ∨ y.val ∈ negativeLine) → ℓ y < ℓ x) (hB : ExplorationBlockStep)
    (hH : ExplorationHolesStep) (hR : RootBlockStep) (hL : LeafSensitiveStep)
    (hF : FluxBalanceStep) (hG : FluxGrowthStep) (hX : GreedyExplorationStep)
    (hA : ExplorationAssemblyStep) (hT : TerminationWindowStep) :
    LargeGradientSensitiveStmt p f := by
  intro hfin
  obtain ⟨Cf, hCf, h520ae⟩ := h520 hfin
  obtain ⟨Cbr, h528ae⟩ := h528 hfin
  obtain ⟨R₁, hR₁⟩ := h524 Cf
  obtain ⟨c₁, hc₁, hLP⟩ := hR₁ (max R₁ 1) (le_max_left _ _)
  set R := max R₁ 1 with hR_def
  set W := ⌈4 * R ^ 2⌉₊ with hW_def
  set Cχ := max 1 (128 * (2 * W + 1) * Real.exp Cbr / c₁) with hCχ_def
  obtain ⟨c, hc, h25⟩ := h525 Cχ (le_max_left _ _)
  obtain ⟨K₀', hK₀'⟩ := h25 Cf R c₁ hLP
  set K₀ := max (max K₀' 1) 1 with hK₀_def
  set C₀ := max (max K₀ (W + 1)) 2 with hC₀_def
  have hK₀1 : 1 ≤ K₀ := (le_max_right _ _).trans (le_max_left _ _)
  refine ⟨Cf, R, c₁, Cχ, K₀, C₀, ?_, ?_⟩
  · obtain ⟨A, hAG, hAm, hAc⟩ := hK₀' K₀ ((le_max_left _ _).trans (le_max_left _ _)) 0
    exact ⟨A, hAG, hAm, (ENNReal.ofReal_pos.2 hc).trans_le hAc⟩
  · filter_upwards [hM (Cf / 2), h528ae, h520ae] with ω hMω h528ω h520ω
    obtain ⟨h, M₂, h528c⟩ := h528ω
    obtain ⟨M₁, hM₁⟩ := hMω h
    obtain ⟨_, h520c⟩ := h520ω
    refine ⟨h, max M₁ M₂, fun u hu hsupp ℓ hℓ x₀ hcone hMx hGω => ?_⟩
    obtain ⟨⟨⟨_, hG1⟩, ⟨_, hG2⟩⟩, ⟨_, hx, X₁, hadj, hΔ⟩⟩ := hGω
    set X₀ : uniqueInfiniteComponent h := ⟨x₀, hx⟩
    have hΔ' : Cχ ≤ ℓ X₁ - ℓ X₀ := hΔ ℓ hℓ
    have hCχ1 : 1 ≤ Cχ := le_max_left _ _
    by_cases hu01 : u X₁ = u X₀
    · have hχ : 128 * (2 * W + 1) * Real.exp Cbr ≤ Cχ * c₁ :=
        (div_le_iff₀ hc₁).1 (le_max_right _ _)
      exact exists_sensitiveEdge_of_steps_neighbor hB hH hR hL hF hG hX hA hT (hCf)
        (le_max_right _ _) (Nat.le_ceil _) hc₁ (by linarith) hχ
        ((le_max_left _ _).trans (le_max_left _ _)) ((le_max_right _ _).trans (le_max_left _ _))
        (le_max_right _ _) hℓ rfl hadj hΔ' hu01
        (fun y hy => hM₁ ℓ hℓ X₀ y hcone ((le_max_left _ _).trans hMx) hy)
        (h520c u hu hsupp (u X₀))
        (h528c u hu hsupp ℓ hℓ X₀ X₁ hadj (by linarith) hu01 hcone
          ((le_max_right _ _).trans hMx))
        (hG1) (hG2 ℓ hℓ)
    · refine ⟨X₀, X₁, hadj, ?_, ?_, fun e => hu01 e.symm⟩
      · simp only [X₀, sub_self]
        have : l1 0 = 0 := by simp [l1]
        rw [this]
        exact (zero_le_two).trans (le_max_right _ _)
      · intro e
        linarith


end Rigidity.Steps.Section5
