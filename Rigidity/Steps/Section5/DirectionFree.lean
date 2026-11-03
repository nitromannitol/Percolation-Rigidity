import Rigidity.Proofs.Assembly.Section5d

/-! # Section 5 with the direction-free third good event (d = 2)

The third good event `G_3(x, C_χ)` of eq. `def-good-event` is direction-free ([C32]): some edge
`(x, y)` of `𝒞_∞` with `ℓ_{e₁}(y) - ℓ_{e₁}(x) ≥ C_χ`, in place of the printed edge `(x, x + e₁)`,
whose lower bound would need the signed variant `HorizontalIncrementStep` of Proposition 3.2
(`Rigidity/Steps/S3/HorizontalIncrement.lean`). The direction-free `G_3` has the lower
bound of Lemma 5.25 from Proposition 3.2 as printed (`Rigidity.Assembly.goodEventLowerBound`).

`G_3` is internal to Lemmas 5.25 and 5.27: the proof of Lemma 5.27 (corrected draft L2434-2657)
uses `x₁ = x₀ + e₁` only through `|x₁ - x₀|₁ = 1`, and Lemma 5.28 (`FiniteBranchesStmt`, proved by
`finiteBranches_of_steps`) holds for any edge `(x₀, x₁)` of `𝒞_∞`. This file proves, from the
proved steps of the carvings:
* Lemma 5.27 in draft form (`LargeGradientSensitiveStmt`, universal `G_1` [C31], direction-free
  `G_3` [C32]): `largeGradientSensitive_of_steps`, with `x₁` the neighbour of `x₀` given by `G_3`.
Proposition 5.11 at the slope `e₁` follows (`levelSetDensityEventuallyAt_e1_of_steps`): the
counting of sensitive edges and the ergodic theorem on triangles do not see `G_3`, only the
translation covariance of the event.
-/

open MeasureTheory Filter Topology LatticeProb.Percolation

namespace Rigidity.Steps.Section5

open Rigidity.Section5

/-! ### Lemma 5.27 -/

/-- Neighbours in an open component are at `l¹`-distance at most one. -/
theorem l1_sub_le_one_of_adj {ω : Configuration 2} {C : OpenComponent ω} {a b : C}
    (hab : (componentGraph C).Adj a b) : l1 (b.val - a.val) ≤ 1 :=
  Proofs.Section5.Termination.l1_sub_le_one_of_lattice_adj
    (openGraph_le ω ((C.toSimpleGraph_adj a.2 b.2).1 hab))

/-- Steps 1-6 of Lemma 5.27 on one cluster, at a point `x₀` of the cone beyond `M_h` and a
neighbour `x₁` of `x₀` in `𝒞_∞` with `u(x₁) = u(x₀)` (the printed proof takes `x₁ = x₀ + e₁` and
uses it only through `|x₁ - x₀|₁ ≤ 1`, [C32]). -/
theorem exists_sensitiveEdge_of_steps_neighbor {ω : Configuration 2}
    {h : HasUniqueInfiniteOpenComponent ω}
    (hB : ExplorationBlockStep) (hH : ExplorationHolesStep) (hR : RootBlockStep)
    (hL : LeafSensitiveStep) (hF : FluxBalanceStep) (hG : FluxGrowthStep)
    (hX : GreedyExplorationStep) (hA : ExplorationAssemblyStep) (hT : TerminationWindowStep)
    {f : Vertex 2 → ℤ} {r Cf Cbr W : ℕ} {R c₁ Cχ K₀ C₀ : ℝ} {u ℓ : uniqueInfiniteComponent h → ℝ}
    {x₀ : Vertex 2} {X₀ X₁ : uniqueInfiniteComponent h} (hf : ∀ x, f x ≠ 0 → x ∈ cube r)
    (hR1 : 1 ≤ R) (hRW : 4 * R ^ 2 ≤ W) (hc₁ : 0 < c₁) (hCχ : 0 < Cχ)
    (hχ : 128 * (2 * W + 1) * Real.exp Cbr ≤ Cχ * c₁) (hK₀ : K₀ ≤ C₀) (hW : (W : ℝ) + 1 ≤ C₀)
    (h2 : 2 ≤ C₀) (hℓ : IsCorrectedPlane _ (Pi.single 0 1) ℓ) (hX₀ : X₀.val = x₀)
    (hadj : (componentGraph _).Adj X₀ X₁) (hΔ : Cχ ≤ ℓ X₁ - ℓ X₀)
    (hu01 : u X₁ = u X₀) (hMh : ∀ y : uniqueInfiniteComponent h,
      (y.val ∈ cube r ∨ y.val ∈ negativeLine) → ℓ y < ℓ X₀)
    (h520 : ∀ S ⊆ levelSet u (u X₀), IsBiconnected _ S →
      (∀ T, IsLatticeComponentOf (Subtype.val '' S)ᶜ T → T.Finite → ∀ x ∈ T, f x = 0) →
      ¬ HasDisjointPathsToInfinity _ S (Cf + 1))
    (h528 : ∀ B₀ : ExplorationBlock _ u ℓ X₀ X₁, X₁ ∈ B₀.val →
      ∀ (n : ℕ) (b : Fin n → Set (PrunedVertex _ u ℓ X₀ X₁ B₀)),
        (∀ k, IsPrunedBranch _ u ℓ X₀ X₁ B₀ (b k)) → Function.Injective b → n ≤ Cbr)
    (hG1 : ∀ (n : ℕ) (γ : Fin (n + 1) → uniqueInfiniteComponent h), IsPathOf _ γ →
      (γ 0).val = x₀ → K₀ ≤ l1 ((γ (Fin.last n)).val - x₀) →
      c₁ * l1 ((γ (Fin.last n)).val - x₀) ≤ (goodCount ω Cf R γ : ℝ))
    (hG2 : ∀ R' : ℕ, K₀ ≤ R' → ∀ y z : uniqueInfiniteComponent h, y.val ∈ cubeAt x₀ R' →
      z.val ∈ cubeAt x₀ R' → ℓ y - ℓ z ≤ 4 * R') :
    ∃ a b : uniqueInfiniteComponent h, (componentGraph _).Adj a b ∧ l1 (a.val - x₀) ≤ C₀ ∧
      ℓ a ≠ ℓ b ∧ u a ≠ u b := by
  have h01 : ℓ X₀ < ℓ X₁ := by linarith
  have holes := hH ω _ f r u ℓ X₀ X₁ hf h01 hMh
  have hfew : ∀ S, IsBlock _ (explorationGraph _ u ℓ X₀ X₁) (explorationSet _ u ℓ X₀ X₁) S →
      ¬ HasDisjointPathsToInfinity _ S (Cf + 1) := fun S hS =>
    h520 S (hB ω _ u ℓ X₀ X₁ S hS).1 (hB ω _ u ℓ X₀ X₁ S hS).2 (holes S hS.1.1)
  rcases hR ω _ u ℓ hℓ X₀ X₁ hadj hu01 Cχ hCχ hΔ with ⟨z, hz⟩ | ⟨B₀, hB₀, hflux⟩
  · refine ⟨X₁, z, hz.1, ?_, hz.2.1, hz.2.2⟩
    have := l1_sub_le_one_of_adj hadj
    rw [hX₀] at this
    linarith
  have hgreedy := hX ω _ u ℓ X₀ X₁ hadj h01 hu01 B₀ hB₀ Cbr (Cχ / 4) (by positivity) hflux
    (hF ω _ u ℓ hℓ X₀ X₁ hadj h01 hu01 B₀ hB₀) (h528 B₀ hB₀)
  have hconc := hA ω _ u ℓ X₀ X₁ hadj h01 hu01 B₀ hB₀ _ hgreedy
    (hG ω _ u ℓ X₀ X₁ hadj h01 hu01 B₀ hB₀) (hL ω _ u ℓ hℓ X₀ X₁ hadj h01 hu01 B₀ hB₀)
  have he : Real.exp (Cbr : ℝ) * Real.exp (-(Cbr : ℝ)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hi : 32 * (2 * W + 1) ≤ Cχ / 4 * Real.exp (-(Cbr : ℝ)) * c₁ := by
    have := mul_le_mul_of_nonneg_right hχ (Real.exp_pos (-(Cbr : ℝ))).le
    nlinarith
  exact exists_sensitiveEdge_of_explorationConclusion hX₀ h01 hc₁ hi hK₀ hW h2 hconc
    (hT ω h u ℓ X₀ X₁ Cf R W h01 hR1 hRW hfew) hG1 hG2

/-- **Lemma 5.27** (`LargeGradientSensitiveStmt`, universal `G_1` [C31], direction-free `G_3` [C32])
from Theorem 2.5, Proposition 5.20, Proposition 5.24, Lemma 5.25, Lemma 5.28 and the steps of the
carving, with `x₁` the neighbour of `x₀` given by `G_3`. -/
theorem largeGradientSensitive_of_steps {p : unitInterval} {f : Vertex 2 → ℤ}
    (hQ : External.CorrectorQuantitativeInput) (hpc : criticalProbability 2 < (p : ℝ))
    (hp1 : (p : ℝ) < 1)
    (h520 : BoundarySizeStmt p f) (h524 : LongPathRenormalizedStmt p)
    (h525 : GoodEventLowerBoundStmt p) (h528 : FiniteBranchesStmt p f)
    (hM : CorrectedPlaneMinimalScaleStep) (hB : ExplorationBlockStep)
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
  · filter_upwards [hM hQ p hpc hp1 (Cf / 2), h528ae, h520ae] with ω hMω h528ω h520ω
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
