import Rigidity.Proofs.Corrector.DarioFlipSplit
import Rigidity.Proofs.Corrector.DarioCaseOneTwo

/-!
# The term (3.15)-(ii) of Dario in Cases 1 and 2

The term (3.15)-(ii) in flip form (`bondFlipDiff_heatCoarseComp_eq`) is
`Φ_{r²} * ∇_j[ℓ₁ - ℓ₀]_{𝒫⁰}(x)`, with the corrected planes `ℓ₁, ℓ₀` of `ω^{e,1}, ω^{e,0}` coarsened by
the partition of `ω^{e,0}`. In Cases 1 and 2 of Step 2 (the endpoints of `e` are not both in the
infinite cluster `𝒞⁰` of `ω^{e,0}`), `ℓ₁ = ℓ₀ + k` on `𝒞⁰` (`ae_exists_correctedPlane_eq_add_const`)
and the anchors of `ω^{e,0}` lie in `𝒞⁰`, so the term vanishes
(`ae_heatComp_coarse_sub_eq_zero`). In Case 3 it is given by
`ae_heatComp_coarse_sub_eq_walkSum_closed`.
-/

namespace Rigidity.Corrector

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation
open scoped Classical

/-- The heat average of the gradient of a constant vanishes. -/
theorem heatComp_const (c r : ℝ) (x : Vertex 2) (j : Fin 2) :
    heatComp (fun _ => c) r x j = 0 := by
  unfold heatComp
  simp

/-- **Cases 1 and 2 of Step 2 for the term (3.15)-(ii)**: almost surely, if the endpoints of the
bond `e` of `a` are not both in the infinite cluster of `ω^{e,0}`, then
`Φ_{r²} * ∇_j[ℓ₁ - ℓ₀]_{𝒫⁰}(x) = 0` for the corrected planes `ℓ₁, ℓ₀` of the same slope. -/
theorem ae_heatComp_coarse_sub_eq_zero {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ a : LatticeEdge,
      ∀ (h₁ : HasUniqueInfiniteOpenComponent (setBond (edgeBond a) true ω))
        (h₀ : HasUniqueInfiniteOpenComponent (setBond (edgeBond a) false ω)),
        ¬ (a.1 ∈ (uniqueInfiniteComponent h₀).supp ∧
          edgeHead a ∈ (uniqueInfiniteComponent h₀).supp) →
        ∀ (q : Fin 2 → ℝ) (ℓ₁ : uniqueInfiniteComponent h₁ → ℝ)
          (ℓ₀ : uniqueInfiniteComponent h₀ → ℝ),
          IsCorrectedPlane (uniqueInfiniteComponent h₁) q ℓ₁ →
          IsCorrectedPlane (uniqueInfiniteComponent h₀) q ℓ₀ →
          PlanarPartitionEvent (setBond (edgeBond a) false ω) → ∀ (r : ℝ) (x : Vertex 2)
            (j : Fin 2),
            heatComp (fun z =>
                extendComp _ ℓ₁ (planarCoarseAnchor (setBond (edgeBond a) false ω) z) -
                extendComp _ ℓ₀ (planarCoarseAnchor (setBond (edgeBond a) false ω) z)) r x j = 0 := by
  filter_upwards [ae_exists_correctedPlane_eq_add_const hpc hp1] with ω hω
  intro a h₁ h₀ hnot q ℓ₁ ℓ₀ hℓ₁ hℓ₀ hP r x j
  obtain ⟨k, hk⟩ := hω a h₁ h₀ hnot q ℓ₁ ℓ₀ hℓ₁ hℓ₀
  have e : (fun z => extendComp _ ℓ₁ (planarCoarseAnchor (setBond (edgeBond a) false ω) z) -
      extendComp _ ℓ₀ (planarCoarseAnchor (setBond (edgeBond a) false ω) z)) = fun _ => k := by
    funext z
    have hz : planarCoarseAnchor (setBond (edgeBond a) false ω) z ∈
        (uniqueInfiniteComponent h₀).supp :=
      (mem_uniqueInfiniteComponent_iff h₀ _).2 (infinite_planarCoarseAnchor hP z)
    rw [hk _ hz]
    ring
  rw [e, heatComp_const]

end Rigidity.Corrector
