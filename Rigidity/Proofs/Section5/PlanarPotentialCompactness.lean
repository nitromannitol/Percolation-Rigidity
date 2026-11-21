import Rigidity.Proofs.Section5.ComponentHeatEquation

/-!
# Compactness of planar potential kernels

Locally bounded truncated potentials have a pointwise convergent subsequence. A uniform
logarithmic bound at infinity then gives a Green column.
-/

open Filter Topology LatticeProb.Percolation
open scoped Classical

namespace Rigidity.Proofs.Section5

/-- Locally bounded truncated potentials with uniform logarithmic growth give a Green column. -/
theorem exists_greenColumn_of_bounded_truncatedPotential {ω : Configuration 2}
    (C : OpenComponent ω) (hC : C.supp.Infinite) (y : C) (K R₀ : ℝ)
    (hlocal : ∀ x : C, ∃ B : ℝ, ∀ n, |truncatedComponentPotential C n y x| ≤ B)
    (hK : 0 ≤ K) (hbound : ∀ n (x : C), R₀ ≤ Rigidity.Section5.eucl x.val →
      |truncatedComponentPotential C n y x| ≤ K * Real.log (Rigidity.Section5.eucl x.val)) :
    ∃ g, IsGreenColumn 2 le_rfl C y g := by
  classical
  choose B hB using hlocal
  let S : Set (C → ℝ) := Set.pi Set.univ (fun x => Set.Icc (-B x) (B x))
  have hS : IsCompact S := isCompact_univ_pi fun _ => isCompact_Icc
  have hmem : ∀ n, truncatedComponentPotential C n y ∈ S := by
    intro n x _
    exact abs_le.mp (hB x n)
  obtain ⟨v, _, φ, hφ, hv⟩ := hS.tendsto_subseq hmem
  have hφ' : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hv' : ∀ x, Tendsto (fun n => truncatedComponentPotential C (φ n) y x)
      atTop (nhds (v x)) := by
    intro x
    exact (tendsto_pi_nhds.mp hv) x
  apply exists_greenColumn_of_truncatedPotential_subsequence_limit C hC y φ hφ' v K R₀ hv' hK
  intro x hx
  exact le_of_tendsto ((hv' x).abs) (Filter.Eventually.of_forall fun n => hbound (φ n) x hx)

end Rigidity.Proofs.Section5
