import Rigidity.Proofs.Section5.PotentialFlowBound

/-!
# Finite-support flows and potential kernels

A flow supported on a finite set needs only one finite energy bound.
-/

open LatticeProb.Percolation LatticeProb.Network
open scoped Classical

namespace Rigidity.Proofs.Section5

/-- The energy of a flow supported on `T` is bounded by its energy on `T`. -/
theorem flowEnergyOn_le_of_support {V : Type*} (G : SimpleGraph V) [G.LocallyFinite]
    (θ : V → V → ℝ) (T S : Finset V) (hθ : ∀ x ∉ T, ∀ y, θ x y = 0) :
    flowEnergyOn G (unitCond G) S θ ≤ flowEnergyOn G (unitCond G) T θ := by
  have heq : flowEnergyOn G (unitCond G) S θ =
      flowEnergyOn G (unitCond G) (S ∩ T) θ := by
    unfold flowEnergyOn
    symm
    apply Finset.sum_subset Finset.inter_subset_left
    intro x hx hxST
    have hxT : x ∉ T := fun hxT => hxST (Finset.mem_inter.mpr ⟨hx, hxT⟩)
    exact Finset.sum_eq_zero fun y _ => by rw [hθ x hxT y]; simp
  rw [heq]
  unfold flowEnergyOn
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
    (fun x _ _ => Finset.sum_nonneg fun y _ =>
      div_nonneg (sq_nonneg _) (isCond_unitCond.nonneg x y))

/-- A finite-support unit flow bounds the truncated potential by its energy. -/
theorem truncatedComponentPotential_le_finite_flow_energy {d : ℕ} {ω : Configuration d}
    (C : OpenComponent ω) (hC : C.supp.Infinite) (y x : C)
    (θ : C → C → ℝ) (T : Finset C) (K : ℝ) (hθ : IsFlow (componentGraph C) θ)
    (hsupport : ∀ z ∉ T, ∀ w, θ z w = 0)
    (hdiv : ∀ z, divergence (componentGraph C) θ z =
      (if z = y then 1 else 0) - (if z = x then 1 else 0))
    (henergy : flowEnergyOn (componentGraph C) (unitCond (componentGraph C)) T θ ≤ 2 * K)
    (n : ℕ) : truncatedComponentPotential C n y x ≤ K :=
  truncatedComponentPotential_le_flow_energy C hC y x θ K hθ hdiv
    (fun S => (flowEnergyOn_le_of_support (componentGraph C) θ T S hsupport).trans henergy) n

end Rigidity.Proofs.Section5
