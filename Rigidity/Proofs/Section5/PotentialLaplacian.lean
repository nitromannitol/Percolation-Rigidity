import Rigidity.Proofs.Section5.PotentialLimit

/-! # Section 5: the Green potential solves `-Δ u_f = f`

On an open component the potential `u_f = Σ_y f(y) G(·, y)` of a finitely supported charge is a
finite sum over the charges in the component; the Laplacian is linear and each column satisfies
`-Δ G(·, y) = δ_y`, so `-Δ u_f = Σ_y f(y) δ_y = f`. -/

open MeasureTheory LatticeProb.Percolation Classical Filter Topology

namespace Rigidity.Proofs.Section5

open Rigidity.Section5 Rigidity.Steps.Section5

/-- The Green potential of a finitely supported charge solves `-Δ u_f = f` on the component. -/
theorem potentialLaplacian : PotentialLaplacian := by
  intro ω C G hG f hf x
  set F : Finset C := (hf.preimage Subtype.val_injective.injOn).toFinset with hF
  have hpot : ∀ z, potential C G f z = ∑ y ∈ F, (f y.val : ℝ) * G z y := fun z => by
    simpa using potential_sub_mass_mul_eq_sum C G f hf 0 z
  have hlap : componentLaplacian C (potential C G f) x =
      ∑ y ∈ F, (f y.val : ℝ) * componentLaplacian C (fun z => G z y) x := by
    simp only [componentLaplacian, hpot, ← Finset.sum_sub_distrib, ← mul_sub, Finset.mul_sum]
    exact Finset.sum_comm
  have hcol : ∀ y, -componentLaplacian C (fun z => G z y) x = if x = y then 1 else 0 :=
    fun y => (hG y).1 x
  rw [hlap, ← Finset.sum_neg_distrib]
  simp_rw [← mul_neg, hcol, mul_ite, mul_one, mul_zero, eq_comm (a := x)]
  rw [Finset.sum_ite_eq']
  split_ifs with hx
  · rfl
  · rw [hF, Set.Finite.mem_toFinset, Set.mem_preimage, Function.mem_support, not_not] at hx
    simp [hx]

end Rigidity.Proofs.Section5
