import LatticeProb.Graph.Zd
import LatticeProb.Network.LocalCaccioppoli
import Rigidity.Proofs.Regularity.MixedDifferenceSobolev

/-!
# Discrete harmonic functions on the lattice

The lattice Laplacian `Δ f(x) = ∑ᵢ (f(x + eᵢ) + f(x - eᵢ) - 2 f(x))` (`latticeLaplacian`) is the
network Laplacian of `ℤ^d` with unit conductances (`netLaplacian_lattice`). It commutes with
translations, so the forward differences, and more generally the mixed differences, of a function
harmonic on a region are harmonic on the region shrunk by the directions of the differences
(`latticeLaplacian_mixedDiff`). These are the first ingredients of the interior regularity of
discrete harmonic functions (Caccioppoli inequalities for their differences of all orders).
-/

namespace Rigidity.Proofs.Regularity

open Finset LatticeProb

variable {d : ℕ}

/-- The lattice Laplacian `Δ f(x) = ∑ᵢ (f(x + eᵢ) + f(x - eᵢ) - 2 f(x))`. -/
noncomputable def latticeLaplacian (f : (Fin d → ℤ) → ℝ) (x : Fin d → ℤ) : ℝ :=
  ∑ i, (f (x + unit i) + f (x - unit i) - 2 * f x)

theorem unit_add_ne_sub (x : Fin d → ℤ) (i : Fin d) : x + unit i ≠ x - unit i := by
  intro h
  have := congrFun h i
  simp only [unit, Pi.add_apply, Pi.sub_apply, Pi.single_eq_same] at this
  omega

/-- The lattice Laplacian is the network Laplacian of `ℤ^d` with unit conductances. -/
theorem netLaplacian_lattice (f : (Fin d → ℤ) → ℝ) (x : Fin d → ℤ) :
    Network.netLaplacian (lattice d) (Network.unitCond (lattice d)) f x = latticeLaplacian f x := by
  classical
  rw [Network.netLaplacian_unitCond, Graph.laplacian, Graph.Zd.neighborFinset_eq, nbrFinset,
    sum_biUnion]
  · refine sum_congr rfl fun i _ => ?_
    rw [sum_pair (unit_add_ne_sub x i)]
    ring
  · intro i _ j _ hij
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_insert, Finset.mem_singleton]
    rintro a (rfl | rfl) (h | h) <;>
      · have h1 := congrFun h i
        have h2 := congrFun h j
        simp [unit, Pi.single_eq_same, Pi.single_eq_of_ne, hij] at h1 h2

/-- The lattice Laplacian commutes with translations. -/
theorem latticeLaplacian_comp_add (f : (Fin d → ℤ) → ℝ) (v x : Fin d → ℤ) :
    latticeLaplacian (fun y => f (y + v)) x = latticeLaplacian f (x + v) := by
  simp only [latticeLaplacian]
  refine sum_congr rfl fun i _ => ?_
  rw [add_right_comm x (unit i) v, sub_add_eq_add_sub, add_sub_right_comm]

theorem latticeLaplacian_sub (f g : (Fin d → ℤ) → ℝ) (x : Fin d → ℤ) :
    latticeLaplacian (fun y => f y - g y) x = latticeLaplacian f x - latticeLaplacian g x := by
  simp only [latticeLaplacian, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  ring

/-- The mixed difference `D_S f` is harmonic wherever `f` is harmonic at all the points
`x + ∑_{j ∈ U} e_j`, `U ⊆ S`. -/
theorem latticeLaplacian_mixedDiff (S : Finset (Fin d)) (f : (Fin d → ℤ) → ℝ) (x : Fin d → ℤ)
    (hf : ∀ U ∈ S.powerset, latticeLaplacian f (x + shiftSum U) = 0) :
    latticeLaplacian (mixedDiff S f) x = 0 := by
  have hi : ∀ i, mixedDiff S f (x + unit i) + mixedDiff S f (x - unit i) - 2 * mixedDiff S f x =
      ∑ U ∈ S.powerset, (-1 : ℝ) ^ (S.card - U.card) *
        (f (x + shiftSum U + unit i) + f (x + shiftSum U - unit i) - 2 * f (x + shiftSum U)) := by
    intro i
    simp only [mixedDiff, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun U _ => ?_
    rw [add_right_comm x (unit i), sub_add_eq_add_sub]
    ring
  have h : latticeLaplacian (mixedDiff S f) x =
      ∑ U ∈ S.powerset, (-1 : ℝ) ^ (S.card - U.card) * latticeLaplacian f (x + shiftSum U) := by
    rw [latticeLaplacian, sum_congr rfl fun i _ => hi i, sum_comm]
    refine sum_congr rfl fun U _ => ?_
    rw [latticeLaplacian, mul_sum]
  rw [h]
  exact sum_eq_zero fun U hU => by rw [hf U hU, mul_zero]

end Rigidity.Proofs.Regularity
