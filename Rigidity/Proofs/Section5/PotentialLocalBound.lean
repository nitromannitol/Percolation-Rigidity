import Rigidity.Proofs.Section5.PotentialNeighborBound
import LatticeProb.Network.VoltageConnected
import LatticeProb.Graph.OnDiagonal

/-!
# Local boundedness of truncated potential kernels

A bounded voltage between two vertices controls the finite-time potential kernel.
-/

open LatticeProb.Percolation LatticeProb.Graph LatticeProb.Network
open scoped Classical

namespace Rigidity.Proofs.Section5

/-- Iterated walk averages preserve nonnegativity. -/
theorem walkOp_iterate_nonneg {V : Type*} (G : SimpleGraph V) [G.LocallyFinite]
    (f : V → ℝ) (hf : ∀ x, 0 ≤ f x) (n : ℕ) (x : V) :
    0 ≤ (walkOp G)^[n] f x := by
  induction n generalizing x with
  | zero => exact hf x
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact div_nonneg (Finset.sum_nonneg fun z _ => ih z) (Nat.cast_nonneg _)

/-- A voltage difference equals a finite-time difference of normalized heat kernels. -/
theorem voltage_sub_walkOp_iterate {V : Type*} (G : SimpleGraph V) [G.LocallyFinite]
    [Infinite V] (hG : G.Connected) (a b : V) (f : V → ℝ)
    (hf : ∀ z, laplacian G f z = (if z = b then 1 else 0) - (if z = a then 1 else 0)) :
    ∀ (n : ℕ) (z : V), f z - (walkOp G)^[n] f z =
      ∑ k ∈ Finset.range n, (heat G k z a / (G.degree a : ℝ) -
        heat G k z b / (G.degree b : ℝ)) := by
  have hstep : ∀ z, f z - walkOp G f z =
      (if z = a then 1 / (G.degree a : ℝ) else 0) -
        (if z = b then 1 / (G.degree b : ℝ) else 0) := by
    intro z
    have h := laplacian_div hG f z
    rw [hf z] at h
    by_cases hza : z = a <;> by_cases hzb : z = b <;> subst_vars <;> simp_all [div_eq_mul_inv] <;> linarith
  intro n
  induction n with
  | zero => intro z; simp
  | succ n ih =>
      intro z
      rw [Function.iterate_succ_apply', Finset.sum_range_succ']
      have hwalk : walkOp G (fun w => f w - (walkOp G)^[n] f w) z =
          ∑ k ∈ Finset.range n, (heat G (k + 1) z a / (G.degree a : ℝ) -
            heat G (k + 1) z b / (G.degree b : ℝ)) := by
        simp_rw [ih]
        rw [walkOp_sum]
        apply Finset.sum_congr rfl
        intro k hk
        rw [walkOp_sub]
        simp only [heat_succ, walkOp, Finset.sum_div]
        congr 1 <;> apply Finset.sum_congr rfl <;> intro w hw <;> ring
      rw [walkOp_sub] at hwalk
      have h0 : heat G 0 z a / (G.degree a : ℝ) - heat G 0 z b / (G.degree b : ℝ) =
          f z - walkOp G f z := by
        rw [hstep]
        simp only [heat]
        split_ifs <;> simp
      rw [h0]
      linarith

/-- The truncated potential is uniformly bounded at each vertex of an infinite component. -/
theorem exists_bound_truncatedComponentPotential {d : ℕ} {ω : Configuration d}
    (C : OpenComponent ω) (hC : C.supp.Infinite) (y x : C) :
    ∃ B : ℝ, ∀ n, |truncatedComponentPotential C n y x| ≤ B := by
  classical
  letI : Infinite C := Set.infinite_coe_iff.mpr hC
  by_cases hxy : x = y
  · subst x
    refine ⟨0, fun n => ?_⟩
    simp [truncatedComponentPotential]
  · obtain ⟨f, M, hM, hf, hlap⟩ :=
      exists_voltage_of_connected C.connected_toSimpleGraph (Ne.symm hxy)
    refine ⟨f y, fun n => ?_⟩
    rw [abs_of_nonneg (truncatedComponentPotential_nonneg C n y x)]
    have ht := voltage_sub_walkOp_iterate (componentGraph C) C.connected_toSimpleGraph y x f hlap n y
    have hnonneg := walkOp_iterate_nonneg (componentGraph C) f (fun z => (hf z).1) n y
    have heq : truncatedComponentPotential C n y x =
        ∑ k ∈ Finset.range n, (heat (componentGraph C) k y y / ((componentGraph C).degree y : ℝ) -
          heat (componentGraph C) k y x / ((componentGraph C).degree x : ℝ)) := by
      simp only [truncatedComponentPotential, sub_div, heat_div_degree_symm]
    rw [heq]
    linarith

end Rigidity.Proofs.Section5
