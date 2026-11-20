import Rigidity.Proofs.S6.LargestClusterExists
import Rigidity.Proofs.Percolation.PlanarWellConnected
import Rigidity.Proofs.Percolation.BondUniqueness

/-!
# Planar box clusters and the infinite cluster

Almost surely the largest clusters of sufficiently large planar boxes lie in the infinite cluster.
-/

open MeasureTheory Filter LatticeProb.Percolation Rigidity.External Rigidity.Section6

namespace Rigidity.Proofs.S6

/-- Almost surely every sufficiently large planar box is well-connected. -/
theorem ae_eventually_planar_wellConnected (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ᶠ N : ℕ in atTop, IsWellConnected ω 0 N := by
  obtain ⟨c, C, s, hc, hC, hs, hbound⟩ := Rigidity.Percolation.wellConnected_input_two p hpc hp1
  have hfs : Summable fun N : ℕ => C * Real.exp (-(c * (N : ℝ) ^ s)) := by
    simpa using (SingleExit.summable_pow_mul_exp_neg_rpow 0 hc hs).mul_left C
  have hsum : ∑' N, latticeBondLaw 2 p {ω | ¬ IsWellConnected ω 0 N} ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum fun N => hbound 0 N)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun N => by positivity) hfs]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  exact hω.mono fun N hN => by simpa using hN

/-- Almost surely a largest cluster of every sufficiently large planar box lies in the infinite
open cluster. -/
theorem planar_largestCluster_subset_infinite (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∀ᵐ ω ∂latticeBondLaw 2 p, ∃ h : HasUniqueInfiniteOpenComponent ω, ∀ᶠ n : ℕ in atTop,
      ∃ V : Finset (Vertex 2), IsLargestBoxCluster ω n V ∧
        ∀ x ∈ V, x ∈ (uniqueInfiniteComponent h).supp := by
  have hU := Rigidity.Percolation.supercritical_bond_uniqueness
  have hU1 : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ uniqueInfiniteComponentEvent 2 :=
    (ae_iff_measure_eq (measurableSet_uniqueInfiniteComponentEvent 2).nullMeasurableSet).2
      ((hU.2 2 le_rfl p hpc hp1).trans measure_univ.symm)
  filter_upwards [hU1, ae_eventually_planar_wellConnected p hpc hp1] with ω hω hW
  refine ⟨hω, ?_⟩
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hW
  filter_upwards [eventually_gt_atTop N₀] with n hn
  have hg : IsGoodSubcube ω 0 n :=
    LargestClusterExists.isGoodSubcube_of_isWellConnected (hN₀ _ (by omega))
  refine ⟨_, LargestClusterExists.isLargestBoxCluster_goodCluster hg, fun x hx => ?_⟩
  rw [Set.Finite.mem_toFinset] at hx
  exact (mem_uniqueInfiniteComponent_iff hω x).mpr
    (LargestClusterExists.mem_infiniteComponentEvent_of_mem_goodCluster hN₀ hn hx)

end Rigidity.Proofs.S6
