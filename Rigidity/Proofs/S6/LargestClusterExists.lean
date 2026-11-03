import Rigidity.Proofs.S6.GadgetCount
import LatticeProb.External.SupercriticalBondUniquenessInput
import LatticeProb.Prob.Percolation.LatticeUniqueClusterEvent

/-! # Section 6: the largest box cluster lies in the infinite cluster

Support for the restriction event of Theorem 6.5 (corrected draft, Section 6.2): almost surely the
infinite open cluster `𝒞_∞` exists and is unique, and for every large `n` some largest open
cluster `𝒞_*(Q_n)` of the cube `Q_n = [-n, n]^d` lies in `𝒞_∞`.

Route (Proposition 2.3 and Borel-Cantelli, as in `SingleExit` and `GadgetCount`).
* Almost surely every large cube `Q_N` is well-connected (`ae_eventually_isWellConnected`).
* If `Q_{10k}` is well-connected then `Q_k` is a good subcube of it; its largest cluster crosses
  `Q_k`. The crossing path of the largest cluster of `Q_k` has length at least `2k`, so it is
  joined, inside `Q_{k+1}`, to the largest cluster of `Q_{k+1}`
  (`reachable_goodCluster_of_subset`).
* By induction the largest cluster of `Q_n` is joined to the largest cluster of every `Q_k`,
  `k ≥ n`, which meets the face `{y_0 = k}`; its open cluster is therefore infinite, hence equal to
  the unique infinite cluster (`LatticeProb.External.SupercriticalBondUniqueness`). -/

open MeasureTheory LatticeProb.Percolation Classical Filter Rigidity.Section6
open Rigidity.External (cubeAt openIn IsGoodSubcube IsWellConnected WellConnectedInput)

namespace Rigidity.Proofs.S6

namespace LargestClusterExists

open SingleExit GadgetCount

variable {d : ℕ}

/-- If `Q_{10k}` is well-connected, `Q_k` is a good subcube of it. -/
theorem isGoodSubcube_of_isWellConnected {ω : Configuration d} {k : ℕ}
    (hW : IsWellConnected ω 0 (10 * k)) : IsGoodSubcube ω 0 k := by
  have hk0 : (0 : ℝ) ≤ k := by positivity
  refine hW.2.2 0 k ?_ ?_ ⟨0, fun i => by simp, fun i => by simp⟩
  · have := hW.1
    push_cast at this ⊢
    linarith
  · push_cast
    linarith

/-- If every cube `Q_N`, `N ≥ N₀`, is well-connected, every site of the largest cluster chosen in
a good cube `Q_n`, `n > N₀`, lies in an infinite open cluster: it is joined to the largest cluster
of every `Q_k`, `k ≥ n`, which meets the face `{y_0 = k}`. -/
theorem mem_infiniteComponentEvent_of_mem_goodCluster [NeZero d] {ω : Configuration d}
    {N₀ n : ℕ} (hN₀ : ∀ N, N₀ ≤ N → IsWellConnected ω 0 N) (hn : N₀ < n) {x : Vertex d}
    (hx : x ∈ goodCluster ω 0 n) : ω ∈ infiniteComponentEvent x := by
  have hgood : ∀ k : ℕ, N₀ < k → IsGoodSubcube ω 0 k := fun k hk =>
    isGoodSubcube_of_isWellConnected (hN₀ (10 * k) (by omega))
  have hreach : ∀ k, n ≤ k → ∀ y ∈ goodCluster ω 0 k, (openGraph ω).Reachable x y := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
      intro y hy
      exact (reachable_of_mem_goodCluster (hgood n hn) hx hy).mono (openIn_le_openGraph ω _)
    | succ k hk ih =>
      intro y hy
      obtain ⟨y', hy'⟩ := goodCluster_nonempty (hgood k (by omega))
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
      have hsub : cubeAt (0 : Vertex d) k ⊆ cubeAt 0 (k + 1) := fun v hv i =>
        le_trans (hv i) (by push_cast; omega)
      have := reachable_goodCluster_of_subset (hgood (k + 1) (by omega)) (hgood k (by omega))
        hsub (by push_cast; linarith) hy' hy
      exact (ih y' hy').trans (this.mono (openIn_le_openGraph ω _))
  refine (mem_infiniteComponentEvent_iff ω x).mpr fun s => ?_
  set K := max n (s.sup fun y => (y 0).natAbs) + 1 with hKdef
  obtain ⟨-, ⟨y, hy, hy0⟩⟩ := (goodCluster_spec (hgood K (by omega))).2.1 0
  refine ⟨y, fun hys => ?_, hreach K (by omega) y hy⟩
  have h1 : (y 0).natAbs ≤ s.sup fun y => (y 0).natAbs :=
    Finset.le_sup (f := fun y : Vertex d => (y 0).natAbs) hys
  have h2 : y 0 = K := by simpa using hy0
  rw [h2, Int.natAbs_natCast] at h1
  omega

theorem cubeAt_zero (n : ℕ) : cubeAt (0 : Vertex d) n = cube d n := by
  ext y
  simp [cubeAt, cube]

/-- The largest cluster chosen in a good cube `Q_n` is a largest box cluster of `Q_n`. -/
theorem isLargestBoxCluster_goodCluster {ω : Configuration d} {n : ℕ}
    (hg : IsGoodSubcube ω 0 n) :
    IsLargestBoxCluster ω n ((cubeAt_finite 0 n).subset (goodCluster_subset hg)).toFinset := by
  have hL := (goodCluster_spec hg).1
  rw [cubeAt_zero] at hL
  obtain ⟨⟨x, hx, hV⟩, hmax⟩ := hL
  rw [openIn_cube] at hV hmax
  refine ⟨⟨x, hx, ?_⟩, fun y hy => ?_⟩
  · rw [Set.Finite.coe_toFinset]
    exact hV
  · rw [← Set.ncard_eq_toFinset_card _ ((cubeAt_finite 0 n).subset (goodCluster_subset hg))]
    exact hmax y hy

end LargestClusterExists

open LargestClusterExists SingleExit GadgetCount in
/-- Support for the restriction event of Theorem 6.5: for `d ≥ 2` and `p_c < p < 1`, almost
surely the infinite open cluster exists and is unique, and for every large `n` some largest open
cluster of `Q_n` lies in it. Inputs: Proposition 2.3 (`WellConnectedInput`) and the existence and
uniqueness of the infinite cluster (`SupercriticalBondUniqueness`). -/
theorem largestClusterExists {d : ℕ} [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hwc : WellConnectedInput)
    (hU : LatticeProb.External.SupercriticalBondUniqueness) :
    ∀ᵐ ω ∂latticeBondLaw d p, ∃ h : HasUniqueInfiniteOpenComponent ω, ∀ᶠ n : ℕ in atTop,
      ∃ V : Finset (Vertex d), IsLargestBoxCluster ω n V ∧
        ∀ x ∈ V, x ∈ (uniqueInfiniteComponent h).supp := by
  have hU1 : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ uniqueInfiniteComponentEvent d :=
    (ae_iff_measure_eq (measurableSet_uniqueInfiniteComponentEvent d).nullMeasurableSet).2
      ((hU.2 d hd p hpc hp1).trans measure_univ.symm)
  filter_upwards [hU1, ae_eventually_isWellConnected hd p hpc hp1 hwc] with ω hω hW
  refine ⟨hω, ?_⟩
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hW
  filter_upwards [eventually_gt_atTop N₀] with n hn
  have hg : IsGoodSubcube ω 0 n := isGoodSubcube_of_isWellConnected (hN₀ _ (by omega))
  refine ⟨_, isLargestBoxCluster_goodCluster hg, fun x hx => ?_⟩
  rw [Set.Finite.mem_toFinset] at hx
  exact (mem_uniqueInfiniteComponent_iff hω x).mpr
    (mem_infiniteComponentEvent_of_mem_goodCluster hN₀ hn hx)

end Rigidity.Proofs.S6
