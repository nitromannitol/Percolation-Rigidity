import Rigidity.Proofs.S6.LargestClusterExists
import Rigidity.Proofs.Percolation.PlanarWellConnected
import PercolationClusterHomogenization.Proofs.Percolation.BondUniqueness
import Rigidity.Proofs.Section5.Peierls

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

/-- Almost surely every infinite-cluster vertex in the inner half of a sufficiently large box
belongs to each largest open cluster of that box. -/
theorem ae_planar_infiniteCluster_mem_largestBox (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ᶠ n : ℕ in atTop,
      ∀ V : Finset (Vertex 2), IsLargestBoxCluster ω n V →
        ∀ x : Vertex 2, (∀ i, 2 * |x i| ≤ (n : ℤ)) →
          ω ∈ infiniteComponentEvent x → x ∈ V := by
  let q : ℕ := 100 * 2 ^ 2
  have hq : q ≠ 0 := by dsimp [q]; positivity
  have hex : ∀ n : ℕ, ∃ m, n ≤ m ^ q := fun n => ⟨n, Nat.le_self_pow hq n⟩
  let mOf : ℕ → ℕ := fun n => Nat.find (hex n)
  have hscale : ∀ n, 22 ^ q ≤ n → 1 ≤ mOf n ∧ 20 * mOf n ≤ n ∧
      (2 * mOf n + 1) ^ 2 < (2 * (n - 2 * mOf n) + 1) / (2 * mOf n + 1) ∧
      (n : ℝ) ^ ((q : ℝ)⁻¹) ≤ mOf n := by
    intro n hn
    have hspec : n ≤ mOf n ^ q := Nat.find_spec (hex n)
    have h22 : 22 ≤ mOf n := by
      by_contra h
      push Not at h
      exact absurd (hn.trans hspec) (not_le.mpr (Nat.pow_lt_pow_left h hq))
    have hlow : (mOf n - 1) ^ q < n := by
      have h := Nat.find_min (hex n) (show mOf n - 1 < mOf n by omega)
      push Not at h
      exact h
    obtain ⟨h20, hK⟩ := SingleExit.scale_conditions (d := 2) (by norm_num) rfl h22 hlow
    refine ⟨by omega, h20, hK, ?_⟩
    calc (n : ℝ) ^ ((q : ℝ)⁻¹) ≤ ((mOf n : ℝ) ^ q) ^ ((q : ℝ)⁻¹) :=
          Real.rpow_le_rpow (by positivity) (by exact_mod_cast hspec) (by positivity)
      _ = mOf n := Real.pow_rpow_inv_natCast (by positivity) hq
  have hδ : (1 / (10 * (2 : ℝ)) ^ 2) = (q : ℝ)⁻¹ := by dsimp [q]; norm_num
  filter_upwards [ae_eventually_planar_wellConnected p hpc hp1] with ω hW
  filter_upwards [hW, eventually_ge_atTop (22 ^ q)] with n hWn hn
  intro V hV x hx hinf
  obtain ⟨hm1, h20, hK, hnm⟩ := hscale n hn
  have hg : SingleExit.CubesGood ω n (mOf n) := by
    intro z hz
    have hmem : ∀ M : ℕ, (cubeAt z M ∩ cubeAt 0 n).Nonempty := fun M =>
      ⟨z, fun i => by simp, fun i => by simpa using hz i⟩
    have h20' : (20 : ℝ) * mOf n ≤ n := by exact_mod_cast h20
    have hpos : 0 ≤ (n : ℝ) ^ (1 / (10 * (2 : ℝ)) ^ 2) := by positivity
    have hlo : (n : ℝ) ^ (1 / (10 * (2 : ℝ)) ^ 2) ≤ mOf n := by rw [hδ]; exact hnm
    exact ⟨hWn.2.2 z _ (by linarith) (by linarith) (hmem _),
      hWn.2.2 z _ (by push_cast; linarith) (by push_cast; linarith) (hmem _)⟩
  have hbound : ∀ i, |x i| ≤ (n : ℤ) - 2 * mOf n := by
    intro i
    have h20' : (20 : ℤ) * (mOf n : ℤ) ≤ n := by exact_mod_cast h20
    linarith [hx i, abs_nonneg (x i)]
  exact GadgetCount.mem_of_mem_infiniteComponentEvent (d := 2) (by norm_num) hg hm1
    (by omega) hK hV hbound hinf

/-- The largest planar box cluster lies in the infinite cluster and contains its inner half-box. -/
theorem planar_largestBox_absorbs_infiniteCluster (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∀ᵐ ω ∂latticeBondLaw 2 p, ∃ h : HasUniqueInfiniteOpenComponent ω, ∀ᶠ n : ℕ in atTop,
      ∃ V : Finset (Vertex 2), IsLargestBoxCluster ω n V ∧
        (∀ x ∈ V, x ∈ (uniqueInfiniteComponent h).supp) ∧
        ∀ x, (∀ i, 2 * |x i| ≤ (n : ℤ)) → x ∈ (uniqueInfiniteComponent h).supp → x ∈ V := by
  filter_upwards [planar_largestCluster_subset_infinite p hpc hp1,
    ae_planar_infiniteCluster_mem_largestBox p hpc hp1] with ω hV hinner
  obtain ⟨h, hV⟩ := hV
  refine ⟨h, ?_⟩
  filter_upwards [hV, hinner] with n hn hninner
  obtain ⟨V, hlarge, hsubset⟩ := hn
  refine ⟨V, hlarge, hsubset, fun x hx hxinf => ?_⟩
  exact hninner V hlarge x hx ((mem_uniqueInfiniteComponent_iff h x).mp hxinf)

end Rigidity.Proofs.S6
