import Rigidity.Proofs.Percolation.ClusterComparison
import Rigidity.Vendor.FormalMathPercolation.Literature.ConnectivityProofs

/-!
# Existence and uniqueness of the infinite cluster

The Burton–Keane uniqueness theorem and the zero–one law yield a unique infinite cluster
whenever the percolation probability is positive.
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

namespace Rigidity.Percolation

open LatticeProb.Percolation _root_.Percolation.Literature

/-- The percolation probability is positive above its critical value. -/
theorem theta_pos_of_criticalProbability_lt (d : ℕ) [NeZero d] (p : unitInterval)
    (hp : criticalProbability d < (p : ℝ)) : 0 < LatticeProb.Percolation.theta d p := by
  obtain ⟨q, hq, hqp⟩ := (criticalProbability_lt_iff (d := d) (p : ℝ)).mp hp
  rw [theta_eq] at hq ⊢
  exact hq.trans_le (theta_mono_holds (LatticeModels.zdGraph d) 0
    (show q ≤ p from hqp.le))

/-- If the origin percolates with positive probability, there is almost surely one infinite cluster. -/
theorem uniqueInfiniteComponentEvent_eq_one_of_theta_pos (d : ℕ) (p : unitInterval)
    (hp : 0 < LatticeProb.Percolation.theta d p) :
    latticeBondLaw d p (uniqueInfiniteComponentEvent d) = 1 := by
  let μ := bondPercolation (LatticeModels.zdGraph d) p
  let F := extendEdges (LatticeModels.zdGraph d) ∘ toEdgeConfig d
  have hF : Measurable F := (measurable_extendEdges _).comp (by unfold toEdgeConfig; fun_prop)
  have hθ : 0 < _root_.Percolation.Literature.theta (LatticeModels.zdGraph d) 0 p := by
    rwa [← theta_eq]
  let E : Set (BondConfig (LatticeModels.Site d)) := {ω | ∃ x, ω ∈ percolatesAt x}
  have hEm : MeasurableSet E := by
    have he : E = ⋃ x : LatticeModels.Site d, percolatesAt x := by ext ω; simp [E]
    rw [he]
    exact MeasurableSet.iUnion fun x => measurableSet_percolatesAt_holds x
  have hEreal : μ.real E = 1 := (Grimmett1999_prob_exists_percolatesAt_holds d p).2 hθ
  have hE : μ E = 1 := (ENNReal.toReal_eq_one_iff (μ E)).mp hEreal
  have hEa : ∀ᵐ ω ∂μ, ω ∈ E := (mem_ae_iff_prob_eq_one hEm).2 hE
  have hU : ∀ᵐ ω ∂μ, numInfiniteClusters ω ≤ 1 :=
    Grimmett1999_numInfiniteClusters_le_one_holds d p
  have hEmap : ∀ᵐ ω ∂latticeBondLaw d p, F ω ∈ E := by
    apply MeasureTheory.ae_of_ae_map hF.aemeasurable
    rwa [map_latticeBondLaw]
  have hUmap : ∀ᵐ ω ∂latticeBondLaw d p, numInfiniteClusters (F ω) ≤ 1 := by
    have hU' : ∀ᵐ ω ∂(latticeBondLaw d p).map F, numInfiniteClusters ω ≤ 1 := by
      rwa [map_latticeBondLaw]
    exact MeasureTheory.ae_of_ae_map hF.aemeasurable hU'
  apply (mem_ae_iff_prob_eq_one (measurableSet_uniqueInfiniteComponentEvent d)).mp
  filter_upwards [hEmap, hUmap] with ω hex huniq
  rw [mem_uniqueInfiniteComponentEvent_iff]
  have hgraph : _root_.Percolation.Literature.openGraph (F ω) =
      LatticeProb.Percolation.openGraph ω := openGraph_eq d ω
  have hiff (x : Vertex d) : F ω ∈ percolatesAt x ↔ ω ∈ infiniteComponentEvent x :=
    (infinite_event_iff d ω x).symm
  constructor
  · obtain ⟨x, hx⟩ := hex
    exact ⟨x, (hiff x).mp hx⟩
  · intro x y hx hy
    have h := (numInfiniteClusters_le_one_iff (F ω)).mp huniq x y ((hiff x).mpr hx) ((hiff y).mpr hy)
    rwa [hgraph] at h

/-- Supercritical Bernoulli bond percolation has almost surely one infinite cluster. -/
theorem uniqueInfiniteComponentEvent_eq_one_of_criticalProbability_lt (d : ℕ) [NeZero d]
    (p : unitInterval) (hp : criticalProbability d < (p : ℝ)) :
    latticeBondLaw d p (uniqueInfiniteComponentEvent d) = 1 :=
  uniqueInfiniteComponentEvent_eq_one_of_theta_pos d p
    (theta_pos_of_criticalProbability_lt d p hp)

end Rigidity.Percolation
