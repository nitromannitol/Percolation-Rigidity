import Rigidity.Proofs.Percolation.BoundedDegreeLattice
import Rigidity.Proofs.Percolation.ClusterComparison
import Rigidity.Vendor.CriticalPercolation.Criticality.PositiveCritical

/-!
# Positivity of the lattice critical probability

The standard bounded-degree exploration estimate gives a positive interval of bond parameters
for which every open cluster is finite. See G. Grimmett, *Percolation*, 2nd ed. (1999),
Theorem (1.10) and its proof in §1.4.
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

namespace Rigidity.Percolation

open LatticeProb.Percolation OAI.CriticalPercolation _root_.Percolation.Literature

/-- The set of bonds assigned `true` by a Boolean configuration. -/
def openBondSet {d : ℕ} (ω : Configuration d) : Set (Bond d) := {e | ω e = true}

/-- The open-bond set depends measurably on the Boolean configuration. -/
theorem measurable_openBondSet (d : ℕ) : Measurable (openBondSet (d := d)) := by
  apply measurable_set_iff.mpr
  intro e
  change Measurable (fun ω : Configuration d => ω e = true)
  fun_prop

/-- Boolean bond configurations become the labelled bond graph's product law. -/
theorem map_openBondSet (d : ℕ) (p : unitInterval) :
    (latticeBondLaw d p).map openBondSet = (labelledLattice d).law p := by
  have hm : Measurable (fun b : Bool => b = true) := by fun_prop
  have hmap : (bernoulliMeasure true false p).map (fun b : Bool => b = true) =
      bernoulliMeasure True False p := by
    rw [map_bernoulliMeasure' _ _ hm p]
    congr 1 <;> apply propext <;> decide
  have hprod : (latticeBondLaw d p).map (fun ω (e : Bond d) => ω e = true) =
      Measure.infinitePi (fun _ : Bond d => bernoulliMeasure True False p) := by
    rw [latticeBondLaw, Measure.infinitePi_map_pi _ (fun _ => hm)]
    congr 1
    funext e
    exact hmap
  calc
    _ = ((latticeBondLaw d p).map (fun ω (e : Bond d) => ω e = true)).map
        (fun q : Bond d → Prop => {e | q e}) := by
      rw [Measure.map_map measurable_setOf (by fun_prop)]
      rfl
    _ = _ := by
      rw [hprod, BondGraph.law, setBernoulli_eq_map]
      congr 1

/-- The labelled-bond and Boolean constructions have the same open graph. -/
theorem labelledLattice_openGraph (d : ℕ) (ω : Configuration d) :
    (labelledLattice d).openGraph (openBondSet ω) = LatticeProb.Percolation.openGraph ω := by
  have heq : (labelledLattice d).ends '' openBondSet ω =
      extendEdges (LatticeModels.zdGraph d) (toEdgeConfig d ω) := by
    ext e
    constructor
    · rintro ⟨b, hb, rfl⟩
      have h : (b : Sym2 (Vertex d)) ∈ (LatticeModels.zdGraph d).edgeSet :=
        (bondEquiv d b).property
      refine ⟨h, ?_⟩
      change ω ((bondEquiv d).symm ⟨b, h⟩) = true
      have hb' : (bondEquiv d).symm ⟨b, h⟩ = b := Subtype.ext rfl
      simpa only [hb', openBondSet, Set.mem_setOf_eq] using hb
    · rintro ⟨h, hw⟩
      refine ⟨(bondEquiv d).symm ⟨e, h⟩, ?_, rfl⟩
      exact hw
  change SimpleGraph.fromEdgeSet ((labelledLattice d).ends '' openBondSet ω) = _
  rw [heq]
  exact openGraph_eq d ω

/-- At a sufficiently small parameter, the origin has no infinite cluster. -/
theorem theta_eq_zero_of_small_parameter (d : ℕ) [NeZero d] (p : unitInterval)
    (hp : 4 * (p : ℝ) * (2 * d : ℕ) ≤ 1) : LatticeProb.Percolation.theta d p = 0 := by
  let G := labelledLattice d
  have hc : G.fullGraph.Connected := by
    rw [labelledLattice_fullGraph]
    exact LatticeProb.Graph.Zd.latticeConnected d
  have hD : ∀ v, (G.incidentEdges {v}).ncard ≤ 2 * d := by
    intro v
    exact (labelledLattice_incidentEdges_ncard d v).le
  have hz : G.law p (G.infiniteEvent (0 : Vertex d)) = 0 :=
    G.small_parameter_infinite_null hc (labelledLattice_locallyFinite d) p (2 * d) hD hp 0
  have he : infiniteComponentEvent (0 : Vertex d) =
      openBondSet ⁻¹' G.infiniteEvent 0 := by
    ext ω
    change ((LatticeProb.Percolation.openGraph ω).connectedComponentMk 0).supp.Infinite ↔
      {y | (G.openGraph (openBondSet ω)).Reachable 0 y}.Infinite
    rw [labelledLattice_openGraph, component_supp_eq_cluster]
  unfold LatticeProb.Percolation.theta
  rw [he, ← map_measureReal_apply (measurable_openBondSet d)
    (G.measurableSet_infiniteEvent 0), map_openBondSet]
  change ((G.law p) (G.infiniteEvent 0)).toReal = 0
  rw [hz, ENNReal.toReal_zero]

/-- The critical bond percolation probability of the integer lattice is strictly positive. -/
theorem criticalProbability_pos (d : ℕ) [NeZero d] : 0 < criticalProbability d := by
  let δ : ℝ := 1 / (4 * (2 * d : ℕ) + 1)
  have hden : 0 < (4 * (2 * d : ℕ) : ℝ) + 1 := by positivity
  have hδ : 0 < δ := one_div_pos.mpr hden
  have hδeq : δ * ((4 * (2 * d : ℕ) : ℝ) + 1) = 1 := by
    exact div_mul_cancel₀ 1 hden.ne'
  refine hδ.trans_le ((le_criticalProbability_iff (d := d) δ).mpr ?_)
  intro p hp
  by_contra h
  have hpδ : (p : ℝ) < δ := lt_of_not_ge h
  have hpbound : 4 * (p : ℝ) * (2 * d : ℕ) ≤ 1 := by
    have hD : (0 : ℝ) ≤ (2 * d : ℕ) := Nat.cast_nonneg _
    nlinarith [mul_nonneg (sub_nonneg.mpr hpδ.le) hD]
  rw [theta_eq_zero_of_small_parameter d p hpbound] at hp
  exact (lt_irrefl 0) hp

end Rigidity.Percolation
