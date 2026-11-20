import Rigidity.Proofs.S2.ClusterDensityInfluenceBound
import Rigidity.Proofs.Percolation.PlanarFiniteCluster
import Rigidity.Proofs.Section5.ConnectingSet
import Mathlib.MeasureTheory.MeasurableSpace.NCard

/-!
# Finite-cluster size as a random variable

Finite component sizes are measurable and inherit stretched-exponential tails from planar
annulus crossings.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory LatticeProb.Percolation
open scoped ENNReal

variable {d : ℕ}

/-- The support of the component of a fixed vertex is a measurable random set. -/
theorem measurable_component_support (x : Vertex d) :
    Measurable fun ω : Configuration d => ((openGraph ω).connectedComponentMk x).supp := by
  apply measurable_set_iff.mpr
  intro y
  have heq : (fun ω : Configuration d => y ∈ ((openGraph ω).connectedComponentMk x).supp) =
      (fun ω => (openGraph ω).Reachable x y) := by
    funext ω
    apply propext
    constructor
    · intro hy
      exact (SimpleGraph.ConnectedComponent.exact
        ((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 hy)).symm
    · intro hxy
      exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).2
        (SimpleGraph.ConnectedComponent.sound hxy.symm)
  rw [heq]
  exact measurableSet_setOf.1 (measurableSet_openGraph_reachable x y)

/-- The size of the finite component, taken to be zero for an infinite component, is measurable. -/
theorem measurable_finiteComponent_size (x : Vertex d) :
    Measurable fun ω : Configuration d => (finiteComponentVertices ω x).card := by
  have heq : (fun ω : Configuration d => (finiteComponentVertices ω x).card) =
      (fun ω => ((openGraph ω).connectedComponentMk x).supp.ncard) := by
    funext ω
    exact card_finiteComponentVertices ω x
  rw [heq]
  exact measurable_ncard.comp (measurable_component_support x)

end Rigidity.Proofs.S2
