import Rigidity.External.PlanarInputs
import Rigidity.Proofs.Section5.GreenFamily

/-!
# A planar Green family

The fixed-pole planar Green-column statement gives a Green family by countability.
-/

namespace Rigidity.Proofs.Section5

open MeasureTheory LatticeProb.Percolation Rigidity.Section5 Rigidity.Steps.Section5

/-- Almost surely the planar infinite cluster carries a Green family. -/
theorem greenFamilyExists_two (hE : Rigidity.External.SupercriticalBondGreenColumnExistenceTwo)
    {p : unitInterval} (hp : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    GreenFamilyExists p := by
  classical
  filter_upwards [ae_all_iff.2 fun y : Vertex 2 => hE p hp hp1 y] with ω H h
  exact ⟨fun x y => (H y.val h y.prop).exists.choose x,
    fun y => (H y.val h y.prop).exists.choose_spec⟩

end Rigidity.Proofs.Section5
