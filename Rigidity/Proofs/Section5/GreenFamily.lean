import Rigidity.Steps.Section5.Common
import LatticeProb.External.GreenColumnExistence

/-! # Section 5: existence of a Green family of the infinite cluster

For each fixed lattice pole `y`, almost surely the infinite cluster carries a Green column with
pole `y` (Dario-Gu, eq. (1.8); cited input `SupercriticalBondGreenColumnExistence`). The lattice
is countable, so almost surely this holds for every pole at once, and choosing one column per pole
of the cluster gives a Green family. -/

open MeasureTheory LatticeProb.Percolation Classical Filter Topology

namespace Rigidity.Proofs.Section5

open Rigidity.Section5 Rigidity.Steps.Section5

/-- Almost surely the infinite cluster carries a Green family: one Green column per pole, from the
cited existence of Green columns for each fixed pole and a countable intersection over poles. -/
theorem greenFamilyExists (hE : LatticeProb.External.SupercriticalBondGreenColumnExistence)
    {p : unitInterval} (hp : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    GreenFamilyExists p := by
  filter_upwards [ae_all_iff.2 fun y : Vertex 2 => hE 2 le_rfl p hp hp1 y] with ω H h
  exact ⟨fun x y => (H y.val h y.prop).exists.choose x,
    fun y => (H y.val h y.prop).exists.choose_spec⟩

end Rigidity.Proofs.Section5
