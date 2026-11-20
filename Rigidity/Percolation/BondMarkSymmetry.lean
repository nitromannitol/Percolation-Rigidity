import Rigidity.Percolation.BondMarkIndependence
import Rigidity.Percolation.BondContactSymmetry

/-!
# Lattice symmetries of uniform bond marks

A lattice symmetry permutes the bond marks without changing their law.
Thresholding commutes with this symmetry.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- A lattice symmetry transports uniform bond marks with their bonds. -/
def latticeBondMarkEquiv {d : ℕ} (f : Vertex d ≃ Vertex d)
    (hf : ∀ x y, latticeL1Dist (f x) (f y) = latticeL1Dist x y) : BondMarks d ≃ᵐ BondMarks d :=
  MeasurableEquiv.piCongrLeft (fun _ : Bond d => unitInterval) (latticeBondEquiv f hf)

/-- Moving a mark together with its bond preserves its value. -/
theorem latticeBondMarkEquiv_apply_bond {d : ℕ} (f : Vertex d ≃ Vertex d)
    (hf : ∀ x y, latticeL1Dist (f x) (f y) = latticeL1Dist x y)
    (ω : BondMarks d) (e : Bond d) :
    latticeBondMarkEquiv f hf ω (latticeBondEquiv f hf e) = ω e :=
  MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Bond d => unitInterval)
    (latticeBondEquiv f hf) ω e

/-- Every lattice symmetry preserves the product law of uniform bond marks. -/
theorem bondMarkLaw_map_latticeBondMarkEquiv {d : ℕ} (f : Vertex d ≃ Vertex d)
    (hf : ∀ x y, latticeL1Dist (f x) (f y) = latticeL1Dist x y) :
    (bondMarkLaw d).map (latticeBondMarkEquiv f hf) = bondMarkLaw d := by
  exact Measure.infinitePi_map_piCongrLeft (fun _ : Bond d => (volume : Measure unitInterval))
    (latticeBondEquiv f hf)

/-- Thresholding marks commutes with the induced lattice symmetry. -/
theorem thresholdBondMarks_latticeBondMarkEquiv {d : ℕ} (p : unitInterval)
    (f : Vertex d ≃ Vertex d)
    (hf : ∀ x y, latticeL1Dist (f x) (f y) = latticeL1Dist x y) (ω : BondMarks d) :
    thresholdBondMarks p (latticeBondMarkEquiv f hf ω) =
      latticeConfigurationEquiv f hf (thresholdBondMarks p ω) := by
  funext e
  obtain ⟨a, rfl⟩ := (latticeBondEquiv f hf).surjective e
  change markThreshold p (latticeBondMarkEquiv f hf ω (latticeBondEquiv f hf a)) = _
  rw [latticeBondMarkEquiv_apply_bond, latticeConfigurationEquiv_apply_bond]
  rfl

/-- Translation by a lattice vector is a distance-preserving equivalence. -/
def latticeVertexTranslation {d : ℕ} (z : Vertex d) : Vertex d ≃ Vertex d :=
  Equiv.addRight z

/-- Translating both vertices preserves lattice distance. -/
theorem latticeL1Dist_latticeVertexTranslation {d : ℕ} (z x y : Vertex d) :
    latticeL1Dist (latticeVertexTranslation z x) (latticeVertexTranslation z y) =
      latticeL1Dist x y := latticeL1Dist_add_right x y z

end Rigidity.Percolation
