import Rigidity.Percolation.IntegerCube

/-!
# Triadic well-connectedness events

The test cubes have sizes between one tenth and one half of the ambient
triadic cube. Selected paths have coordinate diameter at least one tenth of
its side length. The interior region selecting test cubes is a parameter.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory

/-- Test cubes with the prescribed relative sizes that intersect the given
interior region. -/
def TriadicCube.testCubes {d : ℕ} (Q : TriadicCube d) (interior : Set (Vertex d)) :
    Set (IntegerCube d) :=
  {R | Q.side ≤ 10 * (R.size : ℤ) ∧ 2 * (R.size : ℤ) ≤ Q.side ∧
    ∃ x ∈ R.vertices, x ∈ interior}

/-- A finite path has coordinate diameter at least one tenth of the side
length of the given triadic cube. -/
def TriadicCube.largePath {d : ℕ} (Q : TriadicCube d) (n : ℕ)
    (γ : Fin (n + 1) → Vertex d) : Prop :=
  ∃ (i j : Fin (n + 1)) (k : Fin d), Q.side ≤ 10 * |γ i k - γ j k|

/-- The triadic cube is well-connected relative to the supplied interior
region, using the crossing and path-connection conditions. -/
def TriadicCube.wellConnectedIn {d : ℕ} (Q : TriadicCube d)
    (interior : Set (Vertex d)) (ω : Configuration d) : Prop :=
  WellConnectedRegions ω Q.vertices
    (fun i => ↑(Q.toIntegerCube.lowerFace i))
    (fun i => ↑(Q.toIntegerCube.upperFace i))
    (IntegerCube.signatures (Q.testCubes interior)) Q.largePath

/-- The signature formulation is equivalent to the conditions stated
separately for every qualifying integer cube. -/
theorem TriadicCube.wellConnectedIn_iff {d : ℕ} (Q : TriadicCube d)
    (interior : Set (Vertex d)) (ω : Configuration d) :
    Q.wellConnectedIn interior ω ↔
      ∃ root, IsCrossingRoot ω Q.vertices
        (fun i => ↑(Q.toIntegerCube.lowerFace i))
        (fun i => ↑(Q.toIntegerCube.upperFace i)) root ∧
        ∀ R ∈ Q.testCubes interior,
          CrossableRegion ω (↑R.vertices) (fun i => ↑(R.lowerFace i))
            (fun i => ↑(R.upperFace i)) ∧
          ConnectsSelectedPaths ω (↑R.vertices) Q.vertices root Q.largePath := by
  unfold wellConnectedIn WellConnectedRegions
  apply exists_congr
  intro root
  apply and_congr_right
  intro _
  exact IntegerCube.forall_signatures_iff _ _

/-- The relative well-connectedness event is measurable. -/
theorem TriadicCube.measurableSet_wellConnectedIn {d : ℕ} (Q : TriadicCube d)
    (interior : Set (Vertex d)) :
    MeasurableSet {ω : Configuration d | Q.wellConnectedIn interior ω} :=
  measurableSet_wellConnectedRegions Q.vertices
    (fun i => ↑(Q.toIntegerCube.lowerFace i))
    (fun i => ↑(Q.toIntegerCube.upperFace i))
    (IntegerCube.signatures (Q.testCubes interior)) Q.largePath

/-- The family of triadic cubes well-connected relative to their given
interiors. -/
def TriadicCube.wellConnectedFamily {d : ℕ} (interior : TriadicCube d → Set (Vertex d))
    (ω : Configuration d) : Set (TriadicCube d) :=
  {Q | Q.wellConnectedIn (interior Q) ω}

/-- Membership in the well-connected family is a measurable event. -/
theorem TriadicCube.measurableSet_mem_wellConnectedFamily {d : ℕ}
    (interior : TriadicCube d → Set (Vertex d)) (Q : TriadicCube d) :
    MeasurableSet {ω : Configuration d | Q ∈ wellConnectedFamily interior ω} :=
  Q.measurableSet_wellConnectedIn (interior Q)

/-- A well-connected triadic cube has a crossing component. -/
theorem TriadicCube.wellConnectedIn_hasCrossingComponent {d : ℕ}
    {Q : TriadicCube d} {interior : Set (Vertex d)} {ω : Configuration d}
    (h : Q.wellConnectedIn interior ω) :
    HasCrossingComponent ω Q.vertices
      (fun i => ↑(Q.toIntegerCube.lowerFace i))
      (fun i => ↑(Q.toIntegerCube.upperFace i)) :=
  h.hasCrossingComponent

end Rigidity.Percolation
