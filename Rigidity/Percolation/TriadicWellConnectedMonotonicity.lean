import Rigidity.Percolation.TriadicWellConnectedEvent

/-!
# Monotonicity of well-connectedness tests

Enlarging the interior region adds test cubes and strengthens the
well-connectedness event. Testing all cubes that meet the ambient cube
therefore gives a uniform sufficient condition for every smaller interior.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory

/-- Enlarging the interior can only add test cubes. -/
theorem TriadicCube.testCubes_mono {d : ℕ} (Q : TriadicCube d)
    {interior interior' : Set (Vertex d)} (h : interior ⊆ interior') :
    Q.testCubes interior ⊆ Q.testCubes interior' := by
  rintro R ⟨hlo, hhi, x, hxR, hx⟩
  exact ⟨hlo, hhi, x, hxR, h hx⟩

/-- Well-connectedness for a larger interior implies well-connectedness for
a smaller interior. -/
theorem TriadicCube.wellConnectedIn_of_subset {d : ℕ} (Q : TriadicCube d)
    {interior interior' : Set (Vertex d)} (h : interior ⊆ interior')
    {ω : Configuration d} (hω : Q.wellConnectedIn interior' ω) :
    Q.wellConnectedIn interior ω := by
  rw [Q.wellConnectedIn_iff] at hω ⊢
  obtain ⟨root, hroot, htests⟩ := hω
  exact ⟨root, hroot, fun R hR => htests R (Q.testCubes_mono h hR)⟩

/-- The stronger event testing every eligible cube meeting the ambient cube. -/
def TriadicCube.wellConnectedAll {d : ℕ} (Q : TriadicCube d)
    (ω : Configuration d) : Prop := Q.wellConnectedIn Q.vertices ω

/-- Well-connectedness with all tests implies the event for any interior
contained in the ambient cube. -/
theorem TriadicCube.wellConnectedIn_of_wellConnectedAll {d : ℕ} (Q : TriadicCube d)
    {interior : Set (Vertex d)} (h : interior ⊆ Q.vertices) {ω : Configuration d}
    (hω : Q.wellConnectedAll ω) : Q.wellConnectedIn interior ω :=
  Q.wellConnectedIn_of_subset h hω

/-- The stronger all-tests event is measurable. -/
theorem TriadicCube.measurableSet_wellConnectedAll {d : ℕ} (Q : TriadicCube d) :
    MeasurableSet {ω : Configuration d | Q.wellConnectedAll ω} :=
  Q.measurableSet_wellConnectedIn Q.vertices

/-- A probability bound for the stronger event controls the failure probability
for any interior contained in the ambient cube. -/
theorem TriadicCube.measure_not_wellConnectedIn_le_all {d : ℕ}
    (μ : Measure (Configuration d)) (Q : TriadicCube d)
    {interior : Set (Vertex d)} (h : interior ⊆ Q.vertices) :
    μ {ω | ¬ Q.wellConnectedIn interior ω} ≤ μ {ω | ¬ Q.wellConnectedAll ω} := by
  apply measure_mono
  intro ω hω hAll
  exact hω (Q.wellConnectedIn_of_wellConnectedAll h hAll)

end Rigidity.Percolation
