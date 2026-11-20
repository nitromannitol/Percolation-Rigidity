import Rigidity.Percolation.CrossingRootCoalescence

/-!
# Selected paths in small test cubes

A cube whose coordinate diameter is below the selection threshold contains no
selected path. Its crossing-anchor condition therefore holds automatically.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation Rigidity.External

/-- Every vertex of a selected open path lies in its region. -/
theorem IsSelectedOpenPath.mem_region {d : ℕ} {ω : Configuration d}
    {B : Set (Vertex d)} {large : (n : ℕ) → (Fin (n + 1) → Vertex d) → Prop}
    {n : ℕ} {γ : Fin (n + 1) → Vertex d} (h : IsSelectedOpenPath ω B large n γ)
    (i : Fin (n + 1)) : γ i ∈ B := by
  refine Fin.cases ?_ ?_ i
  · exact h.2.1
  · intro j
    exact (h.2.2 j).2.2

/-- A cube whose maximum coordinate diameter is strictly below the selection
threshold contains no selected open path. -/
theorem TriadicCube.not_hasSelectedOpenPath_of_size {d : ℕ} (Q : TriadicCube d)
    (R : IntegerCube d) (ω : Configuration d)
    (hsize : 10 * ((R.size : ℤ) - 1) < Q.side) :
    ¬ HasSelectedOpenPath ω (↑R.vertices) Q.largePath := by
  rintro ⟨n, γ, hγ⟩
  obtain ⟨i, j, t, hlarge⟩ := hγ.1
  have hi := (IntegerCube.mem_vertices R (γ i)).mp (hγ.mem_region i) t
  have hj := (IntegerCube.mem_vertices R (γ j)).mp (hγ.mem_region j) t
  have habs : |γ i t - γ j t| ≤ (R.size : ℤ) - 1 := by
    apply abs_le.mpr
    omega
  omega

/-- If no selected open path exists, the crossing-anchor condition is
satisfied regardless of the configuration. -/
theorem TriadicCube.hasCrossingAnchor_of_no_selected_path {d : ℕ}
    (Q : TriadicCube d) (R : IntegerCube d) (ω : Configuration d)
    (h : ¬ HasSelectedOpenPath ω (↑R.vertices) Q.largePath) :
    Q.hasCrossingAnchor R ω := by
  intro hselected
  exact (h hselected).elim

end Rigidity.Percolation
