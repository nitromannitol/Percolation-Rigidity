import Rigidity.Percolation.IntegerCubeCoverGraph
import Rigidity.Percolation.IntegerCubeBufferedCover

/-!
# Coalescence through subcubes

Uniform coalescence and crossing properties on smaller cubes glue into
coalescence of sufficiently long paths in an ambient cube.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation Rigidity.External

/-- The possible corners of subcubes of a given side length. -/
def IntegerCube.cornerCube {d : ℕ} (Q : IntegerCube d) (s : ℕ) : IntegerCube d where
  corner := Q.corner
  size := Q.size - s + 1

/-- The cube with a given corner and side length. -/
def IntegerCube.atCorner {d : ℕ} (x : Vertex d) (s : ℕ) : IntegerCube d :=
  ⟨x, s⟩

/-- A cube whose corner lies in the corner cube is contained in the ambient cube. -/
theorem IntegerCube.atCorner_subset {d : ℕ} (Q : IntegerCube d) (s : ℕ)
    (hs : s ≤ Q.size) {x : Vertex d} (hx : x ∈ (Q.cornerCube s).vertices) :
    (↑(IntegerCube.atCorner x s).vertices : Set (Vertex d)) ⊆ Q.vertices := by
  have hcast : ((Q.size - s : ℕ) : ℤ) = (Q.size : ℤ) - s := by
    exact Nat.cast_sub hs
  intro y hy
  change y ∈ (IntegerCube.atCorner x s).vertices at hy
  change y ∈ Q.vertices
  rw [IntegerCube.mem_vertices] at hx hy ⊢
  intro i
  have hx' := hx i
  have hy' := hy i
  dsimp only [cornerCube] at hx'
  dsimp only [atCorner] at hy'
  simp only [Nat.cast_add, Nat.cast_one] at hx'
  omega

/-- The clamped buffered subcube has its corner in the corner cube. -/
theorem IntegerCube.bufferedSubcube_corner_mem {d : ℕ} (Q : IntegerCube d)
    (s : ℕ) (R : ℤ) (hs : s ≤ Q.size) (x : Vertex d) :
    (Q.bufferedSubcube s R x).corner ∈ (Q.cornerCube s).vertices := by
  have hcast : ((Q.size - s : ℕ) : ℤ) = (Q.size : ℤ) - s := by
    exact Nat.cast_sub hs
  rw [IntegerCube.mem_vertices]
  intro i
  dsimp only [cornerCube, bufferedSubcube]
  simp only [Nat.cast_add, Nat.cast_one]
  have hs' : (s : ℤ) ≤ Q.size := by exact_mod_cast hs
  omega

/-- Coalescence on all subcubes of side `s`, together with crossings of all
subcubes of side `k`, yields coalescence of long paths in the ambient cube. -/
theorem IntegerCube.largePathsCoalesce_of_subcube_estimates {d : ℕ}
    (hd : 0 < d) (Q : IntegerCube d) (s k : ℕ) (R : ℤ)
    (hR : 0 < R) (hsR : 2 * R + 1 ≤ (s : ℤ))
    (hks : k + 1 ≤ s) (hRk : R ≤ (k : ℤ) - 1) (hsQ : s ≤ Q.size)
    {ω : Configuration d}
    (large : (n : ℕ) → (Fin (n + 1) → Vertex d) → Prop)
    (hdiam : ∀ n γ, large n γ → pathDiameterAtLeast R n γ)
    (hcoal : ∀ T : IntegerCube d, T.size = s →
      (↑T.vertices : Set (Vertex d)) ⊆ Q.vertices →
      LargePathsCoalesce ω (↑T.vertices) (pathDiameterAtLeast R))
    (hcross : ∀ T : IntegerCube d, T.size = k →
      (↑T.vertices : Set (Vertex d)) ⊆ Q.vertices →
      HasCrossingComponent ω (↑T.vertices)
        (fun i => ↑(T.lowerFace i)) (fun i => ↑(T.upperFace i))) :
    LargePathsCoalesce ω (↑Q.vertices) large := by
  let C := Q.cornerCube s
  let B : {x : Vertex d // x ∈ C.vertices} → Set (Vertex d) :=
    fun x => (IntegerCube.atCorner x.val s).vertices
  have hBD : ∀ x, B x ⊆ (↑Q.vertices : Set (Vertex d)) := by
    intro x
    exact Q.atCorner_subset s hsQ x.property
  apply largePathsCoalesce_of_buffered_crossing_cover hd C.neighborGraph B
    (↑Q.vertices) R hR large hBD
  · intro x
    exact hcoal (IntegerCube.atCorner x.val s) rfl (hBD x)
  · intro x
    have hcorner : ∀ i, |x.val i - x.val i| + (k : ℤ) ≤
        (IntegerCube.atCorner x.val s).size := by
      intro i
      simp only [sub_self, abs_zero, zero_add, atCorner]
      exact_mod_cast (show k ≤ s by omega)
    obtain ⟨T, hTk, hT, _⟩ :=
      (IntegerCube.atCorner x.val s).exists_cube_in_intersection_of_corner_dist
        (IntegerCube.atCorner x.val s) k rfl hcorner
    exact T.hasSelectedOpenPath_of_crossing_subset hd R (by rw [hTk]; exact hRk)
      hT (hcross T hTk (hT.trans (hBD x)))
  · intro x y hxy
    have hcorner : ∀ i, |x.val i - y.val i| + (k : ℤ) ≤
        (IntegerCube.atCorner x.val s).size := by
      intro i
      have hc := hxy.2 i
      have hks' : (k : ℤ) + 1 ≤ s := by exact_mod_cast hks
      change |x.val i - y.val i| + (k : ℤ) ≤ (s : ℤ)
      omega
    obtain ⟨T, hTk, hTx, hTy⟩ :=
      (IntegerCube.atCorner x.val s).exists_cube_in_intersection_of_corner_dist
        (IntegerCube.atCorner y.val s) k rfl hcorner
    refine ⟨T, by rw [hTk]; exact hRk, ?_, hcross T hTk (hTx.trans (hBD x))⟩
    exact Set.subset_inter hTx hTy
  · intro x y
    apply C.neighborGraph_reachable
    dsimp only [C, cornerCube]
    omega
  · exact hdiam
  · intro x hx
    have hspec := Q.bufferedSubcube_spec s R hsR hsQ x hx
    let z := (Q.bufferedSubcube s R x).corner
    have hz : z ∈ C.vertices := Q.bufferedSubcube_corner_mem s R hsQ x
    refine ⟨⟨z, hz⟩, ?_⟩
    intro y hy hnear
    have hmem := hspec.2 y hy hnear
    change y ∈ (IntegerCube.atCorner z s).vertices
    exact hmem

end Rigidity.Percolation
