import Rigidity.Percolation.WellConnectedRegions

/-!
# Integer lattice cubes

An integer cube consists of lattice points in a half-open product of integer
intervals. Its marked faces are the two extreme lattice slices in each
coordinate.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation

noncomputable section

/-- A half-open lattice cube, specified by a corner and side length. -/
structure IntegerCube (d : ℕ) where
  corner : Vertex d
  size : ℕ

/-- The finite set of vertices in the cube. -/
def IntegerCube.vertices {d : ℕ} (Q : IntegerCube d) : Finset (Vertex d) :=
  Fintype.piFinset fun i => Finset.Ico (Q.corner i) (Q.corner i + (Q.size : ℤ))

/-- A point belongs to the cube exactly when every coordinate lies in its
half-open interval. -/
theorem IntegerCube.mem_vertices {d : ℕ} (Q : IntegerCube d) (x : Vertex d) :
    x ∈ Q.vertices ↔ ∀ i, Q.corner i ≤ x i ∧ x i < Q.corner i + (Q.size : ℤ) := by
  simp only [vertices, Fintype.mem_piFinset, Finset.mem_Ico]

/-- The lower face in the given coordinate direction. -/
def IntegerCube.lowerFace {d : ℕ} (Q : IntegerCube d) (i : Fin d) : Finset (Vertex d) :=
  Q.vertices.filter fun x => x i = Q.corner i

/-- The upper face in the given coordinate direction. -/
def IntegerCube.upperFace {d : ℕ} (Q : IntegerCube d) (i : Fin d) : Finset (Vertex d) :=
  Q.vertices.filter fun x => x i + 1 = Q.corner i + (Q.size : ℤ)

/-- The region and faces of a cube, as a finite signature. -/
def IntegerCube.signature {d : ℕ} (Q : IntegerCube d) : RegionSignature d :=
  (Q.vertices, Q.lowerFace, Q.upperFace)

/-- Membership in a lower face is membership in the cube and equality to its
lower endpoint in the given coordinate. -/
theorem IntegerCube.mem_lowerFace {d : ℕ} (Q : IntegerCube d) (i : Fin d) (x : Vertex d) :
    x ∈ Q.lowerFace i ↔ x ∈ Q.vertices ∧ x i = Q.corner i := by
  simp only [lowerFace, Finset.mem_filter]

/-- Membership in an upper face is membership in the cube and equality to its
largest coordinate in the given direction. -/
theorem IntegerCube.mem_upperFace {d : ℕ} (Q : IntegerCube d) (i : Fin d) (x : Vertex d) :
    x ∈ Q.upperFace i ↔ x ∈ Q.vertices ∧ x i + 1 = Q.corner i + (Q.size : ℤ) := by
  simp only [upperFace, Finset.mem_filter]


/-- The signatures of an arbitrary collection of integer cubes. -/
def IntegerCube.signatures {d : ℕ} (S : Set (IntegerCube d)) : Set (RegionSignature d) :=
  IntegerCube.signature '' S

/-- Quantifying over cube signatures is equivalent to quantifying over the
cubes themselves. -/
theorem IntegerCube.forall_signatures_iff {d : ℕ} (S : Set (IntegerCube d))
    (P : RegionSignature d → Prop) :
    (∀ T ∈ signatures S, P T) ↔ ∀ Q ∈ S, P Q.signature := by
  constructor
  · intro h Q hQ
    exact h Q.signature ⟨Q, hQ, rfl⟩
  · intro h T hT
    obtain ⟨Q, hQ, rfl⟩ := hT
    exact h Q hQ


/-- The half-open integer cube corresponding to a triadic cube. -/
def TriadicCube.toIntegerCube {d : ℕ} (Q : TriadicCube d) : IntegerCube d where
  corner i := Q.side * Q.index i - Q.side / 2
  size := 3 ^ Q.scale

/-- The integer and centered descriptions have the same vertices. -/
theorem TriadicCube.mem_toIntegerCube_vertices {d : ℕ} (Q : TriadicCube d) (x : Vertex d) :
    x ∈ Q.toIntegerCube.vertices ↔ x ∈ Q.vertices := by
  have ho : Odd Q.side := by
    dsimp only [side]
    exact (show Odd (3 : ℤ) from ⟨1, by norm_num⟩).pow
  have hm : Q.side % 2 = 1 := Int.odd_iff.mp ho
  have hd := Int.emod_add_mul_ediv Q.side 2
  rw [IntegerCube.mem_vertices]
  change (∀ i, Q.side * Q.index i - Q.side / 2 ≤ x i ∧
    x i < Q.side * Q.index i - Q.side / 2 + ((3 ^ Q.scale : ℕ) : ℤ)) ↔
    (∀ i, |2 * (x i - Q.side * Q.index i)| < Q.side)
  have hcast : ((3 ^ Q.scale : ℕ) : ℤ) = Q.side := by simp only [side, Nat.cast_pow, Nat.cast_ofNat]
  rw [hcast]
  constructor <;> intro h i
  · have hi := h i
    rw [abs_lt]
    omega
  · have hi := (abs_lt.mp (h i))
    omega

end

end Rigidity.Percolation
