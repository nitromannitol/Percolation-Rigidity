import Rigidity.Proofs.Section5.SparseOpenPaths
import Rigidity.Vendor.FormalMathPercolation.Literature.PlanarDuality

/-!
# Face boundaries and planar site paths

The endpoints of an edge separating neighboring square faces are corners of both faces.
-/

open Percolation.Literature Rigidity.Steps.Section5 LatticeProb.Percolation

namespace Rigidity.Proofs.Section5

/-- A vertex is a corner of the unit square with the given lower-left corner. -/
def IsFaceCorner (z x : LatticeModels.Site 2) : Prop :=
  z 0 ≤ x 0 ∧ x 0 ≤ z 0 + 1 ∧ z 1 ≤ x 1 ∧ x 1 ≤ z 1 + 1

/-- Both endpoints of an edge between two adjacent faces are corners of each face. -/
theorem separating_edge_corners {z z' : LatticeModels.Site 2}
    (h : (LatticeModels.zdGraph 2).Adj z z') :
    IsFaceCorner z (sepLo z z') ∧ IsFaceCorner z (sepHi z z') ∧
      IsFaceCorner z' (sepLo z z') ∧ IsFaceCorner z' (sepHi z z') := by
  have hstep := stepKind_of_adj h
  rcases hstep with ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h1, h0⟩ | ⟨h1, h0⟩ <;>
    simp only [IsFaceCorner, sepLo, sepHi, Pi.sup_apply, Pi.add_apply,
      Pi.single_apply, Fin.isValue] <;>
    split_ifs <;> omega

/-- Two corners of one face are joined by a star step when both belong to the set. -/
theorem face_corners_star_reachable {A : Set PlanarCarrier}
    {z x y : LatticeModels.Site 2} (hx : IsFaceCorner z x) (hy : IsFaceCorner z y)
    (hxA : (x 0, x 1) ∈ A) (hyA : (y 0, y 1) ∈ A) :
    (starGraphOn A).Reachable (x 0, x 1) (y 0, y 1) := by
  by_cases hxy : (x 0, x 1) = (y 0, y 1)
  · rw [hxy]
  · apply SimpleGraph.Adj.reachable
    rcases hx with ⟨hx0, hx0', hx1, hx1'⟩
    rcases hy with ⟨hy0, hy0', hy1, hy1'⟩
    refine ⟨hxy, ?_, ?_, hxA, hyA⟩
    · change |x 0 - y 0| ≤ 1
      exact abs_le.mpr ⟨by omega, by omega⟩
    · change |x 1 - y 1| ≤ 1
      exact abs_le.mpr ⟨by omega, by omega⟩

/-- A face walk whose separating edges meet `A` gives a star connection through `A` between
corners of its initial and final faces. -/
theorem faceWalk_star_reachable {A : Set PlanarCarrier} {u v : LatticeModels.Site 2}
    (w : (LatticeModels.zdGraph 2).Walk u v) :
    ∀ a, IsFaceCorner u a → (a 0, a 1) ∈ A →
      (∀ d ∈ w.darts, ∃ x, (x = sepLo d.fst d.snd ∨ x = sepHi d.fst d.snd) ∧
        (x 0, x 1) ∈ A) →
      ∃ b, IsFaceCorner v b ∧ (b 0, b 1) ∈ A ∧
        (starGraphOn A).Reachable (a 0, a 1) (b 0, b 1) := by
  induction w with
  | nil =>
    intro a ha haA _
    exact ⟨a, ha, haA, SimpleGraph.Reachable.refl _⟩
  | @cons u u' v h w ih =>
    intro a ha haA hw
    obtain ⟨x, hx, hxA⟩ := hw ⟨(u, u'), h⟩ (by simp)
    have hc := separating_edge_corners h
    have hxu : IsFaceCorner u x := by rcases hx with rfl | rfl <;> tauto
    have hxu' : IsFaceCorner u' x := by rcases hx with rfl | rfl <;> tauto
    obtain ⟨b, hb, hbA, hxb⟩ := ih x hxu' hxA (fun d hd => hw d (by simp [hd]))
    exact ⟨b, hb, hbA, (face_corners_star_reachable ha hxu haA hxA).trans hxb⟩

end Rigidity.Proofs.Section5
