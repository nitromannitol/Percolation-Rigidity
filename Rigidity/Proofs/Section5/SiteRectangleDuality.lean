import Rigidity.Proofs.Section5.SparseOpenPaths
import Rigidity.Proofs.Section5.MengerRays
import PercolationClusterHomogenization.Vendor.FormalMathPercolation.Literature.PlanarDuality

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
    {G : SimpleGraph (LatticeModels.Site 2)} (hG : G ≤ LatticeModels.zdGraph 2)
    (w : G.Walk u v) :
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
    have hc := separating_edge_corners (hG h)
    have hxu : IsFaceCorner u x := by rcases hx with rfl | rfl <;> tauto
    have hxu' : IsFaceCorner u' x := by rcases hx with rfl | rfl <;> tauto
    obtain ⟨b, hb, hbA, hxb⟩ := ih x hxu' hxA (fun d hd => hw d (by simp [hd]))
    exact ⟨b, hb, hbA, (face_corners_star_reachable ha hxu haA hxA).trans hxb⟩

/-- If a coloring changes across a rectangle and every bichromatic edge meets `A`, then `A`
contains a top-to-bottom star connection. -/
theorem star_connection_of_bichromatic_edges (c : LatticeModels.Site 2 → Prop) (m n : ℕ)
    {A : Set PlanarCarrier} (hL : ∀ x ∈ leftSide m n, c x)
    (hR : ∀ x ∈ rightSide m n, ¬c x)
    (hA : ∀ z z', (bichromaticGraph c m n).Adj z z' →
      ∃ x, (x = sepLo z z' ∨ x = sepHi z z') ∧ (x 0, x 1) ∈ A) :
    ∃ x y : LatticeModels.Site 2, x ∈ rectangle m n ∧ x 1 = n ∧
      (x 0, x 1) ∈ A ∧ (y 0, y 1) ∈ A ∧ (n : ℤ) ≤ |x 1 - y 1| ∧
        (starGraphOn A).Reachable (x 0, x 1) (y 0, y 1) := by
  obtain ⟨v, hv, t, ht, ⟨w⟩⟩ := exists_topReach_dualBottomSide hL hR
  have ht' : t 1 = n := (Finset.mem_filter.1 ht).2
  have hv' : v 1 = -1 := (Finset.mem_filter.1 hv).2
  cases w with
  | nil => omega
  | @cons t t' v hadj q =>
    obtain ⟨x, hx, hxA⟩ := hA t t' hadj
    have hxrect : x ∈ rectangle m n := by
      rcases hx with rfl | rfl
      · exact hadj.2.2.2.1
      · exact hadj.2.2.2.2.1
    have hcorner : IsFaceCorner t x := by
      have hc := separating_edge_corners hadj.1
      rcases hx with rfl | rfl <;> tauto
    have hx1 : x 1 = n := by
      have hr := (mem_rectangle_iff.mp hxrect)
      rcases hcorner with ⟨_, _, hl, _⟩
      omega
    let G := bichromaticGraph c m n
    have hG : G ≤ LatticeModels.zdGraph 2 := fun _ _ h => h.1
    obtain ⟨y, hy, hyA, hxy⟩ := faceWalk_star_reachable hG
      (SimpleGraph.Walk.cons hadj q) x hcorner hxA (fun d _ => hA _ _ d.adj)
    refine ⟨x, y, hxrect, hx1, hxA, hyA, ?_, hxy⟩
    have hy1 : y 1 ≤ 0 := by
      rcases hy with ⟨_, _, _, hu⟩
      omega
    exact (by omega : (n : ℤ) ≤ x 1 - y 1) |>.trans (le_abs_self _)

/-- A vertex separator of the horizontal crossings of a rectangle contains a vertical star
connection. -/
theorem star_connection_of_rectangle_separator (m n : ℕ) (hm : 0 < m)
    (A : Set PlanarCarrier)
    (hsep : Menger.Separates
      (Menger.edgesIn (LatticeModels.zdGraph 2) (Finset.finite_toSet (rectangle m n)))
      (↑(leftSide m n)) (↑(rightSide m n)) {x | (x 0, x 1) ∈ A}) :
    ∃ x y : LatticeModels.Site 2, x ∈ rectangle m n ∧ x 1 = n ∧
      (x 0, x 1) ∈ A ∧ (y 0, y 1) ∈ A ∧ (n : ℤ) ≤ |x 1 - y 1| ∧
        (starGraphOn A).Reachable (x 0, x 1) (y 0, y 1) := by
  classical
  let E := Menger.edgesIn (LatticeModels.zdGraph 2) (Finset.finite_toSet (rectangle m n))
  let S : Set (LatticeModels.Site 2) := {x | (x 0, x 1) ∈ A}
  let c : LatticeModels.Site 2 → Prop := fun x =>
    x ∈ leftSide m n ∨ Menger.ReachAvoid E (↑(leftSide m n)) S x
  have hcL : ∀ x ∈ leftSide m n, c x := fun _ hx => Or.inl hx
  have hcR : ∀ x ∈ rightSide m n, ¬c x := by
    intro x hx hcx
    rcases hcx with hxL | ⟨l, hl, hlS⟩
    · have hx0 := (Finset.mem_filter.1 hxL).2
      have hx1 := (Finset.mem_filter.1 hx).2
      omega
    · obtain ⟨b, hb, hbx⟩ := hl.2.2
      have hbx' : b = x := hbx
      subst b
      obtain ⟨v, hv, hvS⟩ := hsep l ⟨hl.1, hl.2.1, x, hb, hx⟩
      exact hlS v hv hvS
  have hprop {x y : LatticeModels.Site 2} (hx : x ∉ S) (hy : y ∉ S)
      (he : s(x, y) ∈ E) (hcx : c x) : c y := by
    apply Or.inr
    rcases hcx with hxL | hxR
    · exact (Menger.reachAvoid_self hxL hx).step he hy
    · exact hxR.step he hy
  apply star_connection_of_bichromatic_edges c m n hcL hcR
  intro z z' hz
  by_contra hnone
  have hx : sepLo z z' ∉ S := fun h => hnone ⟨_, Or.inl rfl, h⟩
  have hy : sepHi z z' ∉ S := fun h => hnone ⟨_, Or.inr rfl, h⟩
  have he : s(sepLo z z', sepHi z z') ∈ E := Menger.mem_edgesIn.2
    ⟨(LatticeModels.zdGraph 2).mem_edgeSet.1 (sepEdge_mem_edgeSet hz.1),
      hz.2.2.2.1, hz.2.2.2.2.1⟩
  have hb := hz.2.2.2.2.2
  by_cases hc : c (sepLo z z')
  · exact (hb.mp hc) (hprop hx hy he hc)
  · have hd : c (sepHi z z') := by
      by_contra hd
      exact hc (hb.mpr hd)
    have he' : s(sepHi z z', sepLo z z') ∈ E := by rwa [Sym2.eq_swap]
    exact hc (hprop hy hx he' hd)

end Rigidity.Proofs.Section5
