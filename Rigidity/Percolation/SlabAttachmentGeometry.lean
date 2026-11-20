import Rigidity.Percolation.SlabAttachment
import Rigidity.Percolation.CoalescenceCover

/-!
# Gluing paths across slab boundaries

Open boundary bonds join paths in an explored region to paths in a fresh slab.
Two such bonds join two previously explored components through the slab.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation Rigidity.External

/-- An open boundary bond joins a past path to a slab path in the ambient
region. -/
theorem reachable_openIn_of_slab_attachment {d : ℕ} {ω : Configuration d}
    {P S D : Set (Vertex d)} (hPD : P ⊆ D) (hSD : S ⊆ D)
    {z x y w : Vertex d} (hx : x ∈ P) (hy : y ∈ S)
    (hxy : (nearestNeighborGraph d).Adj x y) (hopen : ω (bondOfAdjacent hxy) = true)
    (hzx : (openIn ω P).Reachable z x) (hyw : (openIn ω S).Reachable y w) :
    (openIn ω D).Reachable z w := by
  have hbond : (openIn ω D).Adj x y :=
    ⟨(openGraph_adj_iff ω x y).mpr ⟨hxy, hopen⟩, hPD hx, hSD hy⟩
  exact ((reachable_openIn_mono hPD hzx).trans hbond.reachable).trans
    (reachable_openIn_mono hSD hyw)

/-- Two open boundary bonds and a slab path join the past components of their
endpoints in the ambient region. -/
theorem reachable_openIn_of_two_slab_attachments {d : ℕ} {ω : Configuration d}
    {P S D : Set (Vertex d)} (hPD : P ⊆ D) (hSD : S ⊆ D)
    {z x y y' x' z' : Vertex d}
    (hx : x ∈ P) (hy : y ∈ S) (hx' : x' ∈ P) (hy' : y' ∈ S)
    (hxy : (nearestNeighborGraph d).Adj x y) (hx'y' : (nearestNeighborGraph d).Adj x' y')
    (hopen : ω (bondOfAdjacent hxy) = true)
    (hopen' : ω (bondOfAdjacent hx'y') = true)
    (hzx : (openIn ω P).Reachable z x) (hyy' : (openIn ω S).Reachable y y')
    (hz'x' : (openIn ω P).Reachable z' x') : (openIn ω D).Reachable z z' := by
  have hleft := reachable_openIn_of_slab_attachment hPD hSD hx hy hxy hopen hzx hyy'
  have hright := reachable_openIn_of_slab_attachment hPD hSD hx' hy' hx'y' hopen'
    hz'x' (SimpleGraph.Reachable.refl y')
  exact hleft.trans hright.symm

end Rigidity.Percolation
