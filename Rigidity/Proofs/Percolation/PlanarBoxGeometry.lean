import Rigidity.External.WellConnected
import Rigidity.Proofs.Section5.LoopFromCrossings
import Rigidity.Proofs.S3.ChemicalDistance

/-!
# Intersections of planar cube crossings

Horizontal and vertical open crossings of a planar cube are joined inside the cube.
-/

open LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5

namespace Rigidity.Percolation

/-- A cluster inside a planar cube that crosses it in both directions. -/
def IsCrossingCluster (ω : Configuration 2) (x : Vertex 2) (N : ℕ)
    (V : Set (Vertex 2)) : Prop :=
  (∃ a ∈ cubeAt x N, V = {y | (openIn ω (cubeAt x N)).Reachable a y}) ∧ CrossesCube x N V

/-- Horizontal and vertical open paths crossing a cube meet inside it. -/
theorem cube_crossings_meet {ω : Configuration 2} {x : Vertex 2} {N : ℕ}
    {a b c d : Vertex 2}
    (ha : a 0 = x 0 - N) (hb : b 0 = x 0 + N)
    (hc : c 1 = x 1 - N) (hd : d 1 = x 1 + N)
    (hH : ReachIn ω (cubeAt x N) a b) (hV : ReachIn ω (cubeAt x N) c d) :
    ∃ w, ReachIn ω (cubeAt x N) a w ∧ ReachIn ω (cubeAt x N) c w := by
  apply exists_reachIn_of_crossing hH hV
    (xa := x 0 - N) (xb := x 0 + N) (ya := x 1 - N) (yb := x 1 + N)
  · intro w hw
    have h := abs_le.mp (hw 1)
    constructor <;> omega
  · intro w hw
    have h := abs_le.mp (hw 0)
    constructor <;> omega
  · exact le_of_eq ha
  · exact le_of_eq hb.symm
  · exact le_of_eq hc
  · exact le_of_eq hd.symm

/-- Horizontal and vertical crossings of a cube belong to the same open cluster in the cube. -/
theorem cube_crossings_connected {ω : Configuration 2} {x : Vertex 2} {N : ℕ}
    {a b c d : Vertex 2}
    (ha : a 0 = x 0 - N) (hb : b 0 = x 0 + N)
    (hc : c 1 = x 1 - N) (hd : d 1 = x 1 + N)
    (hH : ReachIn ω (cubeAt x N) a b) (hV : ReachIn ω (cubeAt x N) c d) :
    ReachIn ω (cubeAt x N) a c := by
  obtain ⟨w, h₁, h₂⟩ := cube_crossings_meet ha hb hc hd hH hV
  exact h₁.trans h₂.symm

/-- An open path contained in a set is a path of the open graph restricted to that set. -/
theorem reachIn_reachable_openIn {ω : Configuration 2} {S : Set (Vertex 2)}
    {a b : Vertex 2} (h : ReachIn ω S a b) : (openIn ω S).Reachable a b := by
  obtain ⟨W, hW⟩ := h
  have key : ∀ {u v : Vertex 2} (P : (openGraph ω).Walk u v),
      (∀ w ∈ P.support, w ∈ S) → (openIn ω S).Reachable u v := by
    intro u v P
    induction P with
    | nil =>
      intro _
      exact SimpleGraph.Reachable.refl _
    | @cons u v w huv P ih =>
      intro hP
      have hu : u ∈ S := hP u (by simp)
      have hv : v ∈ S := hP v (by simp)
      have htail : ∀ z ∈ P.support, z ∈ S := fun z hz => hP z (by simp [hz])
      have huv' : (openIn ω S).Adj u v := ⟨huv, hu, hv⟩
      exact huv'.reachable.trans (ih htail)
  exact key W hW

/-- A path in the restricted open graph remains inside the restriction set. -/
theorem reachIn_of_reachable_openIn {ω : Configuration 2} {S : Set (Vertex 2)}
    {a b : Vertex 2} (ha : a ∈ S) (h : (openIn ω S).Reachable a b) : ReachIn ω S a b := by
  obtain ⟨P⟩ := h
  refine ⟨P.mapLe (Rigidity.Proofs.S3.openIn_le ω S), fun z hz => ?_⟩
  rw [SimpleGraph.Walk.support_mapLe_eq_support] at hz
  exact Rigidity.Proofs.S3.mem_of_mem_support_openIn P ha z hz

/-- Two transverse crossings give a cluster crossing the cube in both directions. -/
theorem exists_crossing_cluster_of_paths {ω : Configuration 2} {x : Vertex 2} {N : ℕ}
    {a b c d : Vertex 2}
    (ha : a 0 = x 0 - N) (hb : b 0 = x 0 + N)
    (hc : c 1 = x 1 - N) (hd : d 1 = x 1 + N)
    (hH : ReachIn ω (cubeAt x N) a b) (hV : ReachIn ω (cubeAt x N) c d) :
    ∃ u ∈ cubeAt x N, CrossesCube x N {y | (openIn ω (cubeAt x N)).Reachable u y} := by
  refine ⟨a, hH.start_mem, fun i => ?_⟩
  have hab := reachIn_reachable_openIn hH
  have hac := reachIn_reachable_openIn (cube_crossings_connected ha hb hc hd hH hV)
  have hcd := reachIn_reachable_openIn hV
  fin_cases i
  · exact ⟨⟨a, SimpleGraph.Reachable.refl _, ha⟩, ⟨b, hab, hb⟩⟩
  · exact ⟨⟨c, hac, hc⟩, ⟨d, hac.trans hcd, hd⟩⟩

/-- A planar cube has at most one cluster crossing it in both directions. -/
theorem crossing_clusters_unique {ω : Configuration 2} {x : Vertex 2} {N : ℕ}
    {a b : Vertex 2} (ha : a ∈ cubeAt x N) (hb : b ∈ cubeAt x N)
    (hA : CrossesCube x N {y | (openIn ω (cubeAt x N)).Reachable a y})
    (hB : CrossesCube x N {y | (openIn ω (cubeAt x N)).Reachable b y}) :
    {y | (openIn ω (cubeAt x N)).Reachable a y} =
      {y | (openIn ω (cubeAt x N)).Reachable b y} := by
  obtain ⟨⟨a₀, ha₀, ha₀face⟩, ⟨a₁, ha₁, ha₁face⟩⟩ := hA 0
  obtain ⟨⟨b₀, hb₀, hb₀face⟩, ⟨b₁, hb₁, hb₁face⟩⟩ := hB 1
  have ha₀mem := (reachIn_of_reachable_openIn ha ha₀).end_mem
  have hb₀mem := (reachIn_of_reachable_openIn hb hb₀).end_mem
  have hH := reachIn_of_reachable_openIn ha₀mem (ha₀.symm.trans ha₁)
  have hV := reachIn_of_reachable_openIn hb₀mem (hb₀.symm.trans hb₁)
  have hjoin := reachIn_reachable_openIn
    (cube_crossings_connected ha₀face ha₁face hb₀face hb₁face hH hV)
  have hab := ha₀.trans (hjoin.trans hb₀.symm)
  ext y
  exact ⟨fun hy => hab.symm.trans hy, fun hy => hab.trans hy⟩

/-- Transverse crossings give exactly one crossing cluster. -/
theorem existsUnique_crossing_cluster_of_paths {ω : Configuration 2} {x : Vertex 2} {N : ℕ}
    {a b c d : Vertex 2}
    (ha : a 0 = x 0 - N) (hb : b 0 = x 0 + N)
    (hc : c 1 = x 1 - N) (hd : d 1 = x 1 + N)
    (hH : ReachIn ω (cubeAt x N) a b) (hV : ReachIn ω (cubeAt x N) c d) :
    ∃! V, IsCrossingCluster ω x N V := by
  obtain ⟨u, hu, hcross⟩ := exists_crossing_cluster_of_paths ha hb hc hd hH hV
  refine ⟨{y | (openIn ω (cubeAt x N)).Reachable u y}, ⟨⟨u, hu, rfl⟩, hcross⟩, ?_⟩
  intro V ⟨⟨v, hv, hVeq⟩, hVcross⟩
  rw [hVeq] at hVcross ⊢
  exact crossing_clusters_unique hv hu hVcross hcross

end Rigidity.Percolation
