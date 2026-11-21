import Rigidity.Proofs.Section5.SiteRectangleCrossings

/-!
# Intersections of site crossings

Horizontal and vertical lattice crossings of a rectangle share a site.
-/

open LatticeProb.Percolation Percolation.Literature

namespace Rigidity.Proofs.Section5

/-- Every vertex in a chain has a property that holds at its head and propagates along edges. -/
theorem all_of_chain_head {V : Type*} {r : V → V → Prop} {P : V → Prop} :
    ∀ l : List V, l.IsChain r → (∀ a ∈ l.head?, P a) →
      (∀ a b, r a b → P b) → ∀ a ∈ l, P a
  | [], _, _, _, a, ha => by simp at ha
  | x :: l, hc, hh, hs, a, ha => by
    rcases List.mem_cons.1 ha with rfl | ha
    · exact hh a rfl
    · exact all_of_chain_head l hc.tail (fun b hb => hs x b ((List.isChain_cons.1 hc).1 b hb))
        hs a ha

/-- A link walk whose initial side lies in a finite region and whose edges are restricted to that
region stays in it. -/
theorem linkWalk_mem_region {V : Type*} {G : SimpleGraph V} {D A B : Set V} (hD : D.Finite)
    (hA : A ⊆ D) {l : List V} (hl : Menger.IsLinkWalk (Menger.edgesIn G hD) A B l) :
    ∀ z ∈ l, z ∈ D := by
  apply all_of_chain_head l hl.1 ?_ (fun a b h => (Menger.mem_edgesIn.1 h).2.2)
  obtain ⟨a, ha, haA⟩ := hl.2.1
  intro b hb
  have hab : a = b := by
    rw [Option.mem_def] at ha hb
    exact Option.some.inj (ha.symm.trans hb)
  exact hab ▸ hA haA

/-- The head of a link walk lies in its initial set. -/
theorem linkWalk_head_mem {V : Type*} {E : Finset (Sym2 V)} {A B : Set V}
    {l : List V} (hl : Menger.IsLinkWalk E A B l) : l.head hl.ne_nil ∈ A := by
  obtain ⟨a, ha, haA⟩ := hl.2.1
  rw [List.head?_eq_some_head hl.ne_nil, Option.mem_def, Option.some.injEq] at ha
  exact ha ▸ haA

/-- The last vertex of a link walk lies in its final set. -/
theorem linkWalk_last_mem {V : Type*} {E : Finset (Sym2 V)} {A B : Set V}
    {l : List V} (hl : Menger.IsLinkWalk E A B l) : l.getLast hl.ne_nil ∈ B := by
  obtain ⟨a, ha, haB⟩ := hl.2.2
  rw [List.getLast?_eq_some_getLast hl.ne_nil, Option.mem_def, Option.some.injEq] at ha
  exact ha ▸ haB

/-- A link walk maps to a link walk when its edges and endpoint sets are preserved. -/
theorem linkWalk_map {V W : Type*} {E : Finset (Sym2 V)} {F : Finset (Sym2 W)}
    {A B : Set V} {A' B' : Set W} {l : List V} (f : V → W)
    (hl : Menger.IsLinkWalk E A B l)
    (hE : ∀ a b, s(a, b) ∈ E → s(f a, f b) ∈ F)
    (hA : ∀ a ∈ A, f a ∈ A') (hB : ∀ b ∈ B, f b ∈ B') :
    Menger.IsLinkWalk F A' B' (l.map f) := by
  refine ⟨(List.isChain_map f).2 (hl.1.imp hE), ?_, ?_⟩
  · obtain ⟨a, ha, haA⟩ := hl.2.1
    refine ⟨f a, ?_, hA a haA⟩
    rw [Option.mem_def] at ha ⊢
    simp only [List.head?_map, ha, Option.map_some]
  · obtain ⟨b, hb, hbB⟩ := hl.2.2
    refine ⟨f b, ?_, hB b hbB⟩
    rw [Option.mem_def] at hb ⊢
    simp only [List.getLast?_map, hb, Option.map_some]

/-- Horizontal and vertical site link walks inside one rectangle meet. -/
theorem rectangle_link_crossings_intersect {η : PlanarCarrier → Bool} {m n : ℕ}
    {H V : List (LatticeModels.Site 2)}
    (hH : Menger.IsLinkWalk
      (Menger.edgesIn (planarOpenSiteGraph η) (Finset.finite_toSet (rectangle m n)))
      (↑(leftSide m n)) (↑(rightSide m n)) H)
    (hV : Menger.IsLinkWalk
      (Menger.edgesIn (planarOpenSiteGraph η) (Finset.finite_toSet (rectangle m n)))
      (↑(bottomSide m n)) (↑(topSide m n)) V) : ∃ z ∈ H, z ∈ V := by
  have hHchain : H.IsChain (LatticeModels.zdGraph 2).Adj :=
    hH.1.imp fun _ _ he => ((Menger.mem_edgesIn (G := planarOpenSiteGraph η)).1 he).1.1
  have hVchain : V.IsChain (LatticeModels.zdGraph 2).Adj :=
    hV.1.imp fun _ _ he => ((Menger.mem_edgesIn (G := planarOpenSiteGraph η)).1 he).1.1
  let P := SimpleGraph.Walk.ofSupport H hH.ne_nil hHchain
  let Q := SimpleGraph.Walk.ofSupport V hV.ne_nil hVchain
  have hP : ∀ z ∈ P.support, 0 ≤ z 0 ∧ z 0 ≤ m ∧ 0 ≤ z 1 ∧ z 1 ≤ n := by
    intro z hz
    have hzH : z ∈ H := by simpa only [P, SimpleGraph.Walk.support_ofSupport] using hz
    apply mem_rectangle_iff.1
    exact linkWalk_mem_region _ (fun z hz => (Finset.mem_filter.1 hz).1) hH z hzH
  have hQ : ∀ z ∈ Q.support, 0 ≤ z 0 ∧ z 0 ≤ m ∧ 0 ≤ z 1 ∧ z 1 ≤ n := by
    intro z hz
    have hzV : z ∈ V := by simpa only [Q, SimpleGraph.Walk.support_ofSupport] using hz
    apply mem_rectangle_iff.1
    exact linkWalk_mem_region _ (fun z hz => (Finset.mem_filter.1 hz).1) hV z hzV
  have ha := (Finset.mem_filter.1 (linkWalk_head_mem hH)).2
  have hb := (Finset.mem_filter.1 (linkWalk_last_mem hH)).2
  have hc := (Finset.mem_filter.1 (linkWalk_head_mem hV)).2
  have hd := (Finset.mem_filter.1 (linkWalk_last_mem hV)).2
  obtain ⟨z, hzP, hzQ⟩ := exists_mem_support_of_crossing P Q hP hQ ha hb hc hd
  refine ⟨z, ?_, ?_⟩
  · simpa only [P, SimpleGraph.Walk.support_ofSupport] using hzP
  · simpa only [Q, SimpleGraph.Walk.support_ofSupport] using hzQ

end Rigidity.Proofs.Section5
