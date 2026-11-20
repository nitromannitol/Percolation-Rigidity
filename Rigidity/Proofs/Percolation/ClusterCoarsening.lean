import Rigidity.Proofs.Percolation.PlanarLocalConnectivity

/-!
# Coarsening along local cluster paths

The oscillation of a function along an open walk inside a finite region is at most the total
variation of the function over the open edges of the region. Combined with the local connectivity
of meshed planar cubes, this compares a function on the infinite cluster with its coarsening, the
value at the anchor of the partition cube (Armstrong and Dario, Lemmas 3.2 and 3.3, with the
neighbourhoods of the partition cubes replaced by the squares of side `9s`).
-/

open LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped Classical

namespace Rigidity.Percolation

/-- The total variation of `w` over the open edges inside a finite set, each edge counted in both
orientations. -/
noncomputable def edgeVariationIn {d : ℕ} (ω : Configuration d) (S : Finset (Vertex d))
    (w : Vertex d → ℝ) : ℝ :=
  ∑ x ∈ S, ∑ y ∈ S, if (openGraph ω).Adj x y then |w x - w y| else 0

theorem edgeVariationIn_nonneg {d : ℕ} (ω : Configuration d) (S : Finset (Vertex d))
    (w : Vertex d → ℝ) : 0 ≤ edgeVariationIn ω S w :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by
    split_ifs <;> positivity

/-- The oscillation along a walk is at most the sum of the increments along its darts. -/
theorem abs_sub_le_sum_darts {d : ℕ} {ω : Configuration d} (w : Vertex d → ℝ) {u v : Vertex d}
    (p : (openGraph ω).Walk u v) :
    |w u - w v| ≤ (p.darts.map fun e => |w e.fst - w e.snd|).sum := by
  induction p with
  | nil => simp
  | @cons a b c h p ih =>
    simp only [SimpleGraph.Walk.darts_cons, List.map_cons, List.sum_cons]
    calc |w a - w c| ≤ |w a - w b| + |w b - w c| := abs_sub_le _ _ _
      _ ≤ _ := add_le_add le_rfl ih

/-- **Oscillation along local open walks.** If two vertices are joined by an open walk inside a
finite set, the difference of a function at them is at most its total variation over the open
edges inside the set. -/
theorem abs_sub_le_edgeVariationIn {ω : Configuration 2} (S : Finset (Vertex 2))
    (w : Vertex 2 → ℝ) {a b : Vertex 2} (h : ReachIn ω ↑S a b) :
    |w a - w b| ≤ edgeVariationIn ω S w := by
  obtain ⟨W, hW⟩ := h
  set P := W.bypass
  have hPS : ∀ z ∈ P.support, z ∈ S := fun z hz =>
    Finset.mem_coe.1 (hW z (W.support_bypass_subset_support hz))
  have hnodup : P.darts.Nodup :=
    SimpleGraph.Walk.darts_nodup_of_support_nodup W.bypass_isPath.support_nodup
  refine (abs_sub_le_sum_darts w P).trans ?_
  set g : Vertex 2 × Vertex 2 → ℝ := fun q =>
    if (openGraph ω).Adj q.1 q.2 then |w q.1 - w q.2| else 0
  have hsum : (P.darts.map fun e => |w e.fst - w e.snd|).sum =
      ∑ q ∈ P.darts.toFinset.image (fun e => (e.fst, e.snd)), g q := by
    rw [Finset.sum_image (fun e _ e' _ h => SimpleGraph.Dart.ext e e' h)]
    rw [List.sum_toFinset _ hnodup]
    congr 1
    apply List.map_congr_left
    intro e _
    simp only [g, e.adj, if_true]
  rw [hsum]
  have hsub : P.darts.toFinset.image (fun e => (e.fst, e.snd)) ⊆ S ×ˢ S := by
    intro q hq
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hq
    have he' := List.mem_toFinset.1 he
    exact Finset.mem_product.2 ⟨hPS _ (P.dart_fst_mem_support_of_mem_darts he'),
      hPS _ (P.dart_snd_mem_support_of_mem_darts he')⟩
  calc ∑ q ∈ P.darts.toFinset.image (fun e => (e.fst, e.snd)), g q
      ≤ ∑ q ∈ S ×ˢ S, g q :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun q _ _ => by
          simp only [g]; split_ifs <;> positivity
    _ = edgeVariationIn ω S w := by
        rw [Finset.sum_product]
        rfl

/-- **Coarsening at a vertex** (planar form of Armstrong and Dario, Lemma 3.2). A vertex of a
meshed planar cube of side at least `1000` lying in an infinite open cluster differs from the
anchor of the cube, for any function, by at most the total variation of the function over the open
edges of the square of side `9s` around the cube. -/
theorem TriadicCube.abs_sub_planarAnchor_le {ω : Configuration 2} {Q : TriadicCube 2}
    (hQ : Q.planarMeshed ω) (hs : 1000 ≤ 3 ^ Q.scale) {x : Vertex 2} (hx : x ∈ Q.vertices)
    (hinf : ((openGraph ω).connectedComponentMk x).supp.Infinite) (w : Vertex 2 → ℝ) :
    |w x - w (Q.planarAnchor ω)| ≤ edgeVariationIn ω Q.ninefold.vertices w := by
  obtain ⟨-, -, hB⟩ := Q.planarAnchor_spec hQ hs
  have h := Q.reachIn_anchor_of_infinite hB hx hinf
  rw [abs_sub_comm]
  exact abs_sub_le_edgeVariationIn _ w h

/-- **Coarse gradient** (planar form of Armstrong and Dario, Lemma 3.3). The anchors of adjacent
meshed cubes, the second of the same or the next scale, differ by at most the total variation over
the open edges of the square of side `9s` around the first. -/
theorem TriadicCube.abs_planarAnchor_sub_le {ω : Configuration 2} {Q Q' : TriadicCube 2}
    (hQ : Q.planarMeshed ω) (hQ' : Q'.planarMeshed ω) (hs : 1000 ≤ 3 ^ Q.scale)
    (hscale : Q.scale ≤ Q'.scale) (hscale' : Q'.scale ≤ Q.scale + 1) {x y : Vertex 2}
    (hx : x ∈ Q.vertices) (hy : y ∈ Q'.vertices) (hnear : ∀ i, |x i - y i| ≤ 1)
    (w : Vertex 2 → ℝ) :
    |w (Q.planarAnchor ω) - w (Q'.planarAnchor ω)| ≤
      edgeVariationIn ω Q.ninefold.vertices w :=
  abs_sub_le_edgeVariationIn _ w
    (Q.reachIn_planarAnchor_of_near hQ hQ' hs hscale hscale' hx hy hnear)

end Rigidity.Percolation
