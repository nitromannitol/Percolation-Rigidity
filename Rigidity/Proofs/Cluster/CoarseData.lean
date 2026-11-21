import Rigidity.Percolation.IntegerCube

/-!
# Coarse-graining data on a cluster

Armstrong and Dario (Section 3.1) compare a function `w` on the cluster `C_*(U)` with its
coarsening `[w]_𝒫(x) = w(z̄(□_𝒫(x)))`, the value at the anchor of the partition cube of `x`. The
comparison uses only the following structure, recorded here in every dimension:
* a finite domain (the closure `cl_𝒫(U)`) containing a finite cluster;
* a partition cube `part x` containing `x` and contained in the domain, equal to the partition
  cube of each of its vertices;
* an anchor in the cluster and in the partition cube, depending only on the partition cube;
* for each vertex `x` of the cluster, a region `region x` such that `x` is joined to its anchor
  by an open path inside `region x ∩ C_*(U)`;
* for lattice neighbours `x, y` of the domain with different partition cubes, a region
  `pairRegion x y` such that the two anchors are joined by an open path inside
  `pairRegion x y ∩ C_*(U)`.

In Armstrong and Dario these regions are the union of the partition cubes at distance at most one
from `□_𝒫(x)`, respectively `□_𝒫(x) ∪ □_𝒫(y)`. The file also defines the magnitude
`|F|(x) = ((1/2) ∑_{y ∼ x} |F(x, y)|²)^{1/2}` of a gradient on a domain (Armstrong and Dario,
(1.4)) and proves the elementary bounds between it and the sum of the increments at `x`.
-/

open LatticeProb.Percolation
open scoped Classical

namespace Rigidity.Percolation

variable {d : ℕ}

/-- `x` and `y` are joined by an open path inside `S`. -/
def JoinedWithin (ω : Configuration d) (S : Set (Vertex d)) (x y : Vertex d) : Prop :=
  ∃ W : (openGraph ω).Walk x y, ∀ v ∈ W.support, v ∈ S

theorem JoinedWithin.symm {ω : Configuration d} {S : Set (Vertex d)} {x y : Vertex d}
    (h : JoinedWithin ω S x y) : JoinedWithin ω S y x := by
  obtain ⟨W, hW⟩ := h
  exact ⟨W.reverse, fun v hv => hW v (by
    rwa [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hv)⟩

theorem JoinedWithin.mono {ω : Configuration d} {S T : Set (Vertex d)} {x y : Vertex d}
    (h : JoinedWithin ω S x y) (hST : S ⊆ T) : JoinedWithin ω T x y := by
  obtain ⟨W, hW⟩ := h
  exact ⟨W, fun v hv => hST (hW v hv)⟩

/-- The sum of the increments of `w` along the open edges from `x` to the vertices of `C`. -/
noncomputable def vertexVariation (ω : Configuration d) (C : Finset (Vertex d))
    (w : Vertex d → ℝ) (x : Vertex d) : ℝ :=
  ∑ y ∈ C, if (openGraph ω).Adj x y then |w x - w y| else 0

theorem vertexVariation_nonneg (ω : Configuration d) (C : Finset (Vertex d))
    (w : Vertex d → ℝ) (x : Vertex d) : 0 ≤ vertexVariation ω C w x :=
  Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity

theorem vertexVariation_mono (ω : Configuration d) {S T : Finset (Vertex d)} (hST : S ⊆ T)
    (w : Vertex d → ℝ) (x : Vertex d) : vertexVariation ω S w x ≤ vertexVariation ω T w x :=
  Finset.sum_le_sum_of_subset_of_nonneg hST fun _ _ _ => by split_ifs <;> positivity

/-- The oscillation along a walk is at most the sum of the increments along its darts. -/
private theorem abs_sub_le_sum_darts_of_walk {ω : Configuration d} (w : Vertex d → ℝ)
    {u v : Vertex d} (p : (openGraph ω).Walk u v) :
    |w u - w v| ≤ (p.darts.map fun e => |w e.fst - w e.snd|).sum := by
  induction p with
  | nil => simp
  | @cons a b c h p ih =>
    simp only [SimpleGraph.Walk.darts_cons, List.map_cons, List.sum_cons]
    calc |w a - w c| ≤ |w a - w b| + |w b - w c| := abs_sub_le _ _ _
      _ ≤ _ := add_le_add le_rfl ih

/-- **Oscillation along an open path.** If two vertices are joined by an open path inside a finite
set `S`, the difference of a function at them is at most the sum over `z ∈ S` of its increments
along the open edges from `z` into `S`. -/
theorem abs_sub_le_sum_vertexVariation {ω : Configuration d} (S : Finset (Vertex d))
    (w : Vertex d → ℝ) {a b : Vertex d} (h : JoinedWithin ω ↑S a b) :
    |w a - w b| ≤ ∑ z ∈ S, vertexVariation ω S w z := by
  obtain ⟨W, hW⟩ := h
  set P := W.bypass
  have hPS : ∀ z ∈ P.support, z ∈ S := fun z hz =>
    Finset.mem_coe.1 (hW z (W.support_bypass_subset_support hz))
  have hnodup : P.darts.Nodup :=
    SimpleGraph.Walk.darts_nodup_of_support_nodup W.bypass_isPath.support_nodup
  refine (abs_sub_le_sum_darts_of_walk w P).trans ?_
  set g : Vertex d × Vertex d → ℝ := fun q =>
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
    _ = ∑ z ∈ S, vertexVariation ω S w z := by
        rw [Finset.sum_product]
        rfl

/-- The magnitude `|∇f|(x) = ((1/2) ∑_{y ∈ S, y ∼ x} (f x - f y)²)^{1/2}` of the gradient of `f`
at `x`, for the graph `G` on the domain `S` (Armstrong and Dario, (1.4)). With `G` the open graph
this is `|∇w 1_{a ≠ 0}|(x)`; with `G` the lattice it is `|∇f|(x)`. -/
noncomputable def gradNormIn (G : SimpleGraph (Vertex d)) (S : Finset (Vertex d))
    (f : Vertex d → ℝ) (x : Vertex d) : ℝ :=
  √((1 / 2) * ∑ y ∈ S, if G.Adj x y then (f x - f y) ^ 2 else 0)

theorem gradNormIn_nonneg (G : SimpleGraph (Vertex d)) (S : Finset (Vertex d))
    (f : Vertex d → ℝ) (x : Vertex d) : 0 ≤ gradNormIn G S f x :=
  Real.sqrt_nonneg _

/-- The magnitude of a gradient is at most the sum of the absolute increments. -/
theorem gradNormIn_le (G : SimpleGraph (Vertex d)) (S : Finset (Vertex d))
    (f : Vertex d → ℝ) (x : Vertex d) :
    gradNormIn G S f x ≤ ∑ y ∈ S, if G.Adj x y then |f x - f y| else 0 := by
  set a : Vertex d → ℝ := fun y => if G.Adj x y then |f x - f y| else 0
  have ha : ∀ y, 0 ≤ a y := fun y => by simp only [a]; split_ifs <;> positivity
  have hsq : ∑ y ∈ S, (if G.Adj x y then (f x - f y) ^ 2 else 0) = ∑ y ∈ S, a y ^ 2 := by
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [a]
    split_ifs <;> simp [sq_abs]
  have hle : ∑ y ∈ S, a y ^ 2 ≤ (∑ y ∈ S, a y) ^ 2 := by
    rw [sq (∑ y ∈ S, a y), Finset.sum_mul]
    refine Finset.sum_le_sum fun y hy => ?_
    rw [sq]
    exact mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun i _ => ha i) hy) (ha y)
  have h0 : 0 ≤ ∑ y ∈ S, a y ^ 2 := Finset.sum_nonneg fun y _ => sq_nonneg _
  have h1 : 0 ≤ ∑ y ∈ S, a y := Finset.sum_nonneg fun y _ => ha y
  rw [gradNormIn, hsq]
  calc √((1 / 2) * ∑ y ∈ S, a y ^ 2) ≤ √((∑ y ∈ S, a y) ^ 2) :=
        Real.sqrt_le_sqrt (by linarith)
    _ = ∑ y ∈ S, a y := Real.sqrt_sq h1

/-- **Power of the magnitude of a gradient.** If `x` has at most `D` neighbours, then for
`1 ≤ s`, `|∇f|(x)^s ≤ D^{s-1} ∑_{y ∼ x} |f x - f y|^s`. -/
theorem gradNormIn_rpow_le (G : SimpleGraph (Vertex d)) [G.LocallyFinite]
    (S : Finset (Vertex d)) (f : Vertex d → ℝ) (x : Vertex d) {s : ℝ} (hs : 1 ≤ s) {D : ℕ}
    (hdeg : G.degree x ≤ D) :
    gradNormIn G S f x ^ s ≤
      (D : ℝ) ^ (s - 1) * ∑ y ∈ S, if G.Adj x y then |f x - f y| ^ s else 0 := by
  set T := S.filter (G.Adj x)
  have hT : (T.card : ℝ) ≤ D := by
    have h1 : T ⊆ G.neighborFinset x := fun y hy =>
      (SimpleGraph.mem_neighborFinset _ _ _).2 (Finset.mem_filter.1 hy).2
    exact_mod_cast ((Finset.card_le_card h1).trans
      ((SimpleGraph.card_neighborFinset_eq_degree _ _).le.trans hdeg))
  have hsum1 : (∑ y ∈ S, if G.Adj x y then |f x - f y| else 0) = ∑ y ∈ T, |f x - f y| := by
    rw [Finset.sum_filter]
  have hsums : (∑ y ∈ S, if G.Adj x y then |f x - f y| ^ s else 0) =
      ∑ y ∈ T, |f x - f y| ^ s := by
    rw [Finset.sum_filter]
  have hle := gradNormIn_le G S f x
  rw [hsum1] at hle
  rw [hsums]
  have hs0 : 0 ≤ s := by linarith
  have hs1 : 0 ≤ s - 1 := by linarith
  calc gradNormIn G S f x ^ s ≤ (∑ y ∈ T, |f x - f y|) ^ s :=
        Real.rpow_le_rpow (gradNormIn_nonneg G S f x) hle hs0
    _ ≤ (T.card : ℝ) ^ (s - 1) * ∑ y ∈ T, |f x - f y| ^ s :=
        Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (s := T) (f := fun y => |f x - f y|) hs
          (fun y _ => abs_nonneg _)
    _ ≤ (D : ℝ) ^ (s - 1) * ∑ y ∈ T, |f x - f y| ^ s :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (Nat.cast_nonneg _) hT hs1)
          (Finset.sum_nonneg fun y _ => Real.rpow_nonneg (abs_nonneg _) _)

/-- The sum of the open increments at `x` is at most `2 √d` times the magnitude of the open
gradient at `x`. -/
theorem vertexVariation_le_gradNormIn (ω : Configuration d) (C : Finset (Vertex d))
    (w : Vertex d → ℝ) (x : Vertex d) :
    vertexVariation ω C w x ≤ 2 * √(d : ℝ) * gradNormIn (openGraph ω) C w x := by
  set T := C.filter ((openGraph ω).Adj x)
  have hV : vertexVariation ω C w x = ∑ y ∈ T, |w x - w y| := by
    rw [vertexVariation, Finset.sum_filter]
  have hQ : (∑ y ∈ C, if (openGraph ω).Adj x y then (w x - w y) ^ 2 else 0) =
      ∑ y ∈ T, |w x - w y| ^ 2 := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun y _ => ?_
    split_ifs <;> simp [sq_abs]
  have hT : (T.card : ℝ) ≤ 2 * d := by
    have h1 : T ⊆ (openGraph ω).neighborFinset x := fun y hy =>
      (SimpleGraph.mem_neighborFinset _ _ _).2 (Finset.mem_filter.1 hy).2
    exact_mod_cast ((Finset.card_le_card h1).trans
      ((SimpleGraph.card_neighborFinset_eq_degree _ _).le.trans (openGraph_degree_le ω x)))
  have hQ0 : 0 ≤ ∑ y ∈ T, |w x - w y| ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hg : gradNormIn (openGraph ω) C w x ^ 2 = (1 / 2) * ∑ y ∈ T, |w x - w y| ^ 2 := by
    rw [gradNormIn, hQ, Real.sq_sqrt (by positivity)]
  have hcs := sq_sum_le_card_mul_sum_sq (s := T) (f := fun y => |w x - w y|)
  have hnn : 0 ≤ ∑ y ∈ T, |w x - w y| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hrhs : 0 ≤ 2 * √(d : ℝ) * gradNormIn (openGraph ω) C w x := by
    have := gradNormIn_nonneg (openGraph ω) C w x
    positivity
  rw [hV]
  refine (pow_le_pow_iff_left₀ hnn hrhs two_ne_zero).1 ?_
  have hd : (√(d : ℝ)) ^ 2 = d := Real.sq_sqrt (Nat.cast_nonneg d)
  calc (∑ y ∈ T, |w x - w y|) ^ 2 ≤ (T.card : ℝ) * ∑ y ∈ T, |w x - w y| ^ 2 := hcs
    _ ≤ (2 * d) * ∑ y ∈ T, |w x - w y| ^ 2 := mul_le_mul_of_nonneg_right hT hQ0
    _ = (2 * √(d : ℝ) * gradNormIn (openGraph ω) C w x) ^ 2 := by
        rw [mul_pow, mul_pow, hd, hg]
        ring

/-- **Coarse-graining data** on a finite cluster (Armstrong and Dario, Section 3.1): a domain
`cl_𝒫(U)` containing a cluster `C_*(U)`, partition cubes, anchors depending only on the partition
cube, and regions carrying the local open paths used in Lemmas 3.2 and 3.3: from each vertex of
the cluster to its anchor, and between the anchors of lattice neighbours in different partition
cubes. -/
structure CoarseData (d : ℕ) (ω : Configuration d) where
  /-- The domain, the closure `cl_𝒫(U)`. -/
  domain : Finset (Vertex d)
  /-- The cluster `C_*(U)`. -/
  cluster : Finset (Vertex d)
  cluster_subset : cluster ⊆ domain
  /-- The partition cube `□_𝒫(x)`. -/
  part : Vertex d → TriadicCube d
  mem_part : ∀ x ∈ domain, x ∈ (part x).vertices
  part_subset : ∀ x ∈ domain, (part x).vertices ⊆ domain
  part_eq_of_mem : ∀ x ∈ domain, ∀ y ∈ (part x).vertices, part y = part x
  /-- The anchor `z̄(□_𝒫(x))`. -/
  anchor : Vertex d → Vertex d
  anchor_congr : ∀ x y, part x = part y → anchor x = anchor y
  anchor_mem : ∀ x ∈ domain, anchor x ∈ cluster
  anchor_mem_part : ∀ x ∈ domain, anchor x ∈ (part x).vertices
  /-- The region of the open path from a vertex of the cluster to its anchor. -/
  region : Vertex d → Finset (Vertex d)
  joinedWithin_region : ∀ x ∈ cluster, JoinedWithin ω ↑(region x ∩ cluster) x (anchor x)
  /-- The region of the open path between the anchors of lattice neighbours. -/
  pairRegion : Vertex d → Vertex d → Finset (Vertex d)
  joinedWithin_pairRegion : ∀ x ∈ domain, ∀ y ∈ domain, (nearestNeighborGraph d).Adj x y →
    part x ≠ part y → JoinedWithin ω ↑(pairRegion x y ∩ cluster) (anchor x) (anchor y)

namespace CoarseData

variable {ω : Configuration d} (P : CoarseData d ω)

/-- The coarsening `[w]_𝒫(x) = w(z̄(□_𝒫(x)))`. -/
def coarsen (w : Vertex d → ℝ) (x : Vertex d) : ℝ :=
  w (P.anchor x)

theorem coarsen_congr (w : Vertex d → ℝ) {x y : Vertex d} (h : P.part x = P.part y) :
    P.coarsen w x = P.coarsen w y := by
  rw [coarsen, coarsen, P.anchor_congr x y h]

end CoarseData

end Rigidity.Percolation
