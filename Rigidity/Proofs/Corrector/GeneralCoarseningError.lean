import Rigidity.Proofs.Corrector.GeneralCorrectorLipschitz
import Rigidity.Proofs.Corrector.GeneralCoarsenedFields
import Rigidity.Proofs.Corrector.GeneralRandomBallSums
import PercolationClusterHomogenization.Proofs.Partition.Paths
import PercolationClusterHomogenization.Proofs.Percolation.ClusterCoarsening
import PercolationClusterHomogenization.Proofs.Regularity.GeneralHarmonicDist
import PercolationClusterHomogenization.Proofs.Percolation.GeneralDim.CubeSizeMoments

/-!
# The coarsening error (5.10) of the corrector in every dimension

Step 6 of the proof of Dario's Theorem 1 bounds `|χ(y) - [χ]_𝒫(y)| 1_{y ∈ 𝒞_∞}` by the sum of
`|∇χ|` over a ball of radius `C size(□_𝒫(y))`, and this sum by Proposition 2.15. Here, for the
partition into good cubes of `ℤᵈ`:

* `abs_sub_le_edgeVariationIn_of_reachable`: along an open path inside a finite set, the
  oscillation of a function is at most its variation over the open edges of the set;
* `reachable_anchorBox`: on the partition event, a vertex `v` of an infinite open component is
  joined to the anchor of its partition cube `Q` inside the box of radius `3 size(Q)` around `v`
  (from `Rigidity.Percolation.reachable_partitionAnchor_of_infinite`);
* `abs_correctorDiff_guardAnchor_le`: on the partition event, `|χ(v) - χ(a_𝒫(v))|` is at most
  `2d` times the sum of the Lipschitz bounds of the corrector increments over the ball of radius
  `3d size(□_𝒫(v))` around `v`.
-/

namespace Rigidity.Corrector.GeneralDim

open MeasureTheory Filter Set LatticeProb.Percolation Rigidity.Percolation Rigidity.External
open scoped Classical ENNReal

variable {d : ℕ}

/-- Adjacent vertices have the same open component. -/
theorem mem_infiniteComponentEvent_of_adj {ω : Configuration d} {x y : Vertex d}
    (hxy : (openGraph ω).Adj x y) (hx : ω ∈ infiniteComponentEvent x) :
    ω ∈ infiniteComponentEvent y := by
  have : (openGraph ω).connectedComponentMk y = (openGraph ω).connectedComponentMk x :=
    SimpleGraph.ConnectedComponent.eq.2 hxy.reachable.symm
  change ((openGraph ω).connectedComponentMk y).supp.Infinite
  rw [this]
  exact hx

theorem abs_sum_mul_le_of_near (q : Fin d → ℝ) {y : Vertex d} (hy : ∀ i, |y i| ≤ 1) :
    |∑ i, q i * (y i : ℝ)| ≤ ∑ i, |q i| := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  have : |((y i : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast hy i
  nlinarith [abs_nonneg (q i)]

/-- The open neighbours of a vertex inside a finite set are at most `2d`. -/
theorem card_filter_adj_le (ω : Configuration d) (S : Finset (Vertex d)) (x : Vertex d) :
    (S.filter fun y => (openGraph ω).Adj x y).card ≤ 2 * d := by
  have hsub : S.filter (fun y => (openGraph ω).Adj x y) ⊆
      (Finset.univ.image fun j : Fin d => x + LatticeProb.unit j) ∪
        (Finset.univ.image fun j : Fin d => x - LatticeProb.unit j) := by
    intro y hy
    rw [Finset.mem_filter] at hy
    have h : ∃ j : Fin d, y = x + LatticeProb.unit j ∨ x = y + LatticeProb.unit j :=
      openGraph_le ω hy.2
    obtain ⟨j, hj | hj⟩ := h
    · exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨j, Finset.mem_univ _, hj.symm⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_image.2 ⟨j, Finset.mem_univ _, by rw [hj]; abel⟩)
  calc (S.filter fun y => (openGraph ω).Adj x y).card
      ≤ ((Finset.univ.image fun j : Fin d => x + LatticeProb.unit j) ∪
          (Finset.univ.image fun j : Fin d => x - LatticeProb.unit j)).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.univ.image fun j : Fin d => x + LatticeProb.unit j).card +
          (Finset.univ.image fun j : Fin d => x - LatticeProb.unit j).card :=
        Finset.card_union_le _ _
    _ ≤ d + d := add_le_add (Finset.card_image_le.trans (by simp))
          (Finset.card_image_le.trans (by simp))
    _ = 2 * d := by ring

/-- **Oscillation along local open paths.** If two vertices are joined by an open path inside a
finite set, the difference of a function at them is at most its total variation over the open
edges inside the set. -/
theorem abs_sub_le_edgeVariationIn_of_reachable {ω : Configuration d} (S : Finset (Vertex d))
    (w : Vertex d → ℝ) {a b : Vertex d} (h : (openIn ω ↑S).Reachable a b) :
    |w a - w b| ≤ edgeVariationIn ω S w := by
  obtain ⟨W⟩ := h
  set P := W.bypass
  have hnodup : P.darts.Nodup :=
    SimpleGraph.Walk.darts_nodup_of_support_nodup W.bypass_isPath.support_nodup
  have hwalk : ∀ {u v : Vertex d} (p : (openIn ω ↑S).Walk u v),
      |w u - w v| ≤ (p.darts.map fun e => |w e.fst - w e.snd|).sum := by
    intro u v p
    induction p with
    | nil => simp
    | @cons a b c h p ih =>
      simp only [SimpleGraph.Walk.darts_cons, List.map_cons, List.sum_cons]
      calc |w a - w c| ≤ |w a - w b| + |w b - w c| := abs_sub_le _ _ _
        _ ≤ _ := add_le_add le_rfl ih
  refine (hwalk P).trans ?_
  set g : Vertex d × Vertex d → ℝ := fun q =>
    if (openGraph ω).Adj q.1 q.2 then |w q.1 - w q.2| else 0
  have hsum : (P.darts.map fun e => |w e.fst - w e.snd|).sum =
      ∑ q ∈ P.darts.toFinset.image (fun e => (e.fst, e.snd)), g q := by
    rw [Finset.sum_image (fun e _ e' _ h => SimpleGraph.Dart.ext e e' h)]
    rw [List.sum_toFinset _ hnodup]
    congr 1
    apply List.map_congr_left
    intro e _
    have he : (openGraph ω).Adj e.fst e.snd := e.adj.1
    simp only [g, he, if_true]
  rw [hsum]
  have hsub : P.darts.toFinset.image (fun e => (e.fst, e.snd)) ⊆ S ×ˢ S := by
    intro q hq
    obtain ⟨e, -, rfl⟩ := Finset.mem_image.1 hq
    exact Finset.mem_product.2 ⟨Finset.mem_coe.1 e.adj.2.1, Finset.mem_coe.1 e.adj.2.2⟩
  calc ∑ q ∈ P.darts.toFinset.image (fun e => (e.fst, e.snd)), g q
      ≤ ∑ q ∈ S ×ˢ S, g q :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun q _ _ => by
          simp only [g]; split_ifs <;> positivity
    _ = edgeVariationIn ω S w := by
        rw [Finset.sum_product]
        rfl

/-- The box of radius `3 size(□_𝒫(v))` around `v`. -/
noncomputable def anchorBox (ω : Configuration d) (v : Vertex d) : Finset (Vertex d) :=
  LatticeProb.boxFinset v (3 ^ ((partitionCube ω v).scale + 1))

theorem mem_anchorBox {ω : Configuration d} {v x : Vertex d} :
    x ∈ anchorBox ω v ↔ ∀ i, |x i - v i| ≤ ((3 ^ ((partitionCube ω v).scale + 1) : ℕ) : ℤ) := by
  simp only [anchorBox, LatticeProb.boxFinset, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]
  exact forall_congr' fun i => by constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- On the partition event, a vertex of an infinite open component is joined to the anchor of its
partition cube inside `anchorBox`. -/
theorem reachable_anchorBox (hd : 0 < d) {ω : Configuration d} (hP : PartitionEvent ω)
    {v : Vertex d} (hv : ω ∈ infiniteComponentEvent v) :
    (openIn ω ↑(anchorBox ω v)).Reachable v (partitionAnchor ω v) := by
  refine Rigidity.Percolation.openIn_reachable_mono_region ?_
    (reachable_partitionAnchor_of_infinite hd hP hv)
  set Q := partitionCube ω v with hQ
  have hvP : v ∈ Q.parent.vertices := Q.vertices_subset_parent (mem_partitionCube hP v)
  have hpow : (3 : ℤ) ^ (Q.scale + 1) = ((3 ^ (Q.scale + 1) : ℕ) : ℤ) := by push_cast; rfl
  intro y hy
  rw [Finset.mem_coe, mem_anchorBox]
  intro i
  rcases hy with hy | hy
  · have h := Rigidity.Proofs.Regularity.abs_sub_lt_side_of_mem hy hvP i
    change |y i - v i| < 3 ^ (Q.scale + 1) at h
    rw [← hpow]
    exact h.le
  · have h : |y i - v i| ≤ ((3 ^ Q.scale / 2 : ℕ) : ℤ) := hy i
    refine h.trans ?_
    have : 3 ^ Q.scale / 2 ≤ 3 ^ (Q.scale + 1) :=
      (Nat.div_le_self _ _).trans (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ _))
    exact_mod_cast this

/-- The Euclidean norm of a lattice vector with coordinates at most `R` is at most `d R`. -/
theorem norm_latticeEuclideanEmbedding_le_of_abs_le {z : Vertex d} {R : ℝ} (hR : 0 ≤ R)
    (hz : ∀ i, |(z i : ℝ)| ≤ R) : ‖latticeEuclideanEmbedding z‖ ≤ d * R := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_le_left (by positivity)]
  calc ∑ i, ‖latticeEuclideanEmbedding z i‖ ^ 2 ≤ ∑ _i : Fin d, R ^ 2 :=
        Finset.sum_le_sum fun i _ => by
          have h : ‖latticeEuclideanEmbedding z i‖ = |(z i : ℝ)| := Real.norm_eq_abs _
          rw [h]
          exact pow_le_pow_left₀ (abs_nonneg _) (hz i) 2
    _ = d * R ^ 2 := by simp
    _ ≤ (d * R) ^ 2 := by
        rcases Nat.eq_zero_or_pos d with h0 | h0
        · simp [h0]
        · have : (1 : ℝ) ≤ d := by exact_mod_cast h0
          nlinarith [sq_nonneg R]

theorem norm_sub_le_of_mem_anchorBox {ω : Configuration d} {v x : Vertex d}
    (hx : x ∈ anchorBox ω v) :
    ‖latticeEuclideanEmbedding (x - v)‖ ≤ 3 * d * (3 : ℝ) ^ (partitionCube ω v).scale := by
  have h := norm_latticeEuclideanEmbedding_le_of_abs_le (z := x - v)
    (R := 3 * (3 : ℝ) ^ (partitionCube ω v).scale) (by positivity) fun i => by
      have hi := mem_anchorBox.1 hx i
      have : |((x - v) i : ℝ)| ≤ (((3 ^ ((partitionCube ω v).scale + 1) : ℕ) : ℤ) : ℝ) := by
        rw [Pi.sub_apply]
        exact_mod_cast hi
      rw [pow_succ] at this
      push_cast at this
      linarith
  linarith

section Carrier

variable {G : Set (Configuration d)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent d)

/-- **The edge variation of the corrector increments** over a finite set is at most `2d` times
the sum of the Lipschitz bounds. -/
theorem edgeVariationIn_correctorDiff_le {ω : Configuration d} (hω : ω ∈ G) {q : Fin d → ℝ}
    {v : Vertex d} (hv : ω ∈ infiniteComponentEvent v) (S : Finset (Vertex d))
    {Λ : Vertex d → ℝ} (hΛ0 : ∀ x, 0 ≤ Λ x)
    (hΛ : ∀ x, ω ∈ infiniteComponentEvent x → ∀ y, (openGraph ω).Adj x y →
      |correctorDiff hG hGv q ω x y| ≤ Λ x) :
    edgeVariationIn ω S (fun x => if ω ∈ infiniteComponentEvent x then
      correctorDiff hG hGv q ω x v else 0) ≤ (2 * d) * ∑ x ∈ S, Λ x := by
  unfold edgeVariationIn
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  have hterm : ∀ y ∈ S, (if (openGraph ω).Adj x y then
      |(if ω ∈ infiniteComponentEvent x then correctorDiff hG hGv q ω x v else 0) -
        (if ω ∈ infiniteComponentEvent y then correctorDiff hG hGv q ω y v else 0)| else 0) ≤
      if (openGraph ω).Adj x y then Λ x else 0 := by
    intro y _
    by_cases hxy : (openGraph ω).Adj x y
    · rw [if_pos hxy, if_pos hxy]
      by_cases hx : ω ∈ infiniteComponentEvent x
      · have hy := mem_infiniteComponentEvent_of_adj hxy hx
        rw [if_pos hx, if_pos hy, correctorDiff_sub_eq hG hGv hω hx hy hv]
        exact hΛ x hx y hxy
      · have hy : ω ∉ infiniteComponentEvent y := fun hy =>
          hx (mem_infiniteComponentEvent_of_adj hxy.symm hy)
        rw [if_neg hx, if_neg hy, sub_zero, abs_zero]
        exact hΛ0 x
    · rw [if_neg hxy, if_neg hxy]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have h4 : ((S.filter fun y => (openGraph ω).Adj x y).card : ℝ) ≤ 2 * d := by
    exact_mod_cast card_filter_adj_le ω S x
  exact mul_le_mul_of_nonneg_right h4 (hΛ0 x)

/-- **The coarsening error at a cluster vertex** (Dario, (5.10)): on the partition event,
`|χ(v) - χ(a_𝒫(v))|` is at most `2d` times the sum of the Lipschitz bounds over the ball of
radius `3d size(□_𝒫(v))` around `v`. -/
theorem abs_correctorDiff_guardAnchor_le (hd : 0 < d) {ω : Configuration d} (hω : ω ∈ G)
    (hP : PartitionEvent ω) {q : Fin d → ℝ} {v : Vertex d}
    (hv : ω ∈ infiniteComponentEvent v) {Λ : Vertex d → ℝ} (hΛ0 : ∀ x, 0 ≤ Λ x)
    (hΛ : ∀ x, ω ∈ infiniteComponentEvent x → ∀ y, (openGraph ω).Adj x y →
      |correctorDiff hG hGv q ω x y| ≤ Λ x) :
    ENNReal.ofReal |correctorDiff hG hGv q ω v (guardAnchor ω v)| ≤
      ∑' x, ENNReal.ofReal (if ‖latticeEuclideanEmbedding (x - v)‖ ≤
        3 * d * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) v then 2 * d * Λ x
          else 0) := by
  set w : Vertex d → ℝ := fun x => if ω ∈ infiniteComponentEvent x then
    correctorDiff hG hGv q ω x v else 0
  have ha : ω ∈ infiniteComponentEvent (partitionAnchor ω v) := infinite_partitionAnchor hd hP v
  have h1 := abs_sub_le_edgeVariationIn_of_reachable (anchorBox ω v) w
    (reachable_anchorBox hd hP hv)
  have hwv : w v = 0 := by
    simp only [w, if_pos hv]
    obtain ⟨h, -⟩ := hGv hω
    exact correctorDiff_self hG hGv hω (uniqueInfiniteComponent_infinite h)
      ⟨v, (mem_uniqueInfiniteComponent_iff h v).2 hv⟩
  have hwa : w (partitionAnchor ω v) =
      correctorDiff hG hGv q ω (partitionAnchor ω v) v := by
    simp only [w, if_pos ha]
  rw [hwv, hwa, zero_sub, abs_neg, correctorDiff_swap' hG hGv hω hv ha, abs_neg] at h1
  have h2 := edgeVariationIn_correctorDiff_le hG hGv hω hv (anchorBox ω v) hΛ0 hΛ
  have hsize : TriadicCube.stoppingSize (TriadicCube.goodCubes ω) v =
      (3 : ℝ) ^ (partitionCube ω v).scale :=
    TriadicCube.stoppingSize_eq_of_mem (mem_partitionCube hP v) (partitionCube_spec hP v).2
  rw [guardAnchor_of_event hP, hsize]
  calc ENNReal.ofReal |correctorDiff hG hGv q ω v (partitionAnchor ω v)|
      ≤ ENNReal.ofReal (∑ x ∈ anchorBox ω v, 2 * d * Λ x) := by
        refine ENNReal.ofReal_le_ofReal (h1.trans (h2.trans_eq ?_))
        rw [Finset.mul_sum]
    _ = ∑ x ∈ anchorBox ω v, ENNReal.ofReal (2 * d * Λ x) :=
        ENNReal.ofReal_sum_of_nonneg fun x _ => by have := hΛ0 x; positivity
    _ = ∑ x ∈ anchorBox ω v, ENNReal.ofReal (if ‖latticeEuclideanEmbedding (x - v)‖ ≤
          3 * d * (3 : ℝ) ^ (partitionCube ω v).scale then 2 * d * Λ x else 0) := by
        refine Finset.sum_congr rfl fun x hx => ?_
        rw [if_pos (norm_sub_le_of_mem_anchorBox hx)]
    _ ≤ ∑' x, ENNReal.ofReal (if ‖latticeEuclideanEmbedding (x - v)‖ ≤
          3 * d * (3 : ℝ) ^ (partitionCube ω v).scale then 2 * d * Λ x else 0) :=
        ENNReal.sum_le_tsum _

end Carrier

end Rigidity.Corrector.GeneralDim
