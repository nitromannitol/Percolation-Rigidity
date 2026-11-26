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

theorem near_of_nearestNeighbor_adj {a b : Vertex d} (h : (nearestNeighborGraph d).Adj a b) :
    ∀ i, |a i - b i| ≤ 1 := by
  have h' : ∃ j : Fin d, b = a + LatticeProb.unit j ∨ a = b + LatticeProb.unit j := h
  obtain ⟨j, hj | hj⟩ := h' <;> intro i <;> subst hj <;>
    simp only [Pi.add_apply, LatticeProb.unit, Pi.single_apply] <;> split_ifs <;> simp

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

/-! ### Moments -/

/-- The moments of `X + 2` for `X ≤ O_s(θ)`: `E[(X + 2)^{4q}] ≤ 3 (2 D q^{1/s})^{4q}` with
`D = θ (4/s)^{1/s} + 2`. -/
theorem lintegral_add_two_rpow_le {p : unitInterval} {X : Configuration d → ℝ} {s θ : ℝ}
    (hs : 0 < s) (hθ : 0 < θ) (hXm : Measurable X) (hX0 : ∀ ω, 0 ≤ X ω)
    (hXO : IsOsBond d p X s θ) {q : ℝ} (hq : 1 ≤ q) :
    ∫⁻ ω, ENNReal.ofReal ((X ω + 2) ^ (4 * q)) ∂latticeBondLaw d p ≤
      ENNReal.ofReal (3 * (2 * (θ * (4 / s) ^ (1 / s) + 2) * q ^ (1 / s)) ^ (4 * q)) := by
  have hq0 : 0 < q := by linarith
  have h4q : 0 < 4 * q := by linarith
  set D := θ * (4 / s) ^ (1 / s) + 2 with hD
  have hD2 : 2 ≤ D := by have : 0 ≤ θ * (4 / s) ^ (1 / s) := (by positivity); linarith
  have hq1s : 1 ≤ q ^ (1 / s) := Real.one_le_rpow hq (by positivity)
  obtain ⟨hint, hle⟩ := IsOsBond.integral_rpow_le hs hθ h4q hXm hX0 hXO
  -- pointwise
  have hpt : ∀ ω, (X ω + 2) ^ (4 * q) ≤ 2 ^ (4 * q) * (X ω ^ (4 * q) + 2 ^ (4 * q)) := by
    intro ω
    have hm : X ω + 2 ≤ 2 * max (X ω) 2 := by
      have := le_max_left (X ω) 2
      have := le_max_right (X ω) 2
      linarith
    calc (X ω + 2) ^ (4 * q) ≤ (2 * max (X ω) 2) ^ (4 * q) :=
          Real.rpow_le_rpow (by linarith [hX0 ω]) hm h4q.le
      _ = 2 ^ (4 * q) * max (X ω) 2 ^ (4 * q) :=
          Real.mul_rpow (by norm_num) (le_max_of_le_right (by norm_num))
      _ ≤ 2 ^ (4 * q) * (X ω ^ (4 * q) + 2 ^ (4 * q)) := by
          gcongr
          rcases le_total (X ω) 2 with h | h
          · rw [max_eq_right h]
            have := Real.rpow_nonneg (hX0 ω) (4 * q)
            linarith
          · rw [max_eq_left h]
            have : (0 : ℝ) ≤ 2 ^ (4 * q) := by positivity
            linarith
  have hint' : Integrable (fun ω => 2 ^ (4 * q) * (X ω ^ (4 * q) + 2 ^ (4 * q)))
      (latticeBondLaw d p) := (hint.add (integrable_const _)).const_mul _
  calc ∫⁻ ω, ENNReal.ofReal ((X ω + 2) ^ (4 * q)) ∂latticeBondLaw d p
      ≤ ∫⁻ ω, ENNReal.ofReal (2 ^ (4 * q) * (X ω ^ (4 * q) + 2 ^ (4 * q))) ∂latticeBondLaw d p :=
        lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hpt ω)
    _ = ENNReal.ofReal (∫ ω, 2 ^ (4 * q) * (X ω ^ (4 * q) + 2 ^ (4 * q)) ∂latticeBondLaw d p) :=
        (ofReal_integral_eq_lintegral_ofReal hint'
          (Eventually.of_forall fun ω => by
            have := Real.rpow_nonneg (hX0 ω) (4 * q); positivity)).symm
    _ ≤ ENNReal.ofReal (3 * (2 * D * q ^ (1 / s)) ^ (4 * q)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [integral_const_mul, integral_add hint (integrable_const _), integral_const,
          probReal_univ, one_smul]
        have hX4 : ∫ ω, X ω ^ (4 * q) ∂latticeBondLaw d p ≤ 2 * (D * q ^ (1 / s)) ^ (4 * q) := by
          refine hle.trans ?_
          have he : Real.exp (-(4 * q / s)) ≤ 1 := Real.exp_le_one_iff.2 (by
            have := div_pos h4q hs; linarith)
          have hbase : θ ^ (4 * q) * (4 * q / s) ^ (4 * q / s) =
              (θ * (4 / s) ^ (1 / s) * q ^ (1 / s)) ^ (4 * q) := by
            rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow hθ.le (by positivity),
              ← Real.rpow_mul (show (0 : ℝ) ≤ 4 / s by positivity), ← Real.rpow_mul hq0.le,
              mul_assoc, ← Real.mul_rpow (show (0 : ℝ) ≤ 4 / s by positivity) hq0.le]
            congr 2
            · ring
            · ring
          have hle2 : θ * (4 / s) ^ (1 / s) * q ^ (1 / s) ≤ D * q ^ (1 / s) := by
            have : 0 ≤ q ^ (1 / s) := by positivity
            nlinarith
          have h1 : (θ * (4 / s) ^ (1 / s) * q ^ (1 / s)) ^ (4 * q) ≤ (D * q ^ (1 / s)) ^ (4 * q) :=
            Real.rpow_le_rpow (by positivity) hle2 h4q.le
          have h0 : 0 ≤ θ ^ (4 * q) * (4 * q / s) ^ (4 * q / s) := by positivity
          calc 2 * θ ^ (4 * q) * ((4 * q / s) ^ (4 * q / s) * Real.exp (-(4 * q / s)))
              ≤ 2 * (θ ^ (4 * q) * (4 * q / s) ^ (4 * q / s)) := by
                nlinarith [Real.exp_pos (-(4 * q / s))]
            _ ≤ 2 * (D * q ^ (1 / s)) ^ (4 * q) := by rw [hbase]; linarith
        have h2 : (2 : ℝ) ^ (4 * q) ≤ (D * q ^ (1 / s)) ^ (4 * q) :=
          Real.rpow_le_rpow (by norm_num) (by nlinarith) h4q.le
        have he2 : (2 * D * q ^ (1 / s)) ^ (4 * q) = 2 ^ (4 * q) * (D * q ^ (1 / s)) ^ (4 * q) := by
          rw [mul_assoc, Real.mul_rpow (by norm_num) (by positivity)]
        rw [he2]
        have : (0 : ℝ) ≤ 2 ^ (4 * q) := by positivity
        nlinarith

/-- The tail of the radius `3d size(□_𝒫(v))` from the exponential moment of the size. -/
theorem measure_le_stoppingSize_le [NeZero d] {p : unitInterval} {θ : ℝ} (hθ : 0 < θ)
    (v : Vertex d)
    (hint : Integrable
      (fun ω => Real.exp (TriadicCube.stoppingSize (TriadicCube.goodCubes ω) v / θ))
      (latticeBondLaw d p))
    (hb : ∫ ω, Real.exp (TriadicCube.stoppingSize (TriadicCube.goodCubes ω) v / θ)
      ∂latticeBondLaw d p ≤ 2)
    (t : ℝ) :
    latticeBondLaw d p {ω | t ≤ 3 * d * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) v} ≤
      ENNReal.ofReal (2 * Real.exp (-(t / (3 * d * θ)))) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_neZero d
  set f : Configuration d → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal (Real.exp (TriadicCube.stoppingSize (TriadicCube.goodCubes ω) v / θ))
  have hsub : {ω | t ≤ 3 * d * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) v} ⊆
      {ω | ENNReal.ofReal (Real.exp (t / (3 * d * θ))) ≤ f ω} := by
    intro ω hω
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    change t ≤ _ at hω
    rw [div_le_div_iff₀ (by positivity) hθ]
    calc t * θ ≤ (3 * d * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) v) * θ :=
          mul_le_mul_of_nonneg_right hω hθ.le
      _ = _ := by ring
  refine (measure_mono hsub).trans ((meas_ge_le_lintegral_div hint.1.aemeasurable.ennreal_ofReal
    (by simp [Real.exp_pos]) ENNReal.ofReal_ne_top).trans ?_)
  rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun _ => (Real.exp_pos _).le),
    ← ENNReal.ofReal_div_of_pos (Real.exp_pos _)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff_of_pos_right (Real.exp_pos _)]
  exact hb

section Base

variable {G : Set (Configuration d)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent d)

/-- The sum of (5.10): `2d` times the Lipschitz bounds `Λ x` over the ball of radius
`3d size(□_𝒫(v))` around `v`. -/
noncomputable def stepSixSum (Λ : Vertex d → Configuration d → ℝ) (v : Vertex d)
    (ω : Configuration d) : ℝ≥0∞ :=
  ∑' x, ENNReal.ofReal (if ‖latticeEuclideanEmbedding (x - v)‖ ≤
    3 * d * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) v then 2 * d * Λ x ω else 0)

theorem measurable_stepSixSum {Λ : Vertex d → Configuration d → ℝ} (hΛ : ∀ x, Measurable (Λ x))
    (v : Vertex d) : Measurable (stepSixSum Λ v) :=
  Measurable.tsum fun x => (Measurable.ite (measurableSet_le measurable_const
    ((measurable_stoppingSize_goodCubes v).const_mul _)) ((hΛ x).const_mul _)
    measurable_const).ennreal_ofReal

/-- **The Lipschitz bound of the corrector increments at every vertex.** -/
theorem lipschitz_correctorDiff [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) :
    ∃ s θ L : ℝ, 0 < s ∧ 0 < θ ∧ 0 < L ∧ ∃ X : Configuration d → ℝ, Measurable X ∧
      (∀ ω, 0 ≤ X ω) ∧ IsOsBond d p X s θ ∧
      ∀ (q : Fin d → ℝ) (x : Vertex d), ∀ᵐ ω ∂latticeBondLaw d p,
        ω ∈ infiniteComponentEvent x → ∀ y, (openGraph ω).Adj x y →
          |correctorDiff hG hGv q ω x y| ≤
            (L * max (X (configurationTranslation (-x) ω)) 2 ^ d + 1) * ∑ i, |q i| := by
  obtain ⟨s, θ, L, hs, hθ, hL, X, hXm, hX0, hXO, hae⟩ := lipschitz_correctedPlane_origin hd hpc hp1
  refine ⟨s, θ, L, hs, hθ, hL, X, hXm, hX0, hXO, fun q x => ?_⟩
  have hTq := (measurePreserving_configurationTranslation p (-x)).quasiMeasurePreserving
  filter_upwards [hGae, hTq.ae hGae, hTq.ae hae] with ω hω hω' hlip hx y hxy
  set ω' := configurationTranslation (-x) ω with hω'def
  have hy : ω ∈ infiniteComponentEvent y := mem_infiniteComponentEvent_of_adj hxy hx
  rw [← correctorDiff_translate hG hGv (-x) hω hω' hx hy, add_neg_cancel]
  obtain ⟨h', -⟩ := hGv hω'
  set K := uniqueInfiniteComponent h'
  have hKinf := uniqueInfiniteComponent_infinite h'
  obtain ⟨ℓ, hℓ⟩ := exists_correctedPlane_of_valid (hGv hω') hKinf q
  have h0 : (0 : Vertex d) ∈ K.supp := by
    have := mem_infiniteComponentEvent_translation (-x) hx
    rw [add_neg_cancel] at this
    exact (mem_uniqueInfiniteComponent_iff h' 0).2 this
  have hy' : y + -x ∈ K.supp :=
    (mem_uniqueInfiniteComponent_iff h' _).2 (mem_infiniteComponentEvent_translation (-x) hy)
  have hadj' : (openGraph ω').Adj 0 (y + -x) := by
    have := (openGraph_adj_translation_iff (-x) ω x y).2 hxy
    rwa [add_neg_cancel] at this
  have hadjK : (componentGraph K).Adj ⟨0, h0⟩ ⟨y + -x, hy'⟩ := (K.toSimpleGraph_adj h0 hy').2 hadj'
  have hD := correctorDiff_eq hG hGv hω' hKinf hℓ ⟨0, h0⟩ ⟨y + -x, hy'⟩
  have hl := hlip h' q ℓ hℓ ⟨0, h0⟩ ⟨y + -x, hy'⟩ hadjK (by
    show ‖latticeEuclideanEmbedding (0 : Vertex d)‖ < 2
    rw [latticeEuclideanEmbedding_zero, norm_zero]
    norm_num)
  have hnear : ∀ i, |(y + -x) i| ≤ 1 := by
    have h := near_of_nearestNeighbor_adj (openGraph_le ω' hadj')
    intro i
    have h' := h i
    simp only [Pi.zero_apply, zero_sub, abs_neg] at h'
    exact h'
  have hq := abs_sum_mul_le_of_near q hnear
  change correctorDiff hG hGv q ω' (0 : Vertex d) (y + -x) =
    (ℓ ⟨0, h0⟩ - ∑ i, q i * (((0 : Vertex d) i : ℤ) : ℝ)) -
      (ℓ ⟨y + -x, hy'⟩ - ∑ i, q i * (((y + -x) i : ℤ) : ℝ)) at hD
  simp only [Pi.zero_apply, Int.cast_zero, mul_zero, Finset.sum_const_zero, sub_zero] at hD
  rw [hD]
  calc |ℓ ⟨0, h0⟩ - (ℓ ⟨y + -x, hy'⟩ - ∑ i, q i * ((y + -x) i : ℝ))|
      ≤ |ℓ ⟨0, h0⟩ - ℓ ⟨y + -x, hy'⟩| + |∑ i, q i * ((y + -x) i : ℝ)| := by
        rw [show ℓ ⟨0, h0⟩ - (ℓ ⟨y + -x, hy'⟩ - ∑ i, q i * ((y + -x) i : ℝ)) =
          (ℓ ⟨0, h0⟩ - ℓ ⟨y + -x, hy'⟩) + ∑ i, q i * ((y + -x) i : ℝ) by ring]
        exact abs_add_le _ _
    _ ≤ L * max (X ω') 2 ^ d * ∑ i, |q i| + ∑ i, |q i| := add_le_add hl hq
    _ = (L * max (X ω') 2 ^ d + 1) * ∑ i, |q i| := by ring

/-- **The Lipschitz bounds and the moments of the sums of (5.10)**: bounds `Λ i x` for the corrector
increments of slope `e_i` along the open edges at `x`, and moments of order `q` of
`stepSixSum (Λ i) v` growing like `(A q^k)^q`, from the order-zero regularity and the exponential
moments of the partition sizes. -/
theorem stepSix_data [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) :
    ∃ (Λ : Fin d → Vertex d → Configuration d → ℝ) (A k : ℝ), 0 < A ∧ 0 < k ∧
      (∀ i x, Measurable (Λ i x)) ∧ (∀ i x ω, 0 ≤ Λ i x ω) ∧
      (∀ i x, ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ infiniteComponentEvent x → ∀ y,
        (openGraph ω).Adj x y → |correctorDiff hG hGv (Pi.single i 1) ω x y| ≤ Λ i x ω) ∧
      (∀ i v (q : ℝ), 1 ≤ q →
        ∫⁻ ω, stepSixSum (Λ i) v ω ^ q ∂latticeBondLaw d p ≤
          ENNReal.ofReal ((A * q ^ k) ^ q)) := by
  obtain ⟨s, θ, L, hs, hθ, hL, X, hXm, hX0, hXO, hlip⟩ :=
    lipschitz_correctorDiff hG hGv hd hpc hp1 hGae
  obtain ⟨θ', hθ', hexp⟩ := (partition_estimates hd hpc).2.1
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  set D := θ * (4 / s) ^ (1 / s) + 2 with hD
  have hD2 : 2 ≤ D := by have : 0 ≤ θ * (4 / s) ^ (1 / s) := (by positivity); linarith
  set c : ℝ := 2 * d * (L + 1) with hc
  have hc0 : 0 < c := by positivity
  set B₁ : ℝ := (2 * (1 + d * (4 * (3 * d * θ')))) ^ d with hB₁
  have hB₁0 : 0 < B₁ := by positivity
  set E : ℝ := 2 * D * (d / 2) ^ (1 / s) with hE
  have hE0 : 0 < E := by positivity
  set k : ℝ := d + d / s with hk
  have hk0 : 0 < k := by positivity
  set A : ℝ := Real.sqrt 6 * (B₁ * (c * E ^ d)) with hA
  have hA0 : 0 < A := by positivity
  have hQ : ∀ i : Fin d, ∑ j, |(Pi.single i (1 : ℝ) : Fin d → ℝ) j| = 1 := by
    intro i
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
    simp
  set Λ : Fin d → Vertex d → Configuration d → ℝ := fun i x ω =>
    (L * max (X (configurationTranslation (-x) ω)) 2 ^ d + 1) *
      ∑ j, |(Pi.single i (1 : ℝ) : Fin d → ℝ) j| with hΛ
  have hΛ0 : ∀ i x ω, 0 ≤ Λ i x ω := fun i x ω => by simp only [hΛ, hQ]; positivity
  have hΛm : ∀ i x, Measurable (Λ i x) := fun i x =>
    ((((hXm.comp (configurationTranslationMeasurableEquiv (-x)).measurable).max
      measurable_const).pow_const d).const_mul L |>.add_const 1).mul_const _
  refine ⟨Λ, A, k, hA0, hk0, hΛm, hΛ0, fun i x => hlip _ x, fun i v q' hq' => ?_⟩
  have hq'0 : 0 < q' := by linarith
  set r : ℝ := d * q' / 2 with hr
  have hr1 : 1 ≤ r := by rw [hr]; nlinarith
  set P : ℝ := c * (2 * D * r ^ (1 / s)) ^ d with hP
  have hP0 : 0 < P := by positivity
  -- the moments of the summands
  have hYm : ∀ x, ∫⁻ ω, ENNReal.ofReal (2 * d * Λ i x ω) ^ (2 * q') ∂latticeBondLaw d p ≤
      ENNReal.ofReal ((Real.sqrt 3 * P ^ q') ^ 2) := by
    intro x
    have hpt : ∀ ω, ENNReal.ofReal (2 * d * Λ i x ω) ^ (2 * q') ≤
        ENNReal.ofReal (c ^ (2 * q') * (X (configurationTranslation (-x) ω) + 2) ^ (4 * r)) := by
      intro ω
      rw [ENNReal.ofReal_rpow_of_nonneg (by have := hΛ0 i x ω; positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      set Y := X (configurationTranslation (-x) ω)
      have hY0 : 0 ≤ Y := hX0 _
      have h1 : 2 * d * Λ i x ω ≤ c * (Y + 2) ^ d := by
        simp only [hΛ, hQ, mul_one, hc]
        have hm : max Y 2 ^ d ≤ (Y + 2) ^ d := by
          have : max Y 2 ≤ Y + 2 := max_le (by linarith) (by linarith)
          exact pow_le_pow_left₀ (le_max_of_le_right (by norm_num)) this d
        have h4 : 1 ≤ (Y + 2) ^ d := one_le_pow₀ (by linarith)
        have h5 : L * max Y 2 ^ d + 1 ≤ (L + 1) * (Y + 2) ^ d := by nlinarith
        calc 2 * d * (L * max Y 2 ^ d + 1) ≤ 2 * d * ((L + 1) * (Y + 2) ^ d) :=
              mul_le_mul_of_nonneg_left h5 (by positivity)
          _ = 2 * d * (L + 1) * (Y + 2) ^ d := by ring
      calc (2 * d * Λ i x ω) ^ (2 * q') ≤ (c * (Y + 2) ^ d) ^ (2 * q') :=
            Real.rpow_le_rpow (by have := hΛ0 i x ω; positivity) h1 (by positivity)
        _ = c ^ (2 * q') * (Y + 2) ^ (4 * r) := by
            rw [Real.mul_rpow hc0.le (by positivity), ← Real.rpow_natCast,
              ← Real.rpow_mul (by positivity)]
            congr 2
            rw [hr]
            ring
    calc ∫⁻ ω, ENNReal.ofReal (2 * d * Λ i x ω) ^ (2 * q') ∂latticeBondLaw d p
        ≤ ∫⁻ ω, ENNReal.ofReal (c ^ (2 * q') * (X (configurationTranslation (-x) ω) + 2) ^ (4 * r))
            ∂latticeBondLaw d p := lintegral_mono hpt
      _ = ENNReal.ofReal (c ^ (2 * q')) * ∫⁻ ω, ENNReal.ofReal ((X ω + 2) ^ (4 * r))
            ∂latticeBondLaw d p := by
          simp_rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ c ^ (2 * q') by positivity)]
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          congr 1
          exact (measurePreserving_configurationTranslation p (-x)).lintegral_comp
            ((hXm.add_const 2).pow_const _).ennreal_ofReal
      _ ≤ ENNReal.ofReal (c ^ (2 * q')) *
            ENNReal.ofReal (3 * (2 * D * r ^ (1 / s)) ^ (4 * r)) := by
          gcongr
          exact lintegral_add_two_rpow_le hs hθ hXm hX0 hXO hr1
      _ = ENNReal.ofReal ((Real.sqrt 3 * P ^ q') ^ 2) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [mul_pow, Real.sq_sqrt (by norm_num), ← Real.rpow_natCast (P ^ q') 2,
            ← Real.rpow_mul hP0.le, hP, Real.mul_rpow hc0.le (by positivity),
            ← Real.rpow_natCast (2 * D * r ^ (1 / s)) d, ← Real.rpow_mul (by positivity)]
          have e : (4 : ℝ) * r = (d : ℝ) * (q' * ((2 : ℕ) : ℝ)) := by rw [hr]; push_cast; ring
          rw [e]
          ring
  -- the random ball sum
  have hball := lintegral_randomBallSum_le (p := p) v (θ := 3 * d * θ') (by positivity)
    (fun t _ => measure_le_stoppingSize_le hθ' v (hexp v).1 (hexp v).2 t)
    ((measurable_stoppingSize_goodCubes v).const_mul (3 * d))
    (Y := fun x ω => ENNReal.ofReal (2 * d * Λ i x ω))
    (fun x => ((hΛm i x).const_mul (2 * d)).ennreal_ofReal) hq' (by positivity) hYm
  have hEs : ∀ ω, stepSixSum (Λ i) v ω = ∑' x, if ‖latticeEuclideanEmbedding (x - v)‖ ≤
      3 * d * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) v then
        ENNReal.ofReal (2 * d * Λ i x ω) else 0 := by
    intro ω
    unfold stepSixSum
    refine tsum_congr fun x => ?_
    split_ifs <;> simp
  simp only [hEs]
  refine hball.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [← hB₁]
  -- the arithmetic of the constants
  have hqd : (1 : ℝ) ≤ q' ^ d := one_le_pow₀ hq'
  have hbase : (2 * (1 + d * (4 * q' * (3 * d * θ')))) ^ d ≤ B₁ * q' ^ d := by
    rw [hB₁, ← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ d
    have h0 : 0 ≤ d * (4 * (3 * d * θ')) := by positivity
    nlinarith
  have h1 : ((2 * (1 + d * (4 * q' * (3 * d * θ')))) ^ d) ^ (q' - 1) ≤
      (B₁ * q' ^ d) ^ q' / B₁ := by
    calc ((2 * (1 + d * (4 * q' * (3 * d * θ')))) ^ d) ^ (q' - 1) ≤ (B₁ * q' ^ d) ^ (q' - 1) :=
          Real.rpow_le_rpow (by positivity) hbase (by linarith)
      _ = (B₁ * q' ^ d) ^ q' / (B₁ * q' ^ d) := by
          rw [Real.rpow_sub (by positivity), Real.rpow_one]
      _ ≤ (B₁ * q' ^ d) ^ q' / B₁ := by
          gcongr
          exact le_mul_of_one_le_right hB₁0.le hqd
  have hs6 : Real.sqrt 2 * Real.sqrt 3 = Real.sqrt 6 := by
    rw [← Real.sqrt_mul (by norm_num)]
    norm_num
  have h6 : Real.sqrt 6 ≤ Real.sqrt 6 ^ q' := by
    simpa using Real.rpow_le_rpow_of_exponent_le
      (show (1 : ℝ) ≤ Real.sqrt 6 by rw [Real.one_le_sqrt]; norm_num) hq'
  have hPk : q' ^ d * P = c * E ^ d * q' ^ k := by
    have hr' : r ^ (1 / s) = (d / 2) ^ (1 / s) * q' ^ (1 / s) := by
      rw [hr, show (d : ℝ) * q' / 2 = d / 2 * q' by ring, Real.mul_rpow (by positivity) hq'0.le]
    rw [hP, hr', show 2 * D * ((d / 2) ^ (1 / s) * q' ^ (1 / s)) = E * q' ^ (1 / s) by
        rw [hE]; ring, mul_pow, hk, Real.rpow_add hq'0, Real.rpow_natCast,
      ← Real.rpow_natCast (q' ^ (1 / s)) d, ← Real.rpow_mul hq'0.le,
      show 1 / s * (d : ℝ) = d / s by ring]
    ring
  have hB₁ne : B₁ ≠ 0 := hB₁0.ne'
  calc ((2 * (1 + d * (4 * q' * (3 * d * θ')))) ^ d) ^ (q' - 1) *
        (Real.sqrt 2 * B₁ * (Real.sqrt 3 * P ^ q'))
      ≤ (B₁ * q' ^ d) ^ q' / B₁ * (Real.sqrt 2 * B₁ * (Real.sqrt 3 * P ^ q')) := by
        gcongr
    _ = Real.sqrt 6 * ((B₁ * q' ^ d) ^ q' * P ^ q') := by
        rw [← hs6, div_mul_eq_mul_div, div_eq_iff hB₁ne]
        ring
    _ ≤ Real.sqrt 6 ^ q' * ((B₁ * q' ^ d) ^ q' * P ^ q') := by
        gcongr
    _ = (A * q' ^ k) ^ q' := by
        rw [← Real.mul_rpow (by positivity) (by positivity),
          ← Real.mul_rpow (by positivity) (by positivity)]
        congr 1
        rw [hA, mul_assoc B₁, hPk]
        ring

/-- **The coarsening error (5.10) at every vertex**, from the order-zero regularity input and the
exponential moments of the partition sizes. -/
theorem baseCoarseningError [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) :
    ∃ s₆ C₆ : ℝ, 0 < s₆ ∧ 0 < C₆ ∧ BaseCoarseningError hG hGv p s₆ C₆ := by
  obtain ⟨Λ, A, k, hA0, hk0, hΛm, hΛ0, hlip, hmom6⟩ := stepSix_data hG hGv hd hpc hp1 hGae
  set s₆ : ℝ := 1 / (2 * k) with hs₆
  have hs₆0 : 0 < s₆ := by positivity
  have hs₆k : s₆ * k < 1 := by rw [hs₆]; field_simp; linarith
  obtain ⟨C₆, hC₆, hmom⟩ := isOsBond_of_moment_le (d := d) (p := p) hA0 hs₆0 hs₆k
  refine ⟨s₆, C₆, hs₆0, hC₆, fun i v => ?_⟩
  have hE₆m := measurable_stepSixSum (hΛm i) v
  have hfin : ∀ᵐ ω ∂latticeBondLaw d p, stepSixSum (Λ i) v ω < ⊤ := by
    refine ae_lt_top hE₆m ?_
    have := hmom6 i v 1 le_rfl
    simp only [ENNReal.rpow_one] at this
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top this
  refine ⟨fun ω => (stepSixSum (Λ i) v ω).toReal, hE₆m.ennreal_toReal, ?_, ?_⟩
  · refine hmom _ hE₆m.ennreal_toReal (fun ω => ENNReal.toReal_nonneg) fun q' hq' => ?_
    have hq'0 : 0 < q' := by linarith
    have hmq : Measurable fun ω => (stepSixSum (Λ i) v ω).toReal ^ q' :=
      hE₆m.ennreal_toReal.pow_const q'
    have hnn : 0 ≤ᵐ[latticeBondLaw d p] fun ω => (stepSixSum (Λ i) v ω).toReal ^ q' :=
      Eventually.of_forall fun ω => by positivity
    have hlin : ∫⁻ ω, ENNReal.ofReal ((stepSixSum (Λ i) v ω).toReal ^ q') ∂latticeBondLaw d p ≤
        ENNReal.ofReal ((A * q' ^ k) ^ q') := by
      refine (lintegral_mono fun ω => ?_).trans (hmom6 i v q' hq')
      rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hq'0.le]
      exact ENNReal.rpow_le_rpow ENNReal.ofReal_toReal_le hq'0.le
    refine ⟨⟨hmq.aestronglyMeasurable, ?_⟩, ?_⟩
    · rw [hasFiniteIntegral_iff_ofReal hnn]
      exact lt_of_le_of_lt hlin ENNReal.ofReal_lt_top
    · rw [integral_eq_lintegral_of_nonneg_ae hnn hmq.aestronglyMeasurable]
      exact ENNReal.toReal_le_of_le_ofReal (by positivity) hlin
  · have hall : ∀ᵐ ω ∂latticeBondLaw d p, ∀ x, ω ∈ infiniteComponentEvent x →
        ∀ y, (openGraph ω).Adj x y →
          |correctorDiff hG hGv (Pi.single i 1) ω x y| ≤ Λ i x ω :=
      ae_all_iff.2 fun x => hlip i x
    filter_upwards [hGae, ae_partitionEvent hd hpc, hall, hfin] with ω hω hP hl hf hv
    have h := abs_correctorDiff_guardAnchor_le hG hGv (by omega) hω hP hv (Λ := fun x => Λ i x ω)
      (fun x => hΛ0 i x ω) hl
    exact (ENNReal.ofReal_le_iff_le_toReal hf.ne).1 h

end Base

end Rigidity.Corrector.GeneralDim
