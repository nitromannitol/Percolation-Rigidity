import Rigidity.Proofs.Percolation.PlanarCubeEnergyBounds

/-!
# Upper bound for `-μ` on the planar cluster

The coarse gradient across a lattice edge inside a resolved cube `U` is bounded by the variation
over the open edges of the cluster inside a pair window. Summing over the edges, regrouping the
open edges by the number of windows containing them and applying the Cauchy–Schwarz inequality
gives

`-μ(U, q) ≤ 9 (|q₁| + |q₂|) ^ 2 ∑_{a ∈ C_*(U)} W(a) ^ 2 / |U|`,

where `W(a)` counts the lattice edges of `U` whose window contains `a` (Armstrong and Dario,
Lemma 4.3, bound for `μ`, with windows in place of neighbouring partition cubes). Each window lies
in the square of side `9s` around one of the two partition cubes of the edge, so `W(a)` is at most
four times the number of vertices of `U` whose partition cube has its square of side `9s` around
`a`.
-/

open LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped Classical

namespace Rigidity.Percolation

variable {ω : Configuration 2}

/-- The window used for the coarse gradient across two adjacent vertices: the pair window of the
partition cube of smaller scale and the other one, restricted to the cluster. -/
noncomputable def coarseEdgeWindow (ω : Configuration 2) (U : TriadicCube 2) (x y : Vertex 2) :
    Finset (Vertex 2) :=
  if (planarPartCube ω x).scale ≤ (planarPartCube ω y).scale then
    planarClusterPairWindow ω U x y
  else planarClusterPairWindow ω U y x

theorem abs_coarseAnchor_sub_le_coarseEdgeWindow (hP : PlanarPartitionEvent ω)
    {U : TriadicCube 2} (hU : PlanarResolved ω U) {x y : Vertex 2} (hx : x ∈ U.vertices)
    (hy : y ∈ U.vertices) (hnear : ∀ i, |x i - y i| ≤ 1) (w : Vertex 2 → ℝ) :
    |w (planarCoarseAnchor ω x) - w (planarCoarseAnchor ω y)| ≤
      edgeVariationIn ω (coarseEdgeWindow ω U x y) w := by
  unfold coarseEdgeWindow
  split_ifs with h
  · exact abs_coarseAnchor_sub_le_clusterPairWindow hP hU hx hy hnear h w
  · rw [abs_sub_comm]
    exact abs_coarseAnchor_sub_le_clusterPairWindow hP hU hy hx
      (fun i => by rw [abs_sub_comm]; exact hnear i) (le_of_not_ge h) w

theorem coarseEdgeWindow_subset {U : TriadicCube 2} (x y : Vertex 2) :
    coarseEdgeWindow ω U x y ⊆ clusterVertices ω U := by
  intro a ha
  rw [mem_clusterVertices]
  unfold coarseEdgeWindow planarClusterPairWindow at ha
  split_ifs at ha <;> exact (Finset.mem_filter.1 ha).2

/-- The windows lie in the squares of side `9s` around the two partition cubes. -/
theorem mem_ninefold_of_mem_coarseEdgeWindow (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) {x y : Vertex 2} (hx : x ∈ U.vertices) (hy : y ∈ U.vertices)
    (hnear : ∀ i, |x i - y i| ≤ 1) {a : Vertex 2} (ha : a ∈ coarseEdgeWindow ω U x y) :
    a ∈ (planarPartCube ω x).ninefold.vertices ∨ a ∈ (planarPartCube ω y).ninefold.vertices := by
  have hsub := planarPartCube_subset_of_resolved hP hU hx
  have hsub' := planarPartCube_subset_of_resolved hP hU hy
  obtain ⟨hsc1, hsc2⟩ := planarPartCube_scales_close hP hnear
  unfold coarseEdgeWindow planarClusterPairWindow at ha
  split_ifs at ha with h
  · left
    have hspec := TriadicCube.pairWindow_spec (hU x hx) hsub hsub' h hsc2
      (planarPartCube_spec hP x).1 (planarPartCube_spec hP y).1 hnear
    exact TriadicCube.subset_ninefold_of_mem_planarSquares hspec.1 (Finset.mem_filter.1 ha).1
  · right
    have hnear' : ∀ i, |y i - x i| ≤ 1 := fun i => by rw [abs_sub_comm]; exact hnear i
    have hspec := TriadicCube.pairWindow_spec (hU y hy) hsub' hsub (le_of_not_ge h) hsc1
      (planarPartCube_spec hP y).1 (planarPartCube_spec hP x).1 hnear'
    exact TriadicCube.subset_ninefold_of_mem_planarSquares hspec.1 (Finset.mem_filter.1 ha).1

/-- The variation over a subset of the cluster, written as a sum over the cluster. -/
theorem edgeVariationIn_le_of_subset {U : TriadicCube 2} (u : ClusterFun ω U)
    {S : Finset (Vertex 2)} (hS : S ⊆ clusterVertices ω U) :
    edgeVariationIn ω S (clusterExtend ω U u) ≤
      ∑ x : ↥(clusterVertices ω U), ∑ y : ↥(clusterVertices ω U),
        (if (openGraph ω).Adj x.1 y.1 then |u x - u y| else 0) *
          (if x.1 ∈ S then 1 else 0) := by
  set C := clusterVertices ω U
  set G : Vertex 2 → Vertex 2 → ℝ := fun a b =>
    if (openGraph ω).Adj a b then |clusterExtend ω U u a - clusterExtend ω U u b| else 0 with hG
  have hG0 : ∀ a b, 0 ≤ G a b := fun a b => by
    simp only [hG]
    split_ifs <;> positivity
  have h1 : edgeVariationIn ω S (clusterExtend ω U u) = ∑ a ∈ S, ∑ b ∈ S, G a b := rfl
  have h2 : ∑ a ∈ S, ∑ b ∈ S, G a b ≤ ∑ a ∈ S, ∑ b ∈ C, G a b :=
    Finset.sum_le_sum fun a _ =>
      Finset.sum_le_sum_of_subset_of_nonneg hS fun b _ _ => hG0 a b
  have h3 : ∑ a ∈ S, ∑ b ∈ C, G a b = ∑ a ∈ C, ∑ b ∈ C, G a b * (if a ∈ S then 1 else 0) := by
    have hfil : C.filter (· ∈ S) = S := by
      ext a
      simp only [Finset.mem_filter, and_iff_right_iff_imp]
      exact fun ha => hS ha
    rw [← hfil, Finset.sum_filter, hfil]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs
    · simp
    · simp
  have h4 : ∑ a ∈ C, ∑ b ∈ C, G a b * (if a ∈ S then 1 else 0) =
      ∑ x : ↥C, ∑ y : ↥C, (if (openGraph ω).Adj x.1 y.1 then |u x - u y| else 0) *
        (if x.1 ∈ S then 1 else 0) := by
    rw [← Finset.sum_coe_sort C]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_coe_sort C]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [hG]
    rw [clusterExtend_apply_of_mem u x.2, clusterExtend_apply_of_mem u y.2]
  rw [h1]
  exact h2.trans (h3.trans h4).le

/-- **Regrouping.** A sum of variations over subsets of the cluster is at most the sum over
ordered open edges of the increments weighted by the number of subsets containing the first
vertex. -/
theorem sum_edgeVariationIn_le {U : TriadicCube 2} (u : ClusterFun ω U) {ι : Type*}
    (I : Finset ι) (S : ι → Finset (Vertex 2)) (hS : ∀ k, S k ⊆ clusterVertices ω U) :
    ∑ k ∈ I, edgeVariationIn ω (S k) (clusterExtend ω U u) ≤
      ∑ x : ↥(clusterVertices ω U), ∑ y : ↥(clusterVertices ω U),
        (if (openGraph ω).Adj x.1 y.1 then |u x - u y| else 0) *
          ∑ k ∈ I, (if x.1 ∈ S k then 1 else 0) := by
  calc ∑ k ∈ I, edgeVariationIn ω (S k) (clusterExtend ω U u)
      ≤ ∑ k ∈ I, ∑ x : ↥(clusterVertices ω U), ∑ y : ↥(clusterVertices ω U),
          (if (openGraph ω).Adj x.1 y.1 then |u x - u y| else 0) *
            (if x.1 ∈ S k then 1 else 0) :=
        Finset.sum_le_sum fun k _ => edgeVariationIn_le_of_subset u (hS k)
    _ = _ := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.mul_sum]

/-- Sums over ordered open edges of a function of the first vertex are at most nine times the sum
of the function. -/
theorem sum_adj_le_nine_mul {U : TriadicCube 2} (f : ↥(clusterVertices ω U) → ℝ)
    (hf : ∀ x, 0 ≤ f x) :
    ∑ x : ↥(clusterVertices ω U), ∑ y : ↥(clusterVertices ω U),
      (if (openGraph ω).Adj x.1 y.1 then f x else 0) ≤ 9 * ∑ x, f x := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ (hf x)
  have h := card_filter_adj_le (ω := ω) (clusterVertices ω U) x.1
  have hle : (Finset.univ.filter fun y : ↥(clusterVertices ω U) =>
      (openGraph ω).Adj x.1 y.1).card ≤
      ((clusterVertices ω U).filter fun y => (openGraph ω).Adj x.1 y).card := by
    rw [← Finset.card_map (Function.Embedding.subtype _)]
    apply Finset.card_le_card
    intro z hz
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.Embedding.subtype_apply] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    exact Finset.mem_filter.2 ⟨y.2, hy⟩
  exact_mod_cast hle.trans h

/-- The lattice edges `(x, x + e_i)` inside a triadic cube. -/
noncomputable def latticeEdgesIn (U : TriadicCube 2) : Finset (Vertex 2 × Fin 2) :=
  (U.toIntegerCube.vertices ×ˢ Finset.univ).filter
    fun k => k.1 + unitVertex k.2 ∈ U.toIntegerCube.vertices

/-- The number of lattice edges of `U` whose window contains `a`. -/
noncomputable def coarseWeight (ω : Configuration 2) (U : TriadicCube 2) (a : Vertex 2) : ℝ :=
  ∑ k ∈ latticeEdgesIn U,
    if a ∈ coarseEdgeWindow ω U k.1 (k.1 + unitVertex k.2) then 1 else 0

theorem coarseWeight_nonneg (U : TriadicCube 2) (a : Vertex 2) : 0 ≤ coarseWeight ω U a :=
  Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num

theorem abs_sub_unitVertex_le (x : Vertex 2) (i j : Fin 2) : |x j - (x + unitVertex i) j| ≤ 1 := by
  simp only [unitVertex, Pi.add_apply]
  by_cases h : j = i
  · subst h
    simp
  · simp [h]

theorem coarsePairing_eq_sum_latticeEdgesIn {U : TriadicCube 2} (q : Fin 2 → ℝ)
    (u : ClusterFun ω U) :
    coarsePairing ω U q u = ∑ k ∈ latticeEdgesIn U,
      q k.2 * (clusterExtend ω U u (planarCoarseAnchor ω (k.1 + unitVertex k.2)) -
        clusterExtend ω U u (planarCoarseAnchor ω k.1)) := by
  rw [coarsePairing_apply, latticeEdgesIn, Finset.sum_filter, Finset.sum_product]

/-- The variation of a function over the ordered open edges of the cluster, weighted by the
coarse weight of the first vertex. -/
noncomputable def weightedVariation (ω : Configuration 2) (U : TriadicCube 2)
    (u : ClusterFun ω U) : ℝ :=
  ∑ x : ↥(clusterVertices ω U), ∑ y : ↥(clusterVertices ω U),
    (if (openGraph ω).Adj x.1 y.1 then |u x - u y| else 0) * coarseWeight ω U x.1

/-- The sum over ordered open edges of the cluster of the squared coarse weight of the first
vertex. -/
noncomputable def weightSquareSum (ω : Configuration 2) (U : TriadicCube 2) : ℝ :=
  ∑ x : ↥(clusterVertices ω U), ∑ y : ↥(clusterVertices ω U),
    (if (openGraph ω).Adj x.1 y.1 then coarseWeight ω U x.1 ^ 2 else 0)

theorem weightSquareSum_nonneg (U : TriadicCube 2) : 0 ≤ weightSquareSum ω U :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by
    split_ifs
    · exact sq_nonneg _
    · exact le_rfl

theorem weightSquareSum_le (U : TriadicCube 2) :
    weightSquareSum ω U ≤ 9 * ∑ x : ↥(clusterVertices ω U), coarseWeight ω U x.1 ^ 2 :=
  sum_adj_le_nine_mul (fun x => coarseWeight ω U x.1 ^ 2) (fun _ => sq_nonneg _)

/-- The coarse pairing is bounded by the weighted variation. -/
theorem coarsePairing_le_weightedVariation (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) (q : Fin 2 → ℝ) (u : ClusterFun ω U) :
    coarsePairing ω U q u ≤ (|q 0| + |q 1|) * weightedVariation ω U u := by
  have hQ0 : 0 ≤ |q 0| + |q 1| := by positivity
  rw [coarsePairing_eq_sum_latticeEdgesIn]
  have hsum : ∑ k ∈ latticeEdgesIn U,
      q k.2 * (clusterExtend ω U u (planarCoarseAnchor ω (k.1 + unitVertex k.2)) -
        clusterExtend ω U u (planarCoarseAnchor ω k.1)) ≤
      ∑ k ∈ latticeEdgesIn U, (|q 0| + |q 1|) * edgeVariationIn ω
        (coarseEdgeWindow ω U k.1 (k.1 + unitVertex k.2)) (clusterExtend ω U u) := by
    refine Finset.sum_le_sum fun k hk => ?_
    obtain ⟨hk1, hk2⟩ := Finset.mem_filter.1 hk
    have hx : k.1 ∈ U.vertices :=
      (U.mem_toIntegerCube_vertices _).1 (Finset.mem_product.1 hk1).1
    have hy : k.1 + unitVertex k.2 ∈ U.vertices := (U.mem_toIntegerCube_vertices _).1 hk2
    have hbound := abs_coarseAnchor_sub_le_coarseEdgeWindow hP hU hx hy
      (abs_sub_unitVertex_le k.1 k.2) (clusterExtend ω U u)
    have hq : |q k.2| ≤ |q 0| + |q 1| := by
      rcases Fin.exists_fin_two.1 ⟨k.2, rfl⟩ with h | h <;> rw [h]
      · linarith [abs_nonneg (q 1)]
      · linarith [abs_nonneg (q 0)]
    calc q k.2 * (clusterExtend ω U u (planarCoarseAnchor ω (k.1 + unitVertex k.2)) -
          clusterExtend ω U u (planarCoarseAnchor ω k.1))
        ≤ |q k.2| * |clusterExtend ω U u (planarCoarseAnchor ω (k.1 + unitVertex k.2)) -
          clusterExtend ω U u (planarCoarseAnchor ω k.1)| := by
          rw [← abs_mul]
          exact le_abs_self _
      _ ≤ (|q 0| + |q 1|) * edgeVariationIn ω (coarseEdgeWindow ω U k.1 (k.1 + unitVertex k.2))
          (clusterExtend ω U u) := by
          rw [abs_sub_comm]
          exact mul_le_mul hq hbound (abs_nonneg _) hQ0
  refine hsum.trans ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left
    (sum_edgeVariationIn_le u (latticeEdgesIn U) _ fun k => coarseEdgeWindow_subset _ _) hQ0

theorem two_mul_clusterForm_self {U : TriadicCube 2} (u : ClusterFun ω U) :
    2 * clusterForm ω U u u = ∑ x : ↥(clusterVertices ω U), ∑ y : ↥(clusterVertices ω U),
      (if (openGraph ω).Adj x.1 y.1 then |u x - u y| else 0) ^ 2 := by
  rw [clusterForm_apply]
  rw [show 2 * (1 / 2 * ∑ x, ∑ y, clusterFormTerm ω u u x y) =
    ∑ x, ∑ y, clusterFormTerm ω u u x y by ring]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  simp only [clusterFormTerm]
  split_ifs
  · rw [sq_abs, sq]
  · simp

/-- **Cauchy–Schwarz** for the weighted variation. -/
theorem weightedVariation_sq_le {U : TriadicCube 2} (u : ClusterFun ω U) :
    weightedVariation ω U u ^ 2 ≤ weightSquareSum ω U * (2 * clusterForm ω U u u) := by
  rw [two_mul_clusterForm_self, weightedVariation, weightSquareSum]
  simp only [← Finset.sum_product']
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ ×ˢ Finset.univ)
    (fun p : ↥(clusterVertices ω U) × ↥(clusterVertices ω U) =>
      if (openGraph ω).Adj p.1.1 p.2.1 then coarseWeight ω U p.1.1 else 0)
    (fun p : ↥(clusterVertices ω U) × ↥(clusterVertices ω U) =>
      if (openGraph ω).Adj p.1.1 p.2.1 then |u p.1 - u p.2| else 0)
  have e1 : ∀ p : ↥(clusterVertices ω U) × ↥(clusterVertices ω U),
      (if (openGraph ω).Adj p.1.1 p.2.1 then |u p.1 - u p.2| else 0) * coarseWeight ω U p.1.1 =
      (if (openGraph ω).Adj p.1.1 p.2.1 then coarseWeight ω U p.1.1 else 0) *
        (if (openGraph ω).Adj p.1.1 p.2.1 then |u p.1 - u p.2| else 0) := by
    intro p
    split_ifs <;> ring
  have e2 : ∀ p : ↥(clusterVertices ω U) × ↥(clusterVertices ω U),
      (if (openGraph ω).Adj p.1.1 p.2.1 then coarseWeight ω U p.1.1 ^ 2 else 0) =
      (if (openGraph ω).Adj p.1.1 p.2.1 then coarseWeight ω U p.1.1 else 0) ^ 2 := by
    intro p
    split_ifs <;> simp
  simp only [e1, e2]
  exact hcs

/-- An elementary inequality: `B ≤ Q X` and `X² ≤ 2 T B` give `B ≤ 2 Q² T`. -/
theorem le_of_le_mul_of_sq_le {B Q X T : ℝ} (hB : 0 ≤ B) (hT : 0 ≤ T) (h1 : B ≤ Q * X)
    (h2 : X ^ 2 ≤ T * (2 * B)) (hQ : 0 ≤ Q) : B ≤ 2 * Q ^ 2 * T := by
  rcases hB.eq_or_lt with h | hBpos
  · rw [← h]
    positivity
  have hX : 0 ≤ X := by
    by_contra hneg
    push Not at hneg
    nlinarith
  have h3 : B ^ 2 ≤ Q ^ 2 * X ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hB h1 2
  have h4 : B * B ≤ (2 * Q ^ 2 * T) * B := by
    have := h3.trans (mul_le_mul_of_nonneg_left h2 (sq_nonneg Q))
    nlinarith
  exact le_of_mul_le_mul_right h4 hBpos

/-- **Upper bound for `-μ`** (planar form of Armstrong and Dario, Lemma 4.3). -/
theorem neg_planarMu_le (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) (q : Fin 2 → ℝ) :
    -planarMu ω U q ≤
      9 * (|q 0| + |q 1|) ^ 2 * (∑ x : ↥(clusterVertices ω U), coarseWeight ω U x.1 ^ 2) /
        U.volume := by
  obtain ⟨u, hu, hvar, hμ⟩ := exists_planarMu_minimizer hP hU q
  have hvol := U.volume_pos
  have hB0 : 0 ≤ clusterForm ω U u u := clusterForm_self_nonneg u
  have hℓ : coarsePairing ω U q u = clusterForm ω U u u := (hvar u hu).symm
  have hneg : -planarMu ω U q = clusterForm ω U u u / 2 / U.volume := by
    rw [hμ, hℓ]
    ring
  have h1 : clusterForm ω U u u ≤ (|q 0| + |q 1|) * weightedVariation ω U u :=
    hℓ ▸ coarsePairing_le_weightedVariation hP hU q u
  have hB := le_of_le_mul_of_sq_le hB0 (weightSquareSum_nonneg U) h1
    (weightedVariation_sq_le u) (by positivity)
  have hT9 := weightSquareSum_le (ω := ω) U
  rw [hneg]
  apply div_le_div_of_nonneg_right _ hvol.le
  calc clusterForm ω U u u / 2 ≤ (|q 0| + |q 1|) ^ 2 * weightSquareSum ω U := by linarith
    _ ≤ (|q 0| + |q 1|) ^ 2 *
        (9 * ∑ x : ↥(clusterVertices ω U), coarseWeight ω U x.1 ^ 2) :=
        mul_le_mul_of_nonneg_left hT9 (sq_nonneg _)
    _ = _ := by ring

/-- An indicator bounded by the sum of two indicators. -/
theorem indicator_le_add_indicator {P R S : Prop} [Decidable P] [Decidable R] [Decidable S]
    (h : P → R ∨ S) :
    (if P then (1 : ℝ) else 0) ≤ (if R then 1 else 0) + (if S then 1 else 0) := by
  by_cases hP : P
  · rw [if_pos hP]
    rcases h hP with hR | hS
    · rw [if_pos hR]
      have : (0 : ℝ) ≤ if S then 1 else 0 := by split_ifs <;> norm_num
      linarith
    · rw [if_pos hS]
      have : (0 : ℝ) ≤ if R then 1 else 0 := by split_ifs <;> norm_num
      linarith
  · rw [if_neg hP]
    have h1 : (0 : ℝ) ≤ if R then 1 else 0 := by split_ifs <;> norm_num
    have h2 : (0 : ℝ) ≤ if S then 1 else 0 := by split_ifs <;> norm_num
    linarith

/-- Sums over the lattice edges of `U` of a function of the second endpoint. -/
theorem sum_latticeEdgesIn_snd_le (U : TriadicCube 2) (f : Vertex 2 → ℝ) (hf : ∀ z, 0 ≤ f z) :
    ∑ k ∈ latticeEdgesIn U, f (k.1 + unitVertex k.2) ≤
      2 * ∑ z ∈ U.toIntegerCube.vertices, f z := by
  rw [latticeEdgesIn, Finset.sum_filter, Finset.sum_product_right]
  rw [show (2 : ℝ) * ∑ z ∈ U.toIntegerCube.vertices, f z =
      ∑ _i : Fin 2, ∑ z ∈ U.toIntegerCube.vertices, f z by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← Finset.sum_filter]
  calc ∑ x ∈ U.toIntegerCube.vertices.filter
        (fun x => x + unitVertex i ∈ U.toIntegerCube.vertices), f (x + unitVertex i)
      = ∑ z ∈ (U.toIntegerCube.vertices.filter
          fun x => x + unitVertex i ∈ U.toIntegerCube.vertices).image (· + unitVertex i), f z :=
        (Finset.sum_image (fun x _ y _ h => add_right_cancel h)).symm
    _ ≤ ∑ z ∈ U.toIntegerCube.vertices, f z := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun z _ _ => hf z
        intro z hz
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hz
        exact (Finset.mem_filter.1 hx).2

/-- Sums over the lattice edges of `U` of a function of the first endpoint. -/
theorem sum_latticeEdgesIn_fst_le (U : TriadicCube 2) (f : Vertex 2 → ℝ) (hf : ∀ z, 0 ≤ f z) :
    ∑ k ∈ latticeEdgesIn U, f k.1 ≤ 2 * ∑ z ∈ U.toIntegerCube.vertices, f z := by
  calc ∑ k ∈ latticeEdgesIn U, f k.1
      ≤ ∑ k ∈ U.toIntegerCube.vertices ×ˢ (Finset.univ : Finset (Fin 2)), f k.1 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun k _ _ => hf k.1
    _ = 2 * ∑ z ∈ U.toIntegerCube.vertices, f z := by
        rw [Finset.sum_product, Finset.mul_sum]
        refine Finset.sum_congr rfl fun z _ => ?_
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        norm_num

/-- **The weight is controlled by the partition.** Each window lies in the square of side `9s`
around one of the two partition cubes of its edge. -/
theorem coarseWeight_le (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) (a : Vertex 2) :
    coarseWeight ω U a ≤ 4 * ∑ z ∈ U.toIntegerCube.vertices,
      if a ∈ (planarPartCube ω z).ninefold.vertices then 1 else 0 := by
  set f : Vertex 2 → ℝ := fun z =>
    if a ∈ (planarPartCube ω z).ninefold.vertices then 1 else 0 with hf
  have hf0 : ∀ z, 0 ≤ f z := fun z => by
    simp only [hf]
    split_ifs <;> norm_num
  have hstep : ∀ k ∈ latticeEdgesIn U,
      (if a ∈ coarseEdgeWindow ω U k.1 (k.1 + unitVertex k.2) then (1 : ℝ) else 0) ≤
        f k.1 + f (k.1 + unitVertex k.2) := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_filter.1 hk
    have hx : k.1 ∈ U.vertices :=
      (U.mem_toIntegerCube_vertices _).1 (Finset.mem_product.1 hk1).1
    have hy : k.1 + unitVertex k.2 ∈ U.vertices := (U.mem_toIntegerCube_vertices _).1 hk2
    exact indicator_le_add_indicator fun h =>
      mem_ninefold_of_mem_coarseEdgeWindow hP hU hx hy (abs_sub_unitVertex_le k.1 k.2) h
  calc coarseWeight ω U a
      ≤ ∑ k ∈ latticeEdgesIn U, (f k.1 + f (k.1 + unitVertex k.2)) := Finset.sum_le_sum hstep
    _ = ∑ k ∈ latticeEdgesIn U, f k.1 + ∑ k ∈ latticeEdgesIn U, f (k.1 + unitVertex k.2) :=
        Finset.sum_add_distrib
    _ ≤ 2 * ∑ z ∈ U.toIntegerCube.vertices, f z + 2 * ∑ z ∈ U.toIntegerCube.vertices, f z :=
        add_le_add (sum_latticeEdgesIn_fst_le U f hf0) (sum_latticeEdgesIn_snd_le U f hf0)
    _ = 4 * ∑ z ∈ U.toIntegerCube.vertices, f z := by ring

end Rigidity.Percolation
