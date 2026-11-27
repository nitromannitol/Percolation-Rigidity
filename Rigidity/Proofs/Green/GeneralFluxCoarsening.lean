import Rigidity.Proofs.Green.GeneralFluxDensity
import Rigidity.Proofs.Green.GeneralFluxWeakNormStatement
import Rigidity.Proofs.Green.DarioGuFluxCoarsening
import Rigidity.Proofs.Corrector.GeneralCoarseningError

/-!
# The coarsened test function of Dario–Gu, Appendix B, Step 1, on `ℤ^d`

The extension of the first part of `DarioGuFluxCoarsening.lean` from the planar partition to the
partition into good cubes of `ℤ^d` of Percolation-Cluster-Homogenization (`PartitionEvent`,
`partitionCube`, `partitionAnchor`). For a test function `v` of the `H̲^{-1}` norm on
`V = 𝒞_∞ ∩ B_r(y)`, Dario–Gu extend `v` from the infinite cluster to `ℤ^d` by the coarsening
(def.coarsenu): `v` on the cluster, and `v` at the anchor of the partition cube off it, `v` being
first extended by zero off `V` (`zeroExtD`); the coarsened function is `coarseTestD`. With
`partSide ω x = 3^{scale}` the side of the partition cube of `x`:

* `card_fiber_partitionAnchor_le`: at most `partSide^d` points share an anchor;
* `abs_sub_partitionAnchor_lt`: `|x_i - a(x)_i| < partSide(x)`;
* `sum_mul_coarseTestD_eq`: the pairing of a function vanishing off the cluster with `v` on `V`
  is its pairing with `coarseTestD` on `ℤ^d`; `coarseTestD_eq_zero_of_far`: its support;
* `sum_sq_coarseTestD_le`: `‖coarseTestD‖² ≤ (1 + L^d) ‖v‖²_{ℓ²(V)}` ((eq:estcoarseminusu));
* `sum_sq_grad_coarseTestD_le`: `‖∇ coarseTestD‖² ≤ 9 d (3 + 6L)^{2d} Σ_V |∇v|²`
  ((est.nablacoarsenL2)): a vertex of the infinite cluster is joined to its anchor inside the box
  of radius `3 size(□_𝒫)` (`reachable_anchorBox`), and the anchors of two neighbours are joined
  inside the union of their partition cubes (Armstrong–Dario, Corollary 2.10,
  `reachable_partitionAnchor_of_walk`).
-/

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.Percolation Rigidity.Proofs.S2
  Rigidity.Poincare.GeneralDim
open scoped Classical

namespace Rigidity.Green.GeneralFlux

variable {d : ℕ} {ω : Configuration d}

/-- `v` on `V`, zero off `V`. -/
noncomputable def zeroExtD (V : Finset (Vertex d)) (v : Vertex d → ℝ) (x : Vertex d) : ℝ :=
  if x ∈ V then v x else 0

/-- **The coarsened test function**: `v` on the cluster `K`, and `v` at the anchor of the
partition cube off it, `v` extended by zero off `V`. -/
noncomputable def coarseTestD (ω : Configuration d) (K : Set (Vertex d)) (V : Finset (Vertex d))
    (v : Vertex d → ℝ) (x : Vertex d) : ℝ :=
  if x ∈ K then zeroExtD V v x else zeroExtD V v (partitionAnchor ω x)

/-- The side `3^{scale}` of the partition cube containing `x`. -/
noncomputable def partSide (ω : Configuration d) (x : Vertex d) : ℕ :=
  3 ^ (partitionCube ω x).scale

theorem mem_vertices_iff_mem_triadicCubeFinsetD (Q : TriadicCube d) (x : Vertex d) :
    x ∈ Q.vertices ↔ x ∈ triadicCubeFinset d Q.scale Q.index := by
  simp only [TriadicCube.vertices, TriadicCube.side, Set.mem_setOf_eq, triadicCubeFinset,
    Fintype.mem_piFinset, Finset.mem_Icc]
  refine forall_congr' fun i => ?_
  have hQ := three_pow_eq_two_mul_half_add_one Q.scale
  rw [abs_lt]
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> omega
  · rintro ⟨h1, h2⟩
    constructor <;> omega

theorem abs_sub_lt_side_of_memD {Q : TriadicCube d} {x z : Vertex d} (hx : x ∈ Q.vertices)
    (hz : z ∈ Q.vertices) (i : Fin d) : |x i - z i| < (3 : ℤ) ^ Q.scale := by
  have h1 := hx i
  have h2 := hz i
  simp only [TriadicCube.side] at h1 h2
  rw [abs_lt] at h1 h2 ⊢
  constructor <;> omega

theorem partitionCube_partitionAnchor (hP : PartitionEvent ω) (x : Vertex d) :
    partitionCube ω (partitionAnchor ω x) = partitionCube ω x :=
  partitionCube_eq_of_mem hP (partitionAnchor_mem hP x)

theorem partSide_partitionAnchor (hP : PartitionEvent ω) (x : Vertex d) :
    partSide ω (partitionAnchor ω x) = partSide ω x := by
  rw [partSide, partSide, partitionCube_partitionAnchor hP]

/-- **At most `partSide^d` points share an anchor.** -/
theorem card_fiber_partitionAnchor_le (hP : PartitionEvent ω) (W : Finset (Vertex d))
    (z : Vertex d) :
    ((W.filter fun x => partitionAnchor ω x = z).card : ℝ) ≤ (partSide ω z : ℝ) ^ d := by
  have hsub : W.filter (fun x => partitionAnchor ω x = z) ⊆
      triadicCubeFinset d (partitionCube ω z).scale (partitionCube ω z).index := by
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [← mem_vertices_iff_mem_triadicCubeFinsetD]
    have hQ : partitionCube ω x = partitionCube ω z := by
      rw [← hx.2, partitionCube_partitionAnchor hP]
    rw [← hQ]
    exact mem_partitionCube hP x
  have hc := Finset.card_le_card hsub
  have hcard : ((triadicCubeFinset d (partitionCube ω z).scale
      (partitionCube ω z).index).card : ℝ) = (partSide ω z : ℝ) ^ d := by
    rw [card_triadicCubeFinset, partSide]
    push_cast
    rw [← pow_mul, mul_comm]
  calc ((W.filter fun x => partitionAnchor ω x = z).card : ℝ)
      ≤ ((triadicCubeFinset d (partitionCube ω z).scale
          (partitionCube ω z).index).card : ℝ) := by exact_mod_cast hc
    _ = _ := hcard

theorem abs_sub_partitionAnchor_lt (hP : PartitionEvent ω) (x : Vertex d) (i : Fin d) :
    |x i - partitionAnchor ω x i| < (partSide ω x : ℤ) := by
  rw [partSide]
  push_cast
  exact abs_sub_lt_side_of_memD (mem_partitionCube hP x)
    (partitionAnchor_mem hP x) i

/-! ### The pairing and the support -/

/-- **The pairing with the coarsened test function.** -/
theorem sum_mul_coarseTestD_eq {K : Set (Vertex d)} {V W : Finset (Vertex d)}
    (hVK : ∀ x ∈ V, x ∈ K) (hVW : V ⊆ W) (v F : Vertex d → ℝ) (hF : ∀ x, x ∉ K → F x = 0) :
    ∑ x ∈ W, F x * coarseTestD ω K V v x = ∑ x ∈ V, F x * v x := by
  have h1 : ∀ x ∈ W, F x * coarseTestD ω K V v x = if x ∈ V then F x * v x else 0 := by
    intro x _
    unfold coarseTestD zeroExtD
    by_cases hxK : x ∈ K
    · rw [if_pos hxK]
      split_ifs <;> ring
    · rw [hF x hxK, zero_mul, if_neg fun hV => hxK (hVK x hV)]
  rw [Finset.sum_congr rfl h1, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
    Finset.inter_eq_right.2 hVW]

theorem coarseTestD_eq_zero_of_far (hP : PartitionEvent ω) {K : Set (Vertex d)}
    {V : Finset (Vertex d)} {y : Vertex d} {R L : ℕ} (hVR : ∀ z ∈ V, ∀ i, |z i - y i| ≤ R)
    (hside : ∀ z ∈ V, partSide ω z ≤ L) (v : Vertex d → ℝ) {x : Vertex d}
    (hx : coarseTestD ω K V v x ≠ 0) : ∀ i, |x i - y i| ≤ R + L := by
  intro i
  unfold coarseTestD zeroExtD at hx
  by_cases hxK : x ∈ K
  · rw [if_pos hxK] at hx
    by_cases hxV : x ∈ V
    · have := hVR x hxV i
      omega
    · rw [if_neg hxV] at hx
      exact absurd rfl hx
  · rw [if_neg hxK] at hx
    by_cases haV : partitionAnchor ω x ∈ V
    · have h1 := hVR _ haV i
      have h2 := abs_sub_partitionAnchor_lt hP x i
      have h3 := hside _ haV
      rw [partSide_partitionAnchor hP] at h3
      have h3' : (partSide ω x : ℤ) ≤ L := by exact_mod_cast h3
      rw [abs_le] at h1 ⊢
      rw [abs_lt] at h2
      constructor <;> omega
    · rw [if_neg haV] at hx
      exact absurd rfl hx

/-! ### The `ℓ²` norm -/

/-- **(eq:estcoarseminusu)**: `‖coarseTestD‖² ≤ (1 + L^d) ‖v‖²_{ℓ²(V)}`. -/
theorem sum_sq_coarseTestD_le (hP : PartitionEvent ω) (K : Set (Vertex d))
    {V : Finset (Vertex d)} {L : ℕ} (hside : ∀ z ∈ V, partSide ω z ≤ L) (v : Vertex d → ℝ)
    (W : Finset (Vertex d)) :
    ∑ x ∈ W, coarseTestD ω K V v x ^ 2 ≤ (1 + (L : ℝ) ^ d) * ∑ x ∈ V, v x ^ 2 := by
  set g : Vertex d → ℝ := fun z => zeroExtD V v z ^ 2 with hg
  have hg0 : ∀ z, 0 ≤ g z := fun z => sq_nonneg _
  have hgV : ∑ z ∈ V, g z = ∑ z ∈ V, v z ^ 2 :=
    Finset.sum_congr rfl fun z hz => by simp only [hg, zeroExtD, if_pos hz]
  have hsumg : ∀ U : Finset (Vertex d), ∑ z ∈ U, g z ≤ ∑ z ∈ V, v z ^ 2 := by
    intro U
    rw [← hgV]
    calc ∑ z ∈ U, g z = ∑ z ∈ U.filter (· ∈ V), g z := by
          rw [Finset.sum_filter_of_ne]
          intro z _ hz
          by_contra hzV
          exact hz (by simp only [hg, zeroExtD, if_neg hzV]; ring)
      _ ≤ ∑ z ∈ V, g z := Finset.sum_le_sum_of_subset_of_nonneg
          (fun z hz => (Finset.mem_filter.1 hz).2) fun z _ _ => hg0 z
  have hsplit : ∑ x ∈ W, coarseTestD ω K V v x ^ 2 =
      ∑ x ∈ W.filter (· ∈ K), g x + ∑ x ∈ W.filter (· ∉ K), g (partitionAnchor ω x) := by
    rw [← Finset.sum_filter_add_sum_filter_not W (· ∈ K)]
    congr 1
    · exact Finset.sum_congr rfl fun x hx => by
        rw [coarseTestD, if_pos (Finset.mem_filter.1 hx).2]
    · exact Finset.sum_congr rfl fun x hx => by
        rw [coarseTestD, if_neg (Finset.mem_filter.1 hx).2]
  -- the anchors
  set W' := W.filter (· ∉ K)
  have hfib : ∑ x ∈ W', g (partitionAnchor ω x) ≤ (L : ℝ) ^ d * ∑ z ∈ V, v z ^ 2 := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun x => partitionAnchor ω x)
      (t := W'.image fun x => partitionAnchor ω x)
      (fun x hx => Finset.mem_image_of_mem _ hx)]
    have hterm : ∀ z ∈ W'.image fun x => partitionAnchor ω x,
        ∑ x ∈ W'.filter (fun x => partitionAnchor ω x = z), g (partitionAnchor ω x) ≤
          (L : ℝ) ^ d * g z := by
      intro z _
      rw [Finset.sum_congr rfl fun x hx => by rw [(Finset.mem_filter.1 hx).2], Finset.sum_const,
        nsmul_eq_mul]
      by_cases hzV : z ∈ V
      · have hc := card_fiber_partitionAnchor_le hP W' z
        have hs : (partSide ω z : ℝ) ≤ L := by exact_mod_cast hside z hzV
        have hs2 : (partSide ω z : ℝ) ^ d ≤ (L : ℝ) ^ d :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) hs d
        exact mul_le_mul_of_nonneg_right (hc.trans hs2) (hg0 z)
      · have : g z = 0 := by simp only [hg, zeroExtD, if_neg hzV]; ring
        rw [this, mul_zero, mul_zero]
    calc ∑ z ∈ W'.image (fun x => partitionAnchor ω x),
          ∑ x ∈ W'.filter (fun x => partitionAnchor ω x = z), g (partitionAnchor ω x)
        ≤ ∑ z ∈ W'.image (fun x => partitionAnchor ω x), (L : ℝ) ^ d * g z :=
          Finset.sum_le_sum hterm
      _ = (L : ℝ) ^ d * ∑ z ∈ W'.image (fun x => partitionAnchor ω x), g z := by
          rw [Finset.mul_sum]
      _ ≤ (L : ℝ) ^ d * ∑ z ∈ V, v z ^ 2 :=
          mul_le_mul_of_nonneg_left (hsumg _) (by positivity)
  rw [hsplit]
  have h1 := hsumg (W.filter (· ∈ K))
  nlinarith

/-! ### The gradient -/

theorem openGradNormD_nonneg (ω : Configuration d) (V : Finset (Vertex d)) (v : Vertex d → ℝ)
    (x : Vertex d) : 0 ≤ openGradNormD ω V v x :=
  Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity

theorem mem_nbrFinset_of_openAdjD {x z : Vertex d} (h : (openGraph ω).Adj x z) :
    z ∈ nbrFinset x :=
  LatticeProb.Graph.Zd.mem_nbrFinset.mpr (LatticeProb.Graph.Zd.adj_iff.mp (openGraph_le ω h))

/-- `Γ(z) = |∇v|(z)` on `V`, zero off `V`. -/
noncomputable def gradOnD (ω : Configuration d) (V : Finset (Vertex d)) (v : Vertex d → ℝ)
    (z : Vertex d) : ℝ :=
  if z ∈ V then openGradNormD ω V v z else 0

theorem gradOnD_nonneg (V : Finset (Vertex d)) (v : Vertex d → ℝ) (z : Vertex d) :
    0 ≤ gradOnD ω V v z := by
  unfold gradOnD
  split_ifs
  · exact openGradNormD_nonneg ω V v z
  · exact le_rfl

/-- The open edges at `z` inside a box: their variation of `v` extended by zero is at most
`Γ(z)`, since `v` vanishes at the points of `V` with an open neighbour outside `V`. -/
theorem sum_adj_abs_zeroExtD_le {V : Finset (Vertex d)} {v : Vertex d → ℝ}
    (hv : ∀ x ∈ V, x ∉ openInteriorD ω V → v x = 0) (B : Finset (Vertex d)) (z : Vertex d) :
    ∑ z' ∈ B, (if (openGraph ω).Adj z z' then |zeroExtD V v z - zeroExtD V v z'| else 0) ≤
      gradOnD ω V v z := by
  -- vanishing at the points with an open neighbour off `V`
  have hzero : ∀ a b : Vertex d, (openGraph ω).Adj a b → a ∈ V → b ∉ V → v a = 0 :=
    fun a b hab ha hb => hv a ha fun hint => hb (hint.2 b hab)
  by_cases hzV : z ∈ V
  · unfold gradOnD openGradNormD
    rw [if_pos hzV]
    have hle : ∀ z' ∈ B, (if (openGraph ω).Adj z z' then |zeroExtD V v z - zeroExtD V v z'| else 0) =
        if (openGraph ω).Adj z z' ∧ z' ∈ V then |v z' - v z| else 0 := by
      intro z' _
      unfold zeroExtD
      by_cases hadj : (openGraph ω).Adj z z'
      · by_cases hz'V : z' ∈ V
        · rw [if_pos hadj, if_pos (And.intro hadj hz'V), if_pos hzV, if_pos hz'V, abs_sub_comm]
        · rw [if_pos hadj, if_neg (not_and_of_not_right _ hz'V), if_pos hzV, if_neg hz'V,
            hzero z z' hadj hzV hz'V]
          simp
      · rw [if_neg hadj, if_neg (not_and_of_not_left _ hadj)]
    rw [Finset.sum_congr rfl hle]
    calc ∑ z' ∈ B, (if (openGraph ω).Adj z z' ∧ z' ∈ V then |v z' - v z| else 0)
        = ∑ z' ∈ B.filter (· ∈ nbrFinset z),
            (if (openGraph ω).Adj z z' ∧ z' ∈ V then |v z' - v z| else 0) := by
          rw [Finset.sum_filter_of_ne]
          intro z' _ hne
          by_contra hn
          exact hne (if_neg (fun h : (openGraph ω).Adj z z' ∧ z' ∈ V =>
            hn (mem_nbrFinset_of_openAdjD h.1)))
      _ ≤ ∑ z' ∈ nbrFinset z, (if (openGraph ω).Adj z z' ∧ z' ∈ V then |v z' - v z| else 0) :=
          Finset.sum_le_sum_of_subset_of_nonneg (fun z' hz' => (Finset.mem_filter.1 hz').2)
            fun z' _ _ => by split_ifs <;> positivity
  · unfold gradOnD
    rw [if_neg hzV]
    refine le_of_eq (Finset.sum_eq_zero fun z' _ => ?_)
    split_ifs with hadj
    · unfold zeroExtD
      rw [if_neg hzV]
      by_cases hz'V : z' ∈ V
      · rw [if_pos hz'V, hzero z' z hadj.symm hz'V hzV]
        simp
      · rw [if_neg hz'V]
        simp
    · rfl

theorem edgeVariationIn_zeroExtD_le {V : Finset (Vertex d)} {v : Vertex d → ℝ}
    (hv : ∀ x ∈ V, x ∉ openInteriorD ω V → v x = 0) (B : Finset (Vertex d)) :
    edgeVariationIn ω B (zeroExtD V v) ≤ ∑ z ∈ B, gradOnD ω V v z :=
  Finset.sum_le_sum fun z _ => sum_adj_abs_zeroExtD_le hv B z

theorem supBox_subset_of_nearD {x x' : Vertex d} (h : ∀ i, |x' i - x i| ≤ 1) (R : ℕ) :
    supBox x' R ⊆ supBox x (1 + R) := by
  intro z hz
  rw [mem_supBox] at hz ⊢
  intro i
  have h1 := hz i
  have h2 := h i
  rw [abs_le] at h1 h2 ⊢
  push_cast
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem abs_unit_sub_leD (x : Vertex d) (j : Fin d) : ∀ i, |(x + unit j) i - x i| ≤ 1 := by
  intro i
  simp only [Pi.add_apply, add_sub_cancel_left]
  by_cases h : i = j
  · subst h
    simp [unit]
  · simp [unit, h]

theorem cast_anchorBox_radius (x : Vertex d) :
    ((3 ^ ((partitionCube ω x).scale + 1) : ℕ) : ℤ) = 3 * (partSide ω x : ℤ) := by
  simp only [partSide, pow_succ]
  push_cast
  ring

/-- **The gradient of the coarsened test function along an edge.** -/
theorem abs_coarseTestD_sub_le (hd : 0 < d) (hP : PartitionEvent ω) {K : Set (Vertex d)}
    (hK : ∀ x ∈ K, ω ∈ infiniteComponentEvent x)
    {V : Finset (Vertex d)} {v : Vertex d → ℝ} (hv : ∀ x ∈ V, x ∉ openInteriorD ω V → v x = 0)
    {L : ℕ} (x : Vertex d) (j : Fin d) (hx : partSide ω x ≤ L)
    (hx' : partSide ω (x + unit j) ≤ L) :
    |coarseTestD ω K V v (x + unit j) - coarseTestD ω K V v x| ≤
      3 * ∑ z ∈ supBox x (1 + 3 * L), gradOnD ω V v z := by
  set x' := x + unit j
  set w := zeroExtD V v
  set B := supBox x (1 + 3 * L)
  have hnear : ∀ i, |x' i - x i| ≤ 1 := abs_unit_sub_leD x j
  have hE := edgeVariationIn_zeroExtD_le hv B
  have hE0 : 0 ≤ edgeVariationIn ω B w := edgeVariationIn_nonneg ω B w
  have hbox : ∀ u : Vertex d, (∀ i, |u i - x i| ≤ 1) → partSide ω u ≤ L →
      ∀ z : Vertex d, (∀ i, |z i - u i| ≤ 3 * (partSide ω u : ℤ)) → z ∈ B := by
    intro u hu hsu z hz
    rw [mem_supBox]
    intro i
    have h1 := hu i
    have h2 := hz i
    have h3 : (partSide ω u : ℤ) ≤ L := by exact_mod_cast hsu
    rw [abs_le] at h1 h2 ⊢
    push_cast
    constructor <;> omega
  have herr : ∀ u : Vertex d, (∀ i, |u i - x i| ≤ 1) → partSide ω u ≤ L →
      |coarseTestD ω K V v u - w (partitionAnchor ω u)| ≤ edgeVariationIn ω B w := by
    intro u hu hsu
    unfold coarseTestD
    by_cases huK : u ∈ K
    · rw [if_pos huK]
      have hr := Rigidity.Corrector.GeneralDim.reachable_anchorBox hd hP (hK u huK)
      have hsub : Rigidity.Corrector.GeneralDim.anchorBox ω u ⊆ B := by
        intro z hz
        rw [Rigidity.Corrector.GeneralDim.mem_anchorBox, cast_anchorBox_radius] at hz
        exact hbox u hu hsu z hz
      have hr' := Rigidity.Percolation.openIn_reachable_mono_region
        (Finset.coe_subset.2 hsub) hr
      exact Rigidity.Corrector.GeneralDim.abs_sub_le_edgeVariationIn_of_reachable B w hr'
    · rw [if_neg huK, sub_self, abs_zero]
      exact hE0
  have hmid : |w (partitionAnchor ω x') - w (partitionAnchor ω x)| ≤
      edgeVariationIn ω B w := by
    have hadj := Rigidity.Percolation.nearestNeighborGraph_adj_add_unit x j
    set P : (nearestNeighborGraph d).Walk x x' := SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil
    have hr := reachable_partitionAnchor_of_walk hd hP P
    have hsub : (⋃ z ∈ P.support, (partitionCube ω z).vertices) ⊆ (B : Set (Vertex d)) := by
      intro y hy
      simp only [Set.mem_iUnion] at hy
      obtain ⟨z, hz, hyz⟩ := hy
      have hz' : z = x ∨ z = x' := by
        simpa [P, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil] using hz
      have hnz : ∀ i, |z i - x i| ≤ 1 := by
        rcases hz' with rfl | rfl
        · intro i
          simp
        · exact hnear
      have hsz : partSide ω z ≤ L := by
        rcases hz' with rfl | rfl
        · exact hx
        · exact hx'
      refine hbox z hnz hsz y fun i => ?_
      have h1 := abs_sub_lt_side_of_memD hyz (mem_partitionCube hP z) i
      have h2 : (3 : ℤ) ^ (partitionCube ω z).scale = (partSide ω z : ℤ) := by
        simp [partSide]
      rw [h2] at h1
      have h3 : (0 : ℤ) ≤ partSide ω z := by positivity
      linarith
    have hr' := Rigidity.Percolation.openIn_reachable_mono_region hsub hr
    rw [abs_sub_comm]
    exact Rigidity.Corrector.GeneralDim.abs_sub_le_edgeVariationIn_of_reachable B w hr'
  have h1 := herr x' hnear hx'
  have h2 := herr x (fun i => by simp) hx
  calc |coarseTestD ω K V v x' - coarseTestD ω K V v x|
      ≤ |coarseTestD ω K V v x' - w (partitionAnchor ω x')| +
          |w (partitionAnchor ω x') - w (partitionAnchor ω x)| +
          |w (partitionAnchor ω x) - coarseTestD ω K V v x| := by
        have := abs_sub_le (coarseTestD ω K V v x') (w (partitionAnchor ω x'))
          (coarseTestD ω K V v x)
        have h3 := abs_sub_le (w (partitionAnchor ω x')) (w (partitionAnchor ω x))
          (coarseTestD ω K V v x)
        linarith
    _ ≤ 3 * edgeVariationIn ω B w := by
        rw [abs_sub_comm (w (partitionAnchor ω x))]
        linarith
    _ ≤ 3 * ∑ z ∈ B, gradOnD ω V v z := by linarith

theorem sum_sum_supBox_leD {F : Vertex d → ℝ} (hF : ∀ z, 0 ≤ F z) {V : Finset (Vertex d)}
    (hFV : ∀ z ∉ V, F z = 0) (T : Finset (Vertex d)) (R : ℕ) :
    ∑ x ∈ T, ∑ z ∈ supBox x R, F z ≤ (2 * R + 1) ^ d * ∑ z ∈ V, F z := by
  have h1 : ∀ x ∈ T, ∑ z ∈ supBox x R, F z = ∑ z ∈ V, if z ∈ supBox x R then F z else 0 := by
    intro x _
    rw [← Finset.sum_filter]
    symm
    refine Finset.sum_subset (fun z hz => (Finset.mem_filter.1 hz).2) fun z hz hzn => ?_
    by_contra hne
    exact hzn (Finset.mem_filter.2 ⟨by_contra fun h => hne (hFV z h), hz⟩)
  rw [Finset.sum_congr rfl h1, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun z _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ (hF z)
  have hsub : T.filter (fun x => z ∈ supBox x R) ⊆ supBox z R := by
    intro x hx
    rw [Finset.mem_filter, mem_supBox] at hx
    rw [mem_supBox]
    intro i
    rw [abs_sub_comm]
    exact hx.2 i
  have := Finset.card_le_card hsub
  rw [card_supBox] at this
  exact_mod_cast this

/-- **(est.nablacoarsenL2)** on `ℤ^d`:
`‖∇ coarseTestD‖² ≤ 9 d (3 + 6L)^{2d} Σ_V |∇v|²`. -/
theorem sum_sq_grad_coarseTestD_le (hd : 0 < d) (hP : PartitionEvent ω) {K : Set (Vertex d)}
    (hK : ∀ x ∈ K, ω ∈ infiniteComponentEvent x)
    {V : Finset (Vertex d)} {v : Vertex d → ℝ} (hv : ∀ x ∈ V, x ∉ openInteriorD ω V → v x = 0)
    {L : ℕ} (T : Finset (Vertex d))
    (hside : ∀ x ∈ T, partSide ω x ≤ L ∧ ∀ j : Fin d, partSide ω (x + unit j) ≤ L) :
    ∑ j : Fin d, ∑ x ∈ T, (coarseTestD ω K V v (x + unit j) - coarseTestD ω K V v x) ^ 2 ≤
      9 * d * (3 + 6 * (L : ℝ)) ^ (2 * d) * ∑ z ∈ V, openGradNormD ω V v z ^ 2 := by
  set R := 1 + 3 * L
  have hR : (2 * (R : ℝ) + 1) = 3 + 6 * L := by simp only [R]; push_cast; ring
  have hpt : ∀ x ∈ T, ∀ j : Fin d,
      (coarseTestD ω K V v (x + unit j) - coarseTestD ω K V v x) ^ 2 ≤
        9 * ((2 * R + 1) ^ d * ∑ z ∈ supBox x R, gradOnD ω V v z ^ 2) := by
    intro x hx j
    have h := abs_coarseTestD_sub_le hd hP hK hv x j (hside x hx).1 ((hside x hx).2 j)
    have hcs := sq_sum_le_card_mul_sum_sq (s := supBox x R) (f := gradOnD ω V v)
    rw [card_supBox] at hcs
    push_cast at hcs
    calc (coarseTestD ω K V v (x + unit j) - coarseTestD ω K V v x) ^ 2
        = |coarseTestD ω K V v (x + unit j) - coarseTestD ω K V v x| ^ 2 := (sq_abs _).symm
      _ ≤ (3 * ∑ z ∈ supBox x R, gradOnD ω V v z) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) h 2
      _ = 9 * (∑ z ∈ supBox x R, gradOnD ω V v z) ^ 2 := by ring
      _ ≤ 9 * ((2 * R + 1) ^ d * ∑ z ∈ supBox x R, gradOnD ω V v z ^ 2) := by
          exact mul_le_mul_of_nonneg_left hcs (by norm_num)
  have hswap := sum_sum_supBox_leD (F := fun z => gradOnD ω V v z ^ 2) (fun z => sq_nonneg _)
    (V := V) (fun z hz => by simp only [gradOnD, if_neg hz]; ring) T R
  have hV : ∑ z ∈ V, gradOnD ω V v z ^ 2 = ∑ z ∈ V, openGradNormD ω V v z ^ 2 :=
    Finset.sum_congr rfl fun z hz => by simp only [gradOnD, if_pos hz]
  calc ∑ j : Fin d, ∑ x ∈ T, (coarseTestD ω K V v (x + unit j) - coarseTestD ω K V v x) ^ 2
      ≤ ∑ _j : Fin d, ∑ x ∈ T, 9 * ((2 * R + 1) ^ d * ∑ z ∈ supBox x R, gradOnD ω V v z ^ 2) :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun x hx => hpt x hx j
    _ = 9 * d * (2 * R + 1) ^ d * ∑ x ∈ T, ∑ z ∈ supBox x R, gradOnD ω V v z ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum,
          ← Finset.mul_sum]
        ring
    _ ≤ 9 * d * (2 * R + 1) ^ d * ((2 * R + 1) ^ d * ∑ z ∈ V, gradOnD ω V v z ^ 2) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hswap) (by positivity)
    _ = 9 * d * (3 + 6 * (L : ℝ)) ^ (2 * d) * ∑ z ∈ V, openGradNormD ω V v z ^ 2 := by
        rw [hV, hR]
        ring

/-! ### The size of the cluster in a ball -/

theorem dist_le_mul_of_abs_le {x y : Vertex d} {a : ℝ} (h : ∀ i, |((x i - y i : ℤ) : ℝ)| ≤ a) :
    dist (latticeEuclideanEmbedding x) (latticeEuclideanEmbedding y) ≤ d * a := by
  rw [dist_eq_norm, ← LatticeProb.Percolation.latticeEuclideanEmbedding_sub]
  refine (norm_euclid_le_sum_abs (x - y)).trans ?_
  calc ∑ i, |(((x - y) i : ℤ) : ℝ)| ≤ ∑ _i : Fin d, a :=
        Finset.sum_le_sum fun i _ => by simpa using h i
    _ = d * a := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **The size of `𝒞_∞ ∩ B_r(y)`**: the anchors of the partition cubes of the points of
`y + [-m, m]^d` lie in `𝒞_∞ ∩ B_r(y)` when `d (m + L) < r`. -/
theorem card_mul_le_card_dgClusterBallD (hd : 0 < d) (hP : PartitionEvent ω)
    (h : HasUniqueInfiniteOpenComponent ω) (y : Vertex d) {r : ℝ} {m L : ℕ}
    (hmr : d * ((m : ℝ) + L) < r) (hside : ∀ z ∈ supBox y m, partSide ω z ≤ L) :
    ((2 * m + 1 : ℕ) : ℝ) ^ d ≤
      (L : ℝ) ^ d * (dgClusterBallD (uniqueInfiniteComponent h) y r).card := by
  set V := dgClusterBallD (uniqueInfiniteComponent h) y r
  set a : Vertex d → Vertex d := fun x => partitionAnchor ω x
  have himage : (supBox y m).image a ⊆ V := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hz
    rw [mem_dgClusterBallD]
    refine ⟨(mem_uniqueInfiniteComponent_iff h _).2
      (Rigidity.Corrector.GeneralDim.infinite_partitionAnchor hd hP x), ?_⟩
    have hxy := mem_supBox.1 hx
    have hs := hside x hx
    refine lt_of_le_of_lt (dist_le_mul_of_abs_le (a := (m : ℝ) + L) fun i => ?_) hmr
    have h1 := hxy i
    have h2 := abs_sub_partitionAnchor_lt hP x i
    have h3 : (partSide ω x : ℤ) ≤ L := by exact_mod_cast hs
    rw [abs_le] at h1
    rw [abs_lt] at h2
    have : |partitionAnchor ω x i - y i| ≤ (m : ℤ) + L := by
      rw [abs_le]
      constructor <;> omega
    exact_mod_cast this
  have hfib : ∀ z ∈ (supBox y m).image a,
      ((supBox y m).filter fun x => a x = z).card ≤ L ^ d := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hz
    have hc := card_fiber_partitionAnchor_le hP (supBox y m) (a x)
    have hs := hside x hx
    rw [show a x = partitionAnchor ω x from rfl, partSide_partitionAnchor hP] at hc
    have : ((partSide ω x : ℝ)) ^ d ≤ (L : ℝ) ^ d :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hs) d
    exact_mod_cast hc.trans this
  have hc := Finset.card_le_mul_card_image (supBox y m) (L ^ d) hfib
  have hc2 := Finset.card_le_card himage
  rw [card_supBox] at hc
  have : ((2 * m + 1) ^ d : ℕ) ≤ L ^ d * V.card :=
    hc.trans (Nat.mul_le_mul_left _ hc2)
  exact_mod_cast this

end Rigidity.Green.GeneralFlux
