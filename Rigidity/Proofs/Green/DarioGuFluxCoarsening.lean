import Rigidity.Proofs.Green.DarioGuDensityWeakNorm
import Rigidity.Proofs.Green.DarioGuFluxTranslate
import Rigidity.Proofs.Corrector.DarioStepOneLocal
import PercolationClusterHomogenization.Proofs.Regularity.PlanarCoarseCells

/-!
# The coarsened test function of Dario–Gu, Appendix B, Step 1

For a test function `v` of the `H̲^{-1}` norm on `V = 𝒞_∞ ∩ B_r(y)` (vanishing on `V ∖ int_a(V)`),
Dario–Gu extend `v` from the infinite cluster `𝒞_∞` to `ℤ²` by the coarsening (def.coarsenu): `v`
on the cluster, and `v` at a point of the cluster of the partition cube off it. Here the point is
the anchor `planarCoarseAnchor` of the planar partition of the good cubes, and `v` is first
extended by zero off `V` (`zeroExt`); the coarsened function is `coarseTest`. With `L` a bound of
the sides of the partition cubes near `B_r(y)`:

* `sum_mul_coarseTest_eq`: the pairing of a function vanishing off `𝒞_∞` with `v` on `V` is its
  pairing with `coarseTest` on `ℤ²`;
* `coarseTest_eq_zero_of_far`: `coarseTest` vanishes at distance more than `R + L` of `y`;
* `sum_sq_coarseTest_le`: `‖coarseTest‖²_{ℓ²} ≤ (1 + L²) ‖v‖²_{ℓ²(V)}` ((2.8));
* `sum_sq_grad_coarseTest_le`: `‖∇ coarseTest‖²_{ℓ²} ≤ 18 (3 + 10L)⁴ Σ_V |∇v|²`
  ((est.nablacoarsenL2), with the anchors joined inside the boxes of `DarioStepOneLocal`);
* `card_mul_le_card_dgClusterBall`: `(2m + 1)² ≤ L² |V|` when `2(m + L) < r` (the anchors of the
  cubes meeting `y + [-m, m]²` lie in `V`).
-/

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.Poincare Rigidity.Corrector
  Rigidity.Percolation Rigidity.External Rigidity.Proofs.S2
open scoped ENNReal Classical

namespace Rigidity.Green

variable {ω : Configuration 2}

/-- `v` on `V`, zero off `V`. -/
noncomputable def zeroExt (V : Finset (Vertex 2)) (v : Vertex 2 → ℝ) (x : Vertex 2) : ℝ :=
  if x ∈ V then v x else 0

/-- **The coarsened test function**: `v` on the cluster `K`, and `v` at the anchor of the
partition cube off it, `v` extended by zero off `V`. -/
noncomputable def coarseTest (ω : Configuration 2) (K : Set (Vertex 2)) (V : Finset (Vertex 2))
    (v : Vertex 2 → ℝ) (x : Vertex 2) : ℝ :=
  if x ∈ K then zeroExt V v x else zeroExt V v (planarCoarseAnchor ω x)

/-! ### Triadic cubes and partition cubes -/

theorem mem_vertices_iff_mem_triadicCubeFinset (Q : TriadicCube 2) (x : Vertex 2) :
    x ∈ Q.vertices ↔ x ∈ triadicCubeFinset 2 Q.scale Q.index := by
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

theorem abs_sub_lt_side_of_mem {Q : TriadicCube 2} {x z : Vertex 2} (hx : x ∈ Q.vertices)
    (hz : z ∈ Q.vertices) (i : Fin 2) : |x i - z i| < (3 : ℤ) ^ Q.scale := by
  have h1 := hx i
  have h2 := hz i
  simp only [TriadicCube.side] at h1 h2
  rw [abs_lt] at h1 h2 ⊢
  constructor <;> omega

theorem card_fiber_planarCoarseAnchor_le (hP : PlanarPartitionEvent ω) (W : Finset (Vertex 2))
    (z : Vertex 2) :
    ((W.filter fun x => planarCoarseAnchor ω x = z).card : ℝ) ≤ (planarSide ω z : ℝ) ^ 2 := by
  have hsub : W.filter (fun x => planarCoarseAnchor ω x = z) ⊆
      triadicCubeFinset 2 (planarPartCube ω z).scale (planarPartCube ω z).index := by
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [← mem_vertices_iff_mem_triadicCubeFinset]
    have hQ : planarPartCube ω x = planarPartCube ω z := by
      rw [← hx.2, Rigidity.Proofs.Regularity.planarPartCube_planarCoarseAnchor hP]
    rw [← hQ]
    exact (planarPartCube_spec hP x).1
  have hc := Finset.card_le_card hsub
  have hcard : ((triadicCubeFinset 2 (planarPartCube ω z).scale
      (planarPartCube ω z).index).card : ℝ) = (planarSide ω z : ℝ) ^ 2 := by
    rw [card_triadicCubeFinset_two, planarSide_eq hP z]
    push_cast
    rw [← pow_mul, mul_comm (planarPartCube ω z).scale 2, pow_mul]
    norm_num
  calc ((W.filter fun x => planarCoarseAnchor ω x = z).card : ℝ)
      ≤ ((triadicCubeFinset 2 (planarPartCube ω z).scale
          (planarPartCube ω z).index).card : ℝ) := by exact_mod_cast hc
    _ = _ := hcard

theorem abs_sub_planarCoarseAnchor_lt (hP : PlanarPartitionEvent ω) (x : Vertex 2) (i : Fin 2) :
    |x i - planarCoarseAnchor ω x i| < (planarSide ω x : ℤ) := by
  rw [planarSide_eq hP x]
  push_cast
  exact abs_sub_lt_side_of_mem (planarPartCube_spec hP x).1 (planarCoarseAnchor_mem hP x) i

theorem planarSide_planarCoarseAnchor (hP : PlanarPartitionEvent ω) (x : Vertex 2) :
    planarSide ω (planarCoarseAnchor ω x) = planarSide ω x := by
  rw [planarSide_eq hP, planarSide_eq hP, Rigidity.Proofs.Regularity.planarPartCube_planarCoarseAnchor hP]

/-! ### The pairing and the support -/

/-- **The pairing with the coarsened test function.** -/
theorem sum_mul_coarseTest_eq {K : Set (Vertex 2)} {V W : Finset (Vertex 2)}
    (hVK : ∀ x ∈ V, x ∈ K) (hVW : V ⊆ W) (v F : Vertex 2 → ℝ) (hF : ∀ x, x ∉ K → F x = 0) :
    ∑ x ∈ W, F x * coarseTest ω K V v x = ∑ x ∈ V, F x * v x := by
  have h1 : ∀ x ∈ W, F x * coarseTest ω K V v x = if x ∈ V then F x * v x else 0 := by
    intro x _
    unfold coarseTest zeroExt
    by_cases hxK : x ∈ K
    · rw [if_pos hxK]
      split_ifs <;> ring
    · rw [hF x hxK, zero_mul, if_neg fun hV => hxK (hVK x hV)]
  rw [Finset.sum_congr rfl h1, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
    Finset.inter_eq_right.2 hVW]

theorem coarseTest_eq_zero_of_far (hP : PlanarPartitionEvent ω) {K : Set (Vertex 2)}
    {V : Finset (Vertex 2)} {y : Vertex 2} {R L : ℕ} (hVR : ∀ z ∈ V, ∀ i, |z i - y i| ≤ R)
    (hside : ∀ z ∈ V, planarSide ω z ≤ L) (v : Vertex 2 → ℝ) {x : Vertex 2}
    (hx : coarseTest ω K V v x ≠ 0) : ∀ i, |x i - y i| ≤ R + L := by
  intro i
  unfold coarseTest zeroExt at hx
  by_cases hxK : x ∈ K
  · rw [if_pos hxK] at hx
    by_cases hxV : x ∈ V
    · have := hVR x hxV i
      omega
    · rw [if_neg hxV] at hx
      exact absurd rfl hx
  · rw [if_neg hxK] at hx
    by_cases haV : planarCoarseAnchor ω x ∈ V
    · have h1 := hVR _ haV i
      have h2 := abs_sub_planarCoarseAnchor_lt hP x i
      have h3 := hside _ haV
      rw [planarSide_planarCoarseAnchor hP] at h3
      have h3' : (planarSide ω x : ℤ) ≤ L := by exact_mod_cast h3
      rw [abs_le] at h1 ⊢
      rw [abs_lt] at h2
      constructor <;> omega
    · rw [if_neg haV] at hx
      exact absurd rfl hx

/-! ### The `ℓ²` norm -/

/-- **(2.8)**: `‖coarseTest‖² ≤ (1 + L²) ‖v‖²_{ℓ²(V)}`. -/
theorem sum_sq_coarseTest_le (hP : PlanarPartitionEvent ω) (K : Set (Vertex 2))
    {V : Finset (Vertex 2)} {L : ℕ} (hside : ∀ z ∈ V, planarSide ω z ≤ L) (v : Vertex 2 → ℝ)
    (W : Finset (Vertex 2)) :
    ∑ x ∈ W, coarseTest ω K V v x ^ 2 ≤ (1 + (L : ℝ) ^ 2) * ∑ x ∈ V, v x ^ 2 := by
  set g : Vertex 2 → ℝ := fun z => zeroExt V v z ^ 2 with hg
  have hg0 : ∀ z, 0 ≤ g z := fun z => sq_nonneg _
  have hgV : ∑ z ∈ V, g z = ∑ z ∈ V, v z ^ 2 :=
    Finset.sum_congr rfl fun z hz => by simp only [hg, zeroExt, if_pos hz]
  have hsumg : ∀ U : Finset (Vertex 2), ∑ z ∈ U, g z ≤ ∑ z ∈ V, v z ^ 2 := by
    intro U
    rw [← hgV]
    calc ∑ z ∈ U, g z = ∑ z ∈ U.filter (· ∈ V), g z := by
          rw [Finset.sum_filter_of_ne]
          intro z _ hz
          by_contra hzV
          exact hz (by simp only [hg, zeroExt, if_neg hzV]; ring)
      _ ≤ ∑ z ∈ V, g z := Finset.sum_le_sum_of_subset_of_nonneg
          (fun z hz => (Finset.mem_filter.1 hz).2) fun z _ _ => hg0 z
  have hsplit : ∑ x ∈ W, coarseTest ω K V v x ^ 2 =
      ∑ x ∈ W.filter (· ∈ K), g x + ∑ x ∈ W.filter (· ∉ K), g (planarCoarseAnchor ω x) := by
    rw [← Finset.sum_filter_add_sum_filter_not W (· ∈ K)]
    congr 1
    · exact Finset.sum_congr rfl fun x hx => by
        rw [coarseTest, if_pos (Finset.mem_filter.1 hx).2]
    · exact Finset.sum_congr rfl fun x hx => by
        rw [coarseTest, if_neg (Finset.mem_filter.1 hx).2]
  -- the anchors
  set W' := W.filter (· ∉ K)
  have hfib : ∑ x ∈ W', g (planarCoarseAnchor ω x) ≤ (L : ℝ) ^ 2 * ∑ z ∈ V, v z ^ 2 := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun x => planarCoarseAnchor ω x)
      (t := W'.image fun x => planarCoarseAnchor ω x)
      (fun x hx => Finset.mem_image_of_mem _ hx)]
    have hterm : ∀ z ∈ W'.image fun x => planarCoarseAnchor ω x,
        ∑ x ∈ W'.filter (fun x => planarCoarseAnchor ω x = z), g (planarCoarseAnchor ω x) ≤
          (L : ℝ) ^ 2 * g z := by
      intro z _
      rw [Finset.sum_congr rfl fun x hx => by rw [(Finset.mem_filter.1 hx).2], Finset.sum_const,
        nsmul_eq_mul]
      by_cases hzV : z ∈ V
      · have hc := card_fiber_planarCoarseAnchor_le hP W' z
        have hs : (planarSide ω z : ℝ) ≤ L := by exact_mod_cast hside z hzV
        have hs2 : (planarSide ω z : ℝ) ^ 2 ≤ (L : ℝ) ^ 2 :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) hs 2
        exact mul_le_mul_of_nonneg_right (hc.trans hs2) (hg0 z)
      · have : g z = 0 := by simp only [hg, zeroExt, if_neg hzV]; ring
        rw [this, mul_zero, mul_zero]
    calc ∑ z ∈ W'.image (fun x => planarCoarseAnchor ω x),
          ∑ x ∈ W'.filter (fun x => planarCoarseAnchor ω x = z), g (planarCoarseAnchor ω x)
        ≤ ∑ z ∈ W'.image (fun x => planarCoarseAnchor ω x), (L : ℝ) ^ 2 * g z :=
          Finset.sum_le_sum hterm
      _ = (L : ℝ) ^ 2 * ∑ z ∈ W'.image (fun x => planarCoarseAnchor ω x), g z := by
          rw [Finset.mul_sum]
      _ ≤ (L : ℝ) ^ 2 * ∑ z ∈ V, v z ^ 2 :=
          mul_le_mul_of_nonneg_left (hsumg _) (by positivity)
  rw [hsplit]
  have h1 := hsumg (W.filter (· ∈ K))
  nlinarith

/-! ### The gradient -/

theorem mem_nbrFinset_of_openAdj {x z : Vertex 2} (h : (openGraph ω).Adj x z) :
    z ∈ nbrFinset x :=
  LatticeProb.Graph.Zd.mem_nbrFinset.mpr (LatticeProb.Graph.Zd.adj_iff.mp (openGraph_le ω h))

/-- `Γ(z) = |∇v|(z)` on `V`, zero off `V`. -/
noncomputable def gradOn (ω : Configuration 2) (V : Finset (Vertex 2)) (v : Vertex 2 → ℝ)
    (z : Vertex 2) : ℝ :=
  if z ∈ V then openGradNorm ω V v z else 0

theorem gradOn_nonneg (V : Finset (Vertex 2)) (v : Vertex 2 → ℝ) (z : Vertex 2) :
    0 ≤ gradOn ω V v z := by
  unfold gradOn
  split_ifs
  · exact openGradNorm_nonneg ω V v z
  · exact le_rfl

/-- The open edges at `z` inside a box: their variation of `v` extended by zero is at most
`Γ(z)`, since `v` vanishes at the points of `V` with an open neighbour outside `V`. -/
theorem sum_adj_abs_zeroExt_le {V : Finset (Vertex 2)} {v : Vertex 2 → ℝ}
    (hv : ∀ x ∈ V, x ∉ openInterior ω V → v x = 0) (B : Finset (Vertex 2)) (z : Vertex 2) :
    ∑ z' ∈ B, (if (openGraph ω).Adj z z' then |zeroExt V v z - zeroExt V v z'| else 0) ≤
      gradOn ω V v z := by
  -- vanishing at the points with an open neighbour off `V`
  have hzero : ∀ a b : Vertex 2, (openGraph ω).Adj a b → a ∈ V → b ∉ V → v a = 0 :=
    fun a b hab ha hb => hv a ha fun hint => hb (hint.2 b hab)
  by_cases hzV : z ∈ V
  · unfold gradOn openGradNorm
    rw [if_pos hzV]
    have hle : ∀ z' ∈ B, (if (openGraph ω).Adj z z' then |zeroExt V v z - zeroExt V v z'| else 0) =
        if (openGraph ω).Adj z z' ∧ z' ∈ V then |v z' - v z| else 0 := by
      intro z' _
      unfold zeroExt
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
            hn (mem_nbrFinset_of_openAdj h.1)))
      _ ≤ ∑ z' ∈ nbrFinset z, (if (openGraph ω).Adj z z' ∧ z' ∈ V then |v z' - v z| else 0) :=
          Finset.sum_le_sum_of_subset_of_nonneg (fun z' hz' => (Finset.mem_filter.1 hz').2)
            fun z' _ _ => by split_ifs <;> positivity
  · unfold gradOn
    rw [if_neg hzV]
    refine le_of_eq (Finset.sum_eq_zero fun z' _ => ?_)
    split_ifs with hadj
    · unfold zeroExt
      rw [if_neg hzV]
      by_cases hz'V : z' ∈ V
      · rw [if_pos hz'V, hzero z' z hadj.symm hz'V hzV]
        simp
      · rw [if_neg hz'V]
        simp
    · rfl

theorem edgeVariationIn_zeroExt_le {V : Finset (Vertex 2)} {v : Vertex 2 → ℝ}
    (hv : ∀ x ∈ V, x ∉ openInterior ω V → v x = 0) (B : Finset (Vertex 2)) :
    edgeVariationIn ω B (zeroExt V v) ≤ ∑ z ∈ B, gradOn ω V v z :=
  Finset.sum_le_sum fun z _ => sum_adj_abs_zeroExt_le hv B z

theorem supBox_subset_of_near {x x' : Vertex 2} (h : ∀ i, |x' i - x i| ≤ 1) (R : ℕ) :
    supBox x' R ⊆ supBox x (1 + R) := by
  intro z hz
  rw [mem_supBox] at hz ⊢
  intro i
  have h1 := hz i
  have h2 := h i
  rw [abs_le] at h1 h2 ⊢
  push_cast
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem abs_unit_sub_le (x : Vertex 2) (j : Fin 2) : ∀ i, |(x + unit j) i - x i| ≤ 1 := by
  intro i
  simp only [Pi.add_apply, add_sub_cancel_left]
  by_cases h : i = j
  · subst h
    simp [unit]
  · simp [unit, h]

/-- **The gradient of the coarsened test function along an edge.** -/
theorem abs_coarseTest_sub_le (hP : PlanarPartitionEvent ω) {K : Set (Vertex 2)}
    (hK : ∀ x ∈ K, ((openGraph ω).connectedComponentMk x).supp.Infinite)
    {V : Finset (Vertex 2)} {v : Vertex 2 → ℝ} (hv : ∀ x ∈ V, x ∉ openInterior ω V → v x = 0)
    {L : ℕ} (x : Vertex 2) (j : Fin 2) (hx : planarSide ω x ≤ L)
    (hx' : planarSide ω (x + unit j) ≤ L) :
    |coarseTest ω K V v (x + unit j) - coarseTest ω K V v x| ≤
      3 * ∑ z ∈ supBox x (1 + 5 * L), gradOn ω V v z := by
  set x' := x + unit j
  set w := zeroExt V v
  set B := supBox x (1 + 5 * L)
  have hnear : ∀ i, |x' i - x i| ≤ 1 := abs_unit_sub_le x j
  have hE := edgeVariationIn_zeroExt_le hv B
  have hE0 : 0 ≤ edgeVariationIn ω B w := edgeVariationIn_nonneg ω B w
  have hsx : 3 ^ (planarPartCube ω x).scale ≤ L := by rw [← planarSide_eq hP]; exact hx
  have hsx' : 3 ^ (planarPartCube ω x').scale ≤ L := by rw [← planarSide_eq hP]; exact hx'
  -- the coarsening errors at the two ends
  have herr : ∀ u : Vertex 2, (∀ i, |u i - x i| ≤ 1) → planarSide ω u ≤ L →
      |coarseTest ω K V v u - w (planarCoarseAnchor ω u)| ≤ edgeVariationIn ω B w := by
    intro u hu hsu
    unfold coarseTest
    by_cases huK : u ∈ K
    · rw [if_pos huK]
      have h1 := abs_sub_coarseAnchor_le hP (hK u huK) w
      have hsu' : 3 ^ (planarPartCube ω u).scale ≤ L := by rw [← planarSide_eq hP]; exact hsu
      have hsub : (planarPartCube ω u).ninefold.vertices ⊆ B := by
        have := ninefold_subset_supBox (x := u) (L := 0) (planarPartCube_spec hP u).1
          (fun i => by simp) hsu'
        refine this.trans ?_
        have h2 := supBox_subset_of_near hu (0 + 5 * L)
        simpa only [zero_add] using h2
      exact h1.trans (edgeVariationIn_mono hsub w)
    · rw [if_neg huK, sub_self, abs_zero]
      exact hE0
  have hmid : |w (planarCoarseAnchor ω x') - w (planarCoarseAnchor ω x)| ≤
      edgeVariationIn ω B w := by
    have h := abs_coarseAnchor_sub_le_supBox hP (x := x) (y := x') (y' := x) hnear (L := 1)
      (M := L) (Or.inl hsx') hnear (fun i => by simp) w
    exact h
  have h1 := herr x' hnear hx'
  have h2 := herr x (fun i => by simp) hx
  calc |coarseTest ω K V v x' - coarseTest ω K V v x|
      ≤ |coarseTest ω K V v x' - w (planarCoarseAnchor ω x')| +
          |w (planarCoarseAnchor ω x') - w (planarCoarseAnchor ω x)| +
          |w (planarCoarseAnchor ω x) - coarseTest ω K V v x| := by
        have := abs_sub_le (coarseTest ω K V v x') (w (planarCoarseAnchor ω x'))
          (coarseTest ω K V v x)
        have h3 := abs_sub_le (w (planarCoarseAnchor ω x')) (w (planarCoarseAnchor ω x))
          (coarseTest ω K V v x)
        linarith
    _ ≤ 3 * edgeVariationIn ω B w := by
        rw [abs_sub_comm (w (planarCoarseAnchor ω x))]
        linarith
    _ ≤ 3 * ∑ z ∈ B, gradOn ω V v z := by linarith

theorem sum_sum_supBox_le {F : Vertex 2 → ℝ} (hF : ∀ z, 0 ≤ F z) {V : Finset (Vertex 2)}
    (hFV : ∀ z ∉ V, F z = 0) (T : Finset (Vertex 2)) (R : ℕ) :
    ∑ x ∈ T, ∑ z ∈ supBox x R, F z ≤ (2 * R + 1) ^ 2 * ∑ z ∈ V, F z := by
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

/-- **(est.nablacoarsenL2)**: `‖∇ coarseTest‖² ≤ 18 (3 + 10L)⁴ Σ_V |∇v|²`. -/
theorem sum_sq_grad_coarseTest_le (hP : PlanarPartitionEvent ω) {K : Set (Vertex 2)}
    (hK : ∀ x ∈ K, ((openGraph ω).connectedComponentMk x).supp.Infinite)
    {V : Finset (Vertex 2)} {v : Vertex 2 → ℝ} (hv : ∀ x ∈ V, x ∉ openInterior ω V → v x = 0)
    {L : ℕ} (T : Finset (Vertex 2))
    (hside : ∀ x ∈ T, planarSide ω x ≤ L ∧ ∀ j : Fin 2, planarSide ω (x + unit j) ≤ L) :
    ∑ j : Fin 2, ∑ x ∈ T, (coarseTest ω K V v (x + unit j) - coarseTest ω K V v x) ^ 2 ≤
      18 * (3 + 10 * (L : ℝ)) ^ 4 * ∑ z ∈ V, openGradNorm ω V v z ^ 2 := by
  set R := 1 + 5 * L
  have hR : (2 * (R : ℝ) + 1) = 3 + 10 * L := by simp only [R]; push_cast; ring
  have hpt : ∀ x ∈ T, ∀ j : Fin 2,
      (coarseTest ω K V v (x + unit j) - coarseTest ω K V v x) ^ 2 ≤
        9 * ((2 * R + 1) ^ 2 * ∑ z ∈ supBox x R, gradOn ω V v z ^ 2) := by
    intro x hx j
    have h := abs_coarseTest_sub_le hP hK hv x j (hside x hx).1 ((hside x hx).2 j)
    have hs0 : 0 ≤ ∑ z ∈ supBox x R, gradOn ω V v z :=
      Finset.sum_nonneg fun z _ => gradOn_nonneg V v z
    have hcs := sq_sum_le_card_mul_sum_sq (s := supBox x R) (f := gradOn ω V v)
    rw [card_supBox] at hcs
    push_cast at hcs
    calc (coarseTest ω K V v (x + unit j) - coarseTest ω K V v x) ^ 2
        = |coarseTest ω K V v (x + unit j) - coarseTest ω K V v x| ^ 2 := (sq_abs _).symm
      _ ≤ (3 * ∑ z ∈ supBox x R, gradOn ω V v z) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) h 2
      _ = 9 * (∑ z ∈ supBox x R, gradOn ω V v z) ^ 2 := by ring
      _ ≤ 9 * ((2 * R + 1) ^ 2 * ∑ z ∈ supBox x R, gradOn ω V v z ^ 2) := by
          exact mul_le_mul_of_nonneg_left hcs (by norm_num)
  have hswap := sum_sum_supBox_le (F := fun z => gradOn ω V v z ^ 2) (fun z => sq_nonneg _)
    (V := V) (fun z hz => by simp only [gradOn, if_neg hz]; ring) T R
  have hV : ∑ z ∈ V, gradOn ω V v z ^ 2 = ∑ z ∈ V, openGradNorm ω V v z ^ 2 :=
    Finset.sum_congr rfl fun z hz => by simp only [gradOn, if_pos hz]
  calc ∑ j : Fin 2, ∑ x ∈ T, (coarseTest ω K V v (x + unit j) - coarseTest ω K V v x) ^ 2
      ≤ ∑ _j : Fin 2, ∑ x ∈ T, 9 * ((2 * R + 1) ^ 2 * ∑ z ∈ supBox x R, gradOn ω V v z ^ 2) :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun x hx => hpt x hx j
    _ = 18 * (2 * R + 1) ^ 2 * ∑ x ∈ T, ∑ z ∈ supBox x R, gradOn ω V v z ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum,
          ← Finset.mul_sum]
        push_cast
        ring
    _ ≤ 18 * (2 * R + 1) ^ 2 * ((2 * R + 1) ^ 2 * ∑ z ∈ V, gradOn ω V v z ^ 2) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hswap) (by positivity)
    _ = 18 * (3 + 10 * (L : ℝ)) ^ 4 * ∑ z ∈ V, openGradNorm ω V v z ^ 2 := by
        rw [hV, hR]
        ring

/-! ### The size of the cluster in a ball -/

theorem latticeDist_le_two_mul {x y : Vertex 2} {a : ℝ} (h : ∀ i, |((x i - y i : ℤ) : ℝ)| ≤ a) :
    latticeDist x y ≤ 2 * a := by
  unfold latticeDist
  rw [← Rigidity.Corrector.latticeEuclideanEmbedding_sub, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  have h0 : ‖latticeEuclideanEmbedding (x - y) 0‖ = |((x 0 - y 0 : ℤ) : ℝ)| := by
    rw [Real.norm_eq_abs]
    rfl
  have h1 : ‖latticeEuclideanEmbedding (x - y) 1‖ = |((x 1 - y 1 : ℤ) : ℝ)| := by
    rw [Real.norm_eq_abs]
    rfl
  rw [h0, h1, Real.sqrt_le_left (by linarith [h 0, abs_nonneg ((x 0 - y 0 : ℤ) : ℝ)])]
  have ha := h 0
  have hb := h 1
  have ha0 := abs_nonneg ((x 0 - y 0 : ℤ) : ℝ)
  have hb0 := abs_nonneg ((x 1 - y 1 : ℤ) : ℝ)
  nlinarith

/-- **The size of `𝒞_∞ ∩ B_r(y)`**: the anchors of the partition cubes of the points of
`y + [-m, m]²` lie in `𝒞_∞ ∩ B_r(y)` when `2(m + L) < r`. -/
theorem card_mul_le_card_dgClusterBall (hP : PlanarPartitionEvent ω)
    (h : HasUniqueInfiniteOpenComponent ω) (y : Vertex 2) {r : ℝ} {m L : ℕ}
    (hmr : 2 * ((m : ℝ) + L) < r) (hside : ∀ z ∈ supBox y m, planarSide ω z ≤ L) :
    ((2 * m + 1 : ℕ) : ℝ) ^ 2 ≤
      (L : ℝ) ^ 2 * (dgClusterBall (uniqueInfiniteComponent h) y r).card := by
  set V := dgClusterBall (uniqueInfiniteComponent h) y r
  set a : Vertex 2 → Vertex 2 := fun x => planarCoarseAnchor ω x
  have himage : (supBox y m).image a ⊆ V := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hz
    rw [mem_dgClusterBall]
    refine ⟨Rigidity.Proofs.Regularity.planarCoarseAnchor_mem_uniqueInfiniteComponent hP h x, ?_⟩
    have hxy := mem_supBox.1 hx
    have hs := hside x hx
    refine lt_of_le_of_lt (latticeDist_le_two_mul (a := (m : ℝ) + L) fun i => ?_) hmr
    have h1 := hxy i
    have h2 := abs_sub_planarCoarseAnchor_lt hP x i
    have h3 : (planarSide ω x : ℤ) ≤ L := by exact_mod_cast hs
    rw [abs_le] at h1
    rw [abs_lt] at h2
    have : |planarCoarseAnchor ω x i - y i| ≤ (m : ℤ) + L := by
      rw [abs_le]
      constructor <;> omega
    exact_mod_cast this
  have hfib : ∀ z ∈ (supBox y m).image a,
      ((supBox y m).filter fun x => a x = z).card ≤ L ^ 2 := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hz
    have hc := card_fiber_planarCoarseAnchor_le hP (supBox y m) (a x)
    have hs := hside x hx
    rw [show a x = planarCoarseAnchor ω x from rfl, planarSide_planarCoarseAnchor hP] at hc
    have : ((planarSide ω x : ℝ)) ^ 2 ≤ (L : ℝ) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hs) 2
    exact_mod_cast hc.trans this
  have hc := Finset.card_le_mul_card_image (supBox y m) (L ^ 2) hfib
  have hc2 := Finset.card_le_card himage
  rw [card_supBox] at hc
  have : ((2 * m + 1) ^ 2 : ℕ) ≤ L ^ 2 * V.card :=
    hc.trans (Nat.mul_le_mul_left _ hc2)
  exact_mod_cast this

end Rigidity.Green
