import Rigidity.Proofs.Percolation.PlanarAnchorTranslation
import Rigidity.Percolation.TriadicGoodIndependence
import Rigidity.Percolation.TriadicLocalizationGeometry

/-!
# Locality of the planar partition

Open connections inside a region depend only on the open edges inside it. Hence strip meshes,
meshedness and goodness of a triadic cube depend only on the bonds inside the square of side `9s`
around it, and so does the anchor property. The partition capped at scale `n` is local as well:
its cube at `x` depends only on the goodness of the cubes of scale below `n` within twelve of
their side lengths from `x`. For a triadic cube `V` of scale `n`, all these data at the vertices of
`V` depend only on the bonds inside the square of side `14 · 3ⁿ` around `V`.

A function which is measurable and depends only on the bonds inside a region is measurable for the
σ-algebra of these bonds; for disjoint regions these σ-algebras are independent.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.Proofs.Section5

namespace Rigidity.Percolation

/-- A measurable function of the configuration which depends only on the bonds inside a region is
measurable for the σ-algebra of these bonds. -/
theorem measurable_localBondSigma_of_eq {d : ℕ} {β : Type*} [MeasurableSpace β]
    (U : Set (Vertex d)) {f : Configuration d → β} (hf : Measurable f)
    (hloc : ∀ ω ω' : Configuration d, (∀ e ∈ localBonds U, ω e = ω' e) → f ω = f ω') :
    Measurable[localBondSigma U] f := by
  classical
  let π : Configuration d → Configuration d := fun ω e => if e ∈ localBonds U then ω e else false
  have hπ : Measurable[localBondSigma U, MeasurableSpace.pi] π := by
    rw [measurable_iff_comap_le, MeasurableSpace.pi, MeasurableSpace.comap_iSup]
    refine iSup_le fun e => ?_
    rw [MeasurableSpace.comap_comp]
    by_cases he : e ∈ localBonds U
    · have h : (fun b : Configuration d => b e) ∘ π = fun ω => ω e := by
        funext ω
        simp only [Function.comp_apply, π, if_pos he]
      rw [h]
      exact le_iSup_of_le e (le_iSup_of_le he le_rfl)
    · have h : (fun b : Configuration d => b e) ∘ π = fun _ => false := by
        funext ω
        simp only [Function.comp_apply, π, if_neg he]
      rw [h, MeasurableSpace.comap_const]
      exact bot_le
  have hfπ : f = f ∘ π := funext fun ω => hloc ω (π ω) fun e he => by
    simp only [π, if_pos he]
  rw [hfπ]
  exact hf.comp hπ

/-- Configurations agreeing on the bonds inside a region have the same open edges there. -/
theorem adj_iff_of_localBonds {ω ω' : Configuration 2} {S : Set (Vertex 2)}
    (h : ∀ e ∈ localBonds S, ω e = ω' e) :
    ∀ x ∈ S, ∀ y ∈ S, ((openGraph ω').Adj x y ↔ (openGraph ω).Adj x y) := by
  intro x hx y hy
  simp only [openGraph_adj_iff]
  constructor <;> rintro ⟨hxy, ho⟩ <;> refine ⟨hxy, ?_⟩
  · have he : bondOfAdjacent hxy ∈ localBonds S := fun z hz => by
      rcases Sym2.mem_iff.mp hz with rfl | rfl <;> assumption
    rw [h _ he]
    exact ho
  · have he : bondOfAdjacent hxy ∈ localBonds S := fun z hz => by
      rcases Sym2.mem_iff.mp hz with rfl | rfl <;> assumption
    rw [← h _ he]
    exact ho

section Locality

variable {ω ω' : Configuration 2}

/-- Open connections inside a region depend only on the open edges inside it. -/
theorem ReachIn.of_adj_iff {S : Set (Vertex 2)}
    (hagree : ∀ x ∈ S, ∀ y ∈ S, ((openGraph ω').Adj x y ↔ (openGraph ω).Adj x y))
    {a b : Vertex 2} (h : ReachIn ω S a b) : ReachIn ω' S a b := by
  obtain ⟨W, hW⟩ := h
  induction W with
  | nil => exact ⟨SimpleGraph.Walk.nil, hW⟩
  | @cons u v w hadj W ih =>
    have hu : u ∈ S := hW u (by simp)
    have hv : v ∈ S := hW v (by simp)
    obtain ⟨W', hW'⟩ := ih fun z hz => hW z (by simp [hz])
    refine ⟨SimpleGraph.Walk.cons ((hagree u hu v hv).2 hadj) W', fun z hz => ?_⟩
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact hu
    · exact hW' z hz

theorem reachIn_iff_of_adj_iff {S : Set (Vertex 2)}
    (hagree : ∀ x ∈ S, ∀ y ∈ S, ((openGraph ω').Adj x y ↔ (openGraph ω).Adj x y))
    (a b : Vertex 2) : ReachIn ω' S a b ↔ ReachIn ω S a b :=
  ⟨ReachIn.of_adj_iff fun x hx y hy => (hagree x hx y hy).symm, ReachIn.of_adj_iff hagree⟩

/-- Strip meshes depend only on the open edges of the square. -/
theorem planarMesh_iff_of_adj_iff {R : IntegerCube 2} (w : ℕ)
    (hagree : ∀ x ∈ (↑R.vertices : Set (Vertex 2)), ∀ y ∈ (↑R.vertices : Set (Vertex 2)),
      ((openGraph ω').Adj x y ↔ (openGraph ω).Adj x y)) :
    PlanarMesh ω' R w ↔ PlanarMesh ω R w := by
  have hR : ∀ {S : Set (Vertex 2)}, S ⊆ ↑R.vertices → ∀ a b,
      (ReachIn ω' S a b ↔ ReachIn ω S a b) := fun hS a b =>
    reachIn_iff_of_adj_iff (fun x hx y hy => hagree x (hS hx) y (hS hy)) a b
  unfold PlanarMesh
  exact and_congr
    (forall_congr' fun r => imp_congr_right fun hr => imp_congr_right fun hrw =>
      exists_congr fun a => exists_congr fun b =>
        and_congr_left' (hR (IntegerCube.hStrip_subset hr hrw) a b))
    (forall_congr' fun r => imp_congr_right fun hr => imp_congr_right fun hrw =>
      exists_congr fun a => exists_congr fun b =>
        and_congr_left' (hR (IntegerCube.vStrip_subset hr hrw) a b))

/-- The squares around a triadic cube lie in its square of side `9s`. -/
theorem TriadicCube.vertices_subset_ninefold_of_mem_planarSquares {Q : TriadicCube 2}
    {R : IntegerCube 2} (hR : R ∈ Q.planarSquares) :
    (↑R.vertices : Set (Vertex 2)) ⊆ ↑Q.ninefold.vertices := by
  intro v hv
  rw [Finset.mem_coe, IntegerCube.mem_vertices] at hv
  rw [TriadicCube.mem_ninefold]
  obtain ⟨-, -, hb⟩ := TriadicCube.mem_planarSquares.1 hR
  intro i
  obtain ⟨h1, h2⟩ := hv i
  obtain ⟨h3, h4⟩ := hb i
  rw [abs_le]
  constructor <;> omega

/-- A triadic cube lies in its square of side `9s`. -/
theorem TriadicCube.vertices_subset_ninefold (Q : TriadicCube 2) :
    Q.vertices ⊆ ↑Q.ninefold.vertices := by
  intro x hx
  rw [TriadicCube.mem_ninefold]
  intro i
  have h1 := Q.abs_sub_center_le hx i
  have h2 := Q.two_mul_ninefoldRadius
  have h3 := abs_nonneg (x i - Q.center i)
  have h4 : (0 : ℤ) < 3 ^ Q.scale := by positivity
  omega

/-- Meshedness depends only on the bonds inside the square of side `9s`. -/
theorem TriadicCube.planarMeshed_iff_of_adj_iff {Q : TriadicCube 2}
    (hagree : ∀ x ∈ (↑Q.ninefold.vertices : Set (Vertex 2)),
      ∀ y ∈ (↑Q.ninefold.vertices : Set (Vertex 2)),
        ((openGraph ω').Adj x y ↔ (openGraph ω).Adj x y)) :
    Q.planarMeshed ω' ↔ Q.planarMeshed ω := by
  unfold TriadicCube.planarMeshed
  exact forall₂_congr fun R hR => planarMesh_iff_of_adj_iff _ fun x hx y hy =>
    hagree x (vertices_subset_ninefold_of_mem_planarSquares hR hx) y
      (vertices_subset_ninefold_of_mem_planarSquares hR hy)

/-- The squares of side `9s` around the children lie in that of the parent. -/
theorem TriadicCube.child_ninefold_subset {T : TriadicCube 2} (hT : 0 < T.scale)
    (dg : Fin 2 → Fin 3) :
    (↑(T.child dg).ninefold.vertices : Set (Vertex 2)) ⊆ ↑T.ninefold.vertices := by
  intro v hv
  rw [TriadicCube.mem_ninefold] at hv ⊢
  intro i
  obtain ⟨k, hk⟩ : ∃ k, T.scale = k + 1 := ⟨T.scale - 1, by omega⟩
  have h1 := hv i
  have hcs : (T.child dg).scale = k := by
    change T.scale - 1 = k
    omega
  have hrc : 2 * (T.child dg).ninefoldRadius + 1 = 9 * 3 ^ k := by
    rw [(T.child dg).two_mul_ninefoldRadius, hcs]
  have hrT : 2 * T.ninefoldRadius + 1 = 27 * 3 ^ k := by
    rw [T.two_mul_ninefoldRadius, hk, pow_succ]
    ring
  have hd : (T.child dg).center i - T.center i = 3 ^ k * (((dg i : ℕ) : ℤ) - 1) := by
    change (3 : ℤ) ^ (T.child dg).scale * (3 * T.index i + ((dg i : ℕ) : ℤ) - 1) -
      (3 : ℤ) ^ T.scale * T.index i = _
    rw [hcs, hk, pow_succ]
    ring
  have hdg : |((dg i : ℕ) : ℤ) - 1| ≤ 1 := by
    have := (dg i).isLt
    rw [abs_le]
    constructor <;> omega
  have hdb : |(T.child dg).center i - T.center i| ≤ 3 ^ k := by
    rw [hd, abs_mul, abs_of_pos (by positivity : (0 : ℤ) < 3 ^ k)]
    calc (3 : ℤ) ^ k * |((dg i : ℕ) : ℤ) - 1| ≤ 3 ^ k * 1 :=
          mul_le_mul_of_nonneg_left hdg (by positivity)
      _ = 3 ^ k := mul_one _
  have ha : (0 : ℤ) < 3 ^ k := by positivity
  rw [abs_le] at h1 hdb ⊢
  constructor <;> omega

/-- Goodness of a planar cube depends only on the bonds inside its square of side `9s`. -/
theorem mem_planarGoodCubes_iff_of_adj_iff {T : TriadicCube 2}
    (hagree : ∀ x ∈ (↑T.ninefold.vertices : Set (Vertex 2)),
      ∀ y ∈ (↑T.ninefold.vertices : Set (Vertex 2)),
        ((openGraph ω').Adj x y ↔ (openGraph ω).Adj x y)) :
    T ∈ planarGoodCubes ω' ↔ T ∈ planarGoodCubes ω := by
  unfold planarGoodCubes TriadicCube.goodOfWellConnected planarMeshedFamily
  simp only [Set.mem_setOf_eq]
  refine and_congr_right fun hpos => and_congr
    (and_congr Iff.rfl (TriadicCube.planarMeshed_iff_of_adj_iff hagree))
    (forall_congr' fun dg => and_congr Iff.rfl
      (TriadicCube.planarMeshed_iff_of_adj_iff fun x hx y hy =>
        hagree x (TriadicCube.child_ninefold_subset hpos dg hx) y
          (TriadicCube.child_ninefold_subset hpos dg hy)))

/-- The anchor property depends only on the bonds inside the square of side `9s`. -/
theorem TriadicCube.isPlanarAnchor_iff_of_adj_iff {Q : TriadicCube 2}
    (hagree : ∀ x ∈ (↑Q.ninefold.vertices : Set (Vertex 2)),
      ∀ y ∈ (↑Q.ninefold.vertices : Set (Vertex 2)),
        ((openGraph ω').Adj x y ↔ (openGraph ω).Adj x y)) (a : Vertex 2) :
    Q.IsPlanarAnchor ω' a ↔ Q.IsPlanarAnchor ω a := by
  have h1 : ∀ c d, ReachIn ω' Q.vertices c d ↔ ReachIn ω Q.vertices c d :=
    reachIn_iff_of_adj_iff fun x hx y hy =>
      hagree x (Q.vertices_subset_ninefold hx) y (Q.vertices_subset_ninefold hy)
  have h2 : ∀ c d, ReachIn ω' ↑Q.ninefold.vertices c d ↔ ReachIn ω ↑Q.ninefold.vertices c d :=
    reachIn_iff_of_adj_iff hagree
  unfold TriadicCube.IsPlanarAnchor
  simp only [h1, h2]

end Locality

/-- **Locality of the capped partition.** The cube of the partition capped at scale `n` at `x`
depends only on the good cubes of scale below `n` within twelve of their side lengths from `x`. -/
theorem TriadicCube.cappedCube_eq_of_agree {d : ℕ} {G G' : Set (TriadicCube d)} {n : ℕ}
    {x : Vertex d}
    (h : ∀ T : TriadicCube d, T.scale < n → (∀ y ∈ T.vertices, ∀ i, |x i - y i| < 12 * T.side) →
      (T ∈ G' ↔ T ∈ G)) :
    cappedCube G' n x = cappedCube G n x := by
  have key : ∀ {H K : Set (TriadicCube d)}, (∀ T : TriadicCube d, T.scale < n →
      (∀ y ∈ T.vertices, ∀ i, |x i - y i| < 12 * T.side) → (T ∈ K ↔ T ∈ H)) →
      cappedCube H n x = cappedCube (H ∩ K) n x := by
    intro H K hHK
    by_contra hne
    have hsub : capped (H ∩ K) n ⊆ capped H n :=
      Set.union_subset_union_left _ Set.inter_subset_left
    obtain ⟨T, hT1, hT2, hnear⟩ := exists_new_good_near_of_stopping_ne hsub
      (cappedCube_spec (H ∩ K) n x).1 (cappedCube_spec H n x).1
      (cappedCube_spec (H ∩ K) n x).2 (cappedCube_spec H n x).2 (Ne.symm hne)
    simp only [capped, Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq, not_or, not_and,
      not_le] at hT1 hT2
    obtain ⟨hT1a, hT1b⟩ := hT1
    rcases hT2 with hH | hn
    · exact hT1a hH ((hHK T hT1b hnear).2 hH)
    · omega
  rw [key (H := G') (K := G) fun T hT hn => (h T hT hn).symm, key (H := G) (K := G') h,
    Set.inter_comm]

/-- The square of side `14 · 3ⁿ` around a triadic cube of scale `n`. -/
def TriadicCube.planarLocalRegion (V : TriadicCube 2) : Set (Vertex 2) :=
  {y | ∀ i, |y i - V.center i| ≤ 7 * V.side}

theorem TriadicCube.vertices_subset_planarLocalRegion (V : TriadicCube 2) :
    V.vertices ⊆ V.planarLocalRegion := by
  intro x hx
  change ∀ i, |x i - V.center i| ≤ 7 * V.side
  intro i
  have h1 := V.abs_sub_center_le hx i
  have hs : V.side = 3 ^ V.scale := rfl
  have h3 := abs_nonneg (x i - V.center i)
  have h4 : (0 : ℤ) < 3 ^ V.scale := by positivity
  omega

/-- The squares of side `9s` around cubes of scale at most `n` meeting `V` lie in the local
region. -/
theorem TriadicCube.ninefold_subset_planarLocalRegion {V Q : TriadicCube 2} {x : Vertex 2}
    (hxV : x ∈ V.vertices) (hxQ : x ∈ Q.vertices) (hQ : Q.scale ≤ V.scale) :
    (↑Q.ninefold.vertices : Set (Vertex 2)) ⊆ V.planarLocalRegion := by
  intro y hy
  change ∀ i, |y i - V.center i| ≤ 7 * V.side
  intro i
  rw [TriadicCube.mem_ninefold] at hy
  have h1 := hy i
  have h2 := Q.abs_sub_center_le hxQ i
  have h2a := le_abs_self (x i - Q.center i)
  have h2b := neg_abs_le (x i - Q.center i)
  have h3 := V.abs_sub_center_le hxV i
  have h3a := le_abs_self (x i - V.center i)
  have h3b := neg_abs_le (x i - V.center i)
  have h4 := Q.two_mul_ninefoldRadius
  have hs : V.side = 3 ^ V.scale := rfl
  have hpow : (3 : ℤ) ^ Q.scale ≤ 3 ^ V.scale := pow_le_pow_right₀ (by norm_num) hQ
  rw [abs_le] at h1 ⊢
  constructor <;> omega

/-- The squares of side `9s` around the cubes of scale below `n` which may change the capped
partition at a vertex of `V` lie in the local region. -/
theorem TriadicCube.ninefold_subset_planarLocalRegion_of_near {V T : TriadicCube 2}
    {x : Vertex 2} (hxV : x ∈ V.vertices) (hT : T.scale < V.scale)
    (hnear : ∀ y ∈ T.vertices, ∀ i, |x i - y i| < 12 * T.side) :
    (↑T.ninefold.vertices : Set (Vertex 2)) ⊆ V.planarLocalRegion := by
  intro y hy
  change ∀ i, |y i - V.center i| ≤ 7 * V.side
  intro i
  rw [TriadicCube.mem_ninefold] at hy
  have h1 := hy i
  have h2 := hnear T.center T.center_mem i
  have h3 := V.abs_sub_center_le hxV i
  have h3a := le_abs_self (x i - V.center i)
  have h3b := neg_abs_le (x i - V.center i)
  have h4 := T.two_mul_ninefoldRadius
  have hs : V.side = 3 ^ V.scale := rfl
  have hsT : T.side = 3 ^ T.scale := rfl
  have hpow : 3 * (3 : ℤ) ^ T.scale ≤ 3 ^ V.scale := by
    calc 3 * (3 : ℤ) ^ T.scale = 3 ^ (T.scale + 1) := by ring
      _ ≤ 3 ^ V.scale := pow_le_pow_right₀ (by norm_num) hT
  rw [abs_le] at h1 ⊢
  rw [abs_lt] at h2
  constructor <;> omega

end Rigidity.Percolation
