import Rigidity.Proofs.Section5.NoK33Minor
import Rigidity.Steps.Section5.BoundarySize

/-!
# Proposition 5.20: three exits are impossible in the plane

This file proves `ThreeExitsStep` (step:5.20-jordan, corrected draft L2163-2178,
Fig. trisetsoverlap; `Rigidity/Steps/Section5/BoundarySize.lean`) from the Jordan curve theorem
on `S²` (`External.JordanCurveTheoremSphere`). With it, Proposition 5.20 is proved
(`boundarySize_of_steps`).

Let `S ⊆ L` be biconnected, `P`, `N` connected, `L`, `P`, `N` pairwise disjoint, `P ∪ N` off the
finite components of `ℤ² \ S`, and `σ_m [0, r_m] ⊆ L` (`m = 0, 1, 2`) three disjoint stretches
from `S` whose last vertices `z_m` are adjacent to both `P` and `N`.

* **Tails.** Cut each stretch at its last visit `s_m` to `S`: a simple chain `τ_m` from `s_m` to
  `z_m` meeting `S` only at `s_m`.
* **Arcs of `S`.** By biconnectivity, `s_{c+1}` and `s_{c+2}` are joined by a simple chain `ρ_c`
  of `S \ {s_c}`; let `W_c` be its set of interior vertices.
* **Case A**: two of the sets `W_c` meet. Their union `W` is a connected subset of
  `S \ {s_0, s_1, s_2}` adjacent to each `s_m`, and `X = W ∪ ⋃_m (τ_m \ {z_m})` is a connected
  subset of `L` adjacent to each `z_m` and avoiding them: `P`, `N`, `X` and `z_0, z_1, z_2` form
  a `K_{3,3}` minor of the planar lattice (`noK33MinorStep`).
* **Case B**: the sets `W_c` are pairwise disjoint. Then `ρ_2 ρ_0 ρ_1` is a cycle `O` of `S`
  through `s_0, s_1, s_2`, a Jordan curve with inside `I_O`. The vertices of `P` and `N` lie in
  infinite components of `ℤ² \ S`, hence outside `O`. The theta graph with endpoints `z_0, z_1`
  and arcs through `P`, through `N` and along `τ_0, ρ_2, τ_1` is then contradicted by the point
  `w = z_2` (`false_of_theta_links`, the proof of `noK33MinorStep`): `w` is joined to the arcs
  through `P` and `N` off the two other arcs inside `P` and `N`, and to the third arc through
  `τ_2`, `s_2 ∈ O` and the inside `I_O` (whose closure contains `O`). This is where the face of
  `S` is used (a variant of the route of the `BoundarySize.lean` docstring, with the cycle
  `ρ_2 ρ_0 ρ_1` in place of the boundary of the outer face): the graph `S` alone need not
  contain a connected set adjacent to the three points `s_m` (e.g. `S` a cycle).

`boundarySize_of_inputs`: Proposition 5.20 modulo Lemma 5.16 and Proposition 5.12.
-/

open Set Topology Function LatticeProb.Percolation Rigidity.Section5 Rigidity.External

namespace Rigidity.Proofs.Section5

variable {ω : Configuration 2} {C : OpenComponent ω}

/-! ### The theta graph lemma with links -/

/-- `arcTrace_inter_subset` with `3 ≤ L + M` in place of `2 ≤ L`. -/
theorem arcTrace_inter_subset_of_three {X Y : ℤ → C} {L M : ℕ}
    (hX : IsSimpleChain (componentGraph C) X L) (hY : IsSimpleChain (componentGraph C) Y M)
    (h3 : 3 ≤ L + M)
    (hth : ∀ k k' : ℤ, 0 ≤ k → k ≤ L → 0 ≤ k' → k' ≤ M → X k = Y k' →
      (k = 0 ∧ k' = 0) ∨ (k = L ∧ k' = M)) :
    arcTrace X L ∩ arcTrace Y M ⊆ {latticePoint (X 0).val, latticePoint (X L).val} := by
  rintro v ⟨hv, hv'⟩
  have hne : ∀ n ∈ Ico (0 : ℤ) L, ∀ n' ∈ Ico (0 : ℤ) M,
      ¬ (((Subtype.val ∘ X) n = (Subtype.val ∘ Y) n' ∧
        (Subtype.val ∘ X) (n + 1) = (Subtype.val ∘ Y) (n' + 1)) ∨
        ((Subtype.val ∘ X) n = (Subtype.val ∘ Y) (n' + 1) ∧
        (Subtype.val ∘ X) (n + 1) = (Subtype.val ∘ Y) n')) := by
    rintro n ⟨h0, h1⟩ n' ⟨h0', h1'⟩ (⟨e1, e2⟩ | ⟨e1, -⟩)
    · have := hth _ _ h0 h1.le h0' h1'.le (Subtype.ext e1)
      have := hth _ _ (by omega) h1 (by omega) h1' (Subtype.ext e2)
      omega
    · have := hth _ _ h0 h1.le (by omega) h1' (Subtype.ext e1)
      omega
  obtain ⟨z, ⟨hz, hz'⟩, rfl⟩ := mem_chainTrace_inter hX.adj_val hY.adj_val hne hv hv'
  obtain ⟨k, hk0, hk1, rfl⟩ := exists_of_mem_chainVerts hz
  obtain ⟨k', hk0', hk1', e⟩ := exists_of_mem_chainVerts hz'
  rcases hth k k' hk0 hk1 hk0' hk1' (Subtype.ext e) with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The trace of `X` meets the trace of `Y` only at the endpoints of `X` when the vertices of `X`
on `Y` are endpoints of `X` (and `X` has at least two edges). -/
theorem arcTrace_inter_subset_of_verts {X Y : ℤ → C} {L M : ℕ}
    (hX : IsSimpleChain (componentGraph C) X L) (hY : IsSimpleChain (componentGraph C) Y M)
    (hL : 2 ≤ L)
    (hXY : ∀ k k' : ℤ, 0 ≤ k → k ≤ L → 0 ≤ k' → k' ≤ M → X k = Y k' → k = 0 ∨ k = L) :
    arcTrace X L ∩ arcTrace Y M ⊆ {latticePoint (X 0).val, latticePoint (X L).val} := by
  rintro v ⟨hv, hv'⟩
  have hne : ∀ n ∈ Ico (0 : ℤ) L, ∀ n' ∈ Ico (0 : ℤ) M,
      ¬ (((Subtype.val ∘ X) n = (Subtype.val ∘ Y) n' ∧
        (Subtype.val ∘ X) (n + 1) = (Subtype.val ∘ Y) (n' + 1)) ∨
        ((Subtype.val ∘ X) n = (Subtype.val ∘ Y) (n' + 1) ∧
        (Subtype.val ∘ X) (n + 1) = (Subtype.val ∘ Y) n')) := by
    rintro n ⟨h0, h1⟩ n' ⟨h0', h1'⟩ (⟨e1, e2⟩ | ⟨e1, e2⟩)
    · have := hXY _ _ h0 h1.le h0' h1'.le (Subtype.ext e1)
      have := hXY _ _ (by omega) h1 (by omega) h1' (Subtype.ext e2)
      omega
    · have := hXY _ _ h0 h1.le (by omega) h1' (Subtype.ext e1)
      have := hXY _ _ (by omega) h1 h0' h1'.le (Subtype.ext e2)
      omega
  obtain ⟨z, ⟨hz, hz'⟩, rfl⟩ := mem_chainTrace_inter hX.adj_val hY.adj_val hne hv hv'
  obtain ⟨k, hk0, hk1, rfl⟩ := exists_of_mem_chainVerts hz
  obtain ⟨k', hk0', hk1', e⟩ := exists_of_mem_chainVerts hz'
  rcases hXY k k' hk0 hk1 hk0' hk1' (Subtype.ext e) with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem arcInterior_nonempty (X : ℤ → C) {L : ℕ} (hL : 0 < L) : (arcInterior X L).Nonempty :=
  ⟨_, 1 / 2, ⟨by norm_num, by
    have : (1 : ℝ) ≤ L := by exact_mod_cast hL
    linarith⟩, rfl⟩

/-- **Theta graph with links.** Three arcs `A j` from `z₀` to `z₁` meeting only at their
endpoints, and a point `w` off them joined, for each `i`, to the interior of `A i` by a
preconnected set which misses the two other arcs (outside the interior of `A i`): impossible
(the proof of `noK33MinorStep`, from `false_of_theta_sides`). -/
theorem false_of_theta_links (hJ : JordanCurveTheoremSphere) {A : Fin 3 → ℤ → C}
    {ℓ : Fin 3 → ℕ} {w : Plane}
    (hAs : ∀ j, IsSimpleChain (componentGraph C) (A j) (ℓ j)) (hℓ : ∀ j, 0 < ℓ j)
    (h3 : ∀ j k, j ≠ k → 3 ≤ ℓ j + ℓ k)
    (hA0 : ∀ j k, A j 0 = A k 0) (hAL : ∀ j k, A j (ℓ j) = A k (ℓ k))
    (hth : ∀ j j', j ≠ j' → ∀ k k' : ℤ, 0 ≤ k → k ≤ ℓ j → 0 ≤ k' → k' ≤ ℓ j' →
      A j k = A j' k' → (k = 0 ∧ k' = 0) ∨ (k = ℓ j ∧ k' = ℓ j'))
    (hwK : ∀ j, w ∉ arcTrace (A j) (ℓ j))
    (hD : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → ∃ D : Set Plane, IsPreconnected D ∧ w ∈ D ∧
      (D ∩ arcInterior (A i) (ℓ i)).Nonempty ∧
      Disjoint (D \ arcInterior (A i) (ℓ i)) (arcTrace (A j) (ℓ j) ∪ arcTrace (A k) (ℓ k))) :
    False := by
  have hAJ : ∀ i j k : Fin 3, i ≠ j → i ≠ k → Disjoint (arcInterior (A i) (ℓ i))
      (arcTrace (A j) (ℓ j) ∪ arcTrace (A k) (ℓ k)) := fun i j k hij hik =>
    disjoint_arcInterior (hAs i) (by
      rw [Set.inter_union_distrib_left]
      exact union_subset
        (arcTrace_inter_subset_of_three (hAs i) (hAs j) (h3 i j hij) (hth i j hij))
        (arcTrace_inter_subset_of_three (hAs i) (hAs k) (h3 i k hik) (hth i k hik)))
  -- the interior of each arc is on the side of `w` of the curve formed by the two others
  have hnear : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → ∃ P Q,
      CurveSides (arcTrace (A j) (ℓ j) ∪ arcTrace (A k) (ℓ k)) P Q ∧ w ∈ Q ∧
      arcInterior (A i) (ℓ i) ⊆ Q := by
    intro i j k hij hik hjk
    obtain ⟨P, Q, hPQ, hQP⟩ := exists_curveSides_of_arcs hJ (hAs j) (hAs k)
      (hA0 j k) (hAL j k) (h3 j k hjk) (hth j k hjk)
    have hwJ : w ∉ arcTrace (A j) (ℓ j) ∪ arcTrace (A k) (ℓ k) := fun h =>
      h.elim (hwK j) (hwK k)
    obtain ⟨P', Q', h', hwQ'⟩ : ∃ P' Q', CurveSides
        (arcTrace (A j) (ℓ j) ∪ arcTrace (A k) (ℓ k)) P' Q' ∧ w ∈ Q' := by
      have : w ∈ P ∪ Q := hPQ.union_eq ▸ hwJ
      rcases this with h | h
      · exact ⟨Q, P, hQP, h⟩
      · exact ⟨P, Q, hPQ, h⟩
    refine ⟨P', Q', h', hwQ', ?_⟩
    obtain ⟨D, hDc, hwD, ⟨y, hyD, hyA⟩, hDJ⟩ := hD i j k hij hik hjk
    have hDJ' : Disjoint D (arcTrace (A j) (ℓ j) ∪ arcTrace (A k) (ℓ k)) := by
      rw [Set.disjoint_left]
      intro v hvD hvJ
      by_cases hv : v ∈ arcInterior (A i) (ℓ i)
      · exact (hAJ i j k hij hik).ne_of_mem hv hvJ rfl
      · exact hDJ.ne_of_mem ⟨hvD, hv⟩ hvJ rfl
    have hDQ := h'.subset_near hDc hDJ' ⟨w, hwD, hwQ'⟩
    exact h'.subset_near (isPreconnected_arcInterior _ _) (hAJ i j k hij hik) ⟨y, hyA, hDQ hyD⟩
  have hKsub : ∀ i j k : Fin 3, arcTrace (A i) (ℓ i) ⊆
      arcInterior (A i) (ℓ i) ∪ (arcTrace (A j) (ℓ j) ∪ arcTrace (A k) (ℓ k)) := by
    intro i j k v hv
    rcases arcTrace_subset (A i) (hℓ i) hv with h | h
    · exact Or.inl h
    · refine Or.inr (Or.inl ?_)
      rcases h with rfl | rfl
      · rw [hA0 i j]
        exact (endpoints_mem_arcTrace (A j) (hℓ j)).1
      · rw [hAL i j]
        exact (endpoints_mem_arcTrace (A j) (hℓ j)).2
  obtain ⟨P₁, Q₁, h₁, hw₁, hA₁⟩ := hnear 0 1 2 (by decide) (by decide) (by decide)
  obtain ⟨P₂, Q₂, h₂, hw₂, hA₂⟩ := hnear 1 0 2 (by decide) (by decide) (by decide)
  obtain ⟨P₃, Q₃, h₃, hw₃, hA₃⟩ := hnear 2 0 1 (by decide) (by decide) (by decide)
  -- a point of the theta graph off the lattice: the middle of the first edge of `A 0`
  have hfl : ⌊(1 / 2 : ℝ)⌋ = 0 := by rw [Int.floor_eq_iff]; norm_num
  have hl0 : (1 : ℝ) ≤ ℓ 0 := by exact_mod_cast hℓ 0
  have hxA : polyline (latticePoint ∘ (Subtype.val ∘ A 0)) (1 / 2) ∈ arcInterior (A 0) (ℓ 0) :=
    ⟨1 / 2, ⟨by norm_num, by linarith⟩, rfl⟩
  have hxl : polyline (latticePoint ∘ (Subtype.val ∘ A 0)) (1 / 2) ∉ range latticePoint := by
    rintro ⟨z', hz'⟩
    have hadj' := (hAs 0).adj_val ⌊(1 / 2 : ℝ)⌋ (by
      rw [hfl]; exact ⟨le_rfl, by exact_mod_cast hℓ 0⟩)
    obtain ⟨-, hfr⟩ := polyline_eq_latticePoint hadj' hz'.symm
    rw [Int.fract, hfl] at hfr
    norm_num at hfr
  have hΘs : arcTrace (A 0) (ℓ 0) ∪ arcTrace (A 1) (ℓ 1) ∪ arcTrace (A 2) (ℓ 2) ⊆
      latticeSkeleton :=
    union_subset (union_subset (chainTrace_subset_latticeSkeleton (hAs 0).adj_val)
      (chainTrace_subset_latticeSkeleton (hAs 1).adj_val))
      (chainTrace_subset_latticeSkeleton (hAs 2).adj_val)
  have hΘc : IsClosed (arcTrace (A 0) (ℓ 0) ∪ arcTrace (A 1) (ℓ 1) ∪ arcTrace (A 2) (ℓ 2)) :=
    ((isClosed_chainTrace _ (finite_Ico _ _)).union (isClosed_chainTrace _ (finite_Ico _ _))).union
      (isClosed_chainTrace _ (finite_Ico _ _))
  refine false_of_theta_sides hΘc ?_ h₁ h₂ h₃ (hKsub 0 1 2) hA₁ (arcInterior_subset _ _)
    (hKsub 1 0 2) hA₂ (arcInterior_nonempty _ (hℓ 1)) (arcInterior_subset _ _) (hKsub 2 0 1) hA₃
    (arcInterior_nonempty _ (hℓ 2))
    (by rintro ((h | h) | h) <;> [exact hwK 0 h; exact hwK 1 h; exact hwK 2 h]) hw₁ hw₂ hw₃
    ⟨_, Or.inl (Or.inl (arcInterior_subset _ _ hxA)), hxl⟩
  rintro v ((hv | hv) | hv) hvl
  · exact exists_halfBalls_of_arcTrace hΘs (hAs 0) (subset_union_left.trans subset_union_left) hv
      hvl
  · exact exists_halfBalls_of_arcTrace hΘs (hAs 1) (subset_union_right.trans subset_union_left) hv
      hvl
  · exact exists_halfBalls_of_arcTrace hΘs (hAs 2) subset_union_right hv hvl

/-! ### Spans of chains -/

/-- The polygonal path through the vertices of `g` from `g 0` to `g m`. -/
noncomputable def chainSpan (g : ℤ → C) (m : ℕ) : Set Plane :=
  polyline (latticePoint ∘ (Subtype.val ∘ g)) '' Icc 0 (m : ℝ)

theorem isPreconnected_chainSpan (g : ℤ → C) (m : ℕ) : IsPreconnected (chainSpan g m) :=
  isPreconnected_Icc.image _ (continuous_polyline _).continuousOn

theorem latticePoint_mem_chainSpan_zero (g : ℤ → C) (m : ℕ) :
    latticePoint (g 0).val ∈ chainSpan g m := by
  refine ⟨0, ⟨le_rfl, by positivity⟩, ?_⟩
  have := polyline_intCast (latticePoint ∘ (Subtype.val ∘ g)) 0
  push_cast at this
  rw [this]
  rfl

theorem latticePoint_mem_chainSpan_last (g : ℤ → C) (m : ℕ) :
    latticePoint (g m).val ∈ chainSpan g m := by
  refine ⟨m, ⟨by positivity, le_rfl⟩, ?_⟩
  have := polyline_intCast (latticePoint ∘ (Subtype.val ∘ g)) m
  push_cast at this
  rw [this]
  rfl

/-- A chain without common vertices with `Y` spans a set off the trace of `Y`. -/
theorem disjoint_chainSpan {g Y : ℤ → C} {m M : ℕ} (hg : IsSimpleChain (componentGraph C) g m)
    (hY : IsSimpleChain (componentGraph C) Y M)
    (hd : ∀ k k' : ℤ, 0 ≤ k → k ≤ m → 0 ≤ k' → k' ≤ M → g k ≠ Y k') :
    Disjoint (chainSpan g m) (arcTrace Y M) := by
  have hsub : chainSpan g m ⊆ arcTrace g m ∪ {latticePoint (g m).val} := by
    have := polyline_image_Icc_subset (Subtype.val ∘ g) m
    exact this
  refine Set.disjoint_of_subset_left hsub (Set.disjoint_union_left.2 ⟨disjoint_arcTrace hg hY hd,
    Set.disjoint_singleton_left.2 (latticePoint_not_mem_arcTrace hY fun k' h0 h1 =>
      hd m k' (by positivity) le_rfl h0 h1)⟩)

/-- The trace of a chain is the closure of its interior. -/
theorem arcTrace_subset_closure_arcInterior (X : ℤ → C) {L : ℕ} (hL : 0 < L) :
    arcTrace X L ⊆ closure (arcInterior X L) := by
  have h := polyline_image_Icc (Subtype.val ∘ X) (a := 0) (b := L) (by exact_mod_cast hL)
  push_cast at h
  rw [arcTrace, ← h, ← closure_Ioo (by exact_mod_cast hL.ne : (0 : ℝ) ≠ L)]
  exact image_closure_subset_closure_image (continuous_polyline _)

/-! ### Points of infinite components lie outside -/

/-- A vertex `x ∈ A` of `ℤ²` whose component in `A` is infinite lies outside a bounded Jordan
curve `J` missed by the lattice chains of `A`. -/
theorem latticePoint_mem_outside {J I O : Set Plane} (h : JordanSides J I O)
    (hJb : Bornology.IsBounded J) {A : Set (Vertex 2)}
    (hJA : ∀ (g : ℤ → Vertex 2) (m : ℕ),
      (∀ n ∈ Ico (0 : ℤ) m, (nearestNeighborGraph 2).Adj (g n) (g (n + 1))) →
      (∀ k, g k ∈ A) → Disjoint (chainTrace g (Ico 0 m)) J)
    {x : Vertex 2}
    (hinf : {y | ∃ hx : x ∈ A, ∃ hy : y ∈ A,
      ((nearestNeighborGraph 2).induce A).Reachable ⟨x, hx⟩ ⟨y, hy⟩}.Infinite) :
    latticePoint x ∈ O := by
  obtain ⟨ρ₀, hρ₀⟩ := hJb.subset_closedBall (0 : Plane)
  set ρ := max ρ₀ 0 with hρ
  have hJρ : ∀ v ∈ J, ‖v‖ ≤ ρ := fun v hv => by
    have := hρ₀ hv
    rw [Metric.mem_closedBall, dist_zero_right] at this
    exact this.trans (le_max_left _ _)
  have hF := finite_latticeEuclideanBall (0 : Vertex 2) (ρ + 1)
  obtain ⟨q, ⟨hx', hq, hreach⟩, hqF⟩ := (hinf.sdiff hF).nonempty
  have hq0 : latticeEuclideanEmbedding (0 : Vertex 2) = 0 := by
    ext k
    simp [latticeEuclideanEmbedding]
  have hqρ : ρ < ‖latticePoint q‖ := by
    have : ¬ dist (latticeEuclideanEmbedding q) (latticeEuclideanEmbedding 0) < ρ + 1 := hqF
    rw [hq0, dist_zero_right, not_lt] at this
    show ρ < ‖latticeEuclideanEmbedding q‖
    linarith
  -- the far region lies outside
  have hR := isPreconnected_norm_gt (le_max_right ρ₀ 0)
  have hFarJ : Disjoint {v : Plane | ρ < ‖v‖} J := by
    rw [Set.disjoint_left]
    intro v hv hvJ
    exact (not_lt.2 (hJρ v hvJ)) hv
  have hFarb : ¬ Bornology.IsBounded {v : Plane | ρ < ‖v‖} := fun hb =>
    NormedSpace.unbounded_univ ℝ Plane ((Metric.isBounded_closedBall (x := (0 : Plane))
      (r := ρ)).union hb |>.subset fun v _ => by
        by_cases hv : ρ < ‖v‖
        · exact Or.inr hv
        · exact Or.inl (by rw [Metric.mem_closedBall, dist_zero_right]; exact not_lt.1 hv))
  have hFarO := h.subset_outside_of_unbounded hR hFarJ hFarb
  -- a lattice path from `x` to `q` inside `A`
  obtain ⟨f, m, hf0, hfm, hfs, -⟩ := exists_isSimpleChain hreach.some
  set g : ℤ → Vertex 2 := Subtype.val ∘ f with hg
  have hgadj : ∀ n ∈ Ico (0 : ℤ) m, (nearestNeighborGraph 2).Adj (g n) (g (n + 1)) :=
    fun n hn => hfs.adj n hn.1 hn.2
  set D := polyline (latticePoint ∘ g) '' Icc 0 (m : ℝ) with hD
  have hDc : IsPreconnected D := isPreconnected_Icc.image _ (continuous_polyline _).continuousOn
  have hxD : latticePoint x ∈ D := by
    refine ⟨0, ⟨le_rfl, by positivity⟩, ?_⟩
    have := polyline_intCast (latticePoint ∘ g) 0
    push_cast at this
    rw [this]
    simp [hg, hf0]
  have hqD : latticePoint q ∈ D := by
    refine ⟨m, ⟨by positivity, le_rfl⟩, ?_⟩
    have := polyline_intCast (latticePoint ∘ g) m
    push_cast at this
    rw [this]
    simp [hg, hfm]
  have hDJ : Disjoint D J := by
    refine Set.disjoint_of_subset_left (polyline_image_Icc_subset g m)
      (Set.disjoint_union_left.2 ⟨hJA g m hgadj fun k => (f k).2, ?_⟩)
    rw [Set.disjoint_singleton_left]
    intro hqJ
    have : g m = q := by simp [hg, hfm]
    rw [this] at hqJ
    exact (not_lt.2 (hJρ _ hqJ)) hqρ
  exact h.subset_outside_of_mem hDc hDJ hqD (hFarO hqρ) hxD

/-! ### Tails of the stretches -/

/-- The tail of a stretch after its last visit to `S`: a simple chain from a vertex of `S` to the
last vertex of the stretch, through vertices of the stretch, meeting `S` only at its start. -/
theorem exists_tail {S : Set C} {r : ℕ} {σ : ℕ → C}
    (hσ : ∀ t < r, (componentGraph C).Adj (σ t) (σ (t + 1))) (h0 : σ 0 ∈ S) :
    ∃ (τ : ℤ → C) (n : ℕ), τ 0 ∈ S ∧ τ n = σ r ∧ IsSimpleChain (componentGraph C) τ n ∧
      ∀ k, (∃ t ≤ r, σ t = τ k) ∧ (τ k ∈ S → τ k = τ 0) := by
  classical
  set t₀ := Nat.findGreatest (fun t => σ t ∈ S) r with ht₀
  have ht₀S : σ t₀ ∈ S := Nat.findGreatest_spec (P := fun t => σ t ∈ S) (Nat.zero_le r) h0
  have ht₀r : t₀ ≤ r := Nat.findGreatest_le r
  have hj := joinedIn_of_chain (fun i => σ (t₀ + i)) (r - t₀) fun i hi => hσ _ (by omega)
  obtain ⟨τ, n, hτ0, hτn, hτs, hτv⟩ := exists_isSimpleChain_of_joinedIn hj
  simp only [add_zero, show t₀ + (r - t₀) = r by omega] at hτ0 hτn
  refine ⟨τ, n, hτ0 ▸ ht₀S, hτn, hτs, fun k => ?_⟩
  obtain ⟨i, hi, hik⟩ := hτv k
  refine ⟨⟨t₀ + i, by omega, hik⟩, fun hk => ?_⟩
  have hle : t₀ + i ≤ t₀ := Nat.le_findGreatest (P := fun t => σ t ∈ S) (by omega)
    (by simpa [hik] using hk)
  rw [← hik, hτ0, show i = 0 by omega, add_zero]

/-! ### Chains -/

/-- A segment of a chain is joined inside the set of its vertices. -/
theorem joinedIn_segment {f : ℤ → C} {ℓ : ℕ} (hf : IsSimpleChain (componentGraph C) f ℓ)
    {a b : ℤ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ ℓ) :
    JoinedIn C {x | ∃ j : ℤ, a ≤ j ∧ j ≤ b ∧ f j = x} (f a) (f b) := by
  have h := joinedIn_of_chain (fun i => f (a + i)) (b - a).toNat fun i hi => by
    rw [Nat.cast_succ, ← add_assoc]
    exact hf.adj (a + i) (by omega) (by omega)
  simp only [Nat.cast_zero, add_zero, show a + ((b - a).toNat : ℤ) = b by omega] at h
  refine Rigidity.Steps.Section5.joinedIn_mono h ?_
  rintro _ ⟨i, hi, rfl⟩
  exact ⟨a + i, by omega, by omega, rfl⟩

/-- The theta condition from the interior vertices of each arc. -/
theorem theta_of_interiors {X Y : ℤ → C} {L M : ℕ} (h0 : X 0 = Y 0) (hLM : X L = Y M) (hne : X 0 ≠ X L)
    (hd₁ : ∀ k k' : ℤ, 0 < k → k < L → 0 ≤ k' → k' ≤ M → X k ≠ Y k')
    (hd₂ : ∀ k k' : ℤ, 0 ≤ k → k ≤ L → 0 < k' → k' < M → X k ≠ Y k') :
    ∀ k k' : ℤ, 0 ≤ k → k ≤ L → 0 ≤ k' → k' ≤ M → X k = Y k' →
      (k = 0 ∧ k' = 0) ∨ (k = L ∧ k' = M) := by
  intro k k' hk0 hkL hk0' hkM e
  have hk : k = 0 ∨ k = L := by
    by_contra hc
    exact hd₁ k k' (by omega) (by omega) hk0' hkM e
  have hk' : k' = 0 ∨ k' = M := by
    by_contra hc
    exact hd₂ k k' hk0 hkL (by omega) (by omega) e
  rcases hk with rfl | rfl <;> rcases hk' with rfl | rfl
  · exact Or.inl ⟨rfl, rfl⟩
  · exact absurd (e.trans hLM.symm) hne
  · exact absurd (e.trans h0.symm) (Ne.symm hne)
  · exact Or.inr ⟨rfl, rfl⟩

theorem chainAppend_mem_of_forall {V : Type*} {f g : ℤ → V} {ℓ : ℕ} {S : Set V}
    (hf : ∀ k, f k ∈ S) (hg : ∀ k, g k ∈ S) (k : ℤ) : chainAppend f ℓ g k ∈ S := by
  unfold chainAppend
  split_ifs
  · exact hf k
  · exact hg _

theorem joinedIn_symm' {S : Set C} {x y : C} (h : JoinedIn C S x y) : JoinedIn C S y x := by
  obtain ⟨hx, hy, hr⟩ := h
  exact ⟨hy, hx, hr.symm⟩

/-- A simple chain from `z` to `x ∈ X` through `X`, starting with an edge from `z` into `X`. -/
theorem exists_link {X : Set C} (hX : IsConnectedSet C X) {z y x : C} (hy : y ∈ X)
    (hzy : (componentGraph C).Adj z y) (hx : x ∈ X) :
    ∃ (g : ℤ → C) (m : ℕ), IsSimpleChain (componentGraph C) g m ∧ g 0 = z ∧ g m = x ∧
      ∀ k, g k = z ∨ g k ∈ X := by
  have hlink : JoinedIn C (insert z X) z x := by
    obtain ⟨hy', hx', hr⟩ := hX y hy x hx
    refine ⟨mem_insert _ _, mem_insert_of_mem _ hx', ?_⟩
    have hr' := hr.map (SimpleGraph.induceHomOfLE (componentGraph C) (subset_insert z X)).toHom
    have hadj' : ((componentGraph C).induce (insert z X)).Adj ⟨z, mem_insert _ _⟩
        ⟨y, mem_insert_of_mem _ hy⟩ := by simpa using hzy
    exact hadj'.reachable.trans hr'
  obtain ⟨g, m, hg0, hgm, hgs, hgX⟩ := exists_isSimpleChain_of_joinedIn hlink
  exact ⟨g, m, hgs, hg0, hgm, hgX⟩

/-! ### Case A: a connected set of `S` adjacent to the three tails -/

/-- If a connected set `W ⊆ S` avoids the starting points `s_m = τ_m 0` of the tails and is
adjacent to each of them, the sets `P`, `N` and `X = W ∪ ⋃_m (τ_m \ {z_m})` and the last
vertices `z_m` of the tails form a `K_{3,3}` minor. -/
theorem false_of_connected_core (hJ : JordanCurveTheoremSphere) {S L P N W : Set C}
    (hSL : S ⊆ L) (hP : IsConnectedSet C P) (hN : IsConnectedSet C N) (hPN : Disjoint P N)
    (hLP : Disjoint L P) (hLN : Disjoint L N) {τ : Fin 3 → ℤ → C} {n : Fin 3 → ℕ}
    (hτs : ∀ m, IsSimpleChain (componentGraph C) (τ m) (n m))
    (hτS : ∀ m k, τ m k ∈ S → τ m k = τ m 0) (hτL : ∀ m k, τ m k ∈ L)
    (hτd : ∀ m m', m ≠ m' → ∀ k k', τ m k ≠ τ m' k')
    (hzP : ∀ m, ∃ y ∈ P, (componentGraph C).Adj (τ m (n m)) y)
    (hzN : ∀ m, ∃ y ∈ N, (componentGraph C).Adj (τ m (n m)) y)
    (hWS : W ⊆ S) (hWs : ∀ m, τ m 0 ∉ W) (hWc : IsConnectedSet C W)
    (hWa : ∀ m, ∃ y ∈ W, (componentGraph C).Adj (τ m 0) y) : False := by
  set X : Set C := W ∪ {x | ∃ m, ∃ k : ℤ, 0 ≤ k ∧ k < n m ∧ τ m k = x} with hX
  have hXL : X ⊆ L := by
    rintro x (hx | ⟨m, k, -, -, rfl⟩)
    · exact hSL (hWS hx)
    · exact hτL m k
  obtain ⟨b, hbW, -⟩ := hWa 0
  have hXb : ∀ x ∈ X, JoinedIn C X x b := by
    rintro x (hx | ⟨m, k, hk0, hkn, rfl⟩)
    · exact Rigidity.Steps.Section5.joinedIn_mono (hWc x hx b hbW) subset_union_left
    · obtain ⟨y, hyW, hy⟩ := hWa m
      have h1 : JoinedIn C X (τ m k) (τ m 0) := by
        have := joinedIn_segment (hτs m) le_rfl hk0 (by omega)
        refine joinedIn_symm' (Rigidity.Steps.Section5.joinedIn_mono this ?_)
        rintro _ ⟨j, hj0, hjk, rfl⟩
        exact Or.inr ⟨m, j, hj0, by omega, rfl⟩
      have h2 : JoinedIn C X (τ m 0) y := Rigidity.Steps.Section5.joinedIn_of_adj
        (Or.inr ⟨m, 0, le_rfl, by omega, rfl⟩) (Or.inl hyW) hy
      exact joinedIn_trans (joinedIn_trans h1 h2)
        (Rigidity.Steps.Section5.joinedIn_mono (hWc y hyW b hbW) subset_union_left)
  have hXc : IsConnectedSet C X := fun x hx y hy =>
    joinedIn_trans (hXb x hx) (joinedIn_symm' (hXb y hy))
  have hzX : ∀ m, τ m (n m) ∉ X := by
    rintro m (hm | ⟨m', k, hk0, hkn, hk⟩)
    · exact hWs m (hτS m _ (hWS hm) ▸ hm)
    · by_cases hmm : m' = m
      · subst hmm
        have := (hτs m').inj k (n m') hk0 hkn.le (by positivity) le_rfl hk
        omega
      · exact hτd m' m hmm k (n m) hk
  have hzinj : Injective fun m => τ m (n m) := fun m m' h => by
    by_contra hmm
    exact hτd m m' hmm _ _ h
  have hzXa : ∀ m, ∃ y ∈ X, (componentGraph C).Adj (τ m (n m)) y := by
    intro m
    rcases Nat.eq_zero_or_pos (n m) with h0 | hpos
    · obtain ⟨y, hyW, hy⟩ := hWa m
      refine ⟨y, Or.inl hyW, ?_⟩
      rw [h0, Nat.cast_zero]
      exact hy
    · refine ⟨τ m (n m - 1), Or.inr ⟨m, n m - 1, by omega, by omega, rfl⟩, ?_⟩
      have := (hτs m).adj (n m - 1) (by omega) (by omega)
      rw [sub_add_cancel] at this
      exact this.symm
  have hPX : Disjoint P X := hLP.symm.mono_right hXL
  have hNX : Disjoint N X := hLN.symm.mono_right hXL
  refine noK33MinorStep hJ ω C ![P, N, X] (fun m => τ m (n m)) ?_ ?_ hzinj ?_ ?_
  · intro j
    fin_cases j
    · exact hP
    · exact hN
    · exact hXc
  · intro j k hjk
    fin_cases j <;> fin_cases k
    all_goals first
      | exact absurd rfl hjk
      | exact hPN | exact hPN.symm | exact hPX | exact hPX.symm | exact hNX | exact hNX.symm
  · intro i j
    fin_cases j
    · exact fun h => hLP.ne_of_mem (hτL i _) h rfl
    · exact fun h => hLN.ne_of_mem (hτL i _) h rfl
    · exact hzX i
  · intro i j
    fin_cases j
    · exact hzP i
    · exact hzN i
    · exact hzXa i

/-! ### Case B: a cycle of `S` through the three starting points -/

/-- The arcs `ρ_c` of `S \ {s_c}` from `s_{c+1}` to `s_{c+2}`, with pairwise disjoint interiors,
form a cycle `O = ρ_2 ρ_0 ρ_1` of `S`: a bounded Jordan curve `J` through `s_2` and the first edge
of `ρ_2`, missed by the lattice chains off `S`, whose trace meets the arcs whose vertices in `S`
are endpoints only at these endpoints. -/
theorem exists_cycle_sides (hJ : JordanCurveTheoremSphere) {S : Set C} {s : Fin 3 → C}
    (hs : Injective s) {ρ : Fin 3 → ℤ → C} {len : Fin 3 → ℕ}
    (hρs : ∀ c, IsSimpleChain (componentGraph C) (ρ c) (len c))
    (hρ0 : ∀ c, ρ c 0 = s (c + 1)) (hρl : ∀ c, ρ c (len c) = s (c + 2))
    (hρS : ∀ c k, ρ c k ∈ S) (hρne : ∀ c k, ρ c k ≠ s c)
    (hρd : ∀ c c', c ≠ c' → ∀ k k' : ℤ, 0 < k → k < len c → 0 < k' → k' < len c' →
      ρ c k ≠ ρ c' k') :
    ∃ J I O : Set Plane, JordanSides J I O ∧ Bornology.IsBounded J ∧
      (∀ (g : ℤ → Vertex 2) (m : ℕ),
        (∀ n ∈ Ico (0 : ℤ) m, (nearestNeighborGraph 2).Adj (g n) (g (n + 1))) →
        (∀ k, g k ∈ (Subtype.val '' S)ᶜ) → Disjoint (chainTrace g (Ico 0 m)) J) ∧
      latticePoint (s 2).val ∈ J ∧ edgeSegment (ρ 2 0).val (ρ 2 1).val ⊆ J ∧
      ∀ (A : ℤ → C) (ℓ : ℕ), IsSimpleChain (componentGraph C) A ℓ → 2 ≤ ℓ →
        (∀ k : ℤ, 0 ≤ k → k ≤ ℓ → A k ∈ S → k = 0 ∨ k = ℓ) →
        Disjoint (arcInterior A ℓ) J := by
  have hfin : ∀ c m : Fin 3, m = c ∨ m = c + 1 ∨ m = c + 2 := by decide
  have hfin2 : ∀ c : Fin 3, c + 1 ≠ c + 2 := by decide
  have hlen : ∀ c, 0 < len c := by
    intro c
    by_contra h
    have h' : len c = 0 := by omega
    have e := hρl c
    rw [h', Nat.cast_zero, hρ0] at e
    exact hfin2 c (hs e)
  have hint : ∀ c (k : ℤ) m, 0 < k → k < len c → ρ c k ≠ s m := by
    intro c k m hk0 hkl e
    rcases hfin c m with rfl | rfl | rfl
    · exact hρne _ k e
    · have := (hρs c).inj k 0 hk0.le hkl.le le_rfl (by positivity) (e.trans (hρ0 c).symm)
      omega
    · have := (hρs c).inj k (len c) hk0.le hkl.le (by positivity) le_rfl
        (e.trans (hρl c).symm)
      omega
  have hρd' : ∀ c c', c ≠ c' → ∀ k k' : ℤ, 0 < k → k < len c → 0 ≤ k' → k' ≤ len c' →
      ρ c k ≠ ρ c' k' := by
    intro c c' hcc' k k' hk0 hkl hk0' hkl' e
    rcases (show k' = 0 ∨ k' = len c' ∨ (0 < k' ∧ k' < len c') by omega) with
      rfl | rfl | ⟨h1, h2⟩
    · exact hint c k _ hk0 hkl (e.trans (hρ0 c'))
    · exact hint c k _ hk0 hkl (e.trans (hρl c'))
    · exact hρd c c' hcc' k k' hk0 hkl h1 h2 e
  have h20 : ρ 2 0 = s 0 := hρ0 2
  have h2l : ρ 2 (len 2) = s 1 := hρl 2
  have h00 : ρ 0 0 = s 1 := hρ0 0
  have h0l : ρ 0 (len 0) = s 2 := hρl 0
  have h10 : ρ 1 0 = s 2 := hρ0 1
  have h1l : ρ 1 (len 1) = s 0 := hρl 1
  have hfg : ρ 2 (len 2) = ρ 0 0 := h2l.trans h00.symm
  -- the arc `ρ_2 ρ_0` from `s_0` to `s_2`
  set X := chainAppend (ρ 2) (len 2) (ρ 0) with hXdef
  have hXs : IsSimpleChain (componentGraph C) X (len 2 + len 0) := by
    refine (hρs 2).append (hρs 0) hfg fun k k' hk0 hkl hk0' hkl' e => ?_
    have ek' : k' = 0 := by
      by_contra hk'0
      rcases (show k' = len 0 ∨ (0 < k' ∧ k' < len 0) by omega) with rfl | ⟨h1, h2⟩
      · exact hρne 2 k (e.trans h0l)
      · exact hρd' 0 2 (by decide) k' k h1 h2 hk0 hkl e.symm
    subst ek'
    exact ⟨(hρs 2).inj k (len 2) hk0 hkl (by positivity) le_rfl (e.trans hfg.symm), rfl⟩
  have hXS : ∀ k, X k ∈ S := chainAppend_mem_of_forall (hρS 2) (hρS 0)
  set Y := chainRev (ρ 1) (len 1) with hYdef
  have hYs : IsSimpleChain (componentGraph C) Y (len 1) := (hρs 1).rev
  have hYv : ∀ k, Y k = ρ 1 (len 1 - k) := fun k => rfl
  have hYS : ∀ k, Y k ∈ S := fun k => hρS 1 _
  have hX0 : X 0 = s 0 := by rw [hXdef, chainAppend_of_le (by positivity)]; exact h20
  have hY0 : Y 0 = s 0 := by rw [hYv, sub_zero]; exact h1l
  have hXL : X ((len 2 + len 0 : ℕ) : ℤ) = s 2 := by
    rw [hXdef, chainAppend_of_ge hfg (by push_cast; omega)]
    push_cast
    rw [add_sub_cancel_left]
    exact h0l
  have hYM : Y (len 1) = s 2 := by rw [hYv, sub_self]; exact h10
  have hX1 : X 1 = ρ 2 1 := by
    rw [hXdef, chainAppend_of_le (by have := hlen 2; omega)]
  have hth := theta_of_interiors (X := X) (Y := Y) (L := len 2 + len 0) (M := len 1)
    (hX0.trans hY0.symm) (hXL.trans hYM.symm)
    (by rw [hX0, hXL]; exact hs.ne (by decide))
    (fun k k' h0 h1 h0' h1' e => by
      rw [hYv] at e
      by_cases hk : k ≤ len 2
      · rw [hXdef, chainAppend_of_le hk] at e
        rcases (show k = len 2 ∨ k < len 2 by omega) with rfl | hk2
        · exact hρne 1 _ (e.symm.trans h2l)
        · exact hρd' 2 1 (by decide) k _ h0 hk2 (by omega) (by omega) e
      · rw [hXdef, chainAppend_of_ge hfg (by omega)] at e
        exact hρd' 0 1 (by decide) (k - len 2) _ (by omega) (by push_cast at h1; omega)
          (by omega) (by omega) e)
    (fun k k' h0 h1 h0' h1' e => by
      rw [hYv] at e
      rcases chainAppend_mem hfg h0 (by push_cast at h1; exact h1) with
        ⟨j, hj0, hj1, hj⟩ | ⟨j, hj0, hj1, hj⟩
      · rw [hXdef, hj] at e
        exact hρd' 1 2 (by decide) _ j (by omega) (by omega) hj0 hj1 e.symm
      · rw [hXdef, hj] at e
        exact hρd' 1 0 (by decide) _ j (by omega) (by omega) hj0 hj1 e.symm)
  have h3 : 3 ≤ (len 2 + len 0) + len 1 := by
    have := hlen 0; have := hlen 1; have := hlen 2; omega
  obtain ⟨I, O, hIO⟩ := exists_jordanSides_of_arcs hJ hXs hYs (hX0.trans hY0.symm)
    (hXL.trans hYM.symm) h3 hth
  have hbd : ∀ (Z : ℤ → C) (M : ℕ), Bornology.IsBounded (arcTrace Z M) := fun Z M => by
    unfold arcTrace chainTrace
    exact (Bornology.isBounded_biUnion (finite_Ico _ _)).2 fun _ _ =>
      (isCompact_edgeSegment _ _).isBounded
  refine ⟨arcTrace X (len 2 + len 0) ∪ arcTrace Y (len 1), I, O, hIO,
    (hbd _ _).union (hbd _ _), ?_, Or.inl ?_, ?_, ?_⟩
  · intro g m hg hgA
    have hgv : ∀ v ∈ chainVerts g (Ico 0 m), v ∉ Subtype.val '' S := by
      rintro v ⟨k, -, rfl | rfl⟩
      · exact hgA k
      · exact hgA (k + 1)
    have hZv : ∀ (Z : ℤ → C) (M : ℕ), (∀ k, Z k ∈ S) →
        ∀ v ∈ chainVerts (Subtype.val ∘ Z) (Ico 0 M), v ∈ Subtype.val '' S := by
      rintro Z M hZ v ⟨k, -, rfl | rfl⟩
      · exact ⟨_, hZ k, rfl⟩
      · exact ⟨_, hZ (k + 1), rfl⟩
    rw [Set.disjoint_union_right]
    exact ⟨disjoint_chainTrace hg hXs.adj_val (Set.disjoint_left.2 fun v hv hv' =>
        hgv v hv (hZv X _ hXS v hv')),
      disjoint_chainTrace hg hYs.adj_val (Set.disjoint_left.2 fun v hv hv' =>
        hgv v hv (hZv Y _ hYS v hv'))⟩
  · rw [← hXL]
    exact (endpoints_mem_arcTrace X (by have := hlen 0; omega)).2
  · intro v hv
    refine Or.inl (Set.mem_biUnion (x := 0) ⟨le_rfl, by have := hlen 2; push_cast; omega⟩ ?_)
    simp only [Function.comp_apply, zero_add]
    rwa [hX1, show X 0 = ρ 2 0 from hX0.trans h20.symm]
  · intro A ℓ hA hℓ hAS
    refine disjoint_arcInterior hA ?_
    rw [Set.inter_union_distrib_left]
    exact union_subset
      (arcTrace_inter_subset_of_verts hA hXs hℓ fun k k' h0 h1 _ _ e => hAS k h0 h1 (e ▸ hXS k'))
      (arcTrace_inter_subset_of_verts hA hYs hℓ fun k k' h0 h1 _ _ e => hAS k h0 h1 (e ▸ hYS k'))

/-- Case B: when the arcs `ρ_c` of `S` have pairwise disjoint interiors, the theta graph with
endpoints `z_0, z_1` and arcs through `P`, through `N` and along `τ_0 ρ_2 τ_1` is contradicted by
`w = z_2`, joined to the third arc through `τ_2` and the inside of the cycle `ρ_2 ρ_0 ρ_1`. -/
theorem false_of_cycle_core (hJ : JordanCurveTheoremSphere) {S L P N : Set C}
    (hSL : S ⊆ L) (hP : IsConnectedSet C P) (hN : IsConnectedSet C N) (hPN : Disjoint P N)
    (hLP : Disjoint L P) (hLN : Disjoint L N)
    (hhole : ∀ x ∈ P ∪ N, ∀ T, IsLatticeComponentOf (Subtype.val '' S)ᶜ T → T.Finite →
      x.val ∉ T)
    {τ : Fin 3 → ℤ → C} {n : Fin 3 → ℕ}
    (hτs : ∀ m, IsSimpleChain (componentGraph C) (τ m) (n m))
    (hτS : ∀ m k, τ m k ∈ S → τ m k = τ m 0) (hτL : ∀ m k, τ m k ∈ L)
    (hτd : ∀ m m', m ≠ m' → ∀ k k', τ m k ≠ τ m' k')
    (hzP : ∀ m, ∃ y ∈ P, (componentGraph C).Adj (τ m (n m)) y)
    (hzN : ∀ m, ∃ y ∈ N, (componentGraph C).Adj (τ m (n m)) y)
    {ρ : Fin 3 → ℤ → C} {len : Fin 3 → ℕ}
    (hρs : ∀ c, IsSimpleChain (componentGraph C) (ρ c) (len c))
    (hρ0 : ∀ c, ρ c 0 = τ (c + 1) 0) (hρl : ∀ c, ρ c (len c) = τ (c + 2) 0)
    (hρS : ∀ c k, ρ c k ∈ S) (hρne : ∀ c k, ρ c k ≠ τ c 0)
    (hρd : ∀ c c', c ≠ c' → ∀ k k' : ℤ, 0 < k → k < len c → 0 < k' → k' < len c' →
      ρ c k ≠ ρ c' k') : False := by
  have hs : Injective fun m => τ m 0 := fun m m' h => by
    by_contra hmm
    exact hτd m m' hmm _ _ h
  obtain ⟨J, I, O, hIO, hJb, hJA, hs2J, hedge, harcs⟩ :=
    exists_cycle_sides hJ (S := S) (s := fun m => τ m 0) hs hρs hρ0 hρl hρS hρne hρd
  have hlen2 : 0 < len 2 := by
    by_contra h
    have e := hρl 2
    rw [show len 2 = 0 by omega, Nat.cast_zero, hρ0] at e
    exact absurd (hs e) (by decide)
  -- the vertices of `P ∪ N` lie outside the cycle
  have hout : ∀ x ∈ P ∪ N, latticePoint x.val ∈ O := by
    intro x hx
    have hxA : x.val ∈ (Subtype.val '' S)ᶜ := by
      rintro ⟨y, hyS, hyx⟩
      have hxS : x ∈ S := Subtype.ext hyx ▸ hyS
      rcases hx with hx | hx
      · exact hLP.ne_of_mem (hSL hxS) hx rfl
      · exact hLN.ne_of_mem (hSL hxS) hx rfl
    refine latticePoint_mem_outside hIO hJb hJA fun hfin => ?_
    exact hhole x hx _ ⟨x.val, hxA, rfl⟩ hfin
      ⟨hxA, hxA, SimpleGraph.Reachable.refl _⟩
  have hzL : ∀ m, τ m (n m) ∈ L := fun m => hτL m _
  have hz01 : τ 0 (n 0) ≠ τ 1 (n 1) := hτd 0 1 (by decide) _ _
  -- the arcs through `P` and through `N`
  have harc : ∀ Q : Set C, IsConnectedSet C Q → Disjoint L Q →
      (∀ m, ∃ y ∈ Q, (componentGraph C).Adj (τ m (n m)) y) →
      ∃ (A : ℤ → C) (ℓ : ℕ), IsSimpleChain (componentGraph C) A (ℓ + 2) ∧ A 0 = τ 0 (n 0) ∧
        A ((ℓ + 2 : ℕ) : ℤ) = τ 1 (n 1) ∧
        (∀ k, A k = τ 0 (n 0) ∨ A k = τ 1 (n 1) ∨ A k ∈ Q) := by
    intro Q hQ hLQ hzQ
    obtain ⟨a, haQ, ha⟩ := hzQ 0
    obtain ⟨b, hbQ, hb⟩ := hzQ 1
    obtain ⟨f, ℓ, hf0, hfl, hfs, hfv⟩ := exists_isSimpleChain_of_joinedIn (hQ a haQ b hbQ)
    have hzQ' : ∀ m, τ m (n m) ∉ Q := fun m h => hLQ.ne_of_mem (hzL m) h rfl
    exact ⟨chainBracket (τ 0 (n 0)) f ℓ (τ 1 (n 1)), ℓ, hfs.bracket (hf0 ▸ ha) (hfl ▸ hb.symm)
      hz01 (fun j _ _ e => hzQ' 0 (e ▸ hfv j)) (fun j _ _ e => hzQ' 1 (e ▸ hfv j)),
      chainBracket_zero _ _ _ _, chainBracket_last _ _ _ _, chainBracket_mem hfv⟩
  obtain ⟨AP, ℓP, hAPs, hAP0, hAPl, hAPv⟩ := harc P hP hLP hzP
  obtain ⟨AN, ℓN, hANs, hAN0, hANl, hANv⟩ := harc N hN hLN hzN
  -- the arc `τ_0⁻¹ ρ_2 τ_1`
  have hfg1 : ρ 2 (len 2) = τ 1 0 := hρl 2
  set B := chainAppend (ρ 2) (len 2) (τ 1) with hBdef
  have hBs : IsSimpleChain (componentGraph C) B (len 2 + n 1) := by
    refine (hρs 2).append (hτs 1) hfg1 fun k k' hk0 hkl hk0' hkl' e => ?_
    have ek' : k' = 0 := (hτs 1).inj k' 0 hk0' hkl' le_rfl (by positivity)
      (hτS 1 k' (e ▸ hρS 2 k))
    subst ek'
    exact ⟨(hρs 2).inj k (len 2) hk0 hkl (by positivity) le_rfl (e.trans hfg1.symm), rfl⟩
  have hB0 : B 0 = τ 0 0 := by
    rw [hBdef, chainAppend_of_le (by positivity)]
    exact hρ0 2
  have hrev0 : chainRev (τ 0) (n 0) (n 0) = B 0 := by
    rw [hB0]
    show τ 0 (n 0 - n 0) = τ 0 0
    rw [sub_self]
  set AX := chainAppend (chainRev (τ 0) (n 0)) (n 0) B with hAXdef
  have hAXs : IsSimpleChain (componentGraph C) AX (n 0 + (len 2 + n 1)) := by
    refine (hτs 0).rev.append hBs hrev0 fun k k' hk0 hkl hk0' hkl' e => ?_
    change τ 0 (n 0 - k) = B k' at e
    rcases chainAppend_mem hfg1 hk0' (by push_cast at hkl'; exact hkl') with
      ⟨j, hj0, hj1, hj⟩ | ⟨j, hj0, hj1, hj⟩
    · have h1 : τ 0 (n 0 - k) ∈ S := by rw [e]; show chainAppend (ρ 2) (len 2) (τ 1) k' ∈ S; rw [hj]; exact hρS 2 j
      have hk : k = n 0 := by
        have := (hτs 0).inj (n 0 - k) 0 (by omega) (by omega) le_rfl (by positivity)
          (hτS 0 _ h1)
        omega
      subst hk
      refine ⟨rfl, hBs.inj k' 0 hk0' hkl' le_rfl (by positivity) ?_⟩
      rw [← e, sub_self, hB0]
    · exact absurd (e.trans hj) (hτd 0 1 (by decide) _ _)
  have hBv : ∀ k, B k ∈ {v | v ∈ L ∧ ∀ k', v ≠ τ 2 k'} :=
    chainAppend_mem_of_forall (fun k => ⟨hSL (hρS 2 k), fun k' e =>
      hρne 2 k (e.trans (hτS 2 _ (e ▸ hρS 2 k)))⟩)
      (fun k => ⟨hτL 1 k, fun k' => hτd 1 2 (by decide) _ _⟩)
  have hAXv : ∀ k, AX k ∈ {v | v ∈ L ∧ ∀ k', v ≠ τ 2 k'} :=
    chainAppend_mem_of_forall (fun k => ⟨hτL 0 _, fun k' => hτd 0 2 (by decide) _ _⟩) hBv
  have hAX0 : AX 0 = τ 0 (n 0) := by
    rw [hAXdef, chainAppend_of_le (by positivity)]
    show τ 0 (n 0 - 0) = _
    rw [sub_zero]
  have hAXl : AX ((n 0 + (len 2 + n 1) : ℕ) : ℤ) = τ 1 (n 1) := by
    rw [hAXdef, chainAppend_of_ge hrev0 (by push_cast; omega)]
    push_cast
    rw [add_sub_cancel_left, hBdef, chainAppend_of_ge hfg1 (by omega), add_sub_cancel_left]
  -- the three arcs, indexed by `Fin 3`, with the sets `U j` containing their interiors
  obtain ⟨A, ℓ, U, hAj⟩ : ∃ (A : Fin 3 → ℤ → C) (ℓ : Fin 3 → ℕ) (U : Fin 3 → Set C), ∀ j,
      (j = 0 ∧ A j = AP ∧ ℓ j = ℓP + 2 ∧ U j = P) ∨ (j = 1 ∧ A j = AN ∧ ℓ j = ℓN + 2 ∧ U j = N) ∨
      (j = 2 ∧ A j = AX ∧ ℓ j = n 0 + (len 2 + n 1) ∧ U j = L \ {τ 0 (n 0), τ 1 (n 1)}) :=
    ⟨![AP, AN, AX], ![ℓP + 2, ℓN + 2, n 0 + (len 2 + n 1)], ![P, N, L \ {τ 0 (n 0), τ 1 (n 1)}],
      fun j => by
        fin_cases j
        · exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
        · exact Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩)
        · exact Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl⟩)⟩
  have hAs : ∀ j, IsSimpleChain (componentGraph C) (A j) (ℓ j) := by
    intro j
    rcases hAj j with ⟨-, hA, hl, -⟩ | ⟨-, hA, hl, -⟩ | ⟨-, hA, hl, -⟩ <;> rw [hA, hl]
    exacts [hAPs, hANs, hAXs]
  have hℓ1 : ∀ j, 0 < ℓ j := by
    intro j
    rcases hAj j with ⟨-, -, hl, -⟩ | ⟨-, -, hl, -⟩ | ⟨-, -, hl, -⟩ <;> rw [hl] <;> omega
  have hℓ2 : ∀ j, j ≠ 2 → 2 ≤ ℓ j := by
    intro j hj
    rcases hAj j with ⟨-, -, hl, -⟩ | ⟨-, -, hl, -⟩ | ⟨rfl, -, -, -⟩
    · omega
    · omega
    · exact absurd rfl hj
  have hA0 : ∀ j, A j 0 = τ 0 (n 0) := by
    intro j
    rcases hAj j with ⟨-, hA, -, -⟩ | ⟨-, hA, -, -⟩ | ⟨-, hA, -, -⟩ <;> rw [hA]
    exacts [hAP0, hAN0, hAX0]
  have hAL : ∀ j, A j (ℓ j) = τ 1 (n 1) := by
    intro j
    rcases hAj j with ⟨-, hA, hl, -⟩ | ⟨-, hA, hl, -⟩ | ⟨-, hA, hl, -⟩ <;> rw [hA, hl]
    exacts [hAPl, hANl, hAXl]
  have hAv : ∀ j k, A j k = τ 0 (n 0) ∨ A j k = τ 1 (n 1) ∨ A j k ∈ U j := by
    intro j k
    rcases hAj j with ⟨-, hA, -, hU⟩ | ⟨-, hA, -, hU⟩ | ⟨-, hA, -, hU⟩ <;> rw [hA, hU]
    · exact hAPv k
    · exact hANv k
    · by_cases h0 : AX k = τ 0 (n 0)
      · exact Or.inl h0
      by_cases h1 : AX k = τ 1 (n 1)
      · exact Or.inr (Or.inl h1)
      exact Or.inr (Or.inr ⟨(hAXv k).1, by rintro (h | h) <;> contradiction⟩)
  have hUint : ∀ j (k : ℤ), 0 < k → k < ℓ j → A j k ∈ U j := by
    intro j k hk0 hkl
    rcases hAv j k with h | h | h
    · have := (hAs j).inj k 0 hk0.le hkl.le le_rfl (by positivity) (h.trans (hA0 j).symm)
      omega
    · have := (hAs j).inj k (ℓ j) hk0.le hkl.le (by positivity) le_rfl (h.trans (hAL j).symm)
      omega
    · exact h
  have hzU : ∀ i, τ 0 (n 0) ∉ U i ∧ τ 1 (n 1) ∉ U i := by
    intro i
    rcases hAj i with ⟨-, -, -, hU⟩ | ⟨-, -, -, hU⟩ | ⟨-, -, -, hU⟩ <;> rw [hU]
    · exact ⟨fun h => hLP.ne_of_mem (hzL 0) h rfl, fun h => hLP.ne_of_mem (hzL 1) h rfl⟩
    · exact ⟨fun h => hLN.ne_of_mem (hzL 0) h rfl, fun h => hLN.ne_of_mem (hzL 1) h rfl⟩
    · exact ⟨fun h => h.2 (Or.inl rfl), fun h => h.2 (Or.inr rfl)⟩
  have hUd : ∀ i j, i ≠ j → Disjoint (U i) (U j) := by
    have hPX : Disjoint P (L \ {τ 0 (n 0), τ 1 (n 1)}) := hLP.symm.mono_right sdiff_subset
    have hNX : Disjoint N (L \ {τ 0 (n 0), τ 1 (n 1)}) := hLN.symm.mono_right sdiff_subset
    intro i j hij
    rcases hAj i with ⟨rfl, -, -, hU⟩ | ⟨rfl, -, -, hU⟩ | ⟨rfl, -, -, hU⟩ <;>
    rcases hAj j with ⟨rfl, -, -, hU'⟩ | ⟨rfl, -, -, hU'⟩ | ⟨rfl, -, -, hU'⟩ <;>
    first
      | exact absurd rfl hij
      | (rw [hU, hU']
         first
           | exact hPN | exact hPN.symm | exact hPX | exact hPX.symm | exact hNX
           | exact hNX.symm)
  have hV : ∀ i j, i ≠ j → ∀ k, A j k ∉ U i := fun i j hij k h => by
    rcases hAv j k with e | e | e
    · exact (hzU i).1 (e ▸ h)
    · exact (hzU i).2 (e ▸ h)
    · exact (hUd j i (Ne.symm hij)).ne_of_mem e h rfl
  have hth : ∀ j j', j ≠ j' → ∀ k k' : ℤ, 0 ≤ k → k ≤ ℓ j → 0 ≤ k' → k' ≤ ℓ j' →
      A j k = A j' k' → (k = 0 ∧ k' = 0) ∨ (k = ℓ j ∧ k' = ℓ j') := fun j j' hjj' =>
    theta_of_interiors ((hA0 j).trans (hA0 j').symm) ((hAL j).trans (hAL j').symm)
      (by rw [hA0, hAL]; exact hz01)
      (fun k k' h0 h1 _ _ e => hV j j' hjj' k' (e ▸ hUint j k h0 h1))
      (fun k k' _ _ h0' h1' e => hV j' j (Ne.symm hjj') k (e.symm ▸ hUint j' k' h0' h1'))
  have hAτ2 : ∀ j k k', A j k ≠ τ 2 k' := by
    intro j k k' e
    rcases hAv j k with h | h | h
    · exact hτd 0 2 (by decide) _ _ (h.symm.trans e)
    · exact hτd 1 2 (by decide) _ _ (h.symm.trans e)
    · rcases hAj j with ⟨-, -, -, hU⟩ | ⟨-, -, -, hU⟩ | ⟨-, hA, -, -⟩
      · rw [hU] at h
        exact hLP.ne_of_mem (hτL 2 k') (e ▸ h) rfl
      · rw [hU] at h
        exact hLN.ne_of_mem (hτL 2 k') (e ▸ h) rfl
      · rw [hA] at e
        exact (hAXv k).2 k' e
  have hwK : ∀ j, latticePoint (τ 2 (n 2)).val ∉ arcTrace (A j) (ℓ j) := fun j =>
    latticePoint_not_mem_arcTrace (hAs j) fun k' _ _ e => hAτ2 j k' (n 2) e.symm
  -- the arcs through `P` and `N` lie outside the cycle
  have hUPN : ∀ j, j ≠ 2 → U j ⊆ P ∪ N ∧ Disjoint L (U j) := by
    intro j hj
    rcases hAj j with ⟨-, -, -, hU⟩ | ⟨-, -, -, hU⟩ | ⟨rfl, -, -, -⟩
    · rw [hU]
      exact ⟨subset_union_left, hLP⟩
    · rw [hU]
      exact ⟨subset_union_right, hLN⟩
    · exact absurd rfl hj
  have hFar : ∀ j, j ≠ 2 → Disjoint I (arcTrace (A j) (ℓ j)) := by
    intro j hj
    have hl : (1 : ℤ) < ℓ j := by have := hℓ2 j hj; omega
    have h1 : A j 1 ∈ U j := hUint j 1 one_pos hl
    have hint : arcInterior (A j) (ℓ j) ⊆ O :=
      hIO.subset_outside_of_mem (isPreconnected_arcInterior _ _)
        (harcs (A j) (ℓ j) (hAs j) (hℓ2 j hj) fun k h0 h1' hS => by
          by_contra hk
          exact (hUPN j hj).2.ne_of_mem (hSL hS) (hUint j k (by omega) (by omega)) rfl)
        (latticePoint_mem_arcInterior (A j) one_pos hl) (hout _ ((hUPN j hj).1 h1))
    exact (hIO.disjoint.closure_right hIO.isOpen_inside).mono_right
      ((arcTrace_subset_closure_arcInterior (A j) (hℓ1 j)).trans (closure_mono hint))
  -- the links of `w = z_2` to the arcs through `P` and `N`
  have hlinkD : ∀ i, i ≠ 2 → (∃ y ∈ U i, (componentGraph C).Adj (τ 2 (n 2)) y) →
      IsConnectedSet C (U i) →
      ∃ D : Set Plane, IsPreconnected D ∧ latticePoint (τ 2 (n 2)).val ∈ D ∧
        (D ∩ arcInterior (A i) (ℓ i)).Nonempty ∧
        ∀ j, j ≠ i → Disjoint (D \ arcInterior (A i) (ℓ i)) (arcTrace (A j) (ℓ j)) := by
    rintro i hi ⟨y, hyU, hy⟩ hUc
    have hl : (1 : ℤ) < ℓ i := by have := hℓ2 i hi; omega
    obtain ⟨g, m, hg, hg0, hgm, hgv⟩ := exists_link hUc hyU hy (hUint i 1 one_pos hl)
    refine ⟨chainSpan g m, isPreconnected_chainSpan g m, ?_, ⟨_, latticePoint_mem_chainSpan_last g m,
      ?_⟩, fun j hji => ?_⟩
    · rw [← hg0]
      exact latticePoint_mem_chainSpan_zero g m
    · rw [hgm]
      exact latticePoint_mem_arcInterior (A i) one_pos hl
    refine Set.disjoint_of_subset_left sdiff_subset
      (disjoint_chainSpan hg (hAs j) fun k k' _ _ _ _ e => ?_)
    rcases hgv k with h | h
    · exact hAτ2 j k' (n 2) (e.symm.trans h)
    · exact hV i j (Ne.symm hji) k' (e ▸ h)
  -- the link of `w = z_2` to the third arc, through `τ_2` and the inside of the cycle
  have hDX : ∃ D : Set Plane, IsPreconnected D ∧ latticePoint (τ 2 (n 2)).val ∈ D ∧
      (D ∩ arcInterior (A 2) (ℓ 2)).Nonempty ∧
      ∀ j, j ≠ 2 → Disjoint (D \ arcInterior (A 2) (ℓ 2)) (arcTrace (A j) (ℓ j)) := by
    obtain ⟨hA2, hl2⟩ : A 2 = AX ∧ ℓ 2 = n 0 + (len 2 + n 1) := by
      rcases hAj 2 with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, hA, hl, -⟩
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · exact ⟨hA, hl⟩
    rw [hA2, hl2]
    set y := polyline (latticePoint ∘ (Subtype.val ∘ AX)) ((n 0 : ℝ) + 1 / 2) with hy
    have hyA : y ∈ arcInterior AX (n 0 + (len 2 + n 1)) := by
      refine ⟨(n 0 : ℝ) + 1 / 2, ⟨by positivity, ?_⟩, rfl⟩
      have : (1 : ℝ) ≤ len 2 := by exact_mod_cast hlen2
      push_cast
      linarith [(Nat.cast_nonneg (n 1) : (0 : ℝ) ≤ n 1)]
    have hyJ : y ∈ J := by
      refine hedge ?_
      have hfl : ⌊(n 0 : ℝ) + 1 / 2⌋ = n 0 := by
        rw [Int.floor_eq_iff]
        push_cast
        constructor <;> linarith
      have e0 : AX (n 0) = ρ 2 0 := by
        rw [hAXdef, chainAppend_of_ge hrev0 le_rfl, sub_self, hBdef,
          chainAppend_of_le (by positivity)]
      have e1 : AX (n 0 + 1) = ρ 2 1 := by
        rw [hAXdef, chainAppend_of_ge hrev0 (by omega), add_sub_cancel_left, hBdef,
          chainAppend_of_le (by exact_mod_cast hlen2)]
      have := polyline_mem_edgeSegment (Subtype.val ∘ AX) ((n 0 : ℝ) + 1 / 2)
      rw [hfl] at this
      simp only [Function.comp_apply, e0, e1] at this
      exact this
    set a := latticePoint (τ 2 0).val with ha
    have haJ : a ∈ J := hs2J
    have hI' : IsPreconnected (I ∪ {a, y}) :=
      hIO.isPreconnected_inside.subset_closure subset_union_left
        (union_subset subset_closure (by
          rintro v (rfl | rfl)
          · exact hIO.subset_closure haJ
          · exact hIO.subset_closure hyJ))
    refine ⟨chainSpan (τ 2) (n 2) ∪ (I ∪ {a, y}),
      (isPreconnected_chainSpan _ _).union a (latticePoint_mem_chainSpan_zero _ _)
        (Or.inr (mem_insert _ _)) hI',
      Or.inl (latticePoint_mem_chainSpan_last _ _),
      ⟨y, Or.inr (Or.inr (mem_insert_of_mem _ rfl)), hyA⟩, fun j hj => ?_⟩
    rw [Set.disjoint_left]
    rintro v ⟨hv | hv | hv | hv, hvA⟩ hvT
    · exact (disjoint_chainSpan (hτs 2) (hAs j) fun k k' _ _ _ _ e =>
        hAτ2 j k' k e.symm).ne_of_mem hv hvT rfl
    · exact (hFar j hj).ne_of_mem hv hvT rfl
    · rw [hv] at hvT
      exact latticePoint_not_mem_arcTrace (hAs j) (fun k' _ _ e => hAτ2 j k' 0 e.symm) hvT
    · exact hvA (hv ▸ hyA)
  refine false_of_theta_links hJ (A := A) (ℓ := ℓ) (w := latticePoint (τ 2 (n 2)).val) hAs hℓ1
    (fun j k hjk => ?_) (fun j k => (hA0 j).trans (hA0 k).symm)
    (fun j k => (hAL j).trans (hAL k).symm) hth hwK (fun i j k hij hik _ => ?_)
  · have := hℓ1 j
    have := hℓ1 k
    by_cases hj : j = 2
    · subst hj
      have := hℓ2 k (Ne.symm hjk)
      omega
    · have := hℓ2 j hj
      omega
  · obtain ⟨D, hDc, hwD, hDA, hDJ⟩ : ∃ D : Set Plane, IsPreconnected D ∧
        latticePoint (τ 2 (n 2)).val ∈ D ∧ (D ∩ arcInterior (A i) (ℓ i)).Nonempty ∧
        ∀ j, j ≠ i → Disjoint (D \ arcInterior (A i) (ℓ i)) (arcTrace (A j) (ℓ j)) := by
      rcases hAj i with ⟨rfl, -, -, hU⟩ | ⟨rfl, -, -, hU⟩ | ⟨rfl, -, -, -⟩
      · exact hlinkD 0 (by decide) (by rw [hU]; exact hzP 2) (by rw [hU]; exact hP)
      · exact hlinkD 1 (by decide) (by rw [hU]; exact hzN 2) (by rw [hU]; exact hN)
      · exact hDX
    exact ⟨D, hDc, hwD, hDA, Set.disjoint_union_right.2 ⟨hDJ j (Ne.symm hij),
      hDJ k (Ne.symm hik)⟩⟩

/-! ### Proposition 5.20, step:5.20-jordan -/

/-- **step:5.20-jordan** (corrected draft L2163-2178, Fig. trisetsoverlap), from the Jordan curve
theorem on `S²`: let `S ⊆ L` be biconnected, `P` and `N` connected, `L`, `P`, `N` pairwise
disjoint, `P ∪ N` off the finite components of `ℤ² \ S`. There are no three disjoint stretches
of `L` from `S` whose last vertices are adjacent to both `P` and `N`. -/
theorem threeExitsStep : Rigidity.Steps.Section5.ThreeExitsStep := by
  intro hJ ω C S L P N hS hSL hP hN hPN hLP hLN hhole r σ hσa hσ0 hσL hσd hσP hσN
  -- the tails of the stretches after their last visit to `S`
  have htail : ∀ m, ∃ (τ : ℤ → C) (n : ℕ), τ 0 ∈ S ∧ τ n = σ m (r m) ∧
      IsSimpleChain (componentGraph C) τ n ∧
      ∀ k, (∃ t ≤ r m, σ m t = τ k) ∧ (τ k ∈ S → τ k = τ 0) :=
    fun m => exists_tail (hσa m) (hσ0 m)
  choose τ n hτ0 hτn hτs hτv using htail
  have hτS : ∀ m k, τ m k ∈ S → τ m k = τ m 0 := fun m k => (hτv m k).2
  have hτL : ∀ m k, τ m k ∈ L := fun m k => by
    obtain ⟨t, ht, e⟩ := (hτv m k).1
    exact e ▸ hσL m t ht
  have hτd : ∀ m m', m ≠ m' → ∀ k k', τ m k ≠ τ m' k' := fun m m' hmm k k' e => by
    obtain ⟨t, ht, e1⟩ := (hτv m k).1
    obtain ⟨t', ht', e2⟩ := (hτv m' k').1
    exact hσd m m' hmm t ht t' ht' (e1.trans (e.trans e2.symm))
  have hzP : ∀ m, ∃ y ∈ P, (componentGraph C).Adj (τ m (n m)) y := fun m => by
    rw [hτn m]
    exact hσP m
  have hzN : ∀ m, ∃ y ∈ N, (componentGraph C).Adj (τ m (n m)) y := fun m => by
    rw [hτn m]
    exact hσN m
  have hs : Injective fun m => τ m 0 := fun m m' h => by
    by_contra hmm
    exact hτd m m' hmm _ _ h
  -- the arcs `ρ_c` of `S \ {s_c}` from `s_{c+1}` to `s_{c+2}`
  have hfin : ∀ c m : Fin 3, m = c ∨ m = c + 1 ∨ m = c + 2 := by decide
  have hfin3 : ∀ c : Fin 3, c + 1 ≠ c ∧ c + 2 ≠ c := by decide
  have hρ : ∀ c, ∃ (ρ : ℤ → C) (len : ℕ), ρ 0 = τ (c + 1) 0 ∧ ρ len = τ (c + 2) 0 ∧
      IsSimpleChain (componentGraph C) ρ len ∧ ∀ k, ρ k ∈ S \ {τ c 0} := by
    intro c
    have hj := hS.2 (τ c 0) (hτ0 c) (τ (c + 1) 0) ⟨hτ0 _, fun h => (hfin3 c).1 (hs h)⟩
      (τ (c + 2) 0) ⟨hτ0 _, fun h => (hfin3 c).2 (hs h)⟩
    obtain ⟨ρ, len, h0, hl, hρs, hρv⟩ := exists_isSimpleChain_of_joinedIn hj
    exact ⟨ρ, len, h0, hl, hρs, hρv⟩
  choose ρ len hρ0 hρl hρs hρv using hρ
  have hρS : ∀ c k, ρ c k ∈ S := fun c k => (hρv c k).1
  have hρne : ∀ c k, ρ c k ≠ τ c 0 := fun c k => (hρv c k).2
  by_cases hW : ∃ c c', c ≠ c' ∧ ∃ k k' : ℤ, 0 < k ∧ k < len c ∧ 0 < k' ∧ k' < len c' ∧
      ρ c k = ρ c' k'
  · -- Case A: two arcs `ρ_c` share an interior vertex
    set Wi : Fin 3 → Set C := fun c => {x | ∃ k : ℤ, 0 < k ∧ k < len c ∧ ρ c k = x} with hWi
    have hWiS : ∀ c, Wi c ⊆ S := by
      rintro c _ ⟨k, -, -, rfl⟩
      exact hρS c k
    have hWis : ∀ c m, τ m 0 ∉ Wi c := by
      rintro c m ⟨k, hk0, hkl, e⟩
      rcases hfin c m with rfl | rfl | rfl
      · exact hρne _ k e
      · have := (hρs c).inj k 0 hk0.le hkl.le le_rfl (by positivity) (e.trans (hρ0 c).symm)
        omega
      · have := (hρs c).inj k (len c) hk0.le hkl.le (by positivity) le_rfl
          (e.trans (hρl c).symm)
        omega
    have hWic : ∀ c, IsConnectedSet C (Wi c) := by
      rintro c _ ⟨a, ha0, hal, rfl⟩ _ ⟨b, hb0, hbl, rfl⟩
      rcases le_total a b with h | h
      · refine Rigidity.Steps.Section5.joinedIn_mono (joinedIn_segment (hρs c) ha0.le h hbl.le) ?_
        rintro _ ⟨j, hj0, hj1, rfl⟩
        exact ⟨j, by omega, by omega, rfl⟩
      · refine joinedIn_symm' (Rigidity.Steps.Section5.joinedIn_mono
          (joinedIn_segment (hρs c) hb0.le h hal.le) ?_)
        rintro _ ⟨j, hj0, hj1, rfl⟩
        exact ⟨j, by omega, by omega, rfl⟩
    have hWia : ∀ c, (Wi c).Nonempty → ∀ m, m ≠ c →
        ∃ y ∈ Wi c, (componentGraph C).Adj (τ m 0) y := by
      rintro c ⟨_, k₀, hk0, hkl, rfl⟩ m hmc
      rcases hfin c m with rfl | rfl | rfl
      · exact absurd rfl hmc
      · refine ⟨ρ c 1, ⟨1, one_pos, by omega, rfl⟩, ?_⟩
        have := (hρs c).adj 0 le_rfl (by omega)
        rw [hρ0, zero_add] at this
        exact this
      · refine ⟨ρ c (len c - 1), ⟨len c - 1, by omega, by omega, rfl⟩, ?_⟩
        have := (hρs c).adj (len c - 1) (by omega) (by omega)
        rw [sub_add_cancel, hρl] at this
        exact this.symm
    obtain ⟨c, c', hcc', k₀, k₀', hk0, hkl, hk0', hkl', e⟩ := hW
    have hx : ρ c k₀ ∈ Wi c := ⟨k₀, hk0, hkl, rfl⟩
    have hx' : ρ c k₀ ∈ Wi c' := ⟨k₀', hk0', hkl', e.symm⟩
    refine false_of_connected_core hJ (W := Wi c ∪ Wi c') hSL hP hN hPN hLP hLN hτs hτS hτL hτd
      hzP hzN (union_subset (hWiS c) (hWiS c')) (fun m h => h.elim (hWis c m) (hWis c' m))
      ?_ ?_
    · have hxb : ∀ v ∈ Wi c ∪ Wi c', JoinedIn C (Wi c ∪ Wi c') v (ρ c k₀) := by
        rintro v (hv | hv)
        · exact Rigidity.Steps.Section5.joinedIn_mono (hWic c v hv _ hx) subset_union_left
        · exact Rigidity.Steps.Section5.joinedIn_mono (hWic c' v hv _ hx') subset_union_right
      exact fun x hx₁ y hy₁ => joinedIn_trans (hxb x hx₁) (joinedIn_symm' (hxb y hy₁))
    · intro m
      by_cases hm : m = c
      · obtain ⟨y, hy, hadj⟩ := hWia c' ⟨_, hx'⟩ m (by rw [hm]; exact hcc')
        exact ⟨y, Or.inr hy, hadj⟩
      · obtain ⟨y, hy, hadj⟩ := hWia c ⟨_, hx⟩ m hm
        exact ⟨y, Or.inl hy, hadj⟩
  · -- Case B: the interiors of the arcs `ρ_c` are pairwise disjoint
    push Not at hW
    exact false_of_cycle_core hJ hSL hP hN hPN hLP hLN hhole hτs hτS hτL hτd hzP hzN hρs hρ0
      hρl hρS hρne hW

/-- **Proposition 5.20** (corrected draft L2142-2149) modulo the strong maximum principle
(Lemma 5.16) and Proposition 5.12, from the Jordan curve theorem on `S²`. -/
theorem boundarySize_of_inputs {p : unitInterval} {f : Vertex 2 → ℤ}
    (hJ : JordanCurveTheoremSphere) (h516 : StrongMaxPrincipleStmt p)
    (h512 : InfiniteDisjointPathsStmt p f) : BoundarySizeStmt p f :=
  Rigidity.Steps.Section5.boundarySize_of_steps hJ h516 h512 threeExitsStep

end Rigidity.Proofs.Section5
