import Rigidity.Steps.Section5.InfiniteDisjointPaths
import Rigidity.Proofs.Section5.JordanLoopDefs
import Rigidity.Proofs.Section5.TraceCrossing
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Geometry.Manifold.Instances.Sphere

/-! # Proposition 5.12: the Jordan loop around the connectors

This file proves `JordanLoopStep` (Proposition 5.12: step:5.12-loop, the one-point
compactification and step:5.12-thick; corrected draft L2103-2121 with [C22]), using only
the Jordan curve theorem on `S²` (`External.JordanCurveTheoremSphere`).

* One-point compactification: `σ : ℝ² → S² \ {N}` is the inverse stereographic projection
  (`exists_sigma`); `σ x → N` as `x → ∞`, and bounded sets stay away from `N`.
* The loop `α` (a small polygonal regular neighbourhood of the connectors): grow the connectors
  `T` one adjacent vertex at a time, carrying a spanning tree; its vertices and edges give cells
  of side `1/2` (`cells`), whose counterclockwise boundary walk is maintained by inserting a
  four-corner "finger" for each new edge (`WalkProps.finger`, `exists_tree_walk`). The walk has
  no repeated corner, so its polygon is a Jordan curve; it runs exactly along the sides between a
  cell of the tree and a cell outside, so the frontier of the union `P` of the cells lies on it
  (`frontier_cells_subset`): `P` has no holes.
* The arcs `γ_k`: the polyline of the `k`-th ray from a quarter of its first edge (its exit point
  from `P`, the only point of the ray tail in `P`: `IsRay.mem_cell_eq`) to infinity, closed at
  `N` (`rayPath`). These are the hypotheses of Lemma 2.16.
* Sides: every point of the quarter grid skeleton with exactly one quarter-integer coordinate has
  a ball in which `α ∪ ⋃ γ_k` (and the trace of `π`) is a diameter, hence two half-balls
  (`twoSided_of_segment`). The frontier of every component of `S² \ (α ∪ ⋃ γ_k)` contains such a
  generic point (complements of countable sets in `ℝ²` are connected:
  `exists_generic_frontier`), so the components are the inner side `W_A ⊆ σ(P)` of `α` and the
  components `W_j` between consecutive arcs of Lemma 2.16 (`hclass` in `jordanLoopStep_main`).
* Thick side: for `V = W_j`, between the rays `a` and `b`, the bi-infinite path `π` follows the
  ray `a` backwards, the tree path from its start to the start of `b`, then the ray `b`
  (`piPath`). Its trace on `S²` is the Jordan curve `γ_a⁻¹ · (inner arc) · γ_b`; the inner arc
  lies in `W_A` away from its ends. The side `D` of `π` containing `W_j` contains no other `W_l`:
  crossing an arc off `π` stays in `D`, crossing `γ_a` (on `π`) changes the side, and going up
  the cyclic order from `l ≠ j` reaches `j - 1` (`fin_chain`). A lattice point of `𝒞_∞ ∩ D` off
  the skeleton is off `P` and off the rays, hence in some `W_l`, hence in `W_j = V`.
-/

open Set Filter Topology Function LatticeProb LatticeProb.Percolation

namespace Rigidity.Proofs.Section5.JordanLoop

/-! ### Polylines -/

/-- Clamping to `[0, 1]`. -/
noncomputable def clamp01 (s : ℝ) : ℝ := max 0 (min 1 s)

theorem continuous_clamp01 : Continuous clamp01 :=
  continuous_const.max (continuous_const.min continuous_id)

theorem clamp01_of_nonpos {s : ℝ} (hs : s ≤ 0) : clamp01 s = 0 := by
  unfold clamp01; rw [min_eq_right (by linarith)]; exact max_eq_left hs

theorem clamp01_of_one_le {s : ℝ} (hs : 1 ≤ s) : clamp01 s = 1 := by
  unfold clamp01; rw [min_eq_left hs]; exact max_eq_right zero_le_one

theorem clamp01_of_mem {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) : clamp01 s = s := by
  unfold clamp01; rw [min_eq_right h1]; exact max_eq_right h0

/-- The piecewise linear interpolation of `g` on `[0, M]`. -/
noncomputable def polylineN (g : ℕ → E2) (M : ℕ) (s : ℝ) : E2 :=
  g 0 + ∑ i ∈ Finset.range M, clamp01 (s - i) • (g (i + 1) - g i)

/-- The piecewise linear interpolation of a sequence of points: `polyline g (i + t)` is the point
of the segment `[g i, g (i + 1)]` at parameter `t ∈ [0, 1]`. -/
noncomputable def polyline (g : ℕ → E2) (s : ℝ) : E2 := polylineN g ⌈s⌉₊ s

theorem continuous_polylineN (g : ℕ → E2) (M : ℕ) : Continuous (polylineN g M) := by
  unfold polylineN
  refine continuous_const.add (continuous_finsetSum _ fun i _ => ?_)
  exact (continuous_clamp01.comp (continuous_id.sub continuous_const)).smul continuous_const

theorem polylineN_eq {g : ℕ → E2} {M M' : ℕ} {s : ℝ} (hM : s ≤ M) (hMM : M ≤ M') :
    polylineN g M' s = polylineN g M s := by
  induction M', hMM using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    rw [← ih]
    unfold polylineN
    rw [Finset.sum_range_succ, clamp01_of_nonpos (by
      have : (M : ℝ) ≤ k := by exact_mod_cast hk
      linarith), zero_smul, add_zero]

theorem polyline_eq_polylineN {g : ℕ → E2} {M : ℕ} {s : ℝ} (hM : s ≤ M) :
    polyline g s = polylineN g M s :=
  (polylineN_eq (Nat.le_ceil s) (Nat.ceil_le.2 hM)).symm

theorem continuous_polyline (g : ℕ → E2) : Continuous (polyline g) := by
  refine continuous_iff_continuousAt.2 fun s₀ => ?_
  have h : polylineN g (⌈s₀⌉₊ + 1) =ᶠ[𝓝 s₀] polyline g := by
    filter_upwards [Iio_mem_nhds (show s₀ < ((⌈s₀⌉₊ + 1 : ℕ) : ℝ) by
      push_cast; linarith [Nat.le_ceil s₀])] with s hs
    exact (polyline_eq_polylineN hs.le).symm
  exact (continuous_polylineN g _).continuousAt.congr h

theorem polyline_natCast_add (g : ℕ → E2) (i : ℕ) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    polyline g (i + t) = g i + t • (g (i + 1) - g i) := by
  rw [polyline_eq_polylineN (M := i + 1) (by push_cast; linarith)]
  unfold polylineN
  rw [Finset.sum_range_succ, show ((i : ℕ) : ℝ) + t - (i : ℕ) = t by ring, clamp01_of_mem h0 h1]
  have : ∑ x ∈ Finset.range i, clamp01 (↑i + t - ↑x) • (g (x + 1) - g x) =
      ∑ x ∈ Finset.range i, (g (x + 1) - g x) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [clamp01_of_one_le, one_smul]
    have : (x : ℝ) + 1 ≤ i := by exact_mod_cast Finset.mem_range.1 hx
    linarith
  rw [this, Finset.sum_range_sub]
  abel

theorem polyline_natCast (g : ℕ → E2) (i : ℕ) : polyline g i = g i := by
  simpa using polyline_natCast_add g i le_rfl zero_le_one

theorem polyline_zero (g : ℕ → E2) : polyline g 0 = g 0 := by
  simpa using polyline_natCast g 0

theorem polyline_one (g : ℕ → E2) : polyline g 1 = g 1 := by
  simpa using polyline_natCast g 1

theorem polyline_mem_segment (g : ℕ → E2) (i : ℕ) {s : ℝ} (hs : s ∈ Icc (i : ℝ) (i + 1)) :
    polyline g s ∈ segment ℝ (g i) (g (i + 1)) := by
  rw [segment_eq_image']
  refine ⟨s - i, ⟨by linarith [hs.1], by linarith [hs.2]⟩, ?_⟩
  simp only
  rw [← polyline_natCast_add g i (by linarith [hs.1]) (by linarith [hs.2])]
  congr 1; ring

theorem image_polyline_Icc (g : ℕ → E2) (i : ℕ) :
    polyline g '' Icc (i : ℝ) (i + 1) = segment ℝ (g i) (g (i + 1)) := by
  refine Subset.antisymm (image_subset_iff.2 fun s hs => polyline_mem_segment g i hs) ?_
  rw [segment_eq_image']
  rintro _ ⟨t, ht, rfl⟩
  exact ⟨i + t, ⟨by linarith [ht.1], by linarith [ht.2]⟩, polyline_natCast_add g i ht.1 ht.2⟩

/-- A parameter in `[0, M]` lies in some `[i, i + 1]` with `i < M`. -/
theorem exists_index {M : ℕ} (hM : 0 < M) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) M) :
    ∃ i < M, (i : ℝ) ≤ s ∧ s ≤ i + 1 := by
  by_cases h : ⌊s⌋₊ < M
  · exact ⟨⌊s⌋₊, h, Nat.floor_le hs.1, (Nat.lt_floor_add_one s).le⟩
  · refine ⟨M - 1, by omega, ?_, ?_⟩
    · have : (M : ℝ) ≤ s := by
        have := (Nat.floor_le hs.1).trans' (show ((M : ℕ) : ℝ) ≤ ⌊s⌋₊ by exact_mod_cast not_lt.1 h)
        exact this
      rw [Nat.cast_sub hM]; push_cast; linarith
    · rw [Nat.cast_sub hM]; push_cast; linarith [hs.2]

theorem eq_of_add_smul_eq {x y : E2} (hxy : x ≠ y) {t t' : ℝ}
    (h : x + t • (y - x) = x + t' • (y - x)) : t = t' :=
  smul_left_injective ℝ (sub_ne_zero.2 hxy.symm) (add_left_cancel h)

/-- The segment condition for the injectivity of a polyline on `[0, M]`: consecutive segments
meet only at their common point, other segments are disjoint, except that the first and the last
segment may share the point `g 0 = g M` (closed polylines). -/
def SegmentCondition (g : ℕ → E2) (M : ℕ) : Prop :=
  (∀ i < M, g i ≠ g (i + 1)) ∧
  ∀ i j, i < j → j < M → ∀ p ∈ segment ℝ (g i) (g (i + 1)), p ∈ segment ℝ (g j) (g (j + 1)) →
    (j = i + 1 ∧ p = g (i + 1)) ∨ (i = 0 ∧ j + 1 = M ∧ p = g 0 ∧ p = g M)

theorem polyline_eq_aux {g : ℕ → E2} {M : ℕ} (hg : SegmentCondition g M) {i j : ℕ} (hij : i ≤ j)
    (hj : j < M) {s s' : ℝ} (hs : s ∈ Icc (i : ℝ) (i + 1)) (hs' : s' ∈ Icc (j : ℝ) (j + 1))
    (h : polyline g s = polyline g s') : s = s' ∨ (s = 0 ∧ s' = M) := by
  have e1 := polyline_natCast_add g i (t := s - i) (by linarith [hs.1]) (by linarith [hs.2])
  have e2 := polyline_natCast_add g j (t := s' - j) (by linarith [hs'.1]) (by linarith [hs'.2])
  rw [add_sub_cancel] at e1 e2
  rcases hij.lt_or_eq with hij | rfl
  · have hp := polyline_mem_segment g i hs
    have hp' := polyline_mem_segment g j hs'
    rw [← h] at hp'
    rcases hg.2 i j hij hj _ hp hp' with ⟨rfl, hq⟩ | ⟨rfl, hjM, hq0, hqM⟩
    · have hi : (s - i) = 1 := by
        refine eq_of_add_smul_eq (hg.1 i (by omega)) ?_
        rw [← e1, hq, one_smul]; abel
      have hj' : (s' - ↑(i + 1)) = 0 := by
        refine eq_of_add_smul_eq (hg.1 (i + 1) hj) ?_
        rw [← e2, ← h, hq, zero_smul, add_zero]
      left; push_cast at hj'; linarith
    · have hi : (s - (0 : ℕ)) = 0 := by
        refine eq_of_add_smul_eq (hg.1 0 (by omega)) ?_
        rw [← e1, hq0, zero_smul, add_zero]
      have hj' : (s' - j) = 1 := by
        refine eq_of_add_smul_eq (hg.1 j hj) ?_
        rw [← e2, ← h, hqM, ← hjM, one_smul]; abel
      right; constructor
      · simpa using hi
      · have : ((j + 1 : ℕ) : ℝ) = M := by rw [hjM]
        push_cast at this; linarith
  · left
    have := eq_of_add_smul_eq (hg.1 i hj) (e1.symm.trans (h.trans e2))
    linarith

theorem polyline_eq_of_mem {g : ℕ → E2} {M : ℕ} (hg : SegmentCondition g M) {s s' : ℝ}
    (hs : s ∈ Icc (0 : ℝ) M) (hs' : s' ∈ Icc (0 : ℝ) M) (h : polyline g s = polyline g s') :
    s = s' ∨ (s = 0 ∧ s' = M) ∨ (s' = 0 ∧ s = M) := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · left; obtain ⟨h1, h2⟩ := hs; obtain ⟨h3, h4⟩ := hs'; push_cast at h2 h4; linarith
  obtain ⟨i, hi, hsi⟩ := exists_index hM hs
  obtain ⟨j, hj, hsj⟩ := exists_index hM hs'
  rcases le_total i j with hij | hij
  · rcases polyline_eq_aux hg hij hj hsi hsj h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rcases polyline_eq_aux hg hij hi hsj hsi h.symm with h | h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr h)

/-- A polyline satisfying the segment condition is injective on `[0, M)`. -/
theorem polyline_injOn_Ico {g : ℕ → E2} {M : ℕ} (hg : SegmentCondition g M) :
    InjOn (polyline g) (Ico 0 M) := by
  intro s hs s' hs' h
  rcases polyline_eq_of_mem hg ⟨hs.1, hs.2.le⟩ ⟨hs'.1, hs'.2.le⟩ h with h | h | h
  · exact h
  · exact absurd h.2 hs'.2.ne
  · exact absurd h.2 hs.2.ne

/-- A polyline satisfying the segment condition, with distinct endpoints, is injective on
`[0, M]`. -/
theorem polyline_injOn_Icc {g : ℕ → E2} {M : ℕ} (hg : SegmentCondition g M) (h0M : g 0 ≠ g M) :
    InjOn (polyline g) (Icc 0 M) := by
  intro s hs s' hs' h
  rcases polyline_eq_of_mem hg hs hs' h with h' | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h'
  · exact absurd (by rwa [polyline_zero, polyline_natCast] at h) h0M
  · exact absurd (by rwa [polyline_zero, polyline_natCast] at h) h0M.symm

/-! ### Lattice chains -/

/-- The point of the plane at a vertex of `ℤ²`. -/
noncomputable abbrev lp (x : Vertex 2) : E2 := latticeEuclideanEmbedding x

theorem lp_apply (x : Vertex 2) (k : Fin 2) : lp x k = (x k : ℝ) := rfl

theorem coord_of_mem_segment {x y : Vertex 2} {p : E2} (hp : p ∈ segment ℝ (lp x) (lp y)) :
    ∃ s ∈ Icc (0 : ℝ) 1, ∀ k, p k = x k + s * (y k - x k) := by
  rw [segment_eq_image'] at hp
  obtain ⟨s, hs, rfl⟩ := hp
  exact ⟨s, hs, fun k => by simp [lp_apply]⟩

/-- Two distinct unit lattice segments from a common vertex `v` meet only at `v`. -/
theorem eq_of_mem_segment_angle {v a b : Vertex 2} (ha : (lattice 2).Adj v a)
    (hb : (lattice 2).Adj v b) (hab : a ≠ b) {p : E2} (hpa : p ∈ segment ℝ (lp a) (lp v))
    (hpb : p ∈ segment ℝ (lp v) (lp b)) : p = lp v := by
  rw [segment_symm] at hpa
  obtain ⟨s, hs, hps⟩ := coord_of_mem_segment hpa
  obtain ⟨s', hs', hps'⟩ := coord_of_mem_segment hpb
  have key : ∀ k, s * ((a k : ℝ) - v k) = s' * ((b k : ℝ) - v k) := fun k => by
    have := (hps k).symm.trans (hps' k); linarith
  suffices s = 0 by
    ext k; rw [hps k, this, zero_mul, add_zero]; rfl
  have k0 := key 0
  have k1 := key 1
  have h0 := hs.1
  have h0' := hs'.1
  obtain ⟨i, rfl | rfl⟩ := ha <;> obtain ⟨j, rfl | hj⟩ := hb
  · fin_cases i <;> fin_cases j <;> simp [LatticeProb.unit] at k0 k1 hab ⊢ <;> linarith
  · subst hj
    fin_cases i <;> fin_cases j <;> simp [LatticeProb.unit] at k0 k1 hab ⊢ <;> linarith
  · fin_cases i <;> fin_cases j <;> simp [LatticeProb.unit] at k0 k1 hab ⊢ <;> linarith
  · obtain rfl : b = a + LatticeProb.unit i - LatticeProb.unit j := eq_sub_of_add_eq hj.symm
    fin_cases i <;> fin_cases j <;> simp [LatticeProb.unit] at k0 k1 hab ⊢ <;>
      linarith

/-- A lattice chain without repeated vertices (except possibly `c 0 = c M` for a closed chain of
length at least `3`) satisfies the segment condition. -/
theorem segmentCondition_of_chain {c : ℕ → Vertex 2} {M : ℕ}
    (hadj : ∀ i < M, (lattice 2).Adj (c i) (c (i + 1)))
    (hinj : ∀ i j, i ≤ M → j ≤ M → c i = c j → i = j ∨ (i = 0 ∧ j = M) ∨ (i = M ∧ j = 0))
    (hM : 3 ≤ M ∨ c 0 ≠ c M) : SegmentCondition (fun i => lp (c i)) M := by
  have hne : ∀ i j, i ≤ M → j ≤ M → i ≠ j → ¬ (i = 0 ∧ j = M) → ¬ (i = M ∧ j = 0) →
      c i ≠ c j := fun i j hi hj h1 h2 h3 h => by
    rcases hinj i j hi hj h with h | h | h <;> tauto
  refine ⟨fun i hi h => (hadj i hi).ne (latticeEuclideanEmbedding.injective h), ?_⟩
  intro i j hij hjM p hp hp'
  rcases eq_or_eq_of_mem_segment_inter (hadj i (by omega)) (hadj j hjM) hp hp' with h | h | h | h
  · exact absurd h (hne i j (by omega) (by omega) hij.ne (by omega) (by omega))
  · -- `c i = c (j + 1)`: the closing case
    rcases hinj i (j + 1) (by omega) (by omega) h with h' | ⟨rfl, hj⟩ | h'
    · omega
    · right
      have hc : c 0 = c M := by rw [h, hj]
      have hM3 : 3 ≤ M := hM.resolve_right (not_not.2 hc)
      have hv : p = lp (c 0) := by
        refine eq_of_mem_segment_angle (a := c j) (b := c 1) ?_ (hadj 0 (by omega)) ?_ ?_
          (by simpa using hp)
        · rw [h]; exact (hadj j hjM).symm
        · exact hne j 1 (by omega) (by omega) (by omega) (by omega) (by omega)
        · rw [h]; exact hp'
      refine ⟨rfl, hj, hv, ?_⟩
      show p = lp (c M); rw [← hc]; exact hv
    · omega
  · -- `c (i + 1) = c j`: consecutive segments
    rcases hinj (i + 1) j (by omega) (by omega) h with rfl | h' | h'
    · left
      refine ⟨rfl, eq_of_mem_segment_angle (hadj i (by omega)).symm (hadj (i + 1) hjM) ?_ hp hp'⟩
      intro hc
      rcases hinj i (i + 2) (by omega) (by omega) hc with h | ⟨rfl, h⟩ | h
      · omega
      · rcases hM with hM | hM
        · omega
        · exact hM (by rw [← h]; exact hc)
      · omega
    · omega
    · omega
  · rcases hinj (i + 1) (j + 1) (by omega) (by omega) h with h' | h' | h' <;> omega

/-- Affine images of a polyline satisfying the segment condition. -/
theorem SegmentCondition.map {g : ℕ → E2} {M : ℕ} (hg : SegmentCondition g M)
    (A : E2 →ᵃ[ℝ] E2) (hA : Injective A) : SegmentCondition (fun i => A (g i)) M := by
  refine ⟨fun i hi h => hg.1 i hi (hA h), fun i j hij hjM p hp hp' => ?_⟩
  rw [← image_segment] at hp hp'
  obtain ⟨q, hq, rfl⟩ := hp
  obtain ⟨q', hq', hqq⟩ := hp'
  rw [hA hqq] at hq'
  rcases hg.2 i j hij hjM q hq hq' with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩
  · exact Or.inl ⟨h1, by rw [h2]⟩
  · exact Or.inr ⟨h1, h2, by rw [h3], by rw [h4]⟩

/-! ### Quarter grid, generic points and half-balls -/

/-- The point `(a, b)` of the plane. -/
noncomputable def pt (a b : ℝ) : E2 := WithLp.toLp 2 ![a, b]

@[simp] theorem pt_zero (a b : ℝ) : pt a b 0 = a := rfl

@[simp] theorem pt_one (a b : ℝ) : pt a b 1 = b := rfl

theorem E2_ext {p q : E2} (h0 : p 0 = q 0) (h1 : p 1 = q 1) : p = q := by
  ext k; fin_cases k
  · exact h0
  · exact h1

/-- `x` is a quarter-integer. -/
def IsQuarter (x : ℝ) : Prop := ∃ m : ℤ, x = m / 4

/-- The quarter skeleton: the points with a quarter-integer coordinate. -/
def quarterSkeleton : Set E2 := {p | IsQuarter (p 0) ∨ IsQuarter (p 1)}

/-- The points with two quarter-integer coordinates. -/
def quarterPoints : Set E2 := {p | IsQuarter (p 0) ∧ IsQuarter (p 1)}

theorem countable_quarterPoints : quarterPoints.Countable := by
  refine (countable_range fun m : ℤ × ℤ => pt (m.1 / 4) (m.2 / 4)).mono ?_
  rintro p ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  exact ⟨(a, b), E2_ext (by simp [ha]) (by simp [hb])⟩

theorem one_lt_rank_E2 : 1 < Module.rank ℝ E2 := by
  rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]; norm_num

/-- The distance from a non-quarter-integer to the quarter-integers. -/
noncomputable def qdist (x : ℝ) : ℝ := min (Int.fract (4 * x)) (1 - Int.fract (4 * x)) / 4

theorem qdist_pos {x : ℝ} (hx : ¬ IsQuarter x) : 0 < qdist x := by
  have h1 : Int.fract (4 * x) ≠ 0 := by
    intro h
    rw [Int.fract_eq_iff] at h
    obtain ⟨-, -, m, hm⟩ := h
    exact hx ⟨m, by linarith⟩
  have h2 := Int.fract_lt_one (4 * x)
  have h3 := Int.fract_nonneg (4 * x)
  unfold qdist
  exact div_pos (lt_min (lt_of_le_of_ne h3 (Ne.symm h1)) (by linarith)) (by norm_num)

theorem qdist_le_abs {x : ℝ} (m : ℤ) : qdist x ≤ |x - m / 4| := by
  have hf := Int.floor_add_fract (4 * x)
  have h2 := Int.fract_lt_one (4 * x)
  have h3 := Int.fract_nonneg (4 * x)
  unfold qdist
  rcases le_or_gt m ⌊4 * x⌋ with h | h
  · have : (m : ℝ) ≤ ⌊4 * x⌋ := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith)]
    have := min_le_left (Int.fract (4 * x)) (1 - Int.fract (4 * x))
    linarith
  · have : (⌊4 * x⌋ : ℝ) + 1 ≤ m := by exact_mod_cast h
    rw [abs_of_nonpos (by linarith)]
    have := min_le_right (Int.fract (4 * x)) (1 - Int.fract (4 * x))
    linarith

theorem qdist_le {x : ℝ} : qdist x ≤ 1 / 8 := by
  unfold qdist
  have := min_le_left (Int.fract (4 * x)) (1 - Int.fract (4 * x))
  have := min_le_right (Int.fract (4 * x)) (1 - Int.fract (4 * x))
  linarith

/-- Near a point of the quarter skeleton with exactly one quarter-integer coordinate `k`, the
quarter skeleton is the line through it parallel to the other axis. -/
theorem eq_of_mem_quarterSkeleton {x p : E2} {k e : Fin 2} (hke : k ≠ e) (hk : IsQuarter (x k))
    (he : ¬ IsQuarter (x e)) (hp : p ∈ Metric.ball x (qdist (x e))) (hpQ : p ∈ quarterSkeleton) :
    p k = x k := by
  have hd : ∀ j, |p j - x j| < qdist (x e) := fun j => by
    rw [Metric.mem_ball] at hp
    have := (PiLp.dist_apply_le p x j).trans_lt hp
    rwa [Real.dist_eq] at this
  have hQ : IsQuarter (p k) ∨ IsQuarter (p e) := by
    fin_cases k <;> fin_cases e <;> simp only [quarterSkeleton, mem_setOf_eq] at hpQ ⊢ <;>
      first | exact absurd rfl hke | exact hpQ | exact hpQ.symm
  rcases hQ with ⟨m, hm⟩ | ⟨m, hm⟩
  · obtain ⟨m', hm'⟩ := hk
    have h1 := hd k
    rw [hm, hm'] at h1 ⊢
    have h2 : qdist (x e) ≤ 1 / 8 := qdist_le
    have h3 := abs_lt.1 (h1.trans_le h2)
    have h4 : ((m - m' : ℤ) : ℝ) < 1 := by push_cast; linarith [h3.2]
    have h5 : (-1 : ℝ) < ((m - m' : ℤ) : ℝ) := by push_cast; linarith [h3.1]
    have h6 : m - m' < 1 := by exact_mod_cast h4
    have h7 : -1 < m - m' := by exact_mod_cast h5
    rw [show m = m' by omega]
  · have := qdist_le_abs (x := x e) m
    have h1 := hd e
    rw [hm, abs_sub_comm] at h1
    linarith

/-- Membership in an axis-parallel segment. -/
theorem mem_segment_of_axis {a b p : E2} {k e : Fin 2} (hke : k ≠ e) (hak : a k = b k)
    (hpk : p k = a k) (h1 : a e ≤ p e) (h2 : p e ≤ b e) : p ∈ segment ℝ a b := by
  have hother : ∀ j, j ≠ e → j = k := fun j hj => by
    fin_cases j <;> fin_cases k <;> fin_cases e <;> simp_all
  rcases eq_or_lt_of_le (h1.trans h2) with heq | hlt
  · have hab : a = b := by
      ext j; by_cases hj : j = e
      · subst hj; exact heq
      · rw [hother j hj]; exact hak
    have hpa : p = a := by
      ext j; by_cases hj : j = e
      · subst hj; linarith
      · rw [hother j hj]; exact hpk
    rw [hpa, ← hab]; exact left_mem_segment ℝ a a
  · rw [segment_eq_image']
    refine ⟨(p e - a e) / (b e - a e), ⟨div_nonneg (by linarith) (by linarith),
      (div_le_one (by linarith)).2 (by linarith)⟩, ?_⟩
    ext j
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    by_cases hj : j = e
    · subst hj; field_simp; ring
    · rw [hother j hj, hak, sub_self, mul_zero, add_zero, ← hak, hpk]

/-- Around a point `x` of an axis-parallel segment with quarter-integer endpoints, where `x` has a
non-quarter-integer coordinate `e`, the line through `x` parallel to `e` stays in the segment
within distance `qdist (x e)`. -/
theorem mem_segment_of_mem_ball {a b x p : E2} {k e : Fin 2} (hke : k ≠ e) (hak : a k = b k)
    (hae : IsQuarter (a e)) (hbe : IsQuarter (b e)) (he : ¬ IsQuarter (x e))
    (hx : x ∈ segment ℝ a b) (hp : p ∈ Metric.ball x (qdist (x e))) (hpk : p k = x k) :
    p ∈ segment ℝ a b := by
  have hd : |p e - x e| < qdist (x e) := by
    rw [Metric.mem_ball] at hp
    have := (PiLp.dist_apply_le p x e).trans_lt hp
    rwa [Real.dist_eq] at this
  rw [segment_eq_image'] at hx
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hx
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] at hd he hpk ⊢
  rw [hak, sub_self, mul_zero, add_zero] at hpk
  obtain ⟨m, hm⟩ := hae
  obtain ⟨m', hm'⟩ := hbe
  have hqa := qdist_le_abs (x := a e + t * (b e - a e)) m
  have hqb := qdist_le_abs (x := a e + t * (b e - a e)) m'
  rw [← hm] at hqa
  rw [← hm'] at hqb
  rcases le_total (a e) (b e) with hab | hab
  · have h1 : a e + qdist (a e + t * (b e - a e)) ≤ a e + t * (b e - a e) := by
      rw [abs_of_nonneg (by nlinarith)] at hqa; linarith
    have h2 : a e + t * (b e - a e) + qdist (a e + t * (b e - a e)) ≤ b e := by
      rw [abs_of_nonpos (by nlinarith)] at hqb; linarith
    exact mem_segment_of_axis hke (by rw [hak]) (by rw [hpk, hak]) (by linarith [abs_lt.1 hd])
      (by linarith [abs_lt.1 hd])
  · have h1 : b e + qdist (a e + t * (b e - a e)) ≤ a e + t * (b e - a e) := by
      rw [abs_of_nonneg (by nlinarith)] at hqb; linarith
    have h2 : a e + t * (b e - a e) + qdist (a e + t * (b e - a e)) ≤ a e := by
      rw [abs_of_nonpos (by nlinarith)] at hqa; linarith
    rw [segment_symm]
    exact mem_segment_of_axis hke (by rw [hak]) (by rw [hpk]) (by linarith [abs_lt.1 hd])
      (by linarith [abs_lt.1 hd])

/-- The open half-balls on both sides of the line `{p k = x k}`. -/
def halfBall (x : E2) (k : Fin 2) (r : ℝ) (pos : Bool) : Set E2 :=
  Metric.ball x r ∩ {p | if pos then x k < p k else p k < x k}

theorem convex_halfBall (x : E2) (k : Fin 2) (r : ℝ) (pos : Bool) :
    Convex ℝ (halfBall x k r pos) := by
  refine (convex_ball x r).inter ?_
  cases pos
  · exact (convex_Iio (x k)).linear_preimage (EuclideanSpace.proj k : E2 →L[ℝ] ℝ).toLinearMap
  · exact (convex_Ioi (x k)).linear_preimage (EuclideanSpace.proj k : E2 →L[ℝ] ℝ).toLinearMap

theorem halfBall_nonempty (x : E2) (k : Fin 2) {r : ℝ} (hr : 0 < r) (pos : Bool) :
    (halfBall x k r pos).Nonempty := by
  refine ⟨x + EuclideanSpace.single k (if pos then r / 2 else -(r / 2)), ?_, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, EuclideanSpace.single, PiLp.norm_single]
    cases pos <;> simp [abs_of_pos hr] <;> linarith
  · cases pos <;> simp <;> linarith

theorem mem_halfBall_of_ne {x p : E2} {k : Fin 2} {r : ℝ} (hp : p ∈ Metric.ball x r)
    (hpk : p k ≠ x k) : p ∈ halfBall x k r true ∪ halfBall x k r false := by
  rcases lt_or_gt_of_ne hpk with h | h
  · exact Or.inr ⟨hp, by simpa using h⟩
  · exact Or.inl ⟨hp, by simpa using h⟩

/-! ### Components on the sphere -/

open Rigidity.Section2

theorem IsComp.eq {Γ W W' : Set S2} (h : IsComp Γ W) (h' : IsComp Γ W')
    (hWW' : (W ∩ W').Nonempty) : W = W' :=
  Subset.antisymm (h'.maximal W h.isPreconnected h.subset hWW')
    (h.maximal W' h'.isPreconnected h'.subset (by rwa [inter_comm]))

theorem isComp_connectedComponentIn {Γ : Set S2} {z : S2} (_hz : z ∉ Γ) :
    IsComp Γ (connectedComponentIn Γᶜ z) := by
  refine ⟨connectedComponentIn_subset _ _, isPreconnected_connectedComponentIn,
    fun Y hY hYΓ ⟨y, hyY, hyW⟩ => ?_⟩
  rw [connectedComponentIn_eq hyW]
  exact hY.subset_connectedComponentIn hyY hYΓ

theorem IsComp.eq_connectedComponentIn {Γ W : Set S2} (h : IsComp Γ W) {z : S2} (hz : z ∈ W) :
    connectedComponentIn Γᶜ z = W :=
  (isComp_connectedComponentIn (h.subset hz)).eq h ⟨z, mem_connectedComponentIn (h.subset hz), hz⟩

/-- A side of a separation of `S² \ Γ` into two disjoint open sets is a component. -/
theorem isComp_of_sides {Γ U V : Set S2} (hU : IsOpen U) (hV : IsOpen V)
    (hUc : IsPreconnected U) (hUV : Disjoint U V) (hUVΓ : U ∪ V = Γᶜ) : IsComp Γ U := by
  refine ⟨hUVΓ ▸ subset_union_left, hUc, fun Y hY hYΓ hYU => ?_⟩
  exact hY.subset_left_of_subset_union hU hV hUV (hUVΓ ▸ hYΓ) hYU

variable {σ : E2 → S2}

theorem TwoSided.image_subset (hσ : IsOpenEmbedding σ) {Γ W : Set S2} {x : E2}
    {H₁ H₂ : Set E2} (h : TwoSided σ Γ x H₁ H₂) (hW : IsComp Γ W) (hx : σ x ∈ closure W) :
    σ '' H₁ ⊆ W ∨ σ '' H₂ ⊆ W := by
  obtain ⟨r, hr, hcov⟩ := h.cover
  have hopen : IsOpen (σ '' Metric.ball x r) := hσ.isOpenMap _ Metric.isOpen_ball
  obtain ⟨_, ⟨q, hq, rfl⟩, hqW⟩ := mem_closure_iff.1 hx _ hopen ⟨x, Metric.mem_ball_self hr, rfl⟩
  have hsub : ∀ H : Set E2, IsPreconnected H → (∀ q ∈ H, σ q ∉ Γ) → q ∈ H → σ '' H ⊆ W :=
    fun H hH hHΓ hqH => hW.maximal _ (hH.image σ hσ.continuous.continuousOn)
      (by rintro _ ⟨y, hy, rfl⟩; exact hHΓ y hy) ⟨σ q, mem_image_of_mem σ hqH, hqW⟩
  rcases hcov q hq (hW.subset hqW) with h1 | h2
  · exact Or.inl (hsub H₁ h.pre₁ h.avoid₁ h1)
  · exact Or.inr (hsub H₂ h.pre₂ h.avoid₂ h2)

/-- Two distinct components with `σ x` in their closure contain the two sides at `x`. -/
theorem TwoSided.two_comps (hσ : IsOpenEmbedding σ) {Γ W₁ W₂ : Set S2} {x : E2}
    {H₁ H₂ : Set E2} (h : TwoSided σ Γ x H₁ H₂) (hW₁ : IsComp Γ W₁) (hW₂ : IsComp Γ W₂)
    (hne : W₁ ≠ W₂) (hx₁ : σ x ∈ closure W₁) (hx₂ : σ x ∈ closure W₂) :
    (σ '' H₁ ⊆ W₁ ∧ σ '' H₂ ⊆ W₂) ∨ (σ '' H₁ ⊆ W₂ ∧ σ '' H₂ ⊆ W₁) := by
  have hd : ∀ H : Set E2, H.Nonempty → σ '' H ⊆ W₁ → σ '' H ⊆ W₂ → False :=
    fun H ⟨y, hy⟩ h1 h2 => hne (hW₁.eq hW₂ ⟨σ y, h1 ⟨y, hy, rfl⟩, h2 ⟨y, hy, rfl⟩⟩)
  rcases h.image_subset hσ hW₁ hx₁ with a | a <;> rcases h.image_subset hσ hW₂ hx₂ with b | b
  · exact (hd H₁ h.ne₁ a b).elim
  · exact Or.inl ⟨a, b⟩
  · exact Or.inr ⟨b, a⟩
  · exact (hd H₂ h.ne₂ a b).elim

/-- Every component with `σ x` in its closure is one of two given distinct ones. -/
theorem TwoSided.eq_or_eq (hσ : IsOpenEmbedding σ) {Γ W₁ W₂ X : Set S2} {x : E2}
    {H₁ H₂ : Set E2} (h : TwoSided σ Γ x H₁ H₂) (hW₁ : IsComp Γ W₁) (hW₂ : IsComp Γ W₂)
    (hne : W₁ ≠ W₂) (hx₁ : σ x ∈ closure W₁) (hx₂ : σ x ∈ closure W₂) (hX : IsComp Γ X)
    (hx : σ x ∈ closure X) : X = W₁ ∨ X = W₂ := by
  have key : ∀ H : Set E2, H.Nonempty → ∀ W, IsComp Γ W → σ '' H ⊆ X → σ '' H ⊆ W → X = W :=
    fun H ⟨y, hy⟩ W hW h1 h2 => hX.eq hW ⟨σ y, h1 ⟨y, hy, rfl⟩, h2 ⟨y, hy, rfl⟩⟩
  rcases h.two_comps hσ hW₁ hW₂ hne hx₁ hx₂ with ⟨a, b⟩ | ⟨a, b⟩ <;>
    rcases h.image_subset hσ hX hx with c | c
  · exact Or.inl (key H₁ h.ne₁ W₁ hW₁ c a)
  · exact Or.inr (key H₂ h.ne₂ W₂ hW₂ c b)
  · exact Or.inr (key H₁ h.ne₁ W₂ hW₂ c a)
  · exact Or.inl (key H₂ h.ne₂ W₁ hW₁ c b)

/-- The two half-balls at `x`, when near `x` the set `σ⁻¹ Γ` is the line `{q k = x k}`. -/
theorem twoSided_halfBalls {Γ : Set S2} {x : E2} {k : Fin 2} {r : ℝ} (hr : 0 < r)
    (hΓ : ∀ q ∈ Metric.ball x r, σ q ∈ Γ → q k = x k)
    (hdiam : ∀ q ∈ Metric.ball x r, q k = x k → σ q ∈ Γ) :
    TwoSided σ Γ x (halfBall x k r true) (halfBall x k r false) := by
  have havoid : ∀ pos, ∀ q ∈ halfBall x k r pos, σ q ∉ Γ := by
    intro pos q hq hqΓ
    have := hΓ q hq.1 hqΓ
    have h2 := hq.2
    cases pos <;> simp only [Bool.false_eq_true, ↓reduceIte, mem_setOf_eq] at h2 <;> linarith
  refine ⟨halfBall_nonempty x k hr _, halfBall_nonempty x k hr _,
    (convex_halfBall x k _ _).isPreconnected, (convex_halfBall x k _ _).isPreconnected,
    havoid true, havoid false, r, hr, fun q hq hqΓ => ?_⟩
  exact mem_halfBall_of_ne hq fun h => hqΓ (hdiam q hq h)

/-! ### Generic points -/

/-- If an open set `X ⊆ S² \ {N}` misses `σ x₀` with `x₀ ∉ Z`, `Z` countable, then its frontier
contains a point `σ x` with `x ∉ Z`. -/
theorem exists_generic_frontier (hσ : IsOpenEmbedding σ) {X : Set S2} (hX : IsOpen X)
    (hXne : X.Nonempty) (hXσ : X ⊆ range σ) {Z : Set E2} (hZ : Z.Countable) {x₀ : E2}
    (hx₀ : x₀ ∉ Z) (hx₀X : σ x₀ ∉ X) : ∃ x, x ∉ Z ∧ σ x ∈ frontier X := by
  by_contra hcon
  push Not at hcon
  have hpc := (hZ.isConnected_compl_of_one_lt_rank one_lt_rank_E2).isPreconnected
  have hU : IsOpen (σ ⁻¹' X) := hX.preimage hσ.continuous
  have hV : IsOpen (σ ⁻¹' (closure X)ᶜ) := isClosed_closure.isOpen_compl.preimage hσ.continuous
  have hcov : Zᶜ ⊆ σ ⁻¹' X ∪ σ ⁻¹' (closure X)ᶜ := by
    intro y hy
    by_cases hyc : σ y ∈ closure X
    · left
      have := hcon y hy
      rw [frontier, hX.interior_eq] at this
      by_contra hyX; exact this ⟨hyc, hyX⟩
    · exact Or.inr hyc
  have hdis : Disjoint (σ ⁻¹' X) (σ ⁻¹' (closure X)ᶜ) :=
    disjoint_compl_right.mono (preimage_mono subset_closure) (subset_refl _) |>.preimage σ
  rcases hpc.subset_or_subset hU hV hdis hcov with h | h
  · exact hx₀X (h hx₀)
  · obtain ⟨z, hz⟩ := hXne
    obtain ⟨y, rfl⟩ := hXσ hz
    obtain ⟨w, hw, hwZ⟩ := (hZ.dense_compl ℝ).inter_open_nonempty _ hU ⟨y, hz⟩
    exact h hwZ (subset_closure hw)

/-! ### The one-point compactification -/

theorem tendsto_cocompact_northPole (hσ : IsOpenEmbedding σ) (hσr : range σ = {northPole}ᶜ) :
    Tendsto σ (cocompact E2) (𝓝 northPole) := by
  rw [hasBasis_cocompact.tendsto_left_iff]
  intro N hN
  obtain ⟨U, hU₁, hU₂, hU₃⟩ := mem_nhds_iff.mp hN
  refine ⟨σ ⁻¹' Uᶜ, ?_, by simpa using (mapsTo_preimage σ U).mono_right hU₁⟩
  rw [hσ.isEmbedding.isCompact_iff, image_preimage_eq_iff.mpr (by simpa [hσr])]
  exact (isClosed_compl_iff.mpr hU₂).isCompact

theorem northPole_not_mem_closure_image (hσ : IsOpenEmbedding σ)
    (hσr : range σ = {northPole}ᶜ) {B : Set E2} (hB : Bornology.IsBounded B) :
    northPole ∉ closure (σ '' B) := by
  have hK : IsCompact (σ '' closure B) := hB.isCompact_closure.image hσ.continuous
  intro h
  obtain ⟨y, -, hy⟩ := closure_minimal (image_mono subset_closure) hK.isClosed h
  have : σ y ∈ range σ := mem_range_self y
  rw [hσr, hy] at this
  exact this rfl

/-! ### Cyclic lists -/

section Lists

variable {α : Type*}

theorem chainPairs_append_cons (l : List α) (a : α) (l' : List α) :
    chainPairs (l ++ a :: l') = chainPairs (l ++ [a]) ++ chainPairs (a :: l') := by
  induction l with
  | nil => simp [chainPairs]
  | cons x l ih =>
    cases l with
    | nil => simp [chainPairs]
    | cons y l =>
      simp only [List.cons_append] at ih ⊢
      simp only [chainPairs, ih, List.cons_append]

theorem fst_mem_of_mem_chainPairs_concat {l : List α} {x : α} {pr : α × α}
    (h : pr ∈ chainPairs (l ++ [x])) : pr.1 ∈ l := by
  induction l with
  | nil => simp [chainPairs] at h
  | cons y l ih =>
    cases l with
    | nil => simp [chainPairs] at h; simp [h]
    | cons z l =>
      simp only [List.cons_append, chainPairs, List.mem_cons] at h ih
      rcases h with rfl | h
      · simp
      · exact List.mem_cons_of_mem _ (List.mem_cons.2 (ih h))

theorem mem_chainPairs_iff {l : List α} {a b : α} :
    (a, b) ∈ chainPairs l ↔ ∃ l₁ l₂, l = l₁ ++ a :: b :: l₂ := by
  constructor
  · intro h
    induction l with
    | nil => simp [chainPairs] at h
    | cons x l ih =>
      cases l with
      | nil => simp [chainPairs] at h
      | cons y l =>
        simp only [chainPairs, List.mem_cons, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩ | h
        · exact ⟨[], l, rfl⟩
        · obtain ⟨l₁, l₂, hl⟩ := ih h
          exact ⟨x :: l₁, l₂, by rw [hl]; rfl⟩
  · rintro ⟨l₁, l₂, rfl⟩
    rw [chainPairs_append_cons]
    simp [chainPairs]

theorem exists_mem_cyc_fst {L : List α} {a : α} (ha : a ∈ L) : ∃ b, (a, b) ∈ cyc L := by
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem ha
  obtain ⟨b, r, hbr⟩ : ∃ b r, l₂ ++ (l₁ ++ a :: l₂).take 1 = b :: r := by
    cases l₁ with
    | nil => exact ⟨(l₂ ++ [a]).head (by simp), (l₂ ++ [a]).tail, by simp⟩
    | cons x l => exact ⟨(l₂ ++ [x]).head (by simp), (l₂ ++ [x]).tail, by simp⟩
  refine ⟨b, mem_chainPairs_iff.2 ⟨l₁, r, ?_⟩⟩
  rw [List.append_assoc, List.cons_append, hbr]

theorem getElem_mem_chainPairs (l : List α) (i : ℕ) (hi : i + 1 < l.length) :
    (l[i], l[i + 1]) ∈ chainPairs l := by
  induction l generalizing i with
  | nil => simp at hi
  | cons x l ih =>
    cases l with
    | nil => simp at hi
    | cons y l =>
      cases i with
      | zero => simp [chainPairs]
      | succ i =>
        simp only [chainPairs, List.mem_cons]
        right
        exact ih i (by simp only [List.length_cons] at hi ⊢; omega)

theorem getElem_mem_cyc (L : List α) (i : ℕ) (hi : i < L.length) (j : ℕ) (hj : j < L.length)
    (hij : j = (i + 1) % L.length) : (L[i], L[j]) ∈ cyc L := by
  unfold cyc
  have h := getElem_mem_chainPairs (L ++ L.take 1) i (by simp; omega)
  rcases Nat.lt_or_ge (i + 1) L.length with h1 | h1
  · obtain rfl : j = i + 1 := by rw [hij, Nat.mod_eq_of_lt h1]
    rwa [List.getElem_append_left hi, List.getElem_append_left h1] at h
  · have h2 : i + 1 = L.length := by omega
    obtain rfl : j = 0 := by rw [hij, h2, Nat.mod_self]
    rw [List.getElem_append_left hi, List.getElem_append_right (by omega)] at h
    simpa [h2] using h

/-- Insertion of a list `ns` between two cyclically consecutive entries `p`, `q` of a list
without repetitions. -/
theorem exists_insert {L : List α} (hL : L.Nodup) {p q : α} (h : (p, q) ∈ cyc L) (ns : List α) :
    ∃ L' : List α, ∃ A B : List (α × α), L'.Perm (L ++ ns) ∧
      cyc L = A ++ (p, q) :: B ∧ cyc L' = A ++ chainPairs (p :: (ns ++ [q])) ++ B ∧
      ∀ x ∈ A ++ B, x.1 ≠ p := by
  obtain ⟨l₁, l₂, hl⟩ := mem_chainPairs_iff.1 h
  have hne : L ≠ [] := by rintro rfl; simp [cyc, chainPairs] at h
  obtain ⟨a, L₀, rfl⟩ := List.exists_cons_of_ne_nil hne
  rw [show (a :: L₀) ++ (a :: L₀).take 1 = a :: L₀ ++ [a] from rfl] at hl
  rcases List.eq_nil_or_concat l₂ with rfl | ⟨l₂', a', rfl⟩
  · -- the closing pair: `q = a`
    have h1 : a :: L₀ ++ [a] = (l₁ ++ [p]) ++ [q] := by rw [hl]; simp
    obtain ⟨hL₀, h2⟩ := List.append_inj' h1 rfl
    obtain rfl : a = q := by simpa using h2
    refine ⟨a :: L₀ ++ ns, chainPairs (l₁ ++ [p]), [], List.Perm.refl _, ?_, ?_, ?_⟩
    · rw [cyc]; simp only [List.take_succ_cons, List.take_zero]; rw [hl]
      rw [chainPairs_append_cons]; simp [chainPairs]
    · rw [cyc, hL₀]
      have : (l₁ ++ [p] ++ ns ++ (l₁ ++ [p] ++ ns).take 1) = l₁ ++ p :: (ns ++ [a]) := by
        have hh : (l₁ ++ [p] ++ ns).take 1 = [a] := by
          rw [← hL₀]; simp
        rw [hh]; simp
      rw [this, chainPairs_append_cons]; simp
    · intro x hx
      simp only [List.append_nil] at hx
      have := fst_mem_of_mem_chainPairs_concat hx
      have hnd : (l₁ ++ [p]).Nodup := hL₀ ▸ hL
      intro hxp; rw [hxp] at this
      exact (List.nodup_append.1 hnd).2.2 _ this _ (List.mem_singleton_self p) rfl
  · -- an inner pair: `a' = a`
    have h1 : a :: L₀ ++ [a] = (l₁ ++ p :: q :: l₂') ++ [a'] := by rw [hl]; simp
    obtain ⟨hL₀, h2⟩ := List.append_inj' h1 rfl
    obtain rfl : a = a' := by simpa using h2
    have hhead : (l₁ ++ p :: (ns ++ q :: l₂')).take 1 = [a] := by
      cases l₁ with
      | nil => simp at hL₀; simp [hL₀.1]
      | cons y l => simp at hL₀; simp [hL₀.1]
    refine ⟨l₁ ++ p :: (ns ++ q :: l₂'), chainPairs (l₁ ++ [p]), chainPairs (q :: (l₂' ++ [a])),
      ?_, ?_, ?_, ?_⟩
    · rw [hL₀]
      have h3 := ((List.perm_append_comm (l₁ := ns) (l₂ := q :: l₂')).cons p).append_left l₁
      simpa using h3
    · rw [cyc]; simp only [List.take_succ_cons, List.take_zero]; rw [hl]
      rw [chainPairs_append_cons]; simp [chainPairs]
    · rw [cyc, hhead]
      rw [show l₁ ++ p :: (ns ++ q :: l₂') ++ [a] = l₁ ++ p :: (ns ++ q :: (l₂' ++ [a])) by simp]
      rw [chainPairs_append_cons]
      have := chainPairs_append_cons (p :: ns) q (l₂' ++ [a])
      simp only [List.cons_append] at this
      rw [this, List.append_assoc]
    · intro x hx hxp
      have hnd : (l₁ ++ p :: q :: l₂').Nodup := hL₀ ▸ hL
      rw [List.mem_append] at hx
      rcases hx with hx | hx
      · have := fst_mem_of_mem_chainPairs_concat hx
        rw [hxp] at this
        exact (List.nodup_append.1 hnd).2.2 _ this _ (List.mem_cons_self) rfl
      · have := fst_mem_of_mem_chainPairs_concat (l := q :: l₂') (by simpa using hx)
        rw [hxp] at this
        exact (List.nodup_cons.1 (List.nodup_append.1 hnd).2.1).1 this

end Lists

/-! ### The boundary walk of a set of cells

Cells are indexed by `c ∈ ℤ²` (centre `c / 2`, side `1 / 2`); the vertices of the walk are the
corners `m ∈ ℤ²` (the point `((2 m₁ + 1) / 4, (2 m₂ + 1) / 4)`). The side of the cell `c` with
outward normal `n` is traversed counterclockwise from `sideStart c n` to `sideEnd c n`. -/

theorem side_inj {c c' : ℤ × ℤ} {n n' : Dir} (h1 : sideStart c n = sideStart c' n')
    (h2 : sideEnd c n = sideEnd c' n') : c = c' ∧ n = n' := by
  obtain ⟨c1, c2⟩ := c
  obtain ⟨c1', c2'⟩ := c'
  cases n <;> cases n' <;> simp [sideStart, sideEnd, Prod.ext_iff] at h1 h2 ⊢ <;> omega

theorem sideStart_corner (c : ℤ × ℤ) (n : Dir) :
    c = sideStart c n ∨ c = sideStart c n + (1, 0) ∨ c = sideStart c n + (0, 1) ∨
      c = sideStart c n + (1, 1) := by
  obtain ⟨c1, c2⟩ := c
  cases n <;> simp [sideStart, Prod.ext_iff]

/-- The boundary walk of a single cell. -/
theorem walkProps_singleton (c : ℤ × ℤ) :
    WalkProps {c} [sideStart c .S, sideStart c .E, sideStart c .N, sideStart c .W] := by
  obtain ⟨c1, c2⟩ := c
  have hv : ∀ n : Dir, (c1, c2) + n.v ≠ (c1, c2) := fun n => by
    cases n <;> simp [Dir.v, Prod.ext_iff]
  refine ⟨?_, by simp, ?_, ?_⟩
  · simp [sideStart, Prod.ext_iff]; omega
  · intro x hx
    simp only [cyc, chainPairs, List.take, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨_, .S, rfl, hv _, by simp [sideStart, sideEnd]⟩
    · exact ⟨_, .E, rfl, hv _, by simp [sideStart, sideEnd]⟩
    · exact ⟨_, .N, rfl, hv _, by simp [sideStart, sideEnd]⟩
    · exact ⟨_, .W, rfl, hv _, by simp [sideStart, sideEnd]⟩
  · rintro c' n rfl -
    simp only [cyc, chainPairs, List.take, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false]
    cases n <;> simp [sideStart, sideEnd]

section Finger

variable {S : Set (ℤ × ℤ)} {c₀ : ℤ × ℤ} {d : Dir}

/-- The cells which are not in `S` in the finger construction: the new cells `m = c₀ + d`,
`w = c₀ + 2d`, the face cells and the neighbours of `w`. -/
def FingerBad (c₀ : ℤ × ℤ) (d : Dir) (c : ℤ × ℤ) : Prop :=
  c = c₀ + d.v ∨ c = c₀ + d.v + d.v ∨ (c.1 % 2 = 1 ∧ c.2 % 2 = 1) ∨
    c = c₀ + d.v + d.v + Dir.E.v ∨ c = c₀ + d.v + d.v + Dir.N.v ∨
    c = c₀ + d.v + d.v + Dir.W.v ∨ c = c₀ + d.v + d.v + Dir.S.v

theorem not_mem_of_fingerBad (hm : c₀ + d.v ∉ S) (hw : c₀ + d.v + d.v ∉ S)
    (hface : ∀ c ∈ S, ¬ (c.1 % 2 = 1 ∧ c.2 % 2 = 1)) (hnbr : ∀ n : Dir, c₀ + d.v + d.v + n.v ∉ S)
    {c : ℤ × ℤ} (hc : FingerBad c₀ d c) : c ∉ S := by
  rcases hc with rfl | rfl | h | rfl | rfl | rfl | rfl
  · exact hm
  · exact hw
  · exact fun hc => hface c hc h
  all_goals exact hnbr _

/-- The four new corners of the finger. -/
def fingerCorners (c₀ : ℤ × ℤ) (d : Dir) : List (ℤ × ℤ) :=
  [sideStart (c₀ + d.v + d.v) d.rot.neg, sideStart (c₀ + d.v + d.v) d,
    sideStart (c₀ + d.v + d.v) d.rot, sideStart (c₀ + d.v) d.rot]

/-- The five new sides of the finger, as (cell, normal). -/
def fingerSides (c₀ : ℤ × ℤ) (d : Dir) : List ((ℤ × ℤ) × Dir) :=
  [(c₀ + d.v, d.rot.neg), (c₀ + d.v + d.v, d.rot.neg), (c₀ + d.v + d.v, d),
    (c₀ + d.v + d.v, d.rot), (c₀ + d.v, d.rot)]

theorem chainPairs_finger (c₀ : ℤ × ℤ) (d : Dir) :
    chainPairs (sideStart c₀ d :: (fingerCorners c₀ d ++ [sideEnd c₀ d])) =
      (fingerSides c₀ d).map fun cn => (sideStart cn.1 cn.2, sideEnd cn.1 cn.2) := by
  obtain ⟨a, b⟩ := c₀
  cases d <;> simp [chainPairs, fingerCorners, fingerSides, sideStart, sideEnd, Dir.v, Dir.rot,
    Dir.neg, Prod.ext_iff] <;> omega


theorem add_v_neg (x : ℤ × ℤ) (d : Dir) : x + d.v + d.neg.v = x := by
  obtain ⟨a, b⟩ := x; cases d <;> simp [Dir.v, Dir.neg]

theorem eq_or_fingerBad_of_add_eq_m {c₀ c : ℤ × ℤ} {d n : Dir} (heven : c₀.1 % 2 = 0 ∧ c₀.2 % 2 = 0)
    (h : c + n.v = c₀ + d.v) : (c = c₀ ∧ n = d) ∨ FingerBad c₀ d c := by
  obtain ⟨a, b⟩ := c₀; obtain ⟨c1, c2⟩ := c
  cases n <;> cases d <;> simp [FingerBad, Dir.v, Prod.ext_iff] at h heven ⊢ <;> omega

theorem fingerBad_of_add_eq_w {c₀ c : ℤ × ℤ} {d n : Dir} (h : c + n.v = c₀ + d.v + d.v) :
    FingerBad c₀ d c := by
  obtain ⟨a, b⟩ := c₀; obtain ⟨c1, c2⟩ := c
  cases n <;> cases d <;> simp [FingerBad, Dir.v, Prod.ext_iff] at h ⊢ <;> omega

theorem m_cases (d n : Dir) : n = d ∨ n = d.neg ∨ (n = d.rot.neg ∨ n = d.rot) := by
  cases n <;> cases d <;> simp [Dir.rot, Dir.neg]

theorem w_cases (d n : Dir) : n = d.neg ∨ (n = d.rot.neg ∨ n = d ∨ n = d.rot) := by
  cases n <;> cases d <;> simp [Dir.rot, Dir.neg]


theorem fingerBad_of_corner {c₀ c y : ℤ × ℤ} {d : Dir} (heven : c₀.1 % 2 = 0 ∧ c₀.2 % 2 = 0)
    (hy : y ∈ fingerCorners c₀ d)
    (hc : c = y ∨ c = y + (1, 0) ∨ c = y + (0, 1) ∨ c = y + (1, 1)) : FingerBad c₀ d c := by
  obtain ⟨a, b⟩ := c₀
  simp only [fingerCorners, List.mem_cons, List.not_mem_nil, or_false] at hy
  simp only at heven
  rcases hy with rfl | rfl | rfl | rfl <;> cases d <;> rcases hc with rfl | rfl | rfl | rfl <;>
    simp [FingerBad, sideStart, Dir.v, Dir.rot, Dir.neg, Prod.ext_iff] <;> omega

theorem fingerSides_spec {c₀ c : ℤ × ℤ} {d n : Dir} (heven : c₀.1 % 2 = 0 ∧ c₀.2 % 2 = 0)
    (hcn : (c, n) ∈ fingerSides c₀ d) :
    (c = c₀ + d.v ∨ c = c₀ + d.v + d.v) ∧ c + n.v ≠ c₀ + d.v ∧ c + n.v ≠ c₀ + d.v + d.v ∧
      FingerBad c₀ d (c + n.v) := by
  obtain ⟨a, b⟩ := c₀
  simp only at heven
  cases d <;>
    simp only [fingerSides, Dir.rot, Dir.neg, List.mem_cons, List.not_mem_nil, or_false,
      Prod.mk.injEq] at hcn <;>
    rcases hcn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [FingerBad, Dir.v, Prod.ext_iff] <;> omega

/-- Growing a set of cells by a finger `m = c₀ + d`, `w = c₀ + 2d` attached to a cell `c₀`
(the image of a new edge and a new vertex of the tree): insert the four new corners in the
boundary walk between the ends of the side of `c₀` facing `d`. -/
theorem WalkProps.finger {L : List (ℤ × ℤ)} (hW : WalkProps S L) (hc₀ : c₀ ∈ S)
    (hm : c₀ + d.v ∉ S) (hw : c₀ + d.v + d.v ∉ S) (hface : ∀ c ∈ S, ¬ (c.1 % 2 = 1 ∧ c.2 % 2 = 1))
    (hnbr : ∀ n : Dir, c₀ + d.v + d.v + n.v ∉ S) (heven : c₀.1 % 2 = 0 ∧ c₀.2 % 2 = 0) :
    ∃ L', WalkProps (insert (c₀ + d.v) (insert (c₀ + d.v + d.v) S)) L' := by
  have hbad : ∀ {c}, FingerBad c₀ d c → c ∉ S := fun h => not_mem_of_fingerBad hm hw hface hnbr h
  have hpq := hW.complete c₀ d hc₀ hm
  obtain ⟨L', A, B, hperm, hL, hL', hAB⟩ := exists_insert hW.nodup hpq (fingerCorners c₀ d)
  rw [chainPairs_finger] at hL'
  have hold : ∀ x ∈ A ++ B, x ∈ cyc L := fun x hx => by
    rw [hL]; rcases List.mem_append.1 hx with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
  have hnew : ∀ cn ∈ fingerSides c₀ d, (sideStart cn.1 cn.2, sideEnd cn.1 cn.2) ∈ cyc L' :=
    fun cn hcn => by
      rw [hL']; exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨cn, hcn, rfl⟩))
  refine ⟨L', ⟨?_, ?_, ?_, ?_⟩⟩
  · -- no repetitions
    rw [hperm.nodup_iff, List.nodup_append]
    refine ⟨hW.nodup, ?_, ?_⟩
    · obtain ⟨a, b⟩ := c₀
      cases d <;> simp [fingerCorners, sideStart, Dir.v, Dir.rot, Dir.neg, Prod.ext_iff] <;> omega
    · intro x hx y hy hxy
      subst hxy
      obtain ⟨z, hz⟩ := exists_mem_cyc_fst hx
      obtain ⟨c, n, hc, -, hcn⟩ := hW.sound _ hz
      have hxc : x = sideStart c n := (Prod.ext_iff.1 hcn).1
      refine hbad ?_ hc
      have hcorner := sideStart_corner c n
      rw [← hxc] at hcorner
      exact fingerBad_of_corner heven hy hcorner
  · have := hperm.length_eq
    have := hW.length
    simp [fingerCorners] at *
    omega
  · -- every consecutive pair is a boundary side
    intro x hx
    rw [hL', List.mem_append, List.mem_append] at hx
    rcases hx with (hx | hx) | hx
    rotate_left
    · obtain ⟨⟨c, n⟩, hcn, rfl⟩ := List.mem_map.1 hx
      obtain ⟨hc, h1, h2, h3⟩ := fingerSides_spec heven hcn
      refine ⟨c, n, ?_, ?_, rfl⟩
      · rcases hc with rfl | rfl
        · exact Set.mem_insert _ _
        · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
      · simp only [Set.mem_insert_iff, not_or]
        exact ⟨h1, h2, hbad h3⟩
    all_goals
      have hx' : x ∈ A ++ B := by rw [List.mem_append]; first | exact Or.inl hx | exact Or.inr hx
      obtain ⟨c, n, hc, hcn, rfl⟩ := hW.sound x (hold x hx')
      refine ⟨c, n, Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ hc), ?_, rfl⟩
      simp only [Set.mem_insert_iff, not_or]
      refine ⟨fun h => ?_, fun h => hbad (fingerBad_of_add_eq_w h) hc, hcn⟩
      rcases eq_or_fingerBad_of_add_eq_m heven h with ⟨rfl, rfl⟩ | h
      · exact hAB _ hx' rfl
      · exact hbad h hc
  · -- every boundary side is a consecutive pair
    intro c n hc hcn
    simp only [Set.mem_insert_iff, not_or] at hc hcn
    obtain ⟨hcm, hcw, hcS⟩ := hcn
    rcases hc with rfl | rfl | hc
    · rcases m_cases d n with rfl | rfl | hn
      · exact absurd rfl hcw
      · exact absurd (by rw [add_v_neg]; exact hc₀) hcS
      · refine hnew (c₀ + d.v, n) ?_
        simp only [fingerSides, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]
        tauto
    · rcases w_cases d n with rfl | hn
      · exact absurd (by rw [add_v_neg]) hcm
      · refine hnew (c₀ + d.v + d.v, n) ?_
        simp only [fingerSides, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]
        tauto
    · have h := hW.complete c n hc hcS
      rw [hL] at h
      rcases List.mem_append.1 h with h | h
      · rw [hL']; exact List.mem_append_left _ (List.mem_append_left _ h)
      · rcases List.mem_cons.1 h with h | h
        · obtain ⟨rfl, rfl⟩ := side_inj (Prod.ext_iff.1 h).1 (Prod.ext_iff.1 h).2
          exact absurd rfl hcm
        · rw [hL']; exact List.mem_append_right _ h

end Finger

/-! ### Spanning trees of the connectors and their boundary walks -/

theorem pr_injective : Injective pr := fun a b h => by
  funext k; fin_cases k
  · exact (Prod.ext_iff.1 h).1
  · exact (Prod.ext_iff.1 h).2

theorem exists_dir_of_adj {a b : Vertex 2} (h : (lattice 2).Adj a b) :
    ∃ d : Dir, pr b = pr a + d.v := by
  obtain ⟨i, rfl | rfl⟩ := h <;> fin_cases i
  · exact ⟨.E, by simp [pr, LatticeProb.unit, Dir.v]⟩
  · exact ⟨.N, by simp [pr, LatticeProb.unit, Dir.v]⟩
  · exact ⟨.W, by simp [pr, LatticeProb.unit, Dir.v]⟩
  · exact ⟨.S, by simp [pr, LatticeProb.unit, Dir.v]⟩

theorem double_add_v_eq {a x : ℤ × ℤ} {d₁ n : Dir} (h : a + a + d₁.v = x + x + n.v) :
    (a = x ∨ a + d₁.v = x) ∧ (a + d₁.v = x + n.v ∨ a = x + n.v) := by
  obtain ⟨a1, a2⟩ := a; obtain ⟨x1, x2⟩ := x
  cases d₁ <;> cases n <;> simp [Dir.v, Prod.ext_iff] at h ⊢ <;> omega

theorem double_add_v_ne {a x : ℤ × ℤ} {d₁ : Dir} : a + a + d₁.v ≠ x + x := by
  obtain ⟨a1, a2⟩ := a; obtain ⟨x1, x2⟩ := x
  cases d₁ <;> simp [Dir.v, Prod.ext_iff] <;> omega

theorem double_inj {a x : ℤ × ℤ} (h : a + a = x + x) : a = x := by
  obtain ⟨a1, a2⟩ := a; obtain ⟨x1, x2⟩ := x
  simp [Prod.ext_iff] at h ⊢; omega

section Tree

variable {ω : Configuration 2} {C : OpenComponent ω}

theorem lattice_adj_of_adj {a b : C} (h : (componentGraph C).Adj a b) :
    (lattice 2).Adj a.val b.val :=
  openGraph_le ω ((C.toSimpleGraph_adj _ _).1 h)

/-- The cells of the vertices and of the edges. -/
def cells (V : Set C) (E : Set (C × C)) : Set (ℤ × ℤ) :=
  {c | (∃ a ∈ V, c = vcell a.val) ∨ ∃ e ∈ E, c = ecell e.1.val e.2.val}

theorem ecell_eq_of_dir {a b : Vertex 2} {d : Dir} (h : pr b = pr a + d.v) :
    ecell a b = pr a + pr a + d.v := by rw [ecell, h, add_assoc]

theorem cells_face {T V : Set C} {E : Set (C × C)} (hT : TreeData T V E) {c : ℤ × ℤ}
    (hc : c ∈ cells V E) : ¬ (c.1 % 2 = 1 ∧ c.2 % 2 = 1) := by
  rcases hc with ⟨a, -, rfl⟩ | ⟨e, he, rfl⟩
  · simp [vcell, pr]; omega
  · obtain ⟨d, hd⟩ := exists_dir_of_adj (lattice_adj_of_adj (hT.edge e he).2.2)
    rw [ecell_eq_of_dir hd]
    obtain ⟨x1, x2⟩ := pr e.1.val
    cases d <;> simp [Dir.v] <;> omega

/-- Growing the tree by an edge `uv` of `𝒞_∞` from `u ∈ V` to `v ∈ T \ V`. -/
theorem TreeData.grow {T V : Set C} {E : Set (C × C)} (hT : TreeData T V E) {u v : C}
    (hu : u ∈ V) (hvT : v ∈ T) (hv : v ∉ V) (huv : (componentGraph C).Adj u v)
    {L : List (ℤ × ℤ)} (hL : WalkProps (cells V E) L) :
    TreeData T (insert v V) (insert (u, v) E) ∧
      ∃ L', WalkProps (cells (insert v V) (insert (u, v) E)) L' := by
  obtain ⟨d, hd⟩ := exists_dir_of_adj (lattice_adj_of_adj huv)
  set c₀ := pr u.val + pr u.val with hc₀
  have hvc : vcell v.val = c₀ + d.v + d.v := by
    rw [vcell, hd, hc₀]; abel
  have hec : ecell u.val v.val = c₀ + d.v := ecell_eq_of_dir hd
  have hcells : cells (insert v V) (insert (u, v) E) =
      insert (c₀ + d.v) (insert (c₀ + d.v + d.v) (cells V E)) := by
    ext c
    simp only [cells, Set.mem_insert_iff, Set.mem_setOf_eq, exists_eq_or_imp]
    rw [← hvc, ← hec]
    constructor
    · rintro ((h | h) | h | h)
      exacts [Or.inr (Or.inl h), Or.inr (Or.inr (Or.inl h)), Or.inl h, Or.inr (Or.inr (Or.inr h))]
    · rintro (h | h | h | h)
      exacts [Or.inr (Or.inl h), Or.inl (Or.inl h), Or.inl (Or.inr h), Or.inr (Or.inr h)]
  -- the edges of `E` with an endpoint at a given vertex
  have hEdge : ∀ e ∈ E, ∃ d₁ : Dir, pr e.2.val = pr e.1.val + d₁.v := fun e he =>
    exists_dir_of_adj (lattice_adj_of_adj (hT.edge e he).2.2)
  have hvV : ∀ a : C, pr a.val = pr v.val → a ∈ V → False := fun a ha haV =>
    hv (by rwa [← Subtype.ext (pr_injective ha)])
  refine ⟨⟨?_, hT.finite.insert v, ?_, ?_⟩, ?_⟩
  · exact Set.insert_subset hvT hT.sub
  · rintro e (rfl | he)
    · exact ⟨Set.mem_insert_of_mem _ hu, Set.mem_insert _ _, huv⟩
    · obtain ⟨h1, h2, h3⟩ := hT.edge e he
      exact ⟨Set.mem_insert_of_mem _ h1, Set.mem_insert_of_mem _ h2, h3⟩
  · have hmono : treeGraph E ≤ treeGraph (insert (u, v) E) := fun a b h => by
      simp only [treeGraph, SimpleGraph.fromRel_adj] at h ⊢
      exact ⟨h.1, h.2.imp (Set.mem_insert_of_mem _) (Set.mem_insert_of_mem _)⟩
    have huv' : (treeGraph (insert (u, v) E)).Adj u v := by
      simp only [treeGraph, SimpleGraph.fromRel_adj]
      exact ⟨huv.ne, Or.inl (Set.mem_insert _ _)⟩
    have hreach : ∀ a ∈ V, (treeGraph (insert (u, v) E)).Reachable a v := fun a ha =>
      ((hT.conn a ha u hu).mono hmono).trans huv'.reachable
    rintro a (rfl | ha) b (rfl | hb)
    · rfl
    · exact (hreach b hb).symm
    · exact hreach a ha
    · exact (hT.conn a ha b hb).mono hmono
  · rw [hcells]
    refine hL.finger ?_ ?_ ?_ (fun c hc => cells_face hT hc) ?_ ?_
    · exact Or.inl ⟨u, hu, rfl⟩
    · rintro (⟨a, ha, h⟩ | ⟨e, he, h⟩)
      · exact double_add_v_ne h
      · obtain ⟨d₁, hd₁⟩ := hEdge e he
        rw [ecell_eq_of_dir hd₁] at h
        obtain ⟨-, h2 | h2⟩ := double_add_v_eq h.symm
        · rw [← hd₁, ← hd] at h2; exact hvV _ h2 (hT.edge e he).2.1
        · rw [← hd] at h2; exact hvV _ h2 (hT.edge e he).1
    · rintro (⟨a, ha, h⟩ | ⟨e, he, h⟩)
      · rw [← hvc] at h
        exact hvV a (double_inj h.symm) ha
      · obtain ⟨d₁, hd₁⟩ := hEdge e he
        rw [ecell_eq_of_dir hd₁, ← hvc] at h
        exact double_add_v_ne h.symm
    · intro n hn
      rw [← hvc] at hn
      rcases hn with ⟨a, ha, h⟩ | ⟨e, he, h⟩
      · exact double_add_v_ne h
      · obtain ⟨d₁, hd₁⟩ := hEdge e he
        rw [ecell_eq_of_dir hd₁] at h
        obtain ⟨h2 | h2, -⟩ := double_add_v_eq h.symm
        · exact hvV _ h2 (hT.edge e he).1
        · rw [← hd₁] at h2; exact hvV _ h2 (hT.edge e he).2.1
    · simp [hc₀]; omega

/-- The connectors carry a spanning tree whose cells have a boundary walk. -/
theorem exists_tree_walk {T : Set C} (hTf : T.Finite) (hTc : Rigidity.Section5.IsConnectedSet C T)
    (hTne : T.Nonempty) : ∃ E L, TreeData T T E ∧ WalkProps (cells T E) L := by
  suffices h : ∀ k, k < T.ncard → ∃ V E L, V.ncard = k + 1 ∧ TreeData T V E ∧
      WalkProps (cells V E) L by
    have hpos : 0 < T.ncard := (Set.ncard_pos hTf).2 hTne
    obtain ⟨V, E, L, hV, hT, hL⟩ := h (T.ncard - 1) (by omega)
    have hVT : V = T := Set.eq_of_subset_of_ncard_le hT.sub (by omega) hTf
    subst hVT
    exact ⟨E, L, hT, hL⟩
  intro k
  induction k with
  | zero =>
    intro _
    obtain ⟨t, ht⟩ := hTne
    refine ⟨{t}, ∅, [sideStart (vcell t.val) .S, sideStart (vcell t.val) .E,
      sideStart (vcell t.val) .N, sideStart (vcell t.val) .W], Set.ncard_singleton t,
      ⟨Set.singleton_subset_iff.2 ht, Set.finite_singleton t, fun e he => he.elim, ?_⟩, ?_⟩
    · rintro a rfl b rfl; rfl
    · have : cells {t} (∅ : Set (C × C)) = {vcell t.val} := by
        ext c; simp [cells]
      rw [this]
      exact walkProps_singleton _
  | succ k ih =>
    intro hk
    obtain ⟨V, E, L, hV, hT, hL⟩ := ih (by omega)
    obtain ⟨y, hyT, hyV⟩ : (T \ V).Nonempty := by
      rw [Set.nonempty_iff_ne_empty, Ne, Set.sdiff_eq_empty]
      intro h
      have := Set.ncard_le_ncard h hT.finite
      omega
    obtain ⟨x, hx⟩ : V.Nonempty := by
      rw [← Set.ncard_pos hT.finite]; omega
    obtain ⟨hxT, hyT', ⟨p⟩⟩ := hTc x (hT.sub hx) y hyT
    obtain ⟨dt, -, hd1, hd2⟩ := p.exists_boundary_dart {z | z.val ∈ V} hx hyV
    have hadj : (componentGraph C).Adj dt.fst.val dt.snd.val := by
      have := dt.adj
      simpa using this
    obtain ⟨hT', L', hL'⟩ := hT.grow hd1 dt.snd.prop hd2 hadj hL
    exact ⟨_, _, L', by rw [Set.ncard_insert_of_notMem (s := V) (show dt.snd.val ∉ V from hd2) hT.finite, hV], hT', hL'⟩

end Tree

/-! ### Cells in the plane -/

/-- The corner `m` of the walk, as a point of the plane: `((2 m₁ + 1) / 4, (2 m₂ + 1) / 4)`. -/
noncomputable def mpt (m : ℤ × ℤ) : E2 := pt ((2 * m.1 + 1) / 4) ((2 * m.2 + 1) / 4)

/-- The closed cell `c`: the square of side `1 / 2` centred at `c / 2`. -/
def Cell (c : ℤ × ℤ) : Set E2 := {p | |p 0 - c.1 / 2| ≤ 1 / 4 ∧ |p 1 - c.2 / 2| ≤ 1 / 4}

theorem isClosed_cell (c : ℤ × ℤ) : IsClosed (Cell c) := by
  have : Cell c = {p : E2 | |p 0 - c.1 / 2| ≤ 1 / 4} ∩ {p : E2 | |p 1 - c.2 / 2| ≤ 1 / 4} := rfl
  rw [this]
  exact (isClosed_le (((EuclideanSpace.proj (0 : Fin 2) : E2 →L[ℝ] ℝ).continuous.sub
    continuous_const).abs) continuous_const).inter (isClosed_le (((EuclideanSpace.proj (1 : Fin 2) :
      E2 →L[ℝ] ℝ).continuous.sub continuous_const).abs) continuous_const)

theorem coords_of_mem_segment {a b p : E2} (h : p ∈ segment ℝ a b) :
    ∃ t ∈ Icc (0 : ℝ) 1, ∀ k, p k = a k + t * (b k - a k) := by
  rw [segment_eq_image'] at h
  obtain ⟨t, ht, rfl⟩ := h
  exact ⟨t, ht, fun k => by simp⟩

/-- The side of a cell is the intersection with the neighbouring cell. -/
theorem side_eq_inter (c : ℤ × ℤ) (n : Dir) :
    segment ℝ (mpt (sideStart c n)) (mpt (sideEnd c n)) = Cell c ∩ Cell (c + n.v) := by
  obtain ⟨c1, c2⟩ := c
  ext p
  constructor
  · intro hp
    obtain ⟨t, ⟨ht0, ht1⟩, hpt⟩ := coords_of_mem_segment hp
    have h0 := hpt 0
    have h1 := hpt 1
    cases n <;> simp only [mpt, sideStart, sideEnd, pt_zero, pt_one] at h0 h1 <;>
      push_cast at h0 h1 <;>
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp only [Dir.v, Prod.fst_add, Prod.snd_add] <;> push_cast <;>
      rw [abs_le] <;> constructor <;> linarith
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    rw [abs_le] at h1 h2 h3 h4
    cases n <;> simp only [Dir.v, Prod.fst_add, Prod.snd_add, sideStart, sideEnd] at h3 h4 ⊢ <;>
      push_cast at h3 h4
    · exact mem_segment_of_axis (k := 0) (e := 1) (by decide) (by simp [mpt])
        (by simp [mpt]; linarith) (by simp [mpt]; linarith) (by simp [mpt]; linarith)
    · rw [segment_symm]
      exact mem_segment_of_axis (k := 1) (e := 0) (by decide) (by simp [mpt])
        (by simp [mpt]; linarith) (by simp [mpt]; linarith) (by simp [mpt]; linarith)
    · rw [segment_symm]
      exact mem_segment_of_axis (k := 0) (e := 1) (by decide) (by simp [mpt])
        (by simp [mpt]; linarith) (by simp [mpt]; linarith) (by simp [mpt]; linarith)
    · exact mem_segment_of_axis (k := 1) (e := 0) (by decide) (by simp [mpt])
        (by simp [mpt]; linarith) (by simp [mpt]; linarith) (by simp [mpt]; linarith)

/-- One coordinate: near `x`, every `y` lies in a half-integer interval `[m/2 - 1/4, m/2 + 1/4]`
which also contains `x`. -/
theorem exists_cover_1d (x : ℝ) : ∃ δ > 0, ∀ y, |y - x| < δ →
    ∃ m : ℤ, |y - m / 2| ≤ 1 / 4 ∧ |x - m / 2| ≤ 1 / 4 := by
  set m₀ := ⌊2 * x + 1 / 2⌋ with hm₀
  have h1 := Int.floor_le (2 * x + 1 / 2)
  have h2 := Int.lt_floor_add_one (2 * x + 1 / 2)
  rw [← hm₀] at h1 h2
  rcases lt_or_eq_of_le h1 with h | h
  · refine ⟨1 / 4 - |x - m₀ / 2|, ?_, fun y hy => ⟨m₀, ?_, ?_⟩⟩
    · show 0 < 1 / 4 - |x - m₀ / 2|
      rw [sub_pos, abs_lt]; constructor <;> linarith
    · calc |y - m₀ / 2| ≤ |y - x| + |x - m₀ / 2| := abs_sub_le _ _ _
        _ ≤ 1 / 4 := by linarith
    · rw [abs_le]; constructor <;> linarith
  · refine ⟨1 / 4, by norm_num, fun y hy => ?_⟩
    rw [abs_lt] at hy
    rcases le_total x y with hxy | hxy
    · exact ⟨m₀, by rw [abs_le]; constructor <;> linarith, by rw [abs_le]; constructor <;> linarith⟩
    · exact ⟨m₀ - 1, by push_cast; rw [abs_le]; constructor <;> linarith,
        by push_cast; rw [abs_le]; constructor <;> linarith⟩

/-- Near `p`, every point lies in a cell which also contains `p`. -/
theorem exists_cell_cover (p : E2) : ∃ δ > 0, ∀ q ∈ Metric.ball p δ,
    ∃ c : ℤ × ℤ, q ∈ Cell c ∧ p ∈ Cell c := by
  obtain ⟨δ₀, hδ₀, h₀⟩ := exists_cover_1d (p 0)
  obtain ⟨δ₁, hδ₁, h₁⟩ := exists_cover_1d (p 1)
  refine ⟨min δ₀ δ₁, lt_min hδ₀ hδ₁, fun q hq => ?_⟩
  have hd : ∀ j, |q j - p j| < min δ₀ δ₁ := fun j => by
    rw [Metric.mem_ball] at hq
    have := (PiLp.dist_apply_le q p j).trans_lt hq
    rwa [Real.dist_eq] at this
  obtain ⟨m₀, hm₀, hm₀'⟩ := h₀ (q 0) ((hd 0).trans_le (min_le_left _ _))
  obtain ⟨m₁, hm₁, hm₁'⟩ := h₁ (q 1) ((hd 1).trans_le (min_le_right _ _))
  exact ⟨(m₀, m₁), ⟨hm₀, hm₁⟩, ⟨hm₀', hm₁'⟩⟩

theorem int_le_of_cast {m : ℤ} {x : ℝ} (h : (m : ℝ) ≤ x) (hx : x < 1) : m ≤ 0 := by
  have : (m : ℝ) < 1 := h.trans_lt hx
  have : m < 1 := by exact_mod_cast this
  omega

/-- Two cells containing a common point differ by at most one in each coordinate. -/
theorem cell_coord_close {p : E2} {c c' : ℤ × ℤ} (h : p ∈ Cell c) (h' : p ∈ Cell c') :
    |c.1 - c'.1| ≤ 1 ∧ |c.2 - c'.2| ≤ 1 := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  rw [abs_le] at h1 h2 h1' h2'
  have a1 : ((c.1 - c'.1 - 1 : ℤ) : ℝ) ≤ 0 := by push_cast; linarith
  have a2 : ((c'.1 - c.1 - 1 : ℤ) : ℝ) ≤ 0 := by push_cast; linarith
  have a3 : ((c.2 - c'.2 - 1 : ℤ) : ℝ) ≤ 0 := by push_cast; linarith
  have a4 : ((c'.2 - c.2 - 1 : ℤ) : ℝ) ≤ 0 := by push_cast; linarith
  have b1 := int_le_of_cast (m := c.1 - c'.1 - 1) le_rfl (by linarith)
  have b2 := int_le_of_cast (m := c'.1 - c.1 - 1) le_rfl (by linarith)
  have b3 := int_le_of_cast (m := c.2 - c'.2 - 1) le_rfl (by linarith)
  have b4 := int_le_of_cast (m := c'.2 - c.2 - 1) le_rfl (by linarith)
  constructor <;> rw [abs_le] <;> constructor <;> omega

/-- The frontier of a union of cells lies on the sides between a cell of `S` and a cell not in
`S`. -/
theorem frontier_cells_subset {S : Set (ℤ × ℤ)} (hS : S.Finite) {A : Set E2}
    (hA : ∀ c n, c ∈ S → c + n.v ∉ S → segment ℝ (mpt (sideStart c n)) (mpt (sideEnd c n)) ⊆ A) :
    frontier (⋃ c ∈ S, Cell c) ⊆ A := by
  intro p hp
  by_contra hpA
  have hclosed : IsClosed (⋃ c ∈ S, Cell c) := hS.isClosed_biUnion fun c _ => isClosed_cell c
  obtain ⟨c₀, hc₀, hpc₀⟩ := mem_iUnion₂.1 (hclosed.frontier_subset hp)
  -- crossing to an adjacent cell containing `p` stays in `S`
  have step : ∀ c c' : ℤ × ℤ, c ∈ S → p ∈ Cell c → p ∈ Cell c' →
      (c'.1 = c.1 ∨ c'.2 = c.2) → c' ∈ S := by
    intro c c' hc hpc hpc' hax
    have hcl := cell_coord_close hpc hpc'
    by_contra hc'
    obtain ⟨c1, c2⟩ := c
    obtain ⟨c1', c2'⟩ := c'
    simp only at hax hcl
    rw [abs_le, abs_le] at hcl
    have key : ∃ n : Dir, (c1', c2') = (c1, c2) + n.v := by
      rcases hax with rfl | rfl
      · rcases (show c2' = c2 - 1 ∨ c2' = c2 ∨ c2' = c2 + 1 by omega) with rfl | rfl | rfl
        · exact ⟨.S, by simp [Dir.v]; ring⟩
        · exact absurd hc (by simpa using hc')
        · exact ⟨.N, by simp [Dir.v]⟩
      · rcases (show c1' = c1 - 1 ∨ c1' = c1 ∨ c1' = c1 + 1 by omega) with rfl | rfl | rfl
        · exact ⟨.W, by simp [Dir.v]; ring⟩
        · exact absurd hc (by simpa using hc')
        · exact ⟨.E, by simp [Dir.v]⟩
    obtain ⟨n, hn⟩ := key
    rw [hn] at hc' hpc'
    exact hpA (hA _ n hc hc' (by rw [side_eq_inter]; exact ⟨hpc, hpc'⟩))
  have hint : p ∈ interior (⋃ c ∈ S, Cell c) := by
    obtain ⟨δ, hδ, hcov⟩ := exists_cell_cover p
    refine mem_interior.2 ⟨Metric.ball p δ, fun q hq => ?_, Metric.isOpen_ball,
      Metric.mem_ball_self hδ⟩
    obtain ⟨c, hqc, hpc⟩ := hcov q hq
    have hc₁ : (c.1, c₀.2) ∈ S := step c₀ _ hc₀ hpc₀ ⟨hpc.1, hpc₀.2⟩ (Or.inr rfl)
    have hc : c ∈ S := step _ c hc₁ ⟨hpc.1, hpc₀.2⟩ hpc (Or.inl rfl)
    exact mem_iUnion₂.2 ⟨c, hc, hqc⟩
  exact hp.2 hint

theorem int_eq_zero_or_one' {m : ℤ} {s : ℝ} (h : (m : ℝ) = s) (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    m = 0 ∨ m = 1 := by
  have : (0 : ℤ) ≤ m := by exact_mod_cast h ▸ h0
  have : m ≤ 1 := by exact_mod_cast h ▸ h1
  omega

theorem int_ge_of_cast {m : ℤ} {x : ℝ} (h : x ≤ (m : ℝ)) (hx : -1 < x) : 0 ≤ m := by
  have : (-1 : ℝ) < m := hx.trans_le h
  have : -1 < m := by exact_mod_cast this
  omega

theorem half_cell_zero {a c : ℤ} {x : ℝ} (hx : x = a) (h : |x - c / 2| ≤ 1 / 4) : c = a + a := by
  rw [abs_le, hx] at h
  have h1 := int_le_of_cast (m := c - (a + a)) (x := 1 / 2) (by push_cast; linarith) (by norm_num)
  have h2 := int_ge_of_cast (m := c - (a + a)) (x := -1 / 2) (by push_cast; linarith) (by norm_num)
  omega

theorem half_cell_pos {a c : ℤ} {t x : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hx : x = a + t)
    (h : |x - c / 2| ≤ 1 / 4) :
    (c = a + a ∧ t ≤ 1 / 4) ∨ (c = a + a + 1 ∧ 1 / 4 ≤ t ∧ t ≤ 3 / 4) ∨
      (c = a + a + 2 ∧ 3 / 4 ≤ t) := by
  rw [abs_le, hx] at h
  have h1 := int_le_of_cast (m := c - (a + a) - 2) (x := 2 * t - 3 / 2) (by push_cast; linarith)
    (by linarith)
  have h2 := int_ge_of_cast (m := c - (a + a)) (x := 2 * t - 1 / 2) (by push_cast; linarith)
    (by linarith)
  rcases (show c = a + a ∨ c = a + a + 1 ∨ c = a + a + 2 by omega) with rfl | rfl | rfl
  · left; refine ⟨rfl, ?_⟩; push_cast at h; linarith
  · right; left; refine ⟨rfl, ?_, ?_⟩ <;> push_cast at h <;> linarith
  · right; right; refine ⟨rfl, ?_⟩; push_cast at h; linarith

theorem half_cell_neg {a c : ℤ} {t x : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hx : x = a - t)
    (h : |x - c / 2| ≤ 1 / 4) :
    (c = a + a ∧ t ≤ 1 / 4) ∨ (c = a + a - 1 ∧ 1 / 4 ≤ t ∧ t ≤ 3 / 4) ∨
      (c = a + a - 2 ∧ 3 / 4 ≤ t) := by
  have := half_cell_pos (a := -a) (c := -c) (x := -x) ht0 ht1 (by rw [hx]; push_cast; ring)
    (by rw [show -x - ((-c : ℤ) : ℝ) / 2 = -(x - c / 2) by push_cast; ring, abs_neg]; exact h)
  rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨by omega, h2⟩
  · exact Or.inr (Or.inl ⟨by omega, h2⟩)
  · exact Or.inr (Or.inr ⟨by omega, h2⟩)

/-- The cells meeting the unit lattice segment `[a, b]` at parameter `t`. -/
theorem cell_of_mem_lattice_segment {a b : Vertex 2} {d : Dir} (hd : pr b = pr a + d.v) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {c : ℤ × ℤ} (hc : lp a + t • (lp b - lp a) ∈ Cell c) :
    (c = vcell a ∧ t ≤ 1 / 4) ∨ (c = ecell a b ∧ 1 / 4 ≤ t ∧ t ≤ 3 / 4) ∨
      (c = vcell b ∧ 3 / 4 ≤ t) := by
  obtain ⟨hc1, hc2⟩ := hc
  have hb0 : b 0 = a 0 + d.v.1 := congrArg Prod.fst hd
  have hb1 : b 1 = a 1 + d.v.2 := congrArg Prod.snd hd
  obtain ⟨c1, c2⟩ := c
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, lp_apply] at hc1 hc2
  simp only [vcell, ecell, pr, Prod.ext_iff, Prod.fst_add, Prod.snd_add]
  rw [hb0] at hc1; rw [hb1] at hc2; rw [hb0, hb1]
  cases d <;> simp only [Dir.v] at hc1 hc2 ⊢ <;> push_cast at hc1 hc2
  · have e2 := half_cell_zero (a := a 1) (by ring) hc2
    rcases half_cell_pos (a := a 0) ht0 ht1 (by ring) hc1 with ⟨h, ht⟩ | h | ⟨h, ht⟩
    · exact Or.inl ⟨⟨h, e2⟩, ht⟩
    · exact Or.inr (Or.inl ⟨⟨by omega, by omega⟩, h.2⟩)
    · exact Or.inr (Or.inr ⟨⟨by omega, by omega⟩, ht⟩)
  · have e1 := half_cell_zero (a := a 0) (by ring) hc1
    rcases half_cell_pos (a := a 1) ht0 ht1 (by ring) hc2 with ⟨h, ht⟩ | h | ⟨h, ht⟩
    · exact Or.inl ⟨⟨e1, h⟩, ht⟩
    · exact Or.inr (Or.inl ⟨⟨by omega, by omega⟩, h.2⟩)
    · exact Or.inr (Or.inr ⟨⟨by omega, by omega⟩, ht⟩)
  · have e2 := half_cell_zero (a := a 1) (by ring) hc2
    rcases half_cell_neg (a := a 0) ht0 ht1 (by ring) hc1 with ⟨h, ht⟩ | h | ⟨h, ht⟩
    · exact Or.inl ⟨⟨h, e2⟩, ht⟩
    · exact Or.inr (Or.inl ⟨⟨by omega, by omega⟩, h.2⟩)
    · exact Or.inr (Or.inr ⟨⟨by omega, by omega⟩, ht⟩)
  · have e1 := half_cell_zero (a := a 0) (by ring) hc1
    rcases half_cell_neg (a := a 1) ht0 ht1 (by ring) hc2 with ⟨h, ht⟩ | h | ⟨h, ht⟩
    · exact Or.inl ⟨⟨e1, h⟩, ht⟩
    · exact Or.inr (Or.inl ⟨⟨by omega, by omega⟩, h.2⟩)
    · exact Or.inr (Or.inr ⟨⟨by omega, by omega⟩, ht⟩)

/-! ### Paths on the sphere from polylines -/

/-- The vertex with coordinates `m`. -/
def toV (m : ℤ × ℤ) : Vertex 2 := ![m.1, m.2]

@[simp] theorem pr_toV (m : ℤ × ℤ) : pr (toV m) = m := by simp [pr, toV]

theorem toV_injective : Injective toV := fun a b h => by
  rw [← pr_toV a, ← pr_toV b, h]

theorem adj_of_dir {a b : Vertex 2} {d : Dir} (h : pr b = pr a + d.v) : (lattice 2).Adj a b := by
  have hb0 : b 0 = a 0 + d.v.1 := congrArg Prod.fst h
  have hb1 : b 1 = a 1 + d.v.2 := congrArg Prod.snd h
  have e : ∀ x y : Vertex 2, x 0 = y 0 → x 1 = y 1 → x = y := fun x y h0 h1 => by
    funext k; fin_cases k
    · exact h0
    · exact h1
  cases d <;> simp only [Dir.v] at hb0 hb1
  · exact ⟨0, Or.inl (e _ _ (by simp [hb0, LatticeProb.unit]) (by simp [hb1, LatticeProb.unit]))⟩
  · exact ⟨1, Or.inl (e _ _ (by simp [hb0, LatticeProb.unit]) (by simp [hb1, LatticeProb.unit]))⟩
  · exact ⟨0, Or.inr (e _ _ (by simp [hb0, LatticeProb.unit]) (by simp [hb1, LatticeProb.unit]))⟩
  · exact ⟨1, Or.inr (e _ _ (by simp [hb0, LatticeProb.unit]) (by simp [hb1, LatticeProb.unit]))⟩

theorem sideEnd_eq (c : ℤ × ℤ) (n : Dir) : sideEnd c n = sideStart c n + n.rot.v := by
  obtain ⟨c1, c2⟩ := c; cases n <;> simp [sideStart, sideEnd, Dir.rot, Dir.v] <;> ring_nf

/-- The homothety of ratio `1 / 2` sending lattice points to corners. -/
noncomputable def toCorner : E2 →ᵃ[ℝ] E2 := AffineMap.homothety (pt (1 / 2) (1 / 2)) (1 / 2 : ℝ)

theorem toCorner_injective : Injective toCorner := fun x y h => by
  simp only [toCorner, AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add] at h
  have := smul_right_injective E2 (show (1 / 2 : ℝ) ≠ 0 by norm_num) (add_right_cancel h)
  simpa using this

theorem toCorner_lp (m : ℤ × ℤ) : toCorner (lp (toV m)) = mpt m := by
  apply E2_ext <;>
    simp [toCorner, AffineMap.homothety_apply, mpt, toV, lp_apply] <;> ring

theorem exists_index_of_mem_cyc {α : Type*} {L : List α} {a b : α} (h : (a, b) ∈ cyc L) :
    ∃ i, ∃ hi : i < L.length, L[i] = a ∧
      L[(i + 1) % L.length]'(Nat.mod_lt _ (by omega)) = b := by
  obtain ⟨l₁, l₂, hl⟩ := mem_chainPairs_iff.1 h
  have hlen : (L ++ L.take 1).length = l₁.length + 2 + l₂.length := by rw [hl]; simp; omega
  have hne : L ≠ [] := by rintro rfl; simp [cyc, chainPairs] at h
  have hL : 0 < L.length := List.length_pos_iff.2 hne
  have htake : (L.take 1).length = 1 := by simp; omega
  simp only [List.length_append, htake] at hlen
  have hi : l₁.length < L.length := by omega
  have ha : (L ++ L.take 1)[l₁.length]'(by simp; omega) = a := by simp [hl]
  have hb : (L ++ L.take 1)[l₁.length + 1]'(by simp; omega) = b := by simp [hl]
  refine ⟨l₁.length, hi, ?_, ?_⟩
  · rwa [List.getElem_append_left hi] at ha
  · rcases Nat.lt_or_ge (l₁.length + 1) L.length with h1 | h1
    · have : (l₁.length + 1) % L.length = l₁.length + 1 := Nat.mod_eq_of_lt h1
      simp only [this]
      rwa [List.getElem_append_left h1] at hb
    · have h2 : l₁.length + 1 = L.length := by omega
      have : (l₁.length + 1) % L.length = 0 := by rw [h2, Nat.mod_self]
      simp only [this]
      rw [List.getElem_append_right (by omega)] at hb
      simpa [h2] using hb

/-- The corners of a walk, read cyclically. -/
def walkCorner (L : List (ℤ × ℤ)) (i : ℕ) : ℤ × ℤ := L.getD (i % L.length) 0

theorem walkCorner_eq {L : List (ℤ × ℤ)} (hL : 0 < L.length) (i : ℕ) :
    walkCorner L i = L[i % L.length]'(Nat.mod_lt _ hL) := by
  simp [walkCorner, Nat.mod_lt _ hL]

/-- The polygon of a boundary walk satisfies the segment condition. -/
theorem WalkProps.segmentCondition {S : Set (ℤ × ℤ)} {L : List (ℤ × ℤ)} (hW : WalkProps S L) :
    SegmentCondition (fun i => mpt (walkCorner L i)) L.length := by
  have hL : 0 < L.length := by have := hW.length; omega
  have h := (segmentCondition_of_chain (c := fun i => toV (walkCorner L i)) (M := L.length)
    ?_ ?_ (Or.inl hW.length)).map toCorner toCorner_injective
  · simpa [toCorner_lp] using h
  · intro i hi
    have hmem := getElem_mem_cyc L i hi ((i + 1) % L.length) (Nat.mod_lt _ hL) rfl
    obtain ⟨c, n, -, -, hcn⟩ := hW.sound _ hmem
    refine adj_of_dir (d := n.rot) ?_
    simp only [pr_toV, walkCorner_eq hL, Nat.mod_eq_of_lt hi]
    have h1 : L[i] = sideStart c n := congrArg Prod.fst hcn
    have h2 : L[(i + 1) % L.length]'(Nat.mod_lt _ hL) = sideEnd c n := congrArg Prod.snd hcn
    rw [h1, h2, sideEnd_eq]
  · intro i j hi hj hij
    have h1 := toV_injective hij
    rw [walkCorner_eq hL, walkCorner_eq hL] at h1
    have h2 := (hW.nodup.getElem_inj_iff).1 h1
    rcases Nat.lt_or_ge i L.length with hi' | hi' <;> rcases Nat.lt_or_ge j L.length with hj' | hj'
    · rw [Nat.mod_eq_of_lt hi', Nat.mod_eq_of_lt hj'] at h2; exact Or.inl h2
    · have : j = L.length := by omega
      subst this; rw [Nat.mod_self, Nat.mod_eq_of_lt hi'] at h2; exact Or.inr (Or.inl ⟨h2, rfl⟩)
    · have : i = L.length := by omega
      subst this; rw [Nat.mod_self, Nat.mod_eq_of_lt hj'] at h2; exact Or.inr (Or.inr ⟨rfl, h2.symm⟩)
    · left; omega

variable {σ : E2 → S2}

/-- The closed polyline through `g 0, …, g M = g 0`, read on the sphere. -/
noncomputable def loopPath (hσ : Continuous σ) (g : ℕ → E2) (M : ℕ) (hM : g M = g 0) :
    Path (σ (g 0)) (σ (g 0)) where
  toFun t := σ (polyline g (M * t))
  continuous_toFun := hσ.comp ((continuous_polyline g).comp
    (continuous_const.mul continuous_subtype_val))
  source' := by simp [polyline_zero]
  target' := by simp [polyline_natCast, hM]

theorem loopPath_apply (hσ : Continuous σ) (g : ℕ → E2) (M : ℕ) (hM : g M = g 0) (t : unitInterval) :
    loopPath hσ g M hM t = σ (polyline g (M * t)) := rfl

theorem range_loopPath (hσ : Continuous σ) (g : ℕ → E2) (M : ℕ) (hM : g M = g 0) (hM0 : 0 < M) :
    range (loopPath hσ g M hM) = σ '' (polyline g '' Icc 0 M) := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨_, ⟨M * t, ⟨mul_nonneg (Nat.cast_nonneg _) t.2.1,
      by nlinarith [t.2.1, t.2.2, (Nat.cast_nonneg M : (0 : ℝ) ≤ M)]⟩, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    have hM' : (0 : ℝ) < M := by exact_mod_cast hM0
    refine ⟨⟨s / M, div_nonneg hs.1 hM'.le, (div_le_one hM').2 hs.2⟩, ?_⟩
    rw [loopPath_apply]; congr 2; simp only; field_simp

theorem loopPath_injOn (hσi : Injective σ) (hσ : Continuous σ) {g : ℕ → E2} {M : ℕ}
    (hM : g M = g 0) (hM0 : 0 < M) (hg : SegmentCondition g M) :
    InjOn (loopPath hσ g M hM) (Ico 0 1) := by
  intro t ht t' ht' h
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM0
  rw [loopPath_apply, loopPath_apply] at h
  have h1 : (t : ℝ) < 1 := ht.2
  have h2 : (t' : ℝ) < 1 := ht'.2
  have := polyline_injOn_Ico hg ⟨mul_nonneg hM'.le t.2.1, by nlinarith⟩
    ⟨mul_nonneg hM'.le t'.2.1, by nlinarith⟩ (hσi h)
  exact Subtype.ext (mul_left_cancel₀ hM'.ne' this)

/-- Extending a path on `[0, 1)` by the north pole at `1`. -/
theorem continuous_extend_northPole {f : ℝ → S2} (hf : ContinuousOn f (Iio 1))
    (hlim : Tendsto f (𝓝[<] 1) (𝓝 northPole)) :
    Continuous (fun t : unitInterval => if (t : ℝ) < 1 then f t else northPole) := by
  refine continuous_iff_continuousAt.2 fun t => ?_
  by_cases ht : (t : ℝ) < 1
  · have hev : (fun t' : unitInterval => if (t' : ℝ) < 1 then f t' else northPole) =ᶠ[𝓝 t]
        (f ∘ Subtype.val) := by
      filter_upwards [(isOpen_Iio.preimage continuous_subtype_val).mem_nhds ht] with t' ht'
      simp only [mem_preimage, mem_Iio] at ht'
      simp [ht']
    refine ContinuousAt.congr ?_ hev.symm
    exact (hf.continuousAt (Iio_mem_nhds ht)).comp continuous_subtype_val.continuousAt
  · have ht1 : (t : ℝ) = 1 := le_antisymm t.2.2 (not_lt.1 ht)
    show Tendsto _ (𝓝 t) (𝓝 (if (t : ℝ) < 1 then f t else northPole))
    rw [if_neg ht, tendsto_def]
    intro U hU
    obtain ⟨l, hl, hlU⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 (hlim hU)
    have hmem : {t' : unitInterval | l < (t' : ℝ)} ∈ 𝓝 t :=
      (isOpen_Ioi.preimage continuous_subtype_val).mem_nhds (by
        simp only [mem_preimage, mem_Ioi, ht1]; exact hl)
    filter_upwards [hmem] with t' ht'
    by_cases h : (t' : ℝ) < 1
    · simp only [mem_preimage, if_pos h]; exact hlU ⟨ht', h⟩
    · simp only [mem_preimage, if_neg h]; exact mem_of_mem_nhds hU

theorem tendsto_reparam (s₀ : ℝ) : Tendsto (fun t : ℝ => s₀ + t / (1 - t)) (𝓝[<] 1) atTop := by
  have h1 : Tendsto (fun t : ℝ => 1 - t) (𝓝[<] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun t : ℝ => 1 - t) (𝓝 1) (𝓝 (1 - 1)) :=
        (continuous_const.sub continuous_id).tendsto 1
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [mem_Iio] at ht; simp only [mem_Ioi]; linarith
  have h2 := (tendsto_inv_nhdsGT_zero.comp h1).atTop_add (tendsto_const_nhds (x := s₀ - 1))
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp only [mem_Iio] at ht
  have : 1 - t ≠ 0 := by linarith
  simp only [comp_apply]
  field_simp
  ring

theorem lp_zero : lp 0 = 0 := by ext k; simp [lp_apply]

theorem norm_sub_lp_of_adj {a b : Vertex 2} (h : (lattice 2).Adj a b) : ‖lp b - lp a‖ = 1 := by
  obtain ⟨d, hd⟩ := exists_dir_of_adj h
  have hb0 : b 0 = a 0 + d.v.1 := congrArg Prod.fst hd
  have hb1 : b 1 = a 1 + d.v.2 := congrArg Prod.snd hd
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  simp only [PiLp.sub_apply, lp_apply, hb0, hb1, Real.norm_eq_abs, sq_abs]
  cases d <;> simp [Dir.v]

theorem tendsto_norm_lattice {c : ℕ → Vertex 2} (hc : Injective c) :
    Tendsto (fun i => ‖lp (c i)‖) atTop atTop := by
  rw [tendsto_atTop]
  intro R
  have hfin : {i | ‖lp (c i)‖ < R}.Finite := by
    refine ((finite_latticeEuclideanBall (0 : Vertex 2) R).preimage hc.injOn).subset ?_
    intro i hi
    simp only [mem_setOf_eq, mem_preimage] at hi ⊢
    rw [dist_eq_norm]
    change ‖lp (c i) - lp 0‖ < R
    rwa [lp_zero, sub_zero]
  rw [← Nat.cofinite_eq_atTop]
  filter_upwards [hfin.compl_mem_cofinite] with i hi
  simpa using hi

/-- The polyline along an infinite lattice path without repetitions goes to infinity. -/
theorem tendsto_polyline_cocompact {c : ℕ → Vertex 2} (hc : Injective c)
    (hadj : ∀ i, (lattice 2).Adj (c i) (c (i + 1))) :
    Tendsto (polyline fun i => lp (c i)) atTop (cocompact E2) := by
  rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
  have h := ((tendsto_norm_lattice hc).comp (tendsto_nat_floor_atTop (α := ℝ))).atTop_add
    (tendsto_const_nhds (x := (-1 : ℝ)))
  refine tendsto_atTop_mono' _ ?_ h
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
  have hfl := Nat.floor_le hs
  have hfl' := Nat.lt_floor_add_one s
  have e := polyline_natCast_add (fun i => lp (c i)) ⌊s⌋₊ (t := s - ⌊s⌋₊) (by linarith)
    (by linarith)
  rw [add_sub_cancel] at e
  simp only [comp_apply]
  rw [e]
  have hn := norm_sub_lp_of_adj (hadj ⌊s⌋₊)
  have : ‖(s - ⌊s⌋₊) • (lp (c (⌊s⌋₊ + 1)) - lp (c ⌊s⌋₊))‖ ≤ 1 := by
    rw [norm_smul, hn, mul_one, Real.norm_eq_abs, abs_of_nonneg (by linarith)]; linarith
  have := norm_sub_le (lp (c ⌊s⌋₊) + (s - ⌊s⌋₊) • (lp (c (⌊s⌋₊ + 1)) - lp (c ⌊s⌋₊)))
    ((s - ⌊s⌋₊) • (lp (c (⌊s⌋₊ + 1)) - lp (c ⌊s⌋₊)))
  rw [add_sub_cancel_right] at this
  show ‖lp (c ⌊s⌋₊)‖ + -1 ≤ _
  linarith

/-- The ray of a polyline from parameter `s₀`, read on the sphere, ending at the north pole. -/
noncomputable def rayPath (hσ : Continuous σ) (g : ℕ → E2) (s₀ : ℝ)
    (hlim : Tendsto (fun t : ℝ => σ (polyline g (s₀ + t / (1 - t)))) (𝓝[<] 1) (𝓝 northPole)) :
    Path (σ (polyline g s₀)) northPole where
  toFun t := if (t : ℝ) < 1 then σ (polyline g (s₀ + t / (1 - t))) else northPole
  continuous_toFun := by
    refine continuous_extend_northPole ?_ hlim
    refine hσ.comp_continuousOn ((continuous_polyline g).comp_continuousOn
      (continuousOn_const.add (continuousOn_id.div (continuousOn_const.sub continuousOn_id) ?_)))
    intro x hx; simp only [mem_Iio] at hx; linarith
  source' := by simp
  target' := by simp

theorem rayPath_apply (hσ : Continuous σ) (g : ℕ → E2) (s₀ : ℝ) (hlim) (t : unitInterval) :
    rayPath (σ := σ) hσ g s₀ hlim t =
      if (t : ℝ) < 1 then σ (polyline g (s₀ + t / (1 - t))) else northPole := rfl

theorem reparam_mem {s₀ t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) : s₀ ≤ s₀ + t / (1 - t) := by
  have : 0 ≤ t / (1 - t) := div_nonneg ht0 (by linarith)
  linarith

theorem reparam_inj {s₀ t t' : ℝ} (ht : t < 1) (ht' : t' < 1)
    (h : s₀ + t / (1 - t) = s₀ + t' / (1 - t')) : t = t' := by
  have h1 : 1 - t ≠ 0 := by linarith
  have h2 : 1 - t' ≠ 0 := by linarith
  have := add_left_cancel h
  field_simp at this
  linarith

theorem reparam_surj {s₀ s : ℝ} (hs : s₀ ≤ s) :
    ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧ s₀ + t / (1 - t) = s := by
  refine ⟨(s - s₀) / (1 + (s - s₀)), div_nonneg (by linarith) (by linarith),
    (div_lt_one (by linarith)).2 (by linarith), ?_⟩
  have h1 : 1 + (s - s₀) ≠ 0 := by linarith
  have h2 : 1 - (s - s₀) / (1 + (s - s₀)) = 1 / (1 + (s - s₀)) := by field_simp; ring
  rw [h2]; field_simp; ring

theorem range_rayPath (hσ : Continuous σ) (g : ℕ → E2) (s₀ : ℝ) (hlim) :
    range (rayPath (σ := σ) hσ g s₀ hlim) = σ '' (polyline g '' Ici s₀) ∪ {northPole} := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    rw [rayPath_apply]
    split_ifs with h
    · exact Or.inl ⟨_, ⟨_, reparam_mem t.2.1 h, rfl⟩, rfl⟩
    · exact Or.inr rfl
  · rintro (⟨_, ⟨s, hs, rfl⟩, rfl⟩ | rfl)
    · obtain ⟨t, ht0, ht1, rfl⟩ := reparam_surj (s₀ := s₀) hs
      exact ⟨⟨t, ht0, ht1.le⟩, by rw [rayPath_apply]; simp [ht1]⟩
    · exact ⟨1, by rw [rayPath_apply]; simp⟩

theorem rayPath_injective (hσi : Injective σ) (hσr : range σ = {northPole}ᶜ) (hσ : Continuous σ)
    {g : ℕ → E2} {s₀ : ℝ} (hlim) (hinj : InjOn (polyline g) (Ici s₀)) :
    Injective (rayPath (σ := σ) hσ g s₀ hlim) := by
  have hN : ∀ x, σ x ≠ northPole := fun x h => by
    have : σ x ∈ range σ := mem_range_self x
    rw [hσr, h] at this; exact this rfl
  intro t t' h
  rw [rayPath_apply, rayPath_apply] at h
  split_ifs at h with h1 h2 h2
  · exact Subtype.ext (reparam_inj h1 h2 (hinj (reparam_mem t.2.1 h1) (reparam_mem t'.2.1 h2)
      (hσi h)))
  · exact absurd h (hN _)
  · exact absurd h.symm (hN _)
  · exact Subtype.ext ((le_antisymm t.2.2 (not_lt.1 h1)).trans
      (le_antisymm t'.2.2 (not_lt.1 h2)).symm)

/-! ### The one-point compactification map -/

/-- An open embedding `σ : ℝ² → S²` onto `S² \ {N}` (inverse stereographic projection). -/
theorem exists_sigma : ∃ σ : E2 → S2, IsOpenEmbedding σ ∧ range σ = {northPole}ᶜ := by
  have hv : ‖(northPole : EuclideanSpace ℝ (Fin 3))‖ = 1 := norm_eq_of_mem_sphere northPole
  have hv0 : (northPole : EuclideanSpace ℝ (Fin 3)) ≠ 0 := by
    intro h; rw [h, norm_zero] at hv; exact zero_ne_one hv
  haveI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  have hdim : Module.finrank ℝ E2 =
      Module.finrank ℝ (ℝ ∙ (northPole : EuclideanSpace ℝ (Fin 3)))ᗮ := by
    rw [finrank_euclideanSpace_fin, Submodule.finrank_orthogonal_span_singleton (n := 2) hv0]
  let e : E2 ≃L[ℝ] (ℝ ∙ (northPole : EuclideanSpace ℝ (Fin 3)))ᗮ :=
    (FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq hdim).some
  refine ⟨(stereographic hv).symm ∘ e, ?_, ?_⟩
  · exact (isOpenEmbedding_stereographic_symm hv).comp e.toHomeomorph.isOpenEmbedding
  · rw [range_comp, e.surjective.range_eq, image_univ, range_stereographic_symm hv northPole.2]

/-! ### Rays leaving the connectors -/

section Ray

variable {Tv : Set (Vertex 2)} {S : Set (ℤ × ℤ)}

theorem polyline_affine (g : ℕ → E2) (i : ℕ) {s : ℝ} (h0 : (i : ℝ) ≤ s) (h1 : s ≤ i + 1) :
    polyline g s = g i + (s - i) • (g (i + 1) - g i) := by
  have := polyline_natCast_add g i (t := s - i) (by linarith) (by linarith)
  rwa [add_sub_cancel] at this

/-- On `[i, i + 1]` the polyline is affine: the image of a subinterval is a segment. -/
theorem polyline_mem_segment_sub (g : ℕ → E2) (i : ℕ) {a b s : ℝ} (ha : (i : ℝ) ≤ a)
    (hab : a ≤ s) (hsb : s ≤ b) (hb : b ≤ i + 1) :
    polyline g s ∈ segment ℝ (polyline g a) (polyline g b) := by
  rw [polyline_affine g i ha (by linarith), polyline_affine g i (by linarith) hb,
    polyline_affine g i (by linarith) (by linarith), segment_eq_image']
  rcases eq_or_lt_of_le (hab.trans hsb) with heq | hlt
  · refine ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
    have : s = a := by linarith
    subst this; simp
  · refine ⟨(s - a) / (b - a), ⟨div_nonneg (by linarith) (by linarith),
      (div_le_one (by linarith)).2 (by linarith)⟩, ?_⟩
    have hba : b - a ≠ 0 := by linarith
    set Δ := g (i + 1) - g i
    have e1 : g i + (b - i) • Δ - (g i + (a - i) • Δ) = (b - a) • Δ := by
      rw [add_sub_add_left_eq_sub, ← sub_smul]; congr 1; ring
    show g i + (a - i) • Δ + ((s - a) / (b - a)) • (g i + (b - i) • Δ - (g i + (a - i) • Δ)) =
      g i + (s - i) • Δ
    rw [e1, smul_smul, add_assoc, ← add_smul]
    congr 2
    field_simp
    ring

theorem segment_subset_image_polyline (g : ℕ → E2) (i : ℕ) {a b : ℝ} (ha : (i : ℝ) ≤ a)
    (hab : a ≤ b) (hb : b ≤ i + 1) :
    segment ℝ (polyline g a) (polyline g b) ⊆ polyline g '' Icc a b := by
  rw [segment_eq_image']
  rintro _ ⟨t, ⟨ht0, ht1⟩, rfl⟩
  refine ⟨a + t * (b - a), ⟨by nlinarith, by nlinarith⟩, ?_⟩
  rw [polyline_affine g i ha (by linarith), polyline_affine g i (by linarith) hb,
    polyline_affine g i (by nlinarith) (by nlinarith)]
  set Δ := g (i + 1) - g i
  have e1 : g i + (b - i) • Δ - (g i + (a - i) • Δ) = (b - a) • Δ := by
    rw [add_sub_add_left_eq_sub, ← sub_smul]; congr 1; ring
  show g i + (a + t * (b - a) - i) • Δ =
    g i + (a - i) • Δ + t • (g i + (b - i) • Δ - (g i + (a - i) • Δ))
  rw [e1, smul_smul, add_assoc, ← add_smul]
  congr 2; ring

variable {c : ℕ → Vertex 2}

theorem IsRay.segmentCondition (h : IsRay Tv c) (M : ℕ) :
    SegmentCondition (fun i => lp (c i)) M := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · exact ⟨fun i hi => absurd hi (by omega), fun i j _ hj => absurd hj (by omega)⟩
  · exact segmentCondition_of_chain (fun i _ => h.adj i) (fun i j _ _ hij => Or.inl (h.inj hij))
      (Or.inr fun h0 => absurd (h.inj h0) (by omega))

theorem IsRay.injOn (h : IsRay Tv c) : InjOn (polyline fun i => lp (c i)) (Ici 0) := by
  intro s hs s' hs' hss'
  have hM := (h.segmentCondition (⌈max s s'⌉₊ + 1))
  have h0M : (fun i => lp (c i)) 0 ≠ (fun i => lp (c i)) (⌈max s s'⌉₊ + 1) := fun h0 =>
    absurd (h.inj (latticeEuclideanEmbedding.injective h0)) (by omega)
  refine polyline_injOn_Icc hM h0M ⟨hs, ?_⟩ ⟨hs', ?_⟩ hss' <;> push_cast <;>
    linarith [Nat.le_ceil (max s s'), le_max_left s s', le_max_right s s']

end Ray

/-- The two half-balls at a generic point of an axis-parallel segment with quarter-integer
endpoints contained in `σ⁻¹ Γ ⊆` quarter skeleton. -/
theorem twoSided_of_segment {σ : E2 → S2} {Γ : Set S2} {x a b : E2} {k e : Fin 2} (hke : k ≠ e)
    (hx : x ∈ segment ℝ a b) (hab : a k = b k) (hak : IsQuarter (a k)) (hae : IsQuarter (a e))
    (hbe : IsQuarter (b e)) (hxZ : x ∉ quarterPoints)
    (hΓ : ∀ q, σ q ∈ Γ → q ∈ quarterSkeleton) (hseg : ∀ q ∈ segment ℝ a b, σ q ∈ Γ) :
    TwoSided σ Γ x (halfBall x k (qdist (x e)) true) (halfBall x k (qdist (x e)) false) := by
  have hxk : x k = a k := by
    obtain ⟨t, -, ht⟩ := coords_of_mem_segment hx
    rw [ht k, hab, sub_self, mul_zero, add_zero]
  have hk : IsQuarter (x k) := hxk ▸ hak
  have he : ¬ IsQuarter (x e) := fun he => hxZ (by
    fin_cases k <;> fin_cases e <;> simp_all [quarterPoints])
  exact twoSided_halfBalls (qdist_pos he)
    (fun q hq hqΓ => eq_of_mem_quarterSkeleton hke hk he hq (hΓ q hqΓ))
    (fun q hq hqk => hseg q (mem_segment_of_mem_ball hke hab hae hbe he hx hq hqk))

/-- The axis of a direction. -/
def Dir.ax : Dir → Fin 2
  | .E => 0 | .N => 1 | .W => 0 | .S => 1

/-- The other axis. -/
def Dir.ax' : Dir → Fin 2
  | .E => 1 | .N => 0 | .W => 1 | .S => 0

theorem Dir.ax_ne (d : Dir) : d.ax' ≠ d.ax := by cases d <;> decide

theorem isQuarter_int (m : ℤ) : IsQuarter (m : ℝ) := ⟨4 * m, by push_cast; ring⟩

theorem isQuarter_lp (a : Vertex 2) (k : Fin 2) : IsQuarter (lp a k) := isQuarter_int _

theorem lp_axis {a b : Vertex 2} {d : Dir} (hd : pr b = pr a + d.v) : lp a d.ax' = lp b d.ax' := by
  have hb0 : b 0 = a 0 + d.v.1 := congrArg Prod.fst hd
  have hb1 : b 1 = a 1 + d.v.2 := congrArg Prod.snd hd
  cases d <;> simp only [Dir.v, Dir.ax'] at hb0 hb1 ⊢ <;> simp [lp_apply, hb0, hb1]

/-- The quarter skeleton contains the lattice segments. -/
theorem lattice_segment_subset_quarterSkeleton {a b : Vertex 2} (h : (lattice 2).Adj a b) :
    segment ℝ (lp a) (lp b) ⊆ quarterSkeleton := by
  intro q hq
  obtain ⟨d, hd⟩ := exists_dir_of_adj h
  obtain ⟨t, -, ht⟩ := coords_of_mem_segment hq
  have := lp_axis hd
  have hq' : q d.ax' = lp a d.ax' := by rw [ht, ← this, sub_self, mul_zero, add_zero]
  cases d <;> simp only [Dir.ax'] at hq' <;> simp only [quarterSkeleton, mem_setOf_eq, hq']
  · exact Or.inr (isQuarter_lp a 1)
  · exact Or.inl (isQuarter_lp a 0)
  · exact Or.inr (isQuarter_lp a 1)
  · exact Or.inl (isQuarter_lp a 0)

section Ray2

variable {Tv : Set (Vertex 2)} {S : Set (ℤ × ℤ)} {c : ℕ → Vertex 2}

/-- The exit point of a ray from the cells of the connectors, a quarter along its first edge. -/
noncomputable def exitPt (c : ℕ → Vertex 2) : E2 := polyline (fun i => lp (c i)) (1 / 4)

/-- The ray beyond its exit point. -/
def rayTail (c : ℕ → Vertex 2) : Set E2 := polyline (fun i => lp (c i)) '' Ici (1 / 4)

theorem exitPt_eq (c : ℕ → Vertex 2) :
    exitPt c = lp (c 0) + (1 / 4 : ℝ) • (lp (c 1) - lp (c 0)) := by
  have := polyline_natCast_add (fun i => lp (c i)) 0 (t := 1 / 4) (by norm_num) (by norm_num)
  simpa [exitPt] using this

theorem exitPt_mem_rayTail (c : ℕ → Vertex 2) : exitPt c ∈ rayTail c := ⟨1 / 4, self_mem_Ici, rfl⟩

theorem IsRay.mem_cell_eq (h : IsRay Tv c) (hS : CellsOf Tv S) {x : E2} (hx : x ∈ rayTail c)
    {c' : ℤ × ℤ} (hc' : c' ∈ S) (hxc : x ∈ Cell c') : x = exitPt c := by
  obtain ⟨s, hs, rfl⟩ := hx
  simp only [mem_Ici] at hs
  have hs0 : 0 ≤ s := by linarith
  have h1 := Nat.floor_le hs0
  have h2 := Nat.lt_floor_add_one s
  obtain ⟨d, hd⟩ := exists_dir_of_adj (h.adj ⌊s⌋₊)
  rw [polyline_affine _ ⌊s⌋₊ h1 h2.le] at hxc
  rcases cell_of_mem_lattice_segment hd (by linarith) (by linarith) hxc with
    ⟨rfl, ht⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
  · have hT := hS.vert _ hc'
    rcases Nat.eq_zero_or_pos ⌊s⌋₊ with h0 | h0
    · rw [h0] at ht
      push_cast at ht
      rw [show s = 1 / 4 by linarith]; rfl
    · obtain ⟨i, hi⟩ : ∃ i, ⌊s⌋₊ = i + 1 := ⟨⌊s⌋₊ - 1, by omega⟩
      rw [hi] at hT; exact absurd hT (h.leave i)
  · exact absurd (hS.edge _ _ d hd hc').2 (h.leave _)
  · exact absurd (hS.vert _ hc') (h.leave _)

theorem IsRay.exitPt_mem_cells (h : IsRay Tv c) (hS : CellsOf Tv S) {d : Dir}
    (hd : pr (c 1) = pr (c 0) + d.v) :
    exitPt c ∈ Cell (vcell (c 0)) ∩ Cell (vcell (c 0) + d.v) ∧ vcell (c 0) ∈ S ∧
      vcell (c 0) + d.v ∉ S := by
  have hb0 : c 1 0 = c 0 0 + d.v.1 := congrArg Prod.fst hd
  have hb1 : c 1 1 = c 0 1 + d.v.2 := congrArg Prod.snd hd
  refine ⟨?_, hS.mem _ h.start, fun hc => ?_⟩
  · rw [exitPt_eq]
    simp only [Cell, mem_inter_iff, mem_setOf_eq, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply,
      smul_eq_mul, lp_apply, vcell, pr, Prod.fst_add, Prod.snd_add, hb0, hb1]
    cases d <;> simp only [Dir.v] <;> push_cast <;> norm_num [abs_le] <;> constructor <;> linarith
  · have : vcell (c 0) + d.v = ecell (c 0) (c 1) := (ecell_eq_of_dir hd).symm
    rw [this] at hc
    exact h.leave 0 (hS.edge _ _ d hd hc).2

end Ray2

theorem oddq_close {m m' : ℤ} (h : |((2 * m + 1) / 4 : ℝ) - (2 * m' + 1) / 4| < 1 / 4) :
    m = m' := by
  rw [abs_lt] at h
  have h1 := int_le_of_cast (m := m - m') (x := 1 / 2) (by push_cast; linarith) (by norm_num)
  have h2 := int_ge_of_cast (m := m - m') (x := -1 / 2) (by push_cast; linarith) (by norm_num)
  omega

theorem oddq_int_far {m a : ℤ} (h : |((2 * m + 1) / 4 : ℝ) - a| < 1 / 4) : False := by
  rw [abs_lt] at h
  have h1 := int_le_of_cast (m := 2 * m - 4 * a + 1) (x := 4 * ((2 * m + 1) / 4 - a))
    (by push_cast; linarith) (by linarith)
  have h2 := int_ge_of_cast (m := 2 * m - 4 * a + 1) (x := 4 * ((2 * m + 1) / 4 - a))
    (by push_cast; linarith) (by linarith)
  omega

/-- The points of a side have an odd-quarter coordinate along the normal. -/
theorem side_coord {c : ℤ × ℤ} {n : Dir} {p : E2} (hp : p ∈ Cell c ∩ Cell (c + n.v)) :
    ∃ m : ℤ, p n.ax = (2 * m + 1) / 4 := by
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hp
  rw [abs_le] at h1 h2 h3 h4
  obtain ⟨c1, c2⟩ := c
  cases n <;> simp only [Dir.v, Dir.ax, Prod.fst_add, Prod.snd_add] at h1 h2 h3 h4 ⊢ <;>
    push_cast at h1 h2 h3 h4
  · exact ⟨c1, by linarith⟩
  · exact ⟨c2, by linarith⟩
  · exact ⟨c1 - 1, by push_cast; linarith⟩
  · exact ⟨c2 - 1, by push_cast; linarith⟩

theorem ball_coord {x q : E2} {r : ℝ} (hq : q ∈ Metric.ball x r) (k : Fin 2) : |q k - x k| < r := by
  rw [Metric.mem_ball] at hq
  have := (PiLp.dist_apply_le q x k).trans_lt hq
  rwa [Real.dist_eq] at this

section Ray3

variable {Tv : Set (Vertex 2)} {S : Set (ℤ × ℤ)} {c : ℕ → Vertex 2}

theorem exitPt_coords {d : Dir} (hd : pr (c 1) = pr (c 0) + d.v) :
    (∃ m : ℤ, exitPt c d.ax = (2 * m + 1) / 4) ∧ exitPt c d.ax' = c 0 d.ax' := by
  have hb0 : c 1 0 = c 0 0 + d.v.1 := congrArg Prod.fst hd
  have hb1 : c 1 1 = c 0 1 + d.v.2 := congrArg Prod.snd hd
  rw [exitPt_eq]
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, lp_apply]
  cases d <;> simp only [Dir.v, Dir.ax, Dir.ax'] at hb0 hb1 ⊢ <;> rw [hb0, hb1] <;> push_cast
  · exact ⟨⟨2 * c 0 0, by push_cast; ring⟩, by ring⟩
  · exact ⟨⟨2 * c 0 1, by push_cast; ring⟩, by ring⟩
  · exact ⟨⟨2 * c 0 0 - 1, by push_cast; ring⟩, by ring⟩
  · exact ⟨⟨2 * c 0 1 - 1, by push_cast; ring⟩, by ring⟩

/-- Near the exit point, the sides of cells lie on the line through it across the first edge. -/
theorem near_exit {d : Dir} (hd : pr (c 1) = pr (c 0) + d.v) {q : E2}
    (hq : q ∈ Metric.ball (exitPt c) (1 / 4)) {c' : ℤ × ℤ} {n : Dir}
    (hside : q ∈ Cell c' ∩ Cell (c' + n.v)) : q d.ax = exitPt c d.ax := by
  obtain ⟨m, hm⟩ := side_coord hside
  obtain ⟨⟨m', hm'⟩, hm''⟩ := exitPt_coords hd
  have hax : n.ax = d.ax ∨ n.ax = d.ax' := by cases n <;> cases d <;> decide
  rcases hax with h | h
  · have := ball_coord hq d.ax
    rw [← h, hm, h, hm'] at this
    rw [h] at hm; rw [hm, hm', oddq_close this]
  · have := ball_coord hq d.ax'
    rw [← h, hm, h, hm''] at this
    exact (oddq_int_far this).elim

/-- The line through the exit point across the first edge lies on the side of the start cell. -/
theorem diameter_exit {d : Dir} (hd : pr (c 1) = pr (c 0) + d.v) {q : E2}
    (hq : q ∈ Metric.ball (exitPt c) (1 / 4)) (hqd : q d.ax = exitPt c d.ax) :
    q ∈ Cell (vcell (c 0)) ∩ Cell (vcell (c 0) + d.v) := by
  have hb0 : c 1 0 = c 0 0 + d.v.1 := congrArg Prod.fst hd
  have hb1 : c 1 1 = c 0 1 + d.v.2 := congrArg Prod.snd hd
  have h0 := ball_coord hq 0
  have h1 := ball_coord hq 1
  rw [exitPt_eq] at h0 h1 hqd
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, lp_apply] at h0 h1 hqd
  simp only [Cell, mem_inter_iff, mem_setOf_eq, vcell, pr, Prod.fst_add, Prod.snd_add]
  rw [abs_lt] at h0 h1
  cases d <;> simp only [Dir.v, Dir.ax] at hb0 hb1 hqd ⊢ <;>
    simp only [hb0, hb1] at h0 h1 hqd ⊢ <;>
    push_cast at h0 h1 hqd ⊢ <;> norm_num [abs_le] <;> refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;>
    (try constructor) <;> linarith

end Ray3

theorem isQuarter_odd (m : ℤ) : IsQuarter ((2 * m + 1) / 4 : ℝ) := ⟨2 * m + 1, by push_cast; ring⟩

theorem mem_quarterSkeleton_of {p : E2} {k : Fin 2} (h : IsQuarter (p k)) : p ∈ quarterSkeleton := by
  fin_cases k
  · exact Or.inl h
  · exact Or.inr h

/-- The data of a side: an axis-parallel segment with quarter-integer endpoints. -/
theorem side_data (c : ℤ × ℤ) (n : Dir) :
    mpt (sideStart c n) n.ax = mpt (sideEnd c n) n.ax ∧ IsQuarter (mpt (sideStart c n) n.ax) ∧
      IsQuarter (mpt (sideStart c n) n.ax') ∧ IsQuarter (mpt (sideEnd c n) n.ax') := by
  obtain ⟨c1, c2⟩ := c
  refine ⟨?_, ?_, ?_, ?_⟩
  · cases n <;> simp [mpt, sideStart, sideEnd, Dir.ax]
  all_goals cases n <;> simp only [mpt, sideStart, sideEnd, Dir.ax, Dir.ax', pt_zero, pt_one] <;>
    exact isQuarter_odd _

theorem side_subset_quarterSkeleton (c : ℤ × ℤ) (n : Dir) :
    segment ℝ (mpt (sideStart c n)) (mpt (sideEnd c n)) ⊆ quarterSkeleton := by
  intro q hq
  obtain ⟨h1, h2, -, -⟩ := side_data c n
  obtain ⟨t, -, ht⟩ := coords_of_mem_segment hq
  refine mem_quarterSkeleton_of (k := n.ax) ?_
  rw [ht, ← h1, sub_self, mul_zero, add_zero]; exact h2

theorem ax_ne_ax' (n : Dir) : n.ax ≠ n.ax' := by cases n <;> decide

section Walk

variable {S : Set (ℤ × ℤ)} {L : List (ℤ × ℤ)}

/-- The corner polygon of a walk. -/
noncomputable def walkPoly (L : List (ℤ × ℤ)) : ℕ → E2 := fun i => mpt (walkCorner L i)

/-- The plane trace of the boundary walk. -/
def walkTrace (L : List (ℤ × ℤ)) : Set E2 := polyline (walkPoly L) '' Icc 0 L.length

theorem WalkProps.mem_side (hW : WalkProps S L) {x : E2} (hx : x ∈ walkTrace L) :
    ∃ c n, c ∈ S ∧ c + n.v ∉ S ∧ x ∈ segment ℝ (mpt (sideStart c n)) (mpt (sideEnd c n)) := by
  have hL : 0 < L.length := by have := hW.length; omega
  obtain ⟨s, hs, rfl⟩ := hx
  obtain ⟨i, hi, hsi⟩ := exists_index hL hs
  have hmem := polyline_mem_segment (walkPoly L) i hsi
  have hcyc := getElem_mem_cyc L i hi ((i + 1) % L.length) (Nat.mod_lt _ hL) rfl
  obtain ⟨c, n, hc, hcn, hpair⟩ := hW.sound _ hcyc
  refine ⟨c, n, hc, hcn, ?_⟩
  have e1 : walkPoly L i = mpt (sideStart c n) := by
    simp only [walkPoly, walkCorner_eq hL, Nat.mod_eq_of_lt hi]
    exact congrArg mpt (congrArg Prod.fst hpair)
  have e2 : walkPoly L (i + 1) = mpt (sideEnd c n) := by
    simp only [walkPoly, walkCorner_eq hL]
    exact congrArg mpt (congrArg Prod.snd hpair)
  rwa [e1, e2] at hmem

theorem WalkProps.side_subset (hW : WalkProps S L) {c : ℤ × ℤ} {n : Dir} (hc : c ∈ S)
    (hcn : c + n.v ∉ S) :
    segment ℝ (mpt (sideStart c n)) (mpt (sideEnd c n)) ⊆ walkTrace L := by
  have hL : 0 < L.length := by have := hW.length; omega
  obtain ⟨i, hi, h1, h2⟩ := exists_index_of_mem_cyc (hW.complete c n hc hcn)
  have e1 : walkPoly L i = mpt (sideStart c n) := by
    simp only [walkPoly, walkCorner_eq hL, Nat.mod_eq_of_lt hi, h1]
  have e2 : walkPoly L (i + 1) = mpt (sideEnd c n) := by
    simp only [walkPoly, walkCorner_eq hL, h2]
  rw [← e1, ← e2, ← image_polyline_Icc]
  refine image_mono fun s hs => ⟨by linarith [hs.1, (Nat.cast_nonneg i : (0 : ℝ) ≤ i)], ?_⟩
  have : (i : ℝ) + 1 ≤ L.length := by exact_mod_cast hi
  linarith [hs.2]

theorem walkPoly_length (L : List (ℤ × ℤ)) : walkPoly L L.length = walkPoly L 0 := by
  simp [walkPoly, walkCorner]

end Walk

section Ray4

variable {Tv : Set (Vertex 2)} {c : ℕ → Vertex 2}

theorem rayTail_mem_segment {x : E2} (hx : x ∈ rayTail c) :
    ∃ i, x ∈ segment ℝ (lp (c i)) (lp (c (i + 1))) := by
  obtain ⟨s, hs, rfl⟩ := hx
  have hs0 : (0 : ℝ) ≤ s := le_trans (by norm_num) hs
  exact ⟨⌊s⌋₊, polyline_mem_segment (fun i => lp (c i)) ⌊s⌋₊
    ⟨Nat.floor_le hs0, (Nat.lt_floor_add_one s).le⟩⟩

theorem IsRay.rayTail_subset (h : IsRay Tv c) : rayTail c ⊆ quarterSkeleton := fun x hx => by
  obtain ⟨i, hi⟩ := rayTail_mem_segment hx
  exact lattice_segment_subset_quarterSkeleton (h.adj i) hi

/-- A lattice point on a unit lattice segment is one of its endpoints. -/
theorem eq_of_lp_mem_segment {a b v : Vertex 2} (h : (lattice 2).Adj a b)
    (hv : lp v ∈ segment ℝ (lp a) (lp b)) : v = a ∨ v = b := by
  obtain ⟨d, hd⟩ := exists_dir_of_adj h
  have hb0 : b 0 = a 0 + d.v.1 := congrArg Prod.fst hd
  have hb1 : b 1 = a 1 + d.v.2 := congrArg Prod.snd hd
  obtain ⟨t, ⟨ht0, ht1⟩, ht⟩ := coords_of_mem_segment hv
  have h0 := ht 0
  have h1 := ht 1
  simp only [lp_apply, hb0, hb1] at h0 h1
  have e : ∀ x y : Vertex 2, x 0 = y 0 → x 1 = y 1 → x = y := fun x y h0 h1 => by
    funext k; fin_cases k
    · exact h0
    · exact h1
  cases d <;> simp only [Dir.v] at h0 h1 hb0 hb1 <;> push_cast at h0 h1
  · have hv : v 1 = a 1 := by exact_mod_cast (by linarith : (v 1 : ℝ) = a 1)
    rcases int_eq_zero_or_one' (m := v 0 - a 0) (s := t) (by push_cast; linarith) ht0 ht1 with h | h
    · exact Or.inl (e _ _ (by omega) (by omega))
    · exact Or.inr (e _ _ (by omega) (by omega))
  · have hv : v 0 = a 0 := by exact_mod_cast (by linarith : (v 0 : ℝ) = a 0)
    rcases int_eq_zero_or_one' (m := v 1 - a 1) (s := t) (by push_cast; linarith) ht0 ht1 with h | h
    · exact Or.inl (e _ _ (by omega) (by omega))
    · exact Or.inr (e _ _ (by omega) (by omega))
  · have hv : v 1 = a 1 := by exact_mod_cast (by linarith : (v 1 : ℝ) = a 1)
    rcases int_eq_zero_or_one' (m := a 0 - v 0) (s := t) (by push_cast; linarith) ht0 ht1 with h | h
    · exact Or.inl (e _ _ (by omega) (by omega))
    · exact Or.inr (e _ _ (by omega) (by omega))
  · have hv : v 0 = a 0 := by exact_mod_cast (by linarith : (v 0 : ℝ) = a 0)
    rcases int_eq_zero_or_one' (m := a 1 - v 1) (s := t) (by push_cast; linarith) ht0 ht1 with h | h
    · exact Or.inl (e _ _ (by omega) (by omega))
    · exact Or.inr (e _ _ (by omega) (by omega))

end Ray4

section Ray5

variable {Tv : Set (Vertex 2)} {c c' : ℕ → Vertex 2}

theorem IsRay.generic (h : IsRay Tv c) {x : E2} (hx : x ∈ rayTail c) :
    ∃ a b : E2, ∃ k e : Fin 2, k ≠ e ∧ x ∈ segment ℝ a b ∧ segment ℝ a b ⊆ rayTail c ∧
      a k = b k ∧ IsQuarter (a k) ∧ IsQuarter (a e) ∧ IsQuarter (b e) := by
  obtain ⟨s, hs, rfl⟩ := hx
  simp only [mem_Ici] at hs
  have hs0 : (0 : ℝ) ≤ s := le_trans (by norm_num) hs
  have h1 := Nat.floor_le hs0
  have h2 := Nat.lt_floor_add_one s
  rcases Nat.eq_zero_or_pos ⌊s⌋₊ with h0 | h0
  · rw [h0] at h1 h2; push_cast at h1 h2
    obtain ⟨d, hd⟩ := exists_dir_of_adj (h.adj 0)
    obtain ⟨⟨m, hm⟩, hm'⟩ := exitPt_coords hd
    refine ⟨exitPt c, lp (c 1), d.ax', d.ax, d.ax_ne, ?_, ?_, ?_, ?_, ?_, isQuarter_lp _ _⟩
    · have := polyline_mem_segment_sub (fun i => lp (c i)) 0 (a := 1 / 4) (b := 1) (s := s)
        (by norm_num) hs (by linarith) (by norm_num)
      simpa [exitPt, polyline_one] using this
    · intro q hq
      have := segment_subset_image_polyline (fun i => lp (c i)) 0 (a := 1 / 4) (b := 1)
        (by norm_num) (by norm_num) (by norm_num)
      rw [show exitPt c = polyline (fun i => lp (c i)) (1 / 4) from rfl,
        show lp (c 1) = polyline (fun i => lp (c i)) 1 from
          (polyline_one (fun i => lp (c i))).symm] at hq
      obtain ⟨t, ht, rfl⟩ := this hq
      exact ⟨t, ht.1, rfl⟩
    · rw [hm', ← lp_axis hd]; rfl
    · rw [hm']; exact isQuarter_int _
    · rw [hm]; exact isQuarter_odd _
  · obtain ⟨d, hd⟩ := exists_dir_of_adj (h.adj ⌊s⌋₊)
    refine ⟨lp (c ⌊s⌋₊), lp (c (⌊s⌋₊ + 1)), d.ax', d.ax, d.ax_ne,
      polyline_mem_segment (fun i => lp (c i)) ⌊s⌋₊ ⟨h1, h2.le⟩, ?_, lp_axis hd, isQuarter_lp _ _,
      isQuarter_lp _ _, isQuarter_lp _ _⟩
    rw [show segment ℝ (lp (c ⌊s⌋₊)) (lp (c (⌊s⌋₊ + 1))) =
      polyline (fun i => lp (c i)) '' Icc (⌊s⌋₊ : ℝ) (⌊s⌋₊ + 1) from
        (image_polyline_Icc (fun i => lp (c i)) ⌊s⌋₊).symm]
    refine image_mono fun t ht => ?_
    simp only [mem_Ici]
    have : (1 : ℝ) ≤ ⌊s⌋₊ := by exact_mod_cast h0
    linarith [ht.1]

theorem rayTail_disjoint (h : IsRay Tv c) (h' : IsRay Tv c') (hd : ∀ i j, c i ≠ c' j) :
    Disjoint (rayTail c) (rayTail c') := by
  rw [Set.disjoint_left]
  intro x hx hx'
  obtain ⟨i, hi⟩ := rayTail_mem_segment hx
  obtain ⟨j, hj⟩ := rayTail_mem_segment hx'
  rcases eq_or_eq_of_mem_segment_inter (h.adj i) (h'.adj j) hi hj with e | e | e | e <;>
    exact hd _ _ e

theorem lp_mem_rayTail (h : IsRay Tv c) {v : Vertex 2} (hv : lp v ∈ rayTail c) : ∃ i, v = c i := by
  obtain ⟨i, hi⟩ := rayTail_mem_segment hv
  rcases eq_of_lp_mem_segment (h.adj i) hi with e | e
  · exact ⟨i, e⟩
  · exact ⟨i + 1, e⟩

/-- A generic point of the ray tail: one eighth along the second edge. -/
theorem genericPt_not_mem (h : IsRay Tv c) :
    polyline (fun i => lp (c i)) (9 / 8) ∉ quarterPoints := by
  obtain ⟨d, hd⟩ := exists_dir_of_adj (h.adj 1)
  have hb0 : c 2 0 = c 1 0 + d.v.1 := congrArg Prod.fst hd
  have hb1 : c 2 1 = c 1 1 + d.v.2 := congrArg Prod.snd hd
  have e := polyline_natCast_add (fun i => lp (c i)) 1 (t := 1 / 8) (by norm_num) (by norm_num)
  rw [show ((1 : ℕ) : ℝ) + 1 / 8 = 9 / 8 by norm_num] at e
  rw [e]
  rintro ⟨⟨m0, h0⟩, ⟨m1, h1⟩⟩
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, lp_apply,
    show (1 + 1 : ℕ) = 2 from rfl, hb0, hb1] at h0 h1
  cases d <;> simp only [Dir.v] at h0 h1 <;> push_cast at h0 h1
  · have := int_le_of_cast (m := 8 * c 1 0 + 1 - 2 * m0) (x := 0) (by push_cast; linarith)
      (by norm_num)
    have := int_ge_of_cast (m := 8 * c 1 0 + 1 - 2 * m0) (x := 0) (by push_cast; linarith)
      (by norm_num)
    omega
  · have := int_le_of_cast (m := 8 * c 1 1 + 1 - 2 * m1) (x := 0) (by push_cast; linarith)
      (by norm_num)
    have := int_ge_of_cast (m := 8 * c 1 1 + 1 - 2 * m1) (x := 0) (by push_cast; linarith)
      (by norm_num)
    omega
  · have := int_le_of_cast (m := 8 * c 1 0 - 1 - 2 * m0) (x := 0) (by push_cast; linarith)
      (by norm_num)
    have := int_ge_of_cast (m := 8 * c 1 0 - 1 - 2 * m0) (x := 0) (by push_cast; linarith)
      (by norm_num)
    omega
  · have := int_le_of_cast (m := 8 * c 1 1 - 1 - 2 * m1) (x := 0) (by push_cast; linarith)
      (by norm_num)
    have := int_ge_of_cast (m := 8 * c 1 1 - 1 - 2 * m1) (x := 0) (by push_cast; linarith)
      (by norm_num)
    omega

theorem genericPt_mem (c : ℕ → Vertex 2) : polyline (fun i => lp (c i)) (9 / 8) ∈ rayTail c :=
  ⟨9 / 8, by norm_num, rfl⟩

end Ray5

/-! ### Cyclic chains of components -/

section FinChain

variable {N : ℕ}

theorem fin_eq_sub_one {j k : Fin (N + 2)} (h : k + 1 = j) : k = j - 1 := by
  rw [← h, add_sub_cancel_right]

theorem fin_succ_val {i : Fin (N + 2)} (hi : i.val + 1 < N + 2) :
    ((i + 1 : Fin (N + 2)) : ℕ) = i.val + 1 := by
  rw [Fin.val_add_one, if_neg]
  intro h; rw [h, Fin.val_last] at hi; omega

theorem chain_up (Q : Fin (N + 2) → Prop) {a b : ℕ} (hab : a ≤ b) (hb : b < N + 2)
    (hQa : Q ⟨a, by omega⟩) (hstep : ∀ i (hi : i < b), a ≤ i → Q ⟨i, by omega⟩ → Q ⟨i + 1, by omega⟩) :
    Q ⟨b, hb⟩ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction d with
  | zero => exact hQa
  | succ d ih =>
    exact hstep (a + d) (by omega) (by omega) (ih (by omega) (by omega) hQa
      (fun i hi hai hQ => hstep i (by omega) hai hQ))

/-- Walking up the cycle from `l ≠ j` by steps which never land on `j` or `j + 1` reaches
`j - 1`. -/
theorem fin_chain (Q : Fin (N + 2) → Prop) {j l : Fin (N + 2)} (hl : l ≠ j) (hQl : Q l)
    (hstep : ∀ i, Q i → i + 1 ≠ j → i + 1 ≠ j + 1 → Q (i + 1)) : Q (j - 1) := by
  have hsucc : ∀ i : ℕ, (hi : i + 1 < N + 2) →
      (⟨i, by omega⟩ : Fin (N + 2)) + 1 = ⟨i + 1, hi⟩ := fun i hi =>
    Fin.ext (fin_succ_val (i := ⟨i, by omega⟩) hi)
  have hv : ∀ k : Fin (N + 2), ((k + 1 : Fin (N + 2)) : ℕ) = 0 ∧ k.val = N + 1 ∨
      ((k + 1 : Fin (N + 2)) : ℕ) = k.val + 1 := by
    intro k
    have := Fin.val_add_one k
    by_cases hk : k = Fin.last (N + 1)
    · rw [if_pos hk] at this; exact Or.inl ⟨this, by rw [hk, Fin.val_last]⟩
    · rw [if_neg hk] at this; exact Or.inr this
  have hj1 : ∀ i : ℕ, (hi : i + 1 < N + 2) → i + 1 < j.val →
      (⟨i + 1, hi⟩ : Fin (N + 2)) ≠ j + 1 := by
    intro i hi hij h
    have := congrArg Fin.val h
    simp only at this
    rcases hv j with ⟨h1, -⟩ | h1 <;> omega
  -- the case `l < j`
  have below : ∀ l' : Fin (N + 2), l'.val < j.val → Q l' → Q (j - 1) := by
    intro l' hl' hQ
    have hjm : j.val - 1 < N + 2 := by omega
    have key := chain_up Q (a := l'.val) (b := j.val - 1) (by omega) hjm hQ
      (fun i hi hai hQi => by
        rw [← hsucc i (by omega)]
        refine hstep _ hQi ?_ ?_
        · rw [hsucc i (by omega)]; intro h; have := congrArg Fin.val h; simp at this; omega
        · rw [hsucc i (by omega)]; exact hj1 i (by omega) (by omega))
    have : (⟨j.val - 1, hjm⟩ : Fin (N + 2)) = j - 1 := by
      apply fin_eq_sub_one
      rw [hsucc _ (by omega)]
      ext; simp; omega
    rwa [← this]
  rcases lt_or_gt_of_ne (fun h : l.val = j.val => hl (Fin.ext h)) with h | h
  · exact below l h hQl
  · -- walk up to the last position, then wrap around
    have hlast := chain_up Q (a := l.val) (b := N + 1) (by omega) (by omega) hQl
      (fun i hi hai hQi => by
        rw [← hsucc i (by omega)]
        refine hstep _ hQi ?_ ?_
        · rw [hsucc i (by omega)]; intro h'; have := congrArg Fin.val h'; simp at this; omega
        · rw [hsucc i (by omega)]; intro h'
          have := congrArg Fin.val h'
          simp only at this
          rcases hv j with ⟨h1, h2⟩ | h1 <;> omega)
    have hL : (⟨N + 1, by omega⟩ : Fin (N + 2)) = Fin.last (N + 1) := rfl
    by_cases hj0 : j.val = 0
    · have : Fin.last (N + 1) = j - 1 := by
        apply fin_eq_sub_one
        ext; rw [Fin.val_add_one, if_pos rfl]; omega
      rw [← this, ← hL]; exact hlast
    · have h0 : Fin.last (N + 1) + 1 = 0 := by ext; rw [Fin.val_add_one, if_pos rfl]; rfl
      have hQ0 : Q 0 := by
        rw [← h0]
        refine hstep _ (hL ▸ hlast) ?_ ?_
        · rw [h0]; intro h'; exact hj0 (by rw [← h']; rfl)
        · rw [h0]; intro h'
          have := congrArg Fin.val h'
          rw [Fin.val_zero] at this
          have hl2 := l.isLt
          have hjl : j.val < l.val := h
          rcases hv j with ⟨h1, h2⟩ | h1
          · rw [h2] at hjl; omega
          · rw [h1] at this; omega
      exact below 0 (by simpa using Nat.pos_of_ne_zero hj0) hQ0

end FinChain

/-- Every point of the Jordan curve lies on one of the arcs `α_j` between consecutive points. -/
theorem exists_arc_mem {n : ℕ} {q : S2} {α : Path q q} {x : Fin (n + 2) → S2}
    {γ : ∀ i, Path (x i) northPole} {s : Fin (n + 2) → ℝ} {z : S2} (hz : z ∈ range α) :
    ∃ j, z ∈ Proofs.S2.jordanLoop α γ s j := by
  obtain ⟨u, ⟨hu1, hu2⟩, rfl⟩ := Proofs.S2.exists_loopLift_eq α hz (s 0)
  let J := (Finset.univ.filter fun j : Fin (n + 2) => s j ≤ u)
  have hJ : J.Nonempty := ⟨0, by simp [J, hu1]⟩
  set j := J.max' hJ with hj
  have hjJ : s j ≤ u := by have := J.max'_mem hJ; simp [J] at this; exact this
  refine ⟨j, Or.inl (Or.inl ⟨u, ⟨hjJ, ?_⟩, rfl⟩)⟩
  unfold Steps.S2.arcEnd
  split_ifs with hl
  · exact hu2.le
  · by_contra hcon
    push Not at hcon
    have hmem : j + 1 ∈ J := by simp [J]; exact hcon.le
    have := J.le_max' _ hmem
    rw [← hj] at this
    have hlt : j < j + 1 := Fin.lt_add_one_iff.2 (Fin.lt_last_iff_ne_last.2 hl)
    exact absurd this (not_le.2 hlt)

/-! ### The bi-infinite path through two consecutive rays -/

section PiPath

variable {ω : Configuration 2} {C : OpenComponent ω}

/-- The bi-infinite path: the ray `ra` reversed, the tree path `w 0, …, w K`, the ray `rb`. -/
noncomputable def piPath (ra rb w : ℕ → C) (K : ℕ) (m : ℤ) : C :=
  if m < 0 then ra m.natAbs else if m ≤ K then w m.toNat else rb (m.toNat - K)

variable {T : Set C} {ra rb w : ℕ → C} {K : ℕ}

theorem piPath_neg (hJ : JoinData T ra rb w K) (i : ℕ) : piPath ra rb w K (-(i : ℤ)) = ra i := by
  unfold piPath
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [hJ.w0]
  · rw [if_pos (by omega)]; simp

theorem piPath_mid {i : ℕ} (hi : i ≤ K) : piPath ra rb w K (i : ℤ) = w i := by
  unfold piPath
  rw [if_neg (by omega), if_pos (by exact_mod_cast hi)]; simp

theorem piPath_right (hJ : JoinData T ra rb w K) (i : ℕ) :
    piPath ra rb w K ((K + i : ℕ) : ℤ) = rb i := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [Nat.add_zero, piPath_mid le_rfl, hJ.wK]
  · unfold piPath
    rw [if_neg (by omega), if_neg (by push_cast; omega)]
    congr 1; omega

theorem int_cases (K : ℕ) (m : ℤ) :
    (∃ i : ℕ, m = -((i + 1 : ℕ) : ℤ)) ∨ (∃ i : ℕ, i ≤ K ∧ m = i) ∨
      ∃ i : ℕ, m = ((K + (i + 1) : ℕ) : ℤ) := by
  rcases lt_or_ge m 0 with h | h
  · exact Or.inl ⟨m.natAbs - 1, by omega⟩
  · rcases le_or_gt m K with h' | h'
    · exact Or.inr (Or.inl ⟨m.toNat, by omega, by omega⟩)
    · exact Or.inr (Or.inr ⟨m.toNat - K - 1, by omega⟩)

theorem piPath_adj (hJ : JoinData T ra rb w K) (m : ℤ) :
    (componentGraph C).Adj (piPath ra rb w K m) (piPath ra rb w K (m + 1)) := by
  rcases int_cases K m with ⟨i, rfl⟩ | ⟨i, hi, rfl⟩ | ⟨i, rfl⟩
  · rw [show -((i + 1 : ℕ) : ℤ) + 1 = -(i : ℤ) by push_cast; ring, piPath_neg hJ, piPath_neg hJ]
    exact (hJ.rayA i).symm
  · rcases eq_or_lt_of_le hi with rfl | hi'
    · rw [show (i : ℤ) + 1 = ((i + 1 : ℕ) : ℤ) by push_cast; ring,
        show i + 1 = i + 1 from rfl, piPath_mid le_rfl, hJ.wK,
        show ((i + 1 : ℕ) : ℤ) = ((i + 1 : ℕ) : ℤ) from rfl, piPath_right hJ 1]
      exact hJ.rayB 0
    · rw [show (i : ℤ) + 1 = ((i + 1 : ℕ) : ℤ) by push_cast; ring, piPath_mid hi,
        piPath_mid (by omega)]
      exact hJ.wadj i hi'
  · rw [show ((K + (i + 1) : ℕ) : ℤ) + 1 = ((K + (i + 2) : ℕ) : ℤ) by push_cast; ring,
      piPath_right hJ, piPath_right hJ]
    exact hJ.rayB (i + 1)

theorem piPath_injective (hJ : JoinData T ra rb w K) : Injective (piPath ra rb w K) := by
  intro m m' h
  rcases int_cases K m with ⟨i, rfl⟩ | ⟨i, hi, rfl⟩ | ⟨i, rfl⟩ <;>
    rcases int_cases K m' with ⟨j, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨j, rfl⟩
  · rw [piPath_neg hJ, piPath_neg hJ] at h; rw [hJ.injA h]
  · rw [piPath_neg hJ, piPath_mid hj] at h; exact (hJ.leaveA i (h ▸ hJ.wT j)).elim
  · rw [piPath_neg hJ, piPath_right hJ] at h; exact (hJ.disj _ _ h).elim
  · rw [piPath_mid hi, piPath_neg hJ] at h; exact (hJ.leaveA j (h ▸ hJ.wT i)).elim
  · rw [piPath_mid hi, piPath_mid hj] at h; rw [hJ.winj i j hi hj h]
  · rw [piPath_mid hi, piPath_right hJ] at h; exact (hJ.leaveB j (h ▸ hJ.wT i)).elim
  · rw [piPath_right hJ, piPath_neg hJ] at h; exact (hJ.disj _ _ h.symm).elim
  · rw [piPath_right hJ, piPath_mid hj] at h; exact (hJ.leaveB i (h ▸ hJ.wT j)).elim
  · rw [piPath_right hJ, piPath_right hJ] at h
    have := hJ.injB h
    rw [show i = j by omega]

theorem piPath_mem (hJ : JoinData T ra rb w K) (m : ℤ) :
    piPath ra rb w K m ∈ T ∨ (∃ i, piPath ra rb w K m = ra i) ∨ ∃ i, piPath ra rb w K m = rb i := by
  rcases int_cases K m with ⟨i, rfl⟩ | ⟨i, hi, rfl⟩ | ⟨i, rfl⟩
  · exact Or.inr (Or.inl ⟨_, piPath_neg hJ _⟩)
  · rw [piPath_mid hi]; exact Or.inl (hJ.wT i)
  · exact Or.inr (Or.inr ⟨_, piPath_right hJ _⟩)

/-- The vertices of the inner part: `ra 1, w 0, …, w K, rb 1`. -/
noncomputable def innerChain (ra rb w : ℕ → C) (K : ℕ) (i : ℕ) : Vertex 2 :=
  (piPath ra rb w K ((i : ℤ) - 1)).val

theorem innerChain_adj (hJ : JoinData T ra rb w K) (i : ℕ) :
    (lattice 2).Adj (innerChain ra rb w K i) (innerChain ra rb w K (i + 1)) := by
  have := lattice_adj_of_adj (piPath_adj hJ ((i : ℤ) - 1))
  simpa [innerChain] using this

theorem innerChain_segmentCondition (hJ : JoinData T ra rb w K) (M : ℕ) :
    SegmentCondition (fun i => lp (innerChain ra rb w K i)) M := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · exact ⟨fun i hi => absurd hi (by omega), fun i j _ hj => absurd hj (by omega)⟩
  refine segmentCondition_of_chain (fun i _ => innerChain_adj hJ i)
    (fun i j _ _ hij => Or.inl ?_) (Or.inr fun h0 => ?_)
  · have := piPath_injective hJ (Subtype.ext hij); omega
  · have := piPath_injective hJ (Subtype.ext h0); omega

end PiPath

section PiTrace

variable {ω : Configuration 2} {C : OpenComponent ω} {T : Set C} {ra rb w : ℕ → C} {K : ℕ}

theorem mem_pathTrace {π : ℤ → C} {x : E2} (m : ℤ)
    (hx : x ∈ segment ℝ (lp (π m).val) (lp (π (m + 1)).val)) : x ∈ Rigidity.Section5.pathTrace π :=
  mem_iUnion.2 ⟨m, hx⟩

theorem rayTailA_subset (hJ : JoinData T ra rb w K) :
    rayTail (fun i => (ra i).val) ⊆ Rigidity.Section5.pathTrace (piPath ra rb w K) := by
  intro x hx
  obtain ⟨i, hi⟩ := rayTail_mem_segment hx
  refine mem_pathTrace (-((i + 1 : ℕ) : ℤ)) ?_
  rw [show -((i + 1 : ℕ) : ℤ) + 1 = -(i : ℤ) by push_cast; ring, piPath_neg hJ, piPath_neg hJ,
    segment_symm]
  exact hi

theorem rayTailB_subset (hJ : JoinData T ra rb w K) :
    rayTail (fun i => (rb i).val) ⊆ Rigidity.Section5.pathTrace (piPath ra rb w K) := by
  intro x hx
  obtain ⟨i, hi⟩ := rayTail_mem_segment hx
  refine mem_pathTrace ((K + i : ℕ) : ℤ) ?_
  rw [show ((K + i : ℕ) : ℤ) + 1 = ((K + (i + 1) : ℕ) : ℤ) by push_cast; ring, piPath_right hJ,
    piPath_right hJ]
  exact hi

theorem inner_subset :
    polyline (fun i => lp (innerChain ra rb w K i)) '' Icc 0 (K + 2 : ℕ) ⊆
      Rigidity.Section5.pathTrace (piPath ra rb w K) := by
  rintro _ ⟨s, hs, rfl⟩
  obtain ⟨i, -, hsi⟩ := exists_index (by omega) hs
  refine mem_pathTrace ((i : ℤ) - 1) ?_
  have := polyline_mem_segment (fun i => lp (innerChain ra rb w K i)) i hsi
  simpa [innerChain] using this

theorem pathTrace_subset (hJ : JoinData T ra rb w K) :
    Rigidity.Section5.pathTrace (piPath ra rb w K) ⊆ quarterSkeleton := by
  intro x hx
  obtain ⟨m, hm⟩ := mem_iUnion.1 hx
  exact lattice_segment_subset_quarterSkeleton (lattice_adj_of_adj (piPath_adj hJ m)) hm

theorem innerChain_zero (hJ : JoinData T ra rb w K) : innerChain ra rb w K 0 = (ra 1).val := by
  simp [innerChain, show (-1 : ℤ) = -((1 : ℕ) : ℤ) by simp, piPath_neg hJ 1]

theorem innerChain_succ {i : ℕ} (hi : i ≤ K) : innerChain ra rb w K (i + 1) = (w i).val := by
  simp [innerChain, piPath_mid hi]

theorem innerChain_last (hJ : JoinData T ra rb w K) : innerChain ra rb w K (K + 2) = (rb 1).val := by
  simp only [innerChain]
  rw [show ((K + 2 : ℕ) : ℤ) - 1 = ((K + 1 : ℕ) : ℤ) by push_cast; ring, piPath_right hJ 1]

theorem inner_start (hJ : JoinData T ra rb w K) :
    polyline (fun i => lp (innerChain ra rb w K i)) (3 / 4) = exitPt (fun i => (ra i).val) := by
  rw [polyline_affine _ 0 (by norm_num) (by norm_num), exitPt_eq]
  simp only [innerChain_zero hJ, innerChain_succ (Nat.zero_le K), hJ.w0]
  norm_num
  module

theorem inner_minus (hJ : JoinData T ra rb w K) :
    polyline (fun i => lp (innerChain ra rb w K i)) (7 / 8) =
      polyline (fun i => lp (ra i).val) (1 / 8) := by
  rw [polyline_affine _ 0 (by norm_num) (by norm_num),
    polyline_affine _ 0 (by norm_num) (by norm_num)]
  simp only [innerChain_zero hJ, innerChain_succ (Nat.zero_le K), hJ.w0]
  norm_num
  module

theorem inner_end (hJ : JoinData T ra rb w K) :
    polyline (fun i => lp (innerChain ra rb w K i)) ((K + 2 : ℕ) - 3 / 4) =
      exitPt (fun i => (rb i).val) := by
  rw [polyline_affine _ (K + 1) (by push_cast; linarith) (by push_cast; linarith), exitPt_eq]
  simp only [innerChain_succ (le_refl K), innerChain_last hJ, hJ.wK]
  push_cast
  rw [show (K : ℝ) + 2 - 3 / 4 - (K + 1) = 1 / 4 by ring]

/-- The points of the open inner part lie only in cells of the connectors. -/
theorem inner_cells (hJ : JoinData T ra rb w K) {S : Set (ℤ × ℤ)}
    (hvS : ∀ t ∈ T, vcell t.val ∈ S) (heS : ∀ i < K, ecell (w i).val (w (i + 1)).val ∈ S)
    {s : ℝ} (hs1 : 3 / 4 < s) (hs2 : s < (K + 2 : ℕ) - 3 / 4) {c : ℤ × ℤ}
    (hc : polyline (fun i => lp (innerChain ra rb w K i)) s ∈ Cell c) : c ∈ S := by
  have hs0 : (0 : ℝ) ≤ s := by linarith
  have h1 := Nat.floor_le hs0
  have h2 := Nat.lt_floor_add_one s
  set i := ⌊s⌋₊ with hi
  have hiK : i ≤ K + 1 := by
    have : (i : ℝ) < K + 2 := by push_cast at hs2; linarith
    have : i < K + 2 := by exact_mod_cast this
    omega
  obtain ⟨d, hd⟩ := exists_dir_of_adj (innerChain_adj hJ i)
  rw [polyline_affine _ i h1 h2.le] at hc
  rcases cell_of_mem_lattice_segment hd (by linarith) (by linarith) hc with
    ⟨rfl, ht⟩ | ⟨rfl, ht1, ht2⟩ | ⟨rfl, ht⟩
  · rcases Nat.eq_zero_or_pos i with h0 | h0
    · rw [h0] at ht; push_cast at ht; linarith
    · obtain ⟨j, hj⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      rw [hj, innerChain_succ (by omega)]
      exact hvS _ (hJ.wT j)
  · rcases Nat.eq_zero_or_pos i with h0 | h0
    · rw [h0] at ht2; push_cast at ht2; linarith
    · rcases eq_or_lt_of_le hiK with hK | hK
      · rw [hK] at ht1; push_cast at ht1 hs2; linarith
      · obtain ⟨j, hj⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        rw [hj, innerChain_succ (by omega), innerChain_succ (by omega)]
        exact heS j (by omega)
  · rcases eq_or_lt_of_le hiK with hK | hK
    · rw [hK] at ht; push_cast at ht hs2; linarith
    · rw [innerChain_succ (by omega)]
      exact hvS _ (hJ.wT i)

end PiTrace

/-! ### Assembly lemmas -/

section Assembly

variable {ω : Configuration 2} {C : OpenComponent ω} {T : Set C} {E : Set (C × C)}

theorem TreeData.cellsOf (hT : TreeData T T E) : CellsOf (Subtype.val '' T) (cells T E) := by
  refine ⟨fun a ha => ?_, fun a b d hd hab => ?_, fun a ⟨t, ht, hta⟩ => ?_⟩
  · rcases ha with ⟨t, ht, h⟩ | ⟨e, he, h⟩
    · exact ⟨t, ht, pr_injective (double_inj h.symm)⟩
    · obtain ⟨d₁, hd₁⟩ := exists_dir_of_adj (lattice_adj_of_adj (hT.edge e he).2.2)
      rw [ecell_eq_of_dir hd₁] at h
      exact absurd h.symm double_add_v_ne
  · rcases hab with ⟨t, ht, h⟩ | ⟨e, he, h⟩
    · rw [ecell_eq_of_dir hd] at h; exact absurd h double_add_v_ne
    · obtain ⟨d₁, hd₁⟩ := exists_dir_of_adj (lattice_adj_of_adj (hT.edge e he).2.2)
      rw [ecell_eq_of_dir hd, ecell_eq_of_dir hd₁] at h
      obtain ⟨h1, h2⟩ := double_add_v_eq h.symm
      have he1 := (hT.edge e he).1
      have he2 := (hT.edge e he).2.1
      rw [← hd₁] at h1; rw [← hd₁, ← hd] at h2
      refine ⟨?_, ?_⟩
      · rcases h1 with h1 | h1
        · exact ⟨e.1, he1, pr_injective h1⟩
        · exact ⟨e.2, he2, pr_injective h1⟩
      · rcases h2 with h2 | h2
        · exact ⟨e.2, he2, pr_injective h2⟩
        · exact ⟨e.1, he1, pr_injective h2⟩
  · exact hta ▸ Or.inl ⟨t, ht, rfl⟩

theorem cells_finite (hT : TreeData T T E) (hTf : T.Finite) : (cells T E).Finite := by
  have hE : E.Finite := (hTf.prod hTf).subset fun e he => ⟨(hT.edge e he).1, (hT.edge e he).2.1⟩
  refine ((hTf.image fun a => vcell a.val).union (hE.image fun e => ecell e.1.val e.2.val)).subset ?_
  rintro c (⟨a, ha, rfl⟩ | ⟨e, he, rfl⟩)
  · exact Or.inl ⟨a, ha, rfl⟩
  · exact Or.inr ⟨e, he, rfl⟩

theorem ecell_comm (a b : Vertex 2) : ecell a b = ecell b a := add_comm _ _

theorem treeGraph_adj_cells {a b : C} (h : (treeGraph E).Adj a b) :
    ecell a.val b.val ∈ cells T E := by
  simp only [treeGraph, SimpleGraph.fromRel_adj] at h
  rcases h.2 with h | h
  · exact Or.inr ⟨(a, b), h, rfl⟩
  · exact Or.inr ⟨(b, a), h, ecell_comm _ _⟩

theorem treeGraph_adj (hT : TreeData T T E) {a b : C} (h : (treeGraph E).Adj a b) :
    (componentGraph C).Adj a b := by
  simp only [treeGraph, SimpleGraph.fromRel_adj] at h
  rcases h.2 with h | h
  · exact (hT.edge _ h).2.2
  · exact (hT.edge _ h).2.2.symm

/-- A path of the tree between two vertices of `T`, as a sequence. -/
theorem exists_treePath (hT : TreeData T T E) {u v : C} (hu : u ∈ T) (hv : v ∈ T) :
    ∃ (w : ℕ → C) (K : ℕ), w 0 = u ∧ w K = v ∧ (∀ i < K, (treeGraph E).Adj (w i) (w (i + 1))) ∧
      (∀ i j, i ≤ K → j ≤ K → w i = w j → i = j) ∧ ∀ i, w i ∈ T := by
  obtain ⟨p⟩ := hT.conn u hu v hv
  let p' := p.toPath
  have hp' : p'.val.IsPath := p'.property
  have hsupp : ∀ (x y : C) (q : (treeGraph E).Walk x y), x ∈ T → ∀ z ∈ q.support, z ∈ T := by
    intro x y q
    induction q with
    | nil => intro hx z hz; simp at hz; rwa [hz]
    | cons h q ih =>
      intro hx z hz
      rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact hx
      · simp only [treeGraph, SimpleGraph.fromRel_adj] at h
        refine ih ?_ z hz
        rcases h.2 with h | h
        · exact (hT.edge _ h).2.1
        · exact (hT.edge _ h).1
  refine ⟨p'.val.getVert, p'.val.length, p'.val.getVert_zero, p'.val.getVert_length,
    fun i hi => p'.val.adj_getVert_succ hi, fun i j hi hj h => hp'.getVert_injOn hi hj h,
    fun i => hsupp _ _ p'.val hu _ (p'.val.getVert_mem_support i)⟩

end Assembly

section Assembly2

theorem halfBall_not_mem {x q : E2} {k e : Fin 2} (hke : k ≠ e) (hk : IsQuarter (x k))
    (he : ¬ IsQuarter (x e)) {pos : Bool} (hq : q ∈ halfBall x k (qdist (x e)) pos) :
    q ∉ quarterSkeleton := fun hQ => by
  have := eq_of_mem_quarterSkeleton hke hk he hq.1 hQ
  have h2 := hq.2
  cases pos <;> simp only [Bool.false_eq_true, ↓reduceIte, mem_setOf_eq] at h2 <;> linarith

/-- The two points one eighth before and after the exit point lie on opposite sides of the side
of the start cell. -/
theorem exit_sides {c : ℕ → Vertex 2} (hadj : (lattice 2).Adj (c 0) (c 1)) {d : Dir}
    (hd : pr (c 1) = pr (c 0) + d.v) : ∃ b : Bool,
    polyline (fun i => lp (c i)) (3 / 8) ∈ halfBall (exitPt c) d.ax (1 / 4) b ∧
      polyline (fun i => lp (c i)) (1 / 8) ∈ halfBall (exitPt c) d.ax (1 / 4) (!b) := by
  set v := lp (c 1) - lp (c 0) with hv
  have ep : polyline (fun i => lp (c i)) (3 / 8) = exitPt c + (1 / 8 : ℝ) • v := by
    rw [polyline_affine _ 0 (by norm_num) (by norm_num), exitPt_eq]; norm_num; module
  have em : polyline (fun i => lp (c i)) (1 / 8) = exitPt c - (1 / 8 : ℝ) • v := by
    rw [polyline_affine _ 0 (by norm_num) (by norm_num), exitPt_eq]; norm_num; module
  have hn : ‖v‖ = 1 := norm_sub_lp_of_adj hadj
  have hb1 : ‖(1 / 8 : ℝ) • v‖ < 1 / 4 := by rw [norm_smul, hn]; norm_num
  have hball1 : exitPt c + (1 / 8 : ℝ) • v ∈ Metric.ball (exitPt c) (1 / 4) := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]; exact hb1
  have hball2 : exitPt c - (1 / 8 : ℝ) • v ∈ Metric.ball (exitPt c) (1 / 4) := by
    rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg]; exact hb1
  have hb0 : c 1 0 = c 0 0 + d.v.1 := congrArg Prod.fst hd
  have hb1' : c 1 1 = c 0 1 + d.v.2 := congrArg Prod.snd hd
  rw [ep, em]
  cases d
  · refine ⟨true, ⟨hball1, ?_⟩, ⟨hball2, ?_⟩⟩ <;>
      simp [hv, lp_apply, hb0, Dir.v, Dir.ax]
  · refine ⟨true, ⟨hball1, ?_⟩, ⟨hball2, ?_⟩⟩ <;>
      simp [hv, lp_apply, hb1', Dir.v, Dir.ax]
  · refine ⟨false, ⟨hball1, ?_⟩, ⟨hball2, ?_⟩⟩ <;>
      simp [hv, lp_apply, hb0, Dir.v, Dir.ax]
  · refine ⟨false, ⟨hball1, ?_⟩, ⟨hball2, ?_⟩⟩ <;>
      simp [hv, lp_apply, hb1', Dir.v, Dir.ax]

variable {σ : E2 → S2}

/-- The polyline between two parameters, read on the sphere. -/
noncomputable def segPath (hσ : Continuous σ) (g : ℕ → E2) (a b : ℝ) :
    Path (σ (polyline g a)) (σ (polyline g b)) where
  toFun t := σ (polyline g (a + t * (b - a)))
  continuous_toFun := hσ.comp ((continuous_polyline g).comp
    (continuous_const.add (continuous_subtype_val.mul continuous_const)))
  source' := by simp
  target' := by simp

theorem range_segPath (hσ : Continuous σ) (g : ℕ → E2) {a b : ℝ} (hab : a ≤ b) :
    range (segPath hσ g a b) = σ '' (polyline g '' Icc a b) := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨_, ⟨_, ⟨by nlinarith [t.2.1, t.2.2], by nlinarith [t.2.1, t.2.2]⟩, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    rcases eq_or_lt_of_le hab with rfl | hlt
    · refine ⟨0, ?_⟩
      simp [segPath, show s = a by linarith [hs.1, hs.2]]
    · refine ⟨⟨(s - a) / (b - a), div_nonneg (by linarith [hs.1]) (by linarith),
        (div_le_one (by linarith)).2 (by linarith [hs.2])⟩, ?_⟩
      show σ (polyline g (a + (s - a) / (b - a) * (b - a))) = _
      rw [div_mul_cancel₀ _ (by linarith)]; congr 2; ring

theorem segPath_injective (hσi : Injective σ) (hσ : Continuous σ) {g : ℕ → E2} {a b : ℝ}
    (hab : a < b) (hinj : InjOn (polyline g) (Icc a b)) : Injective (segPath hσ g a b) := by
  intro t t' h
  have h' := hinj ⟨by nlinarith [t.2.1, t.2.2], by nlinarith [t.2.1, t.2.2]⟩
    ⟨by nlinarith [t'.2.1, t'.2.2], by nlinarith [t'.2.1, t'.2.2]⟩ (hσi h)
  exact Subtype.ext (mul_right_cancel₀ (sub_ne_zero.2 hab.ne') (add_left_cancel h'))

theorem walk_generic {S : Set (ℤ × ℤ)} {L : List (ℤ × ℤ)} (hW : WalkProps S L) :
    polyline (walkPoly L) (1 / 4) ∈ walkTrace L ∧ polyline (walkPoly L) (1 / 4) ∉ quarterPoints := by
  have hL3 := hW.length
  have hL : 0 < L.length := by omega
  refine ⟨⟨1 / 4, ⟨by norm_num, by
    have : (3 : ℝ) ≤ L.length := by exact_mod_cast hL3
    linarith⟩, rfl⟩, ?_⟩
  have hcyc := getElem_mem_cyc L 0 hL (1 % L.length) (Nat.mod_lt _ hL) rfl
  obtain ⟨c, n, -, -, hpair⟩ := hW.sound _ hcyc
  have e0 : walkPoly L 0 = mpt (sideStart c n) := by
    simp only [walkPoly, walkCorner_eq hL, Nat.zero_mod]
    exact congrArg mpt (congrArg Prod.fst hpair)
  have e1 : walkPoly L 1 = mpt (sideEnd c n) := by
    simp only [walkPoly, walkCorner_eq hL]
    exact congrArg mpt (congrArg Prod.snd hpair)
  rw [polyline_affine _ 0 (by norm_num) (by norm_num)]
  simp only [Nat.cast_zero, sub_zero, zero_add, e1]
  rw [e0]
  rintro ⟨⟨m0, h0⟩, ⟨m1, h1⟩⟩
  obtain ⟨c1, c2⟩ := c
  cases n <;> simp only [mpt, sideStart, sideEnd, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply,
    smul_eq_mul, pt_zero, pt_one] at h0 h1 <;> push_cast at h0 h1
  · have := int_le_of_cast (m := 4 * c2 - 1 - 2 * m1) (x := 0) (by push_cast; linarith) (by norm_num)
    have := int_ge_of_cast (m := 4 * c2 - 1 - 2 * m1) (x := 0) (by push_cast; linarith) (by norm_num)
    omega
  · have := int_le_of_cast (m := 4 * c1 + 1 - 2 * m0) (x := 0) (by push_cast; linarith) (by norm_num)
    have := int_ge_of_cast (m := 4 * c1 + 1 - 2 * m0) (x := 0) (by push_cast; linarith) (by norm_num)
    omega
  · have := int_le_of_cast (m := 4 * c2 + 1 - 2 * m1) (x := 0) (by push_cast; linarith) (by norm_num)
    have := int_ge_of_cast (m := 4 * c2 + 1 - 2 * m1) (x := 0) (by push_cast; linarith) (by norm_num)
    omega
  · have := int_le_of_cast (m := 4 * c1 - 1 - 2 * m0) (x := 0) (by push_cast; linarith) (by norm_num)
    have := int_ge_of_cast (m := 4 * c1 - 1 - 2 * m0) (x := 0) (by push_cast; linarith) (by norm_num)
    omega

end Assembly2

section Assembly3

theorem generic_coords {x a b : E2} {k e : Fin 2} (hke : k ≠ e) (hx : x ∈ segment ℝ a b)
    (hab : a k = b k) (hak : IsQuarter (a k)) (hxZ : x ∉ quarterPoints) :
    IsQuarter (x k) ∧ ¬ IsQuarter (x e) := by
  have hxk : x k = a k := by
    obtain ⟨t, -, ht⟩ := coords_of_mem_segment hx
    rw [ht k, hab, sub_self, mul_zero, add_zero]
  refine ⟨hxk ▸ hak, fun he => hxZ ?_⟩
  fin_cases k <;> fin_cases e <;> simp_all [quarterPoints]

theorem isBounded_cell (c : ℤ × ℤ) : Bornology.IsBounded (Cell c) := by
  refine (Metric.isBounded_closedBall (x := pt (c.1 / 2) (c.2 / 2)) (r := 1)).subset ?_
  intro p ⟨h1, h2⟩
  rw [Metric.mem_closedBall, EuclideanSpace.dist_eq, Fin.sum_univ_two]
  simp only [pt_zero, pt_one, Real.dist_eq, sq_abs]
  rw [Real.sqrt_le_one]
  have := sq_le_sq' (abs_le.1 h1).1 (abs_le.1 h1).2
  have := sq_le_sq' (abs_le.1 h2).1 (abs_le.1 h2).2
  nlinarith

theorem isBounded_cells {S : Set (ℤ × ℤ)} (hS : S.Finite) :
    Bornology.IsBounded (⋃ c ∈ S, Cell c) :=
  (Bornology.isBounded_biUnion hS).2 fun c _ => isBounded_cell c

/-- A simple path minus its starting point is preconnected. -/
theorem isPreconnected_range_diff {X : Type*} [TopologicalSpace X] {a b : X} (γ : Path a b)
    (hγ : Injective γ) : IsPreconnected (range γ \ {a}) := by
  have : range γ \ {a} = γ.extend '' Ioc 0 1 := by
    ext z
    constructor
    · rintro ⟨⟨t, rfl⟩, hz⟩
      refine ⟨t, ⟨lt_of_le_of_ne t.2.1 fun h => hz ?_, t.2.2⟩, Path.extend_extends' γ t⟩
      have ht : t = 0 := Subtype.ext h.symm
      rw [mem_singleton_iff, ht, γ.source]
    · rintro ⟨s, ⟨hs0, hs1⟩, rfl⟩
      refine ⟨⟨⟨s, hs0.le, hs1⟩, (Path.extend_apply γ ⟨hs0.le, hs1⟩).symm⟩, fun h => ?_⟩
      rw [mem_singleton_iff, Path.extend_apply γ ⟨hs0.le, hs1⟩] at h
      have := congrArg Subtype.val (hγ (h.trans γ.source.symm)); simp at this; linarith
  rw [this]
  exact isPreconnected_Ioc.image _ γ.continuous_extend.continuousOn

theorem lp_not_mem_cells {Tv : Set (Vertex 2)} {S : Set (ℤ × ℤ)} (hS : CellsOf Tv S)
    {v : Vertex 2} (hv : v ∉ Tv) : lp v ∉ ⋃ c ∈ S, Cell c := by
  intro h
  obtain ⟨c, hc, h1, h2⟩ := mem_iUnion₂.1 h
  have e1 := half_cell_zero (a := v 0) rfl h1
  have e2 := half_cell_zero (a := v 1) rfl h2
  have : c = vcell v := Prod.ext e1 e2
  exact hv (hS.vert v (this ▸ hc))

end Assembly3

/-! ### `JordanLoopStep` -/

/-- The sphere is locally connected (it is a manifold). -/
theorem locallyConnectedSpace_S2 : LocallyConnectedSpace S2 := by
  haveI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  exact ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 2)) S2

/-- `JordanLoopStep`, from the Jordan curve theorem on `S²`. -/
theorem jordanLoopStep_main (hJ : External.JordanCurveTheoremSphere) :
    Steps.Section5.JordanLoopStep := by
  intro ω C T hTf hTc n hn ρ hρ hρ0 hρT hρd
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
  obtain ⟨σ, hσ, hσr⟩ := exists_sigma
  have hσc : Continuous σ := hσ.continuous
  have hσi : Injective σ := hσ.injective
  have hσN : ∀ y, σ y ≠ northPole := fun y h => by
    have : σ y ∈ range σ := mem_range_self y
    rw [hσr, h] at this; exact this rfl
  -- the tree of the connectors and its boundary walk
  obtain ⟨E, L, hTree, hW⟩ := exists_tree_walk hTf hTc ⟨ρ 0 0, hρ0 0⟩
  have hCells := hTree.cellsOf
  have hSfin := cells_finite hTree hTf
  set S := cells T E with hS
  set P : Set E2 := ⋃ c ∈ S, Cell c with hP
  -- the rays
  set cr : Fin (n' + 2) → ℕ → Vertex 2 := fun k i => (ρ k i).val with hcr
  have hray : ∀ k, IsRay (Subtype.val '' T) (cr k) := fun k =>
    ⟨fun i j h => (hρ k).1 (Subtype.ext h), fun i => lattice_adj_of_adj ((hρ k).2.1 i),
      ⟨_, hρ0 k, rfl⟩, fun i ⟨t, ht, hti⟩ => hρT k i (by rwa [← Subtype.ext hti])⟩
  have hdisj : ∀ k l, k ≠ l → ∀ i j, cr k i ≠ cr l j := fun k l hkl i j h =>
    Set.disjoint_left.1 (hρd k l hkl) ⟨i, rfl⟩ ⟨j, (Subtype.ext h).symm⟩
  -- the Jordan loop around the tree
  have hL3 := hW.length
  have hM0 : 0 < L.length := by omega
  set α := loopPath hσc (walkPoly L) L.length (walkPoly_length L) with hα
  have hαr : range α = σ '' walkTrace L := range_loopPath hσc _ _ _ hM0
  have hα_inj : InjOn α (Ico 0 1) := loopPath_injOn hσi hσc _ hM0 hW.segmentCondition
  -- the arcs to the north pole along the rays
  have hlim : ∀ k, Tendsto (fun t : ℝ => σ (polyline (fun i => lp (cr k i)) (1 / 4 + t / (1 - t))))
      (𝓝[<] 1) (𝓝 northPole) := fun k =>
    (tendsto_cocompact_northPole hσ hσr).comp ((tendsto_polyline_cocompact (hray k).inj
      (hray k).adj).comp (tendsto_reparam _))
  set γ : ∀ k, Path (σ (exitPt (cr k))) northPole := fun k =>
    rayPath hσc (fun i => lp (cr k i)) (1 / 4) (hlim k) with hγ
  set x : Fin (n' + 2) → S2 := fun k => σ (exitPt (cr k)) with hx
  have hγr : ∀ k, range (γ k) = σ '' rayTail (cr k) ∪ {northPole} := fun k =>
    range_rayPath hσc _ _ _
  have hγ_inj : ∀ k, Injective (γ k) := fun k =>
    rayPath_injective hσi hσr hσc _ ((hray k).injOn.mono (Ici_subset_Ici.2 (by norm_num)))
  -- the walk trace and the cells
  have hAside := fun {y : E2} (hy : y ∈ walkTrace L) => hW.mem_side hy
  have hAP : walkTrace L ⊆ P := fun y hy => by
    obtain ⟨c, n, hc, -, hyc⟩ := hW.mem_side hy
    rw [side_eq_inter] at hyc
    exact mem_iUnion₂.2 ⟨c, hc, hyc.1⟩
  have hGP : ∀ k, ∀ y ∈ rayTail (cr k), y ∈ P → y = exitPt (cr k) := fun k y hy hyP => by
    obtain ⟨c, hc, hyc⟩ := mem_iUnion₂.1 hyP
    exact (hray k).mem_cell_eq hCells hy hc hyc
  have hxA : ∀ k, exitPt (cr k) ∈ walkTrace L := fun k => by
    obtain ⟨d, hd⟩ := exists_dir_of_adj ((hray k).adj 0)
    obtain ⟨h1, h2, h3⟩ := (hray k).exitPt_mem_cells hCells hd
    exact hW.side_subset h2 h3 (by rw [side_eq_inter]; exact h1)
  have hαγ : ∀ k, range α ∩ range (γ k) = {x k} := fun k => by
    ext z
    simp only [mem_inter_iff, mem_singleton_iff, hαr, hγr, mem_union, mem_image]
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, ⟨y', hy', hyy'⟩ | hN⟩
      · rw [hσi hyy'] at hy'
        rw [hGP k y hy' (hAP hy)]
      · exact absurd hN (hσN y)
    · rintro rfl
      exact ⟨⟨_, hxA k, rfl⟩, Or.inl ⟨_, exitPt_mem_rayTail _, rfl⟩⟩
  have hγγ : ∀ k l, k ≠ l → range (γ k) ∩ range (γ l) = {northPole} := fun k l hkl => by
    ext z
    simp only [mem_inter_iff, mem_singleton_iff, hγr, mem_union, mem_image]
    constructor
    · rintro ⟨⟨y, hy, rfl⟩ | hN, ⟨y', hy', hyy'⟩ | hN'⟩
      · rw [hσi hyy'] at hy'
        exact absurd hy' (Set.disjoint_left.1 (rayTail_disjoint (hray k) (hray l)
          (hdisj k l hkl)) hy)
      · exact absurd hN' (hσN y)
      · exact hN
      · exact hN
    · rintro rfl
      exact ⟨Or.inr rfl, Or.inr rfl⟩
  have hx_inj : Injective x := fun k l h => by
    by_contra hkl
    have h' := hσi h
    exact Set.disjoint_left.1 (rayTail_disjoint (hray k) (hray l) (hdisj k l hkl))
      (exitPt_mem_rayTail _) (h' ▸ exitPt_mem_rayTail _)
  have hNα : northPole ∉ range α := by
    rw [hαr]; rintro ⟨y, -, hy⟩; exact hσN y hy
  refine ⟨σ, hσ, hσr, x, γ, _, α, hx_inj, hα_inj, hNα, hγ_inj, hαγ, hγγ, ?_⟩
  intro z hzΓ hzN
  haveI := locallyConnectedSpace_S2
  set Γ := range α ∪ ⋃ k, range (γ k) with hΓ
  have hΓσ : ∀ q, σ q ∈ Γ ↔ q ∈ walkTrace L ∨ ∃ k, q ∈ rayTail (cr k) := by
    intro q
    simp only [hΓ, mem_union, mem_iUnion, hαr, hγr, mem_image, hσi.eq_iff, exists_eq_right,
      mem_singleton_iff, hσN q, or_false]
  have hNΓ : northPole ∈ Γ := Or.inr (mem_iUnion.2 ⟨0, ⟨1, (γ 0).target⟩⟩)
  have hΓc : IsClosed Γ := (isCompact_range α.continuous).isClosed.union
    (isClosed_iUnion_of_finite fun k => (isCompact_range (γ k).continuous).isClosed)
  have hAQ : walkTrace L ⊆ quarterSkeleton := fun q hq => by
    obtain ⟨c, n, -, -, h⟩ := hW.mem_side hq
    exact side_subset_quarterSkeleton c n h
  have hΓQ : ∀ q, σ q ∈ Γ → q ∈ quarterSkeleton := fun q hq => by
    rcases (hΓσ q).1 hq with h | ⟨k, h⟩
    · exact hAQ h
    · exact (hray k).rayTail_subset h
  -- cyclic order of the points `x k` along `α`
  obtain ⟨perm, sP, hsP, hs01, hsx⟩ := Proofs.S2.parametrizeStep (n' + 2) _ α x hα_inj hx_inj
    fun i => ((hαγ i).ge (mem_singleton (x i))).1
  set x' : Fin (n' + 2) → S2 := fun k => x (perm k) with hx'
  set γ' : ∀ k, Path (x' k) northPole := fun k => γ (perm k) with hγ'
  have hD : Steps.S2.IsJordanCurvesData x' γ' α :=
    ⟨hx_inj.comp perm.injective, hα_inj, hNα, fun k => hγ_inj _, fun k => hαγ _,
      fun k l hkl => hγγ _ _ (perm.injective.ne hkl)⟩
  have hSc : Steps.S2.IsCyclicParametrization α x' sP :=
    ⟨hsP, by linarith [(hs01 (Fin.last (n' + 1))).2, (hs01 0).1], hsx⟩
  have hΓ' : range α ∪ ⋃ k, range (γ' k) = Γ := by
    rw [hΓ]; congr 1; exact perm.surjective.iUnion_comp fun i => range (γ i)
  -- the components `W j` between consecutive rays
  have hWex : ∀ j, ∃ W : Set S2, W.Nonempty ∧ frontier W = Proofs.S2.jordanLoop α γ' sP j ∧
      ∀ z ∈ W, z ∉ Γ ∧ connectedComponentIn Γᶜ z = W := by
    intro j
    obtain ⟨β, hβ, hβr⟩ := Proofs.S2.loopsStep n' _ α x' γ' sP hD hSc j
    obtain ⟨D, hD1, hD2, hD3⟩ := Proofs.S2.exists_preconnected hD hSc j
    have hβΓ : range β ⊆ range α ∪ ⋃ k, range (γ' k) := by
      rw [hβr]
      rintro y ((⟨u, -, rfl⟩ | hy) | hy)
      · exact Or.inl (Proofs.S2.loopLift_mem_range α u)
      · exact Or.inr (mem_iUnion.2 ⟨j, hy⟩)
      · exact Or.inr (mem_iUnion.2 ⟨j + 1, hy⟩)
    have h := Proofs.S2.exists_component_of_loop hJ _ β hβ hβΓ hD1
      (by rw [hβr]; exact hD2) (by rw [hβr]; exact hD3)
    rw [hΓ', hβr] at h
    exact h
  choose W hWne hWfr hWc using hWex
  have hWcomp : ∀ j, IsComp Γ (W j) := fun j => by
    obtain ⟨z0, hz0⟩ := hWne j
    rw [← (hWc j z0 hz0).2]
    exact isComp_connectedComponentIn (hWc j z0 hz0).1
  have hWcl : ∀ j, Proofs.S2.jordanLoop α γ' sP j ⊆ closure (W j) := fun j => by
    rw [← hWfr j]; exact frontier_subset_closure
  have hJ1 : ∀ j, range (γ' j) ⊆ Proofs.S2.jordanLoop α γ' sP j := fun j y hy => Or.inl (Or.inr hy)
  have hJ2 : ∀ j, range (γ' (j + 1)) ⊆ Proofs.S2.jordanLoop α γ' sP j := fun j y hy => Or.inr hy
  have hWN : ∀ j, northPole ∈ closure (W j) := fun j => hWcl j (hJ1 j ⟨1, (γ' j).target⟩)
  have hWne' : ∀ j k, j ≠ k → W j ≠ W k := fun j k h e =>
    Proofs.S2.jordanLoop_ne hD hSc h (by rw [← hWfr, ← hWfr, e])
  have hsub1 : ∀ m : Fin (n' + 2), m - 1 ≠ m := fun m h => by
    have : (1 : Fin (n' + 2)) = 0 := by simpa using congrArg (m - ·) h.symm
    exact absurd this (by simp)
  have hγ'm : ∀ m : Fin (n' + 2), range (γ' m) ⊆ Proofs.S2.jordanLoop α γ' sP (m - 1) := by
    intro m y hy
    have := hJ2 (m - 1)
    rw [sub_add_cancel] at this
    exact this hy
  -- the inner side `W_A` of `α`
  set D0 := ⋃ k, (range (γ k) \ {x k}) with hD0
  have hND0 : northPole ∈ D0 := mem_iUnion.2 ⟨0, ⟨⟨1, (γ 0).target⟩, fun h => hσN _ h.symm⟩⟩
  have hD0c : IsPreconnected D0 := isPreconnected_iUnion ⟨northPole, mem_iInter.2 fun k =>
    ⟨⟨1, (γ k).target⟩, fun h => hσN _ h.symm⟩⟩ fun k => isPreconnected_range_diff _ (hγ_inj k)
  have hD0α : D0 ⊆ (range α)ᶜ := by
    intro y hy hyα
    obtain ⟨k, hyk, hyx⟩ := mem_iUnion.1 hy
    have : y ∈ range α ∩ range (γ k) := ⟨hyα, hyk⟩
    rw [hαγ] at this; exact hyx this
  obtain ⟨U, V, hU, hV, hUc, hVc, hUV, hUVα, hfU, hfV⟩ := hJ _ α hα_inj
  obtain ⟨WA, OA, hWAo, hOAo, hWAc, hOAc, hAO, hAOα, hfWA, hfOA, hD0OA⟩ :
      ∃ WA OA : Set S2, IsOpen WA ∧ IsOpen OA ∧ IsConnected WA ∧ IsConnected OA ∧
        Disjoint WA OA ∧ WA ∪ OA = (range α)ᶜ ∧ frontier WA = range α ∧ frontier OA = range α ∧
        D0 ⊆ OA := by
    rcases hD0c.subset_or_subset hU hV hUV (hUVα ▸ hD0α) with h | h
    · exact ⟨V, U, hV, hU, hVc, hUc, hUV.symm, by rw [union_comm, hUVα], hfV, hfU, h⟩
    · exact ⟨U, V, hU, hV, hUc, hVc, hUV, hUVα, hfU, hfV, h⟩
  have hWAα : IsComp (range α) WA := isComp_of_sides hWAo hOAo hWAc.isPreconnected hAO hAOα
  have hOAα : IsComp (range α) OA :=
    isComp_of_sides hOAo hWAo hOAc.isPreconnected hAO.symm (by rw [union_comm, hAOα])
  have hWAΓ : IsComp Γ WA := by
    refine ⟨fun y hy hyΓ => ?_, hWAc.isPreconnected, fun Y hY hYΓ hYW =>
      hWAα.maximal Y hY (fun y hy hyα => hYΓ hy (Or.inl hyα)) hYW⟩
    rcases hyΓ with hyα | hyγ
    · exact hWAα.subset hy hyα
    · obtain ⟨k, hyk⟩ := mem_iUnion.1 hyγ
      by_cases hyx : y = x k
      · exact hWAα.subset hy (hyx ▸ (hαγ k).ge (mem_singleton _) |>.1)
      · exact Set.disjoint_left.1 hAO hy (hD0OA (mem_iUnion.2 ⟨k, hyk, hyx⟩))
  -- the points just inside the exit points lie in `W_A`
  have hfrP : frontier P ⊆ walkTrace L :=
    frontier_cells_subset hSfin fun c n hc hcn => hW.side_subset hc hcn
  have hqm : ∀ k, σ (polyline (fun i => lp (cr k i)) (1 / 8)) ∈ WA := by
    intro k
    obtain ⟨d, hd⟩ := exists_dir_of_adj ((hray k).adj 0)
    obtain ⟨hxc, hc0, hc0d⟩ := (hray k).exitPt_mem_cells hCells hd
    have hTS : TwoSided σ (range α) (exitPt (cr k)) (halfBall (exitPt (cr k)) d.ax (1 / 4) true)
        (halfBall (exitPt (cr k)) d.ax (1 / 4) false) := by
      refine twoSided_halfBalls (by norm_num) (fun q hq hqα => ?_) (fun q hq hqd => ?_)
      · rw [hαr] at hqα
        obtain ⟨q', hq', hqq'⟩ := hqα
        rw [hσi hqq'] at hq'
        obtain ⟨c, n, -, -, hqs⟩ := hW.mem_side hq'
        rw [side_eq_inter] at hqs
        exact near_exit hd hq hqs
      · rw [hαr]
        refine ⟨q, hW.side_subset hc0 hc0d ?_, rfl⟩
        rw [side_eq_inter]; exact diameter_exit hd hq hqd
    have hxα : σ (exitPt (cr k)) ∈ range α := by rw [hαr]; exact ⟨_, hxA k, rfl⟩
    have hWAOA : WA ≠ OA := fun h => by
      obtain ⟨y, hy⟩ := hWAc.nonempty
      exact Set.disjoint_left.1 hAO hy (h ▸ hy)
    obtain ⟨b, hqp, hqm'⟩ := exit_sides ((hray k).adj 0) hd
    have hqpOA : σ (polyline (fun i => lp (cr k i)) (3 / 8)) ∈ OA := by
      refine hD0OA (mem_iUnion.2 ⟨k, ?_, fun h => ?_⟩)
      · rw [hγr]; exact Or.inl ⟨_, ⟨3 / 8, by norm_num, rfl⟩, rfl⟩
      · have := (hray k).injOn (show (3 / 8 : ℝ) ∈ Ici 0 by norm_num)
          (show (1 / 4 : ℝ) ∈ Ici 0 by norm_num) (hσi h)
        norm_num at this
    rcases hTS.two_comps hσ hWAα hOAα hWAOA (by rw [← hfWA] at hxα; exact frontier_subset_closure hxα)
      (by rw [← hfOA] at hxα; exact frontier_subset_closure hxα) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      cases b
    · exact h1 ⟨_, hqm', rfl⟩
    · exact absurd hqpOA (Set.disjoint_left.1 hAO (h1 ⟨_, hqp, rfl⟩))
    · exact absurd hqpOA (Set.disjoint_left.1 hAO (h2 ⟨_, hqp, rfl⟩))
    · exact h2 ⟨_, hqm', rfl⟩
  -- `W_A` lies in the cells of the connectors
  have hq8P : ∀ k, polyline (fun i => lp (cr k i)) (1 / 8) ∈ P := by
    intro k
    obtain ⟨δ, hδ, hcov⟩ := exists_cell_cover (polyline (fun i => lp (cr k i)) (1 / 8))
    obtain ⟨c, hc, -⟩ := hcov _ (Metric.mem_ball_self hδ)
    obtain ⟨d, hd⟩ := exists_dir_of_adj ((hray k).adj 0)
    have hc' := hc
    rw [polyline_affine _ 0 (by norm_num) (by norm_num)] at hc'
    rcases cell_of_mem_lattice_segment hd (by norm_num) (by norm_num) hc' with
      ⟨rfl, -⟩ | ⟨-, h, -⟩ | ⟨-, h⟩
    · exact mem_iUnion₂.2 ⟨_, hCells.mem _ (hray k).start, hc⟩
    · norm_num at h
    · norm_num at h
  have hPc : IsClosed P := hSfin.isClosed_biUnion fun c _ => isClosed_cell c
  have hWAσ : WA ⊆ range σ := fun z hz => by
    rw [hσr]; intro hzN'
    rw [mem_singleton_iff] at hzN'
    exact Set.disjoint_left.1 hAO hz (hzN' ▸ hD0OA hND0)
  have hWAσP : WA ⊆ σ '' P := by
    have hcover : WA ⊆ σ '' Pᶜ ∪ σ '' interior P := by
      intro z hz
      obtain ⟨y, rfl⟩ := hWAσ hz
      by_cases hyP : y ∈ P
      · by_cases hyi : y ∈ interior P
        · exact Or.inr ⟨y, hyi, rfl⟩
        · exfalso
          have hyA : y ∈ walkTrace L := hfrP ⟨subset_closure hyP, hyi⟩
          exact hWAα.subset hz (by rw [hαr]; exact ⟨y, hyA, rfl⟩)
      · exact Or.inl ⟨y, hyP, rfl⟩
    have hdisjP : Disjoint (σ '' Pᶜ) (σ '' interior P) :=
      (disjoint_image_iff hσi).2 (disjoint_compl_left.mono_right interior_subset)
    rcases hWAc.isPreconnected.subset_or_subset (hσ.isOpenMap _ hPc.isOpen_compl)
      (hσ.isOpenMap _ isOpen_interior) hdisjP hcover with h | h
    · exfalso
      obtain ⟨y, hy, hyy⟩ := h (hqm 0)
      exact hy (hσi hyy ▸ hq8P 0)
    · exact h.trans (image_mono interior_subset)
  have hWAP : ∀ y, σ y ∈ WA → y ∈ P := fun y hy => by
    obtain ⟨y', hy', hyy'⟩ := hWAσP hy
    rwa [← hσi hyy']
  have hWA_N : northPole ∉ closure WA := fun h =>
    northPole_not_mem_closure_image hσ hσr (isBounded_cells hSfin) (closure_mono hWAσP h)
  have hWAne : ∀ j, WA ≠ W j := fun j h => hWA_N (h ▸ hWN j)
  have hfWAcl : range α ⊆ closure WA := by rw [← hfWA]; exact frontier_subset_closure
  -- classification of the components of `S² \ Γ`
  have hclass : ∀ z' ∉ Γ, connectedComponentIn Γᶜ z' = WA ∨
      ∃ j, connectedComponentIn Γᶜ z' = W j := by
    intro z' hz'
    have hXo : IsOpen (connectedComponentIn Γᶜ z') := hΓc.isOpen_compl.connectedComponentIn
    have hXc : IsComp Γ (connectedComponentIn Γᶜ z') := isComp_connectedComponentIn hz'
    have hXσ : connectedComponentIn Γᶜ z' ⊆ range σ := fun y hy => by
      rw [hσr]; intro hyN
      rw [mem_singleton_iff] at hyN
      exact hXc.subset hy (hyN ▸ hNΓ)
    obtain ⟨hx0A, hx0Q⟩ := walk_generic hW
    obtain ⟨xg, hxgZ, hxgF⟩ := exists_generic_frontier hσ hXo
      ⟨z', mem_connectedComponentIn hz'⟩ hXσ countable_quarterPoints hx0Q
      (fun h => hXc.subset h ((hΓσ _).2 (Or.inl hx0A)))
    have hxgcl : σ xg ∈ closure (connectedComponentIn Γᶜ z') := frontier_subset_closure hxgF
    have hxgΓ : σ xg ∈ Γ := by
      by_contra hn
      have h2 : σ xg ∉ connectedComponentIn Γᶜ z' := fun h => hxgF.2 (by rwa [hXo.interior_eq])
      have hO : IsOpen (connectedComponentIn Γᶜ (σ xg)) := hΓc.isOpen_compl.connectedComponentIn
      obtain ⟨y, hy1, hy2⟩ := mem_closure_iff.1 hxgcl _ hO (mem_connectedComponentIn hn)
      exact h2 ((isComp_connectedComponentIn hn).eq hXc ⟨y, hy1, hy2⟩ ▸
        mem_connectedComponentIn hn)
    rcases (hΓσ xg).1 hxgΓ with hxA' | ⟨k, hxk⟩
    · obtain ⟨c, n, hc, hcn, hxs⟩ := hW.mem_side hxA'
      obtain ⟨h1, h2, h3, h4⟩ := side_data c n
      have hTS := twoSided_of_segment (σ := σ) (Γ := Γ) (ax_ne_ax' n) hxs h1 h2 h3 h4 hxgZ hΓQ
        fun q hq => (hΓσ q).2 (Or.inl (hW.side_subset hc hcn hq))
      have hxα : σ xg ∈ range α := by rw [hαr]; exact ⟨xg, hxA', rfl⟩
      obtain ⟨j, hj⟩ := exists_arc_mem (γ := γ') (s := sP) hxα
      rcases hTS.eq_or_eq hσ hWAΓ (hWcomp j) (hWAne j) (hfWAcl hxα) (hWcl j hj) hXc hxgcl with
        h | h
      · exact Or.inl h
      · exact Or.inr ⟨j, h⟩
    · obtain ⟨a, b, k', e, hke, hxs, hsub, h1, h2, h3, h4⟩ := (hray k).generic hxk
      have hTS := twoSided_of_segment (σ := σ) (Γ := Γ) hke hxs h1 h2 h3 h4 hxgZ hΓQ
        fun q hq => (hΓσ q).2 (Or.inr ⟨k, hsub hq⟩)
      obtain ⟨m, rfl⟩ := perm.surjective k
      have hxr : σ xg ∈ range (γ' m) := by
        show σ xg ∈ range (γ (perm m)); rw [hγr]; exact Or.inl ⟨xg, hxk, rfl⟩
      rcases hTS.eq_or_eq hσ (hWcomp (m - 1)) (hWcomp m) (hWne' _ _ (hsub1 m))
        (hWcl _ (hγ'm m hxr)) (hWcl _ (hJ1 m hxr)) hXc hxgcl with h | h
      · exact Or.inr ⟨_, h⟩
      · exact Or.inr ⟨_, h⟩
  obtain ⟨j, hzj⟩ : ∃ j, connectedComponentIn Γᶜ z = W j := by
    rcases hclass z hzΓ with h | h
    · exact absurd (h ▸ hzN) hWA_N
    · exact h
  have hne1 : ∀ i : Fin (n' + 2), i ≠ i + 1 := fun i h => by
    have : (1 : Fin (n' + 2)) = 0 := by simpa using congrArg (· - i) h.symm
    exact absurd this (by simp)
  -- the two rays bounding `W j`, joined through the tree
  set a := perm j with ha
  set b := perm (j + 1) with hb
  have hab : a ≠ b := fun h => hne1 j (perm.injective h)
  obtain ⟨w, K, hw0, hwK, hwadj, hwinj, hwT⟩ := exists_treePath hTree (hρ0 a) (hρ0 b)
  have hJn : JoinData T (ρ a) (ρ b) w K :=
    ⟨(hρ a).2.1, (hρ b).2.1, (hρ a).1, (hρ b).1, hρT a, hρT b,
      fun i i' h => Set.disjoint_left.1 (hρd a b hab) ⟨i, rfl⟩ ⟨i', h.symm⟩, hw0, hwK,
      fun i hi => treeGraph_adj hTree (hwadj i hi), hwinj, hwT⟩
  set π := piPath (ρ a) (ρ b) w K with hπ
  set gI : ℕ → E2 := fun i => lp (innerChain (ρ a) (ρ b) w K i) with hgI
  set eI : ℝ := ((K + 2 : ℕ) : ℝ) - 3 / 4 with heI
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hK1 : (3 / 4 : ℝ) < eI := by rw [heI]; push_cast; linarith
  set Inner : Set E2 := polyline gI '' Icc (3 / 4) eI with hInner
  have hgI_inj : InjOn (polyline gI) (Icc (3 / 4) eI) := by
    refine (polyline_injOn_Icc (innerChain_segmentCondition hJn (K + 2)) ?_).mono ?_
    · intro h
      have := latticeEuclideanEmbedding.injective h
      rw [innerChain_zero hJn, innerChain_last hJn] at this
      exact hJn.disj 1 1 (Subtype.ext this)
    · intro s hs; exact ⟨by linarith [hs.1], by rw [heI] at hs; linarith [hs.2]⟩
  have hIstart : polyline gI (3 / 4) = exitPt (cr a) := inner_start hJn
  have hIend : polyline gI eI = exitPt (cr b) := inner_end hJn
  have hIcells : ∀ s, 3 / 4 < s → s < eI → ∀ c, polyline gI s ∈ Cell c → c ∈ S :=
    fun s h1 h2 c hc => inner_cells hJn (fun t ht => hCells.mem _ ⟨t, ht, rfl⟩)
      (fun i hi => treeGraph_adj_cells (hwadj i hi)) h1 h2 hc
  have hInnerP : Inner ⊆ P := by
    rintro _ ⟨s, hs, rfl⟩
    rcases eq_or_lt_of_le hs.1 with h | h
    · rw [← h, hIstart]; exact hAP (hxA a)
    rcases eq_or_lt_of_le hs.2 with h' | h'
    · rw [h', hIend]; exact hAP (hxA b)
    obtain ⟨δ, hδ, hcov⟩ := exists_cell_cover (polyline gI s)
    obtain ⟨c, hc, -⟩ := hcov _ (Metric.mem_ball_self hδ)
    exact mem_iUnion₂.2 ⟨c, hIcells s h h' c hc, hc⟩
  have hInnerA : ∀ s, 3 / 4 < s → s < eI → polyline gI s ∉ walkTrace L := by
    intro s h1 h2 hA
    obtain ⟨c, n, -, hcn, hs⟩ := hW.mem_side hA
    rw [side_eq_inter] at hs
    exact hcn (hIcells s h1 h2 _ hs.2)
  have hInnerWA : ∀ s, 3 / 4 < s → s < eI → σ (polyline gI s) ∈ WA := by
    have hpre : IsPreconnected (σ '' (polyline gI '' Ioo (3 / 4) eI)) :=
      (isPreconnected_Ioo.image _ (continuous_polyline gI).continuousOn).image _ hσc.continuousOn
    have h78 : (7 / 8 : ℝ) < eI := by rw [heI]; push_cast; linarith
    have hsub : σ '' (polyline gI '' Ioo (3 / 4) eI) ⊆ WA := by
      refine hWAα.maximal _ hpre ?_ ⟨σ (polyline gI (7 / 8)),
        ⟨_, ⟨7 / 8, ⟨by norm_num, h78⟩, rfl⟩, rfl⟩, by rw [inner_minus hJn]; exact hqm a⟩
      rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩ hα'
      rw [hαr] at hα'
      obtain ⟨y, hy, hyy⟩ := hα'
      rw [hσi hyy] at hy
      exact hInnerA s hs.1 hs.2 hy
    exact fun s h1 h2 => hsub ⟨_, ⟨s, ⟨h1, h2⟩, rfl⟩, rfl⟩
  -- the other rays miss the inner part
  have hInnerRay : ∀ m', m' ≠ a → m' ≠ b → ∀ q ∈ rayTail (cr m'), q ∉ Inner := by
    intro m' hma hmb q hq hqI
    have hqx := hGP m' q hq (hInnerP hqI)
    obtain ⟨s, hs, hqs⟩ := hqI
    rw [hqx] at hqs
    rcases eq_or_lt_of_le hs.1 with h | h
    · rw [← h, hIstart] at hqs
      exact Set.disjoint_left.1 (rayTail_disjoint (hray a) (hray m') (hdisj a m' (Ne.symm hma)))
        (exitPt_mem_rayTail _) (hqs ▸ exitPt_mem_rayTail _)
    rcases eq_or_lt_of_le hs.2 with h' | h'
    · rw [h', hIend] at hqs
      exact Set.disjoint_left.1 (rayTail_disjoint (hray b) (hray m') (hdisj b m' (Ne.symm hmb)))
        (exitPt_mem_rayTail _) (hqs ▸ exitPt_mem_rayTail _)
    obtain ⟨d, hd⟩ := exists_dir_of_adj ((hray m').adj 0)
    obtain ⟨hxc, -, hc0d⟩ := (hray m').exitPt_mem_cells hCells hd
    exact hc0d (hIcells s h h' _ (hqs ▸ hxc.2))
  -- the loop `β` through the north pole along `π`
  set ip := (segPath hσc gI (3 / 4) eI).cast (congrArg σ hIstart).symm (congrArg σ hIend).symm
    with hip
  have hipr : range ip = σ '' Inner := range_segPath hσc gI hK1.le
  have hip_inj : Injective ip := segPath_injective hσi hσc hK1 hgI_inj
  have hIγ : ∀ k ∈ ({a, b} : Set (Fin (n' + 2))), ∀ z ∈ range ip, z ∈ range (γ k) → z = x k := by
    intro k hk z hz1 hz2
    rw [hipr] at hz1; obtain ⟨y, hyI, rfl⟩ := hz1
    rw [hγr] at hz2
    rcases hz2 with ⟨y', hy', hyy'⟩ | hN
    · rw [hσi hyy'] at hy'
      rw [hGP k y hy' (hInnerP hyI)]
    · exact absurd hN (hσN y)
  set β := (γ a).symm.trans (ip.trans (γ b)) with hβ
  have hβ_inj : InjOn β (Ico 0 1) := by
    refine Proofs.S2.injOn_trans_Ico _ _ (Proofs.S2.injective_symm (hγ_inj a))
      (Proofs.S2.injective_trans _ _ hip_inj (hγ_inj b)
        fun z hz => hIγ b (Or.inr rfl) z hz.1 hz.2) ?_
    rw [Path.symm_range, Path.trans_range]
    rintro z ⟨hza, hz | hz⟩
    · exact Or.inr (hIγ a (Or.inl rfl) z hz hza)
    · exact Or.inl ((hγγ a b hab).subset ⟨hza, hz⟩)
  have hβr : range β = range (γ a) ∪ (range ip ∪ range (γ b)) := by
    rw [hβ, Path.trans_range, Path.symm_range, Path.trans_range]
  have hΓπσ : ∀ q, σ q ∈ range β → q ∈ rayTail (cr a) ∨ q ∈ Inner ∨ q ∈ rayTail (cr b) := by
    intro q hq
    rw [hβr, hγr, hipr, hγr] at hq
    rcases hq with (⟨y, hy, hyy⟩ | hN) | (⟨y, hy, hyy⟩ | (⟨y, hy, hyy⟩ | hN))
    · exact Or.inl (hσi hyy ▸ hy)
    · exact absurd hN (hσN q)
    · exact Or.inr (Or.inl (hσi hyy ▸ hy))
    · exact Or.inr (Or.inr (hσi hyy ▸ hy))
    · exact absurd hN (hσN q)
  have hΓπtr : ∀ q, σ q ∈ range β → q ∈ Rigidity.Section5.pathTrace π := by
    intro q hq
    rcases hΓπσ q hq with h | h | h
    · exact rayTailA_subset hJn h
    · obtain ⟨s, hs, rfl⟩ := h
      have hs2 : s ≤ ((K + 2 : ℕ) : ℝ) := by linarith [hs.2]
      exact inner_subset ⟨s, ⟨by linarith [hs.1], hs2⟩, rfl⟩
    · exact rayTailB_subset hJn h
  have hΓπQ : ∀ q, σ q ∈ range β → q ∈ quarterSkeleton := fun q hq =>
    pathTrace_subset hJn (hΓπtr q hq)
  -- a point `w` of `W j` next to the ray `a`, off the quarter skeleton
  have hxa_mem := genericPt_mem (cr a)
  have hxa_Z := genericPt_not_mem (hray a)
  obtain ⟨a1, b1, k1, e1, hke1, hxs1, hsub1', h11, h12, h13, h14⟩ := (hray a).generic hxa_mem
  set xa := polyline (fun i => lp (cr a i)) (9 / 8) with hxa
  have hTSa := twoSided_of_segment (σ := σ) (Γ := Γ) hke1 hxs1 h11 h12 h13 h14 hxa_Z hΓQ
    fun q hq => (hΓσ q).2 (Or.inr ⟨a, hsub1' hq⟩)
  have hxar : σ xa ∈ range (γ' j) := by
    show σ xa ∈ range (γ a); rw [hγr]; exact Or.inl ⟨xa, hxa_mem, rfl⟩
  have hcoord := generic_coords hke1 hxs1 h11 h12 hxa_Z
  have hWW := hTSa.two_comps hσ (hWcomp (j - 1)) (hWcomp j) (hWne' _ _ (hsub1 j))
    (hWcl _ (hγ'm j hxar)) (hWcl _ (hJ1 j hxar))
  obtain ⟨H, hHne, hHW, hHQ⟩ : ∃ H : Set E2, H.Nonempty ∧ σ '' H ⊆ W j ∧
      ∀ q ∈ H, q ∉ quarterSkeleton := by
    rcases hWW with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact ⟨_, hTSa.ne₂, h2, fun q hq => halfBall_not_mem hke1 hcoord.1 hcoord.2 hq⟩
    · exact ⟨_, hTSa.ne₁, h1, fun q hq => halfBall_not_mem hke1 hcoord.1 hcoord.2 hq⟩
  obtain ⟨wpt, hwH⟩ := hHne
  have hwW : σ wpt ∈ W j := hHW ⟨wpt, hwH, rfl⟩
  have hwtr : wpt ∉ Rigidity.Section5.pathTrace π := fun h =>
    hHQ wpt hwH (pathTrace_subset hJn h)
  -- the components `W i` miss the loop `β`
  have hWβ : ∀ i, ∀ y ∈ W i, y ∉ range β := by
    intro i y hy hyβ
    rw [hβr] at hyβ
    rcases hyβ with h | h | h
    · exact (hWcomp i).subset hy (Or.inr (mem_iUnion.2 ⟨a, h⟩))
    · rw [hipr] at h
      obtain ⟨q, ⟨s, hs, rfl⟩, rfl⟩ := h
      rcases eq_or_lt_of_le hs.1 with h1 | h1
      · rw [← h1, hIstart] at hy
        exact (hWcomp i).subset hy (Or.inl (by rw [hαr]; exact ⟨_, hxA a, rfl⟩))
      rcases eq_or_lt_of_le hs.2 with h2 | h2
      · rw [h2, hIend] at hy
        exact (hWcomp i).subset hy (Or.inl (by rw [hαr]; exact ⟨_, hxA b, rfl⟩))
      exact hWAne i (hWAΓ.eq (hWcomp i) ⟨_, hInnerWA s h1 h2, hy⟩)
    · exact (hWcomp i).subset hy (Or.inr (mem_iUnion.2 ⟨b, h⟩))
  -- the side `D` of `π` containing `w`
  obtain ⟨Uπ, Vπ, hUπ, hVπ, hUπc, hVπc, hUVπ, hUVπβ, hfUπ, hfVπ⟩ := hJ _ β hβ_inj
  have hwβ : σ wpt ∉ range β := hWβ j _ hwW
  obtain ⟨D, D', hDo, hD'o, hDc, hD'c, hDD', hDDβ, hfD, hfD', hwD⟩ :
      ∃ D D' : Set S2, IsOpen D ∧ IsOpen D' ∧ IsConnected D ∧ IsConnected D' ∧ Disjoint D D' ∧
        D ∪ D' = (range β)ᶜ ∧ frontier D = range β ∧ frontier D' = range β ∧ σ wpt ∈ D := by
    have : σ wpt ∈ Uπ ∪ Vπ := hUVπβ ▸ hwβ
    rcases this with h | h
    · exact ⟨Uπ, Vπ, hUπ, hVπ, hUπc, hVπc, hUVπ, hUVπβ, hfUπ, hfVπ, h⟩
    · exact ⟨Vπ, Uπ, hVπ, hUπ, hVπc, hUπc, hUVπ.symm, by rw [union_comm, hUVπβ], hfVπ, hfUπ, h⟩
  have hDcomp : IsComp (range β) D := isComp_of_sides hDo hD'o hDc.isPreconnected hDD' hDDβ
  have hD'comp : IsComp (range β) D' :=
    isComp_of_sides hD'o hDo hD'c.isPreconnected hDD'.symm (by rw [union_comm, hDDβ])
  have hDne : D ≠ D' := fun h => by
    obtain ⟨y, hy⟩ := hDc.nonempty
    exact Set.disjoint_left.1 hDD' hy (h ▸ hy)
  have hWD : ∀ i, (W i ∩ D).Nonempty → W i ⊆ D := fun i h =>
    hDcomp.maximal _ (hWcomp i).isPreconnected (fun y hy => hWβ i y hy) h
  have hWjD : W j ⊆ D := hWD j ⟨_, hwW, hwD⟩
  -- crossing the ray `a`, which lies on `π`, changes the side
  have hcross : ¬ (W (j - 1) ⊆ D ∧ W j ⊆ D) := by
    rintro ⟨h1, h2⟩
    have hTSaπ := twoSided_of_segment (σ := σ) (Γ := range β) hke1 hxs1 h11 h12 h13 h14 hxa_Z
      hΓπQ fun q hq => by
        rw [hβr]; exact Or.inl (by rw [hγr]; exact Or.inl ⟨q, hsub1' hq, rfl⟩)
    have hxaβ : σ xa ∈ range β := by rw [hβr]; exact Or.inl hxar
    have hbad : ∀ H' : Set E2, H'.Nonempty → σ '' H' ⊆ D → σ '' H' ⊆ D' → False :=
      fun H' ⟨y, hy⟩ hD1 hD2 => Set.disjoint_left.1 hDD' (hD1 ⟨y, hy, rfl⟩) (hD2 ⟨y, hy, rfl⟩)
    rcases hWW with ⟨g1, g2⟩ | ⟨g1, g2⟩ <;>
      rcases hTSaπ.two_comps hσ hDcomp hD'comp hDne
        (frontier_subset_closure (hfD.symm ▸ hxaβ))
        (frontier_subset_closure (hfD'.symm ▸ hxaβ)) with ⟨k1', k2'⟩ | ⟨k1', k2'⟩
    · exact hbad _ hTSa.ne₂ (g2.trans h2) k2'
    · exact hbad _ hTSa.ne₁ (g1.trans h1) k1'
    · exact hbad _ hTSa.ne₂ (g2.trans h1) k2'
    · exact hbad _ hTSa.ne₁ (g1.trans h2) k1'
  -- crossing a ray off `π` keeps the side
  have hstep : ∀ i, W i ⊆ D → i + 1 ≠ j → i + 1 ≠ j + 1 → W (i + 1) ⊆ D := by
    intro i hiD hi1 hi2
    set m' := perm (i + 1) with hm'
    have hm'a : m' ≠ a := fun h => hi1 (perm.injective h)
    have hm'b : m' ≠ b := fun h => hi2 (perm.injective h)
    have hxm_mem := genericPt_mem (cr m')
    have hxm_Z := genericPt_not_mem (hray m')
    obtain ⟨a2, b2, k2, e2, hke2, hxs2, hsub2, h21, h22, h23, h24⟩ := (hray m').generic hxm_mem
    set xm := polyline (fun i => lp (cr m' i)) (9 / 8) with hxm
    have hTSm := twoSided_of_segment (σ := σ) (Γ := Γ) hke2 hxs2 h21 h22 h23 h24 hxm_Z hΓQ
      fun q hq => (hΓσ q).2 (Or.inr ⟨m', hsub2 hq⟩)
    have hxmr : σ xm ∈ range (γ' (i + 1)) := by
      show σ xm ∈ range (γ m'); rw [hγr]; exact Or.inl ⟨xm, hxm_mem, rfl⟩
    have hcoord2 := generic_coords hke2 hxs2 h21 h22 hxm_Z
    have hball : ∀ q ∈ Metric.ball xm (qdist (xm e2)), σ q ∉ range β := by
      intro q hq hqβ
      have hqk := eq_of_mem_quarterSkeleton hke2 hcoord2.1 hcoord2.2 hq (hΓπQ q hqβ)
      have hqs := hsub2 (mem_segment_of_mem_ball hke2 h21 h23 h24 hcoord2.2 hxs2 hq hqk)
      rcases hΓπσ q hqβ with h | h | h
      · exact Set.disjoint_left.1 (rayTail_disjoint (hray a) (hray m') (hdisj a m' (Ne.symm hm'a)))
          h hqs
      · exact hInnerRay m' hm'a hm'b q hqs h
      · exact Set.disjoint_left.1 (rayTail_disjoint (hray b) (hray m') (hdisj b m' (Ne.symm hm'b)))
          h hqs
    have hpreB : IsPreconnected (σ '' Metric.ball xm (qdist (xm e2))) :=
      (convex_ball _ _).isPreconnected.image _ hσc.continuousOn
    have hBβ : σ '' Metric.ball xm (qdist (xm e2)) ⊆ (range β)ᶜ := by
      rintro _ ⟨q, hq, rfl⟩; exact hball q hq
    rcases hTSm.two_comps hσ (hWcomp i) (hWcomp (i + 1)) (hWne' _ _ (hne1 i))
      (hWcl _ (hJ2 i hxmr)) (hWcl _ (hJ1 (i + 1) hxmr)) with ⟨g1, g2⟩ | ⟨g1, g2⟩
    · obtain ⟨y1, hy1⟩ := hTSm.ne₁
      obtain ⟨y2, hy2⟩ := hTSm.ne₂
      have hBD := hDcomp.maximal _ hpreB hBβ ⟨σ y1, ⟨y1, hy1.1, rfl⟩, hiD (g1 ⟨y1, hy1, rfl⟩)⟩
      exact hWD _ ⟨σ y2, g2 ⟨y2, hy2, rfl⟩, hBD ⟨y2, hy2.1, rfl⟩⟩
    · obtain ⟨y1, hy1⟩ := hTSm.ne₁
      obtain ⟨y2, hy2⟩ := hTSm.ne₂
      have hBD := hDcomp.maximal _ hpreB hBβ ⟨σ y2, ⟨y2, hy2.1, rfl⟩, hiD (g2 ⟨y2, hy2, rfl⟩)⟩
      exact hWD _ ⟨σ y1, g1 ⟨y1, hy1, rfl⟩, hBD ⟨y1, hy1.1, rfl⟩⟩
  have hchainD : ∀ l, W l ⊆ D → l = j := fun l hl => by
    by_contra hlj
    exact hcross ⟨fin_chain (fun i => W i ⊆ D) hlj hl hstep, hWjD⟩
  -- the conclusion
  refine ⟨π, piPath_injective hJn, piPath_adj hJn, fun m => ?_, wpt, hwtr, fun y hy => ?_⟩
  · rcases piPath_mem hJn m with h | ⟨i, h⟩ | ⟨i, h⟩
    · exact Or.inl h
    · exact Or.inr (mem_iUnion.2 ⟨a, ⟨i, h.symm⟩⟩)
    · exact Or.inr (mem_iUnion.2 ⟨b, ⟨i, h.symm⟩⟩)
  · by_cases hys : y ∈ Steps.Section5.connectorSkeleton T ρ
    · exact Or.inr hys
    left
    rw [hzj]
    have hyT : y ∉ T := fun h => hys (Or.inl h)
    have hyP : lp y.val ∉ P := lp_not_mem_cells hCells fun ⟨t, ht, hty⟩ =>
      hyT (Subtype.ext hty ▸ ht)
    have hyΓ : σ (lp y.val) ∉ Γ := by
      rw [hΓσ]
      rintro (h | ⟨k, h⟩)
      · exact hyP (hAP h)
      · obtain ⟨i, hi⟩ := lp_mem_rayTail (hray k) h
        exact hys (Or.inr (mem_iUnion.2 ⟨k, ⟨i, (Subtype.ext hi).symm⟩⟩))
    have hyD : σ (lp y.val) ∈ D := by
      have hpre : IsPreconnected (σ '' connectedComponentIn
          (Rigidity.Section5.pathTrace π)ᶜ wpt) :=
        isPreconnected_connectedComponentIn.image _ hσc.continuousOn
      refine hDcomp.maximal _ hpre ?_ ⟨σ wpt, ⟨wpt, mem_connectedComponentIn hwtr, rfl⟩, hwD⟩
        ⟨_, hy, rfl⟩
      rintro _ ⟨q, hq, rfl⟩ hqβ
      exact connectedComponentIn_subset _ _ hq (hΓπtr q hqβ)
    rcases hclass _ hyΓ with h | ⟨l, hl⟩
    · exact absurd (hWAP _ (h ▸ mem_connectedComponentIn hyΓ)) hyP
    · have hyW : σ (lp y.val) ∈ W l := hl ▸ mem_connectedComponentIn hyΓ
      have := hchainD l (hWD l ⟨_, hyW, hyD⟩)
      rw [← this]; exact hyW

end Rigidity.Proofs.Section5.JordanLoop

namespace Rigidity.Proofs.Section5

/-- **`JordanLoopStep`** (step:5.12-loop, the one-point compactification and step:5.12-thick of
Proposition 5.12), from the Jordan curve theorem on `S²`. -/
theorem jordanLoopStep (hJ : External.JordanCurveTheoremSphere) : Steps.Section5.JordanLoopStep :=
  JordanLoop.jordanLoopStep_main hJ

end Rigidity.Proofs.Section5
