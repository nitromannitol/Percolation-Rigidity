import LatticeProb.Prob.Percolation.LatticeClusterBall
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# Lemma 5.19: planar geometry of lattice paths

Planar facts about the unit segments of the lattice `ℤ²` used in the proof of `SeparationStep`
(step:5.19-jordan, corrected draft L2051-2089): "lattice segments meet only at lattice points".

* `edgeSegment_inter`: two unit lattice segments are equal or meet only at common endpoints.
* `exists_halfBalls`: a point of a unit segment which is not a lattice point has a ball around it
  which, off the segment, consists of two convex half-balls missing every lattice segment.
* `polyline`: the piecewise linear interpolation of a sequence of points; it is continuous, and
  injective along a lattice chain without repeated vertices (`polyline_injOn`).
* `isConnected_compl_range_latticePoint`: the plane minus the lattice points is connected.
-/

open Set Filter Topology LatticeProb LatticeProb.Percolation

namespace Rigidity.Proofs.Section5

/-- The plane `ℝ²`. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The point of the plane at a vertex of `ℤ²`. -/
noncomputable abbrev latticePoint (x : Vertex 2) : Plane := latticeEuclideanEmbedding x

theorem latticePoint_apply (x : Vertex 2) (k : Fin 2) : latticePoint x k = (x k : ℝ) := rfl

theorem latticePoint_injective : Function.Injective latticePoint :=
  latticeEuclideanEmbedding.injective

/-- The unit segment of the plane between the lattice points of `x` and `y`. -/
def edgeSegment (x y : Vertex 2) : Set Plane := segment ℝ (latticePoint x) (latticePoint y)

theorem edgeSegment_comm (x y : Vertex 2) : edgeSegment x y = edgeSegment y x :=
  segment_symm ℝ _ _

theorem left_mem_edgeSegment (x y : Vertex 2) : latticePoint x ∈ edgeSegment x y :=
  left_mem_segment ℝ _ _

theorem right_mem_edgeSegment (x y : Vertex 2) : latticePoint y ∈ edgeSegment x y :=
  right_mem_segment ℝ _ _

theorem isCompact_edgeSegment (x y : Vertex 2) : IsCompact (edgeSegment x y) := by
  rw [edgeSegment, segment_eq_image_lineMap]
  exact isCompact_Icc.image (AffineMap.lineMap_continuous)

/-- The union of all unit segments of the lattice. -/
def latticeSkeleton : Set Plane :=
  ⋃ (x : Vertex 2) (y : Vertex 2) (_ : (nearestNeighborGraph 2).Adj x y), edgeSegment x y

theorem unit_apply (i k : Fin 2) : (unit i : Vertex 2) k = if k = i then 1 else 0 := by
  show (Pi.single i (1 : ℤ) : Fin 2 → ℤ) k = _
  simp [Pi.single_apply]

theorem mem_edgeSegment_add_unit {a : Vertex 2} {i : Fin 2} {v : Plane} :
    v ∈ edgeSegment a (a + unit i) ↔
      ∃ t ∈ Icc (0 : ℝ) 1, ∀ k, v k = a k + if k = i then t else 0 := by
  rw [edgeSegment, segment_eq_image']
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t, ht, fun k => ?_⟩
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, latticePoint_apply,
      Pi.add_apply, unit_apply, smul_eq_mul]
    split_ifs <;> push_cast <;> ring
  · rintro ⟨t, ht, h⟩
    refine ⟨t, ht, ?_⟩
    ext k
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, latticePoint_apply,
      Pi.add_apply, unit_apply, smul_eq_mul, h k]
    split_ifs <;> push_cast <;> ring

/-- An integer in `[0, 1]` is `0` or `1`. -/
theorem int_eq_zero_or_one {m : ℤ} {s : ℝ} (h : (m : ℝ) = s) (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    m = 0 ∨ m = 1 := by
  have : (0 : ℤ) ≤ m := by exact_mod_cast h ▸ h0
  have : m ≤ 1 := by exact_mod_cast h ▸ h1
  omega

theorem eq_latticePoint_iff {v : Plane} {z : Vertex 2} :
    v = latticePoint z ↔ v 0 = z 0 ∧ v 1 = z 1 := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h0, h1⟩
    ext k; fin_cases k
    · exact h0
    · exact h1

theorem vertex_ext_iff {x y : Vertex 2} : x = y ↔ x 0 = y 0 ∧ x 1 = y 1 := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h0, h1⟩
    funext k; fin_cases k
    · exact h0
    · exact h1

/-- Two unit lattice segments in normal form are equal or meet at a common endpoint. -/
theorem edgeSegment_unit_inter {a b : Vertex 2} {i j : Fin 2} {v : Plane}
    (ha : v ∈ edgeSegment a (a + unit i)) (hb : v ∈ edgeSegment b (b + unit j)) :
    (a = b ∧ i = j) ∨
      ∃ z, v = latticePoint z ∧ (z = a ∨ z = a + unit i) ∧ (z = b ∨ z = b + unit j) := by
  obtain ⟨t, ⟨t0, t1⟩, hv⟩ := mem_edgeSegment_add_unit.1 ha
  obtain ⟨s, ⟨s0, s1⟩, hw⟩ := mem_edgeSegment_add_unit.1 hb
  have e0 := (hv 0).symm.trans (hw 0)
  have e1 := (hv 1).symm.trans (hw 1)
  have v0 := hv 0
  have v1 := hv 1
  simp only [vertex_ext_iff, eq_latticePoint_iff, Pi.add_apply, unit_apply] at *
  fin_cases i <;> fin_cases j <;> simp at e0 e1 v0 v1 ⊢
  · -- both horizontal
    have hb1 : a 1 = b 1 := by exact_mod_cast e1
    have hd : ((a 0 - b 0 : ℤ) : ℝ) = s - t := by push_cast; linarith
    have hlo : (-1 : ℤ) ≤ a 0 - b 0 := by
      have : (-1 : ℝ) ≤ ((a 0 - b 0 : ℤ) : ℝ) := by rw [hd]; linarith
      exact_mod_cast this
    have hhi : a 0 - b 0 ≤ 1 := by
      have : ((a 0 - b 0 : ℤ) : ℝ) ≤ 1 := by rw [hd]; linarith
      exact_mod_cast this
    rcases (by omega : a 0 - b 0 = 0 ∨ a 0 - b 0 = 1 ∨ a 0 - b 0 = -1) with h | h | h
    · left; exact ⟨by omega, hb1⟩
    · have : ((a 0 - b 0 : ℤ) : ℝ) = 1 := by exact_mod_cast h
      push_cast at this hd
      right; refine ⟨a, ⟨by rw [v0]; linarith, v1⟩, Or.inl ⟨rfl, rfl⟩, Or.inr ⟨by omega, hb1⟩⟩
    · have : ((a 0 - b 0 : ℤ) : ℝ) = -1 := by exact_mod_cast h
      push_cast at this hd
      right; refine ⟨b, ⟨by rw [v0]; linarith, by rw [v1]; exact_mod_cast hb1⟩,
        Or.inr ⟨by omega, hb1.symm⟩, Or.inl ⟨rfl, rfl⟩⟩
  · -- a horizontal, b vertical
    have h0 : ((b 0 - a 0 : ℤ) : ℝ) = t := by push_cast; linarith
    have h1 : ((a 1 - b 1 : ℤ) : ℝ) = s := by push_cast; linarith
    rcases int_eq_zero_or_one h0 t0 t1 with m | m <;> rcases int_eq_zero_or_one h1 s0 s1 with n | n
    all_goals
      have hm : ((b 0 - a 0 : ℤ) : ℝ) = _ := congrArg (fun z : ℤ => (z : ℝ)) m
      have hn : ((a 1 - b 1 : ℤ) : ℝ) = _ := congrArg (fun z : ℤ => (z : ℝ)) n
      push_cast at hm hn
      refine ⟨![b 0, a 1], ⟨by simp; linarith, by simp; linarith⟩, ?_, ?_⟩ <;> simp <;> omega
  · -- a vertical, b horizontal
    have h0 : ((a 0 - b 0 : ℤ) : ℝ) = s := by push_cast; linarith
    have h1 : ((b 1 - a 1 : ℤ) : ℝ) = t := by push_cast; linarith
    rcases int_eq_zero_or_one h0 s0 s1 with m | m <;> rcases int_eq_zero_or_one h1 t0 t1 with n | n
    all_goals
      have hm : ((a 0 - b 0 : ℤ) : ℝ) = _ := congrArg (fun z : ℤ => (z : ℝ)) m
      have hn : ((b 1 - a 1 : ℤ) : ℝ) = _ := congrArg (fun z : ℤ => (z : ℝ)) n
      push_cast at hm hn
      refine ⟨![a 0, b 1], ⟨by simp; linarith, by simp; linarith⟩, ?_, ?_⟩ <;> simp <;> omega
  · -- both vertical
    have hb0 : a 0 = b 0 := by exact_mod_cast e0
    have hd : ((a 1 - b 1 : ℤ) : ℝ) = s - t := by push_cast; linarith
    have hlo : (-1 : ℤ) ≤ a 1 - b 1 := by
      have : (-1 : ℝ) ≤ ((a 1 - b 1 : ℤ) : ℝ) := by rw [hd]; linarith
      exact_mod_cast this
    have hhi : a 1 - b 1 ≤ 1 := by
      have : ((a 1 - b 1 : ℤ) : ℝ) ≤ 1 := by rw [hd]; linarith
      exact_mod_cast this
    rcases (by omega : a 1 - b 1 = 0 ∨ a 1 - b 1 = 1 ∨ a 1 - b 1 = -1) with h | h | h
    · left; exact ⟨hb0, by omega⟩
    · have : ((a 1 - b 1 : ℤ) : ℝ) = 1 := by exact_mod_cast h
      push_cast at this hd
      right; refine ⟨a, ⟨v0, by rw [v1]; linarith⟩, Or.inl ⟨rfl, rfl⟩, Or.inr ⟨hb0, by omega⟩⟩
    · have : ((a 1 - b 1 : ℤ) : ℝ) = -1 := by exact_mod_cast h
      push_cast at this hd
      right; refine ⟨b, ⟨by rw [v0]; exact_mod_cast hb0, by rw [v1]; linarith⟩,
        Or.inr ⟨hb0.symm, by omega⟩, Or.inl ⟨rfl, rfl⟩⟩

/-- A lattice edge in normal form `(a, a + e_i)`. -/
theorem exists_unit_of_adj {x y : Vertex 2} (h : (nearestNeighborGraph 2).Adj x y) :
    ∃ a i, ((x = a ∧ y = a + unit i) ∨ (x = a + unit i ∧ y = a)) ∧
      edgeSegment x y = edgeSegment a (a + unit i) := by
  obtain ⟨i, rfl | rfl⟩ := h
  · exact ⟨x, i, Or.inl ⟨rfl, rfl⟩, rfl⟩
  · exact ⟨y, i, Or.inr ⟨rfl, rfl⟩, edgeSegment_comm _ _⟩

/-- Two unit lattice segments are equal or meet only at common endpoints. -/
theorem edgeSegment_inter {x y x' y' : Vertex 2} (h : (nearestNeighborGraph 2).Adj x y)
    (h' : (nearestNeighborGraph 2).Adj x' y') {v : Plane} (hv : v ∈ edgeSegment x y)
    (hv' : v ∈ edgeSegment x' y') :
    (x = x' ∧ y = y') ∨ (x = y' ∧ y = x') ∨
      ∃ z, v = latticePoint z ∧ (z = x ∨ z = y) ∧ (z = x' ∨ z = y') := by
  obtain ⟨a, i, hxy, hs⟩ := exists_unit_of_adj h
  obtain ⟨b, j, hxy', hs'⟩ := exists_unit_of_adj h'
  rw [hs] at hv
  rw [hs'] at hv'
  rcases edgeSegment_unit_inter hv hv' with ⟨rfl, rfl⟩ | ⟨z, hz, hza, hzb⟩
  · rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hxy' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  · right; right
    refine ⟨z, hz, ?_, ?_⟩
    · rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> tauto
    · rcases hxy' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> tauto

/-- The trace of the lattice chain `g` along the edges `(g n, g (n + 1))`, `n ∈ S`. -/
def chainTrace (g : ℤ → Vertex 2) (S : Set ℤ) : Set Plane :=
  ⋃ n ∈ S, edgeSegment (g n) (g (n + 1))

/-- The vertices of the chain `g` on the edges indexed by `S`. -/
def chainVerts (g : ℤ → Vertex 2) (S : Set ℤ) : Set (Vertex 2) :=
  {z | ∃ n ∈ S, z = g n ∨ z = g (n + 1)}

theorem chainTrace_mono (g : ℤ → Vertex 2) {S T : Set ℤ} (h : S ⊆ T) :
    chainTrace g S ⊆ chainTrace g T :=
  biUnion_subset_biUnion_left h

theorem isClosed_chainTrace (g : ℤ → Vertex 2) {S : Set ℤ} (hS : S.Finite) :
    IsClosed (chainTrace g S) :=
  (hS.isCompact_biUnion fun _ _ => isCompact_edgeSegment _ _).isClosed

/-- Two lattice chains without common edges meet only at common vertices. -/
theorem mem_chainTrace_inter {g g' : ℤ → Vertex 2} {S S' : Set ℤ}
    (hg : ∀ n ∈ S, (nearestNeighborGraph 2).Adj (g n) (g (n + 1)))
    (hg' : ∀ n ∈ S', (nearestNeighborGraph 2).Adj (g' n) (g' (n + 1)))
    (hne : ∀ n ∈ S, ∀ n' ∈ S', ¬ ((g n = g' n' ∧ g (n + 1) = g' (n' + 1)) ∨
      (g n = g' (n' + 1) ∧ g (n + 1) = g' n')))
    {v : Plane} (hv : v ∈ chainTrace g S) (hv' : v ∈ chainTrace g' S') :
    ∃ z ∈ chainVerts g S ∩ chainVerts g' S', v = latticePoint z := by
  simp only [chainTrace, mem_iUnion] at hv hv'
  obtain ⟨n, hn, hv⟩ := hv
  obtain ⟨n', hn', hv'⟩ := hv'
  rcases edgeSegment_inter (hg n hn) (hg' n' hn') hv hv' with h | h | ⟨z, hz, h1, h2⟩
  · exact absurd (Or.inl h) (hne n hn n' hn')
  · exact absurd (Or.inr h) (hne n hn n' hn')
  · exact ⟨z, ⟨⟨n, hn, h1⟩, ⟨n', hn', h2⟩⟩, hz⟩

/-- Lattice chains without common vertices have disjoint traces. -/
theorem disjoint_chainTrace {g g' : ℤ → Vertex 2} {S S' : Set ℤ}
    (hg : ∀ n ∈ S, (nearestNeighborGraph 2).Adj (g n) (g (n + 1)))
    (hg' : ∀ n ∈ S', (nearestNeighborGraph 2).Adj (g' n) (g' (n + 1)))
    (hd : Disjoint (chainVerts g S) (chainVerts g' S')) :
    Disjoint (chainTrace g S) (chainTrace g' S') := by
  have hne : ∀ n ∈ S, ∀ n' ∈ S', ¬ ((g n = g' n' ∧ g (n + 1) = g' (n' + 1)) ∨
      (g n = g' (n' + 1) ∧ g (n + 1) = g' n')) := by
    rintro n hn n' hn' (⟨h, -⟩ | ⟨h, -⟩)
    · exact hd.ne_of_mem ⟨n, hn, Or.inl rfl⟩ ⟨n', hn', Or.inl rfl⟩ h
    · exact hd.ne_of_mem ⟨n, hn, Or.inl rfl⟩ ⟨n', hn', Or.inr rfl⟩ h
  rw [Set.disjoint_left]
  intro v hv hv'
  obtain ⟨z, hz, -⟩ := mem_chainTrace_inter hg hg' hne hv hv'
  exact hd.ne_of_mem hz.1 hz.2 rfl

/-! ### Piecewise linear interpolation -/

/-- The piecewise linear interpolation through the points `g n` at the integers `n`. -/
noncomputable def polyline (g : ℤ → Plane) (s : ℝ) : Plane :=
  AffineMap.lineMap (g ⌊s⌋) (g (⌊s⌋ + 1)) (Int.fract s)

theorem polyline_intCast (g : ℤ → Plane) (n : ℤ) : polyline g n = g n := by
  simp [polyline]

theorem polyline_eqOn (g : ℤ → Plane) (n : ℤ) :
    EqOn (polyline g) (fun s => AffineMap.lineMap (g n) (g (n + 1)) (s - n))
      (Icc (n : ℝ) (n + 1)) := by
  rintro s ⟨h1, h2⟩
  rcases h2.lt_or_eq with h2 | h2
  · have : ⌊s⌋ = n := Int.floor_eq_iff.2 ⟨h1, h2⟩
    simp [polyline, this, Int.fract]
  · have : s = ((n + 1 : ℤ) : ℝ) := by push_cast; exact h2
    simp only [this, polyline_intCast]
    push_cast
    simp

theorem continuous_polyline (g : ℤ → Plane) : Continuous (polyline g) := by
  have hc : ∀ n : ℤ, Continuous (fun s : ℝ => AffineMap.lineMap (g n) (g (n + 1)) (s - n)) :=
    fun n => AffineMap.lineMap_continuous.comp (continuous_id.sub continuous_const)
  refine continuous_iff_continuousAt.2 fun s => continuousAt_iff_continuous_left_right.2 ⟨?_, ?_⟩
  · have h1 : ((⌈s⌉ - 1 : ℤ) : ℝ) < s := by
      push_cast; linarith [Int.ceil_lt_add_one s]
    have h2 : s ≤ ((⌈s⌉ - 1 : ℤ) : ℝ) + 1 := by push_cast; linarith [Int.le_ceil s]
    have hmem : Icc ((⌈s⌉ - 1 : ℤ) : ℝ) ((⌈s⌉ - 1 : ℤ) + 1) ∈ 𝓝[≤] s :=
      Icc_mem_nhdsLE_of_mem ⟨h1, h2⟩
    exact (hc _).continuousWithinAt.congr_of_eventuallyEq
      (eventually_of_mem hmem (polyline_eqOn g _)) (polyline_eqOn g _ ⟨h1.le, h2⟩)
  · have h1 : ((⌊s⌋ : ℤ) : ℝ) ≤ s := Int.floor_le s
    have h2 : s < ((⌊s⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one s
    have hmem : Icc ((⌊s⌋ : ℤ) : ℝ) ((⌊s⌋ : ℤ) + 1) ∈ 𝓝[≥] s :=
      Icc_mem_nhdsGE_of_mem ⟨h1, h2⟩
    exact (hc _).continuousWithinAt.congr_of_eventuallyEq
      (eventually_of_mem hmem (polyline_eqOn g _)) (polyline_eqOn g _ ⟨h1, h2.le⟩)

theorem polyline_mem_edgeSegment (g : ℤ → Vertex 2) (s : ℝ) :
    polyline (latticePoint ∘ g) s ∈ edgeSegment (g ⌊s⌋) (g (⌊s⌋ + 1)) := by
  rw [edgeSegment, segment_eq_image_lineMap]
  exact ⟨Int.fract s, ⟨Int.fract_nonneg s, (Int.fract_lt_one s).le⟩, rfl⟩

theorem polyline_mem_chainTrace (g : ℤ → Vertex 2) {S : Set ℤ} {s : ℝ} (hs : ⌊s⌋ ∈ S) :
    polyline (latticePoint ∘ g) s ∈ chainTrace g S :=
  mem_biUnion hs (polyline_mem_edgeSegment g s)

theorem polyline_image_Icc (g : ℤ → Vertex 2) {a b : ℤ} (hab : a < b) :
    polyline (latticePoint ∘ g) '' Icc (a : ℝ) b = chainTrace g (Ico a b) := by
  ext v
  constructor
  · rintro ⟨s, ⟨h1, h2⟩, rfl⟩
    rcases h2.lt_or_eq with h2 | rfl
    · exact polyline_mem_chainTrace g ⟨Int.le_floor.2 h1, Int.floor_lt.2 h2⟩
    · refine mem_biUnion (x := b - 1) ⟨by omega, by omega⟩ ?_
      rw [polyline_intCast]
      simpa using right_mem_edgeSegment (g (b - 1)) (g b)
  · intro hv
    simp only [chainTrace, mem_iUnion] at hv
    obtain ⟨n, ⟨hn1, hn2⟩, hv⟩ := hv
    rw [edgeSegment, segment_eq_image_lineMap] at hv
    obtain ⟨t, ⟨t0, t1⟩, rfl⟩ := hv
    have ha : (a : ℝ) ≤ n := by exact_mod_cast hn1
    have hb : (n : ℝ) + 1 ≤ b := by exact_mod_cast hn2
    refine ⟨n + t, ⟨by linarith, by linarith⟩, ?_⟩
    rw [polyline_eqOn _ n ⟨by linarith, by linarith⟩]
    simp

theorem range_polyline (g : ℤ → Vertex 2) :
    range (polyline (latticePoint ∘ g)) = chainTrace g univ := by
  ext v
  constructor
  · rintro ⟨s, rfl⟩
    exact polyline_mem_chainTrace g (mem_univ _)
  · intro hv
    simp only [chainTrace, mem_iUnion] at hv
    obtain ⟨n, -, hv⟩ := hv
    have : v ∈ chainTrace g (Ico n (n + 1)) := mem_biUnion (x := n) ⟨le_rfl, by omega⟩ hv
    rw [← polyline_image_Icc g (by omega : n < n + 1)] at this
    obtain ⟨s, -, rfl⟩ := this
    exact ⟨s, rfl⟩

/-- The interpolation of a lattice chain without repeated vertices or edges is injective. -/
theorem polyline_injOn {g : ℤ → Vertex 2} {S : Set ℝ}
    (hadj : ∀ s ∈ S, (nearestNeighborGraph 2).Adj (g ⌊s⌋) (g (⌊s⌋ + 1)))
    (hinj : ∀ s ∈ S, ∀ s' ∈ S, g ⌊s⌋ = g ⌊s'⌋ → ⌊s⌋ = ⌊s'⌋)
    (hback : ∀ s ∈ S, ∀ s' ∈ S, ⌊s⌋ ≠ ⌊s'⌋ → g ⌊s⌋ = g (⌊s'⌋ + 1) →
      g (⌊s⌋ + 1) ≠ g ⌊s'⌋) :
    InjOn (polyline (latticePoint ∘ g)) S := by
  have hne : ∀ s ∈ S, latticePoint (g ⌊s⌋) ≠ latticePoint (g (⌊s⌋ + 1)) :=
    fun s hs h => (hadj s hs).ne (latticePoint_injective h)
  have key : ∀ s ∈ S, ∀ z, polyline (latticePoint ∘ g) s = latticePoint z →
      (z = g ⌊s⌋ ∨ z = g (⌊s⌋ + 1)) → z = g ⌊s⌋ ∧ Int.fract s = 0 := by
    intro s hs z hz hz'
    rcases hz' with rfl | rfl
    · refine ⟨rfl, AffineMap.lineMap_injective ℝ (hne s hs) ?_⟩
      simpa [polyline] using hz
    · exfalso
      have : Int.fract s = 1 := AffineMap.lineMap_injective ℝ (hne s hs) (by simpa [polyline] using hz)
      exact (Int.fract_lt_one s).ne this
  intro s hs s' hs' heq
  have hm' := polyline_mem_edgeSegment g s'
  rw [← heq] at hm'
  rcases edgeSegment_inter (hadj s hs) (hadj s' hs') (polyline_mem_edgeSegment g s) hm' with
    ⟨h1, -⟩ | ⟨h1, h2⟩ | ⟨z, hz, h1, h2⟩
  · have hn := hinj s hs s' hs' h1
    have : Int.fract s = Int.fract s' := by
      apply AffineMap.lineMap_injective ℝ (hne s hs)
      have := heq
      simp only [polyline, Function.comp] at this
      rw [hn] at this ⊢
      exact this
    rw [← Int.floor_add_fract s, ← Int.floor_add_fract s', hn, this]
  · by_cases hn : ⌊s⌋ = ⌊s'⌋
    · rw [← hn] at h2
      exact absurd h2.symm (hadj s hs).ne
    · exact absurd h2 (hback s hs s' hs' hn h1)
  · obtain ⟨hz1, hf1⟩ := key s hs z hz h1
    obtain ⟨hz2, hf2⟩ := key s' hs' z (heq ▸ hz) h2
    have hn := hinj s hs s' hs' (hz1.symm.trans hz2)
    rw [← Int.floor_add_fract s, ← Int.floor_add_fract s', hn, hf1, hf2]

/-! ### Half-balls around a point of a lattice segment -/

theorem abs_coord_sub_lt {v w : Plane} {δ : ℝ} (hw : w ∈ Metric.ball v δ) (k : Fin 2) :
    |w k - v k| < δ := by
  rw [← Real.dist_eq]
  exact (PiLp.dist_apply_le w v k).trans_lt hw

/-- Off a unit lattice segment, a small ball around a non-lattice point of the segment consists
of two convex half-balls which miss every lattice segment. -/
theorem exists_halfBalls {x y : Vertex 2} (h : (nearestNeighborGraph 2).Adj x y) {v : Plane}
    (hv : v ∈ edgeSegment x y) (hvl : v ∉ range latticePoint) :
    ∃ δ > 0, ∃ H₁ H₂ : Set Plane, IsPreconnected H₁ ∧ IsPreconnected H₂ ∧ H₁.Nonempty ∧
      H₂.Nonempty ∧ Disjoint H₁ latticeSkeleton ∧ Disjoint H₂ latticeSkeleton ∧
      Metric.ball v δ ⊆ H₁ ∪ H₂ ∪ edgeSegment x y := by
  obtain ⟨a, i, -, hs⟩ := exists_unit_of_adj h
  rw [hs] at hv ⊢
  obtain ⟨t, ⟨t0, t1⟩, hvt⟩ := mem_edgeSegment_add_unit.1 hv
  obtain ⟨j, hji, hk⟩ : ∃ j : Fin 2, j ≠ i ∧ ∀ k, k = i ∨ k = j := by
    fin_cases i
    · exact ⟨1, by decide, by decide⟩
    · exact ⟨0, by decide, by decide⟩
  have vi : v i = a i + t := by simpa using hvt i
  have vj : v j = a j := by simpa [hji] using hvt j
  have tpos : 0 < t := by
    rcases t0.lt_or_eq with h | h
    · exact h
    · refine absurd ⟨a, ?_⟩ hvl
      ext k
      rw [hvt k, ← h]
      simp [latticePoint_apply]
  have tlt : t < 1 := by
    rcases t1.lt_or_eq with h | h
    · exact h
    · refine absurd ⟨a + unit i, ?_⟩ hvl
      ext k
      rw [hvt k, h]
      rcases hk k with rfl | rfl <;> simp [latticePoint_apply, unit_apply, hji]
  set δ := min t (1 - t) with hδ
  have hδt : δ ≤ t := min_le_left _ _
  have hδt' : δ ≤ 1 - t := min_le_right _ _
  have hδ0 : 0 < δ := lt_min tpos (by linarith)
  have hlin : IsLinearMap ℝ (fun w : Plane => w j) := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  -- a point of the ball on a lattice segment lies on the line of `[a, a + e_i]`
  have hskel : ∀ w ∈ Metric.ball v δ, w ∈ latticeSkeleton → w j = v j := by
    intro w hw hws
    simp only [latticeSkeleton, mem_iUnion] at hws
    obtain ⟨x', y', hxy', hw'⟩ := hws
    obtain ⟨b, l, -, hs'⟩ := exists_unit_of_adj hxy'
    rw [hs'] at hw'
    obtain ⟨s, ⟨s0, s1⟩, hws⟩ := mem_edgeSegment_add_unit.1 hw'
    have hi := abs_coord_sub_lt hw i
    have hj := abs_coord_sub_lt hw j
    rcases hk l with rfl | rfl
    · have wj : w j = b j := by simpa [hji] using hws j
      rw [wj, vj] at hj ⊢
      have : |((b j - a j : ℤ) : ℝ)| < 1 := by push_cast; linarith
      have : |b j - a j| < 1 := by exact_mod_cast this
      have : b j = a j := by rw [abs_lt] at this; omega
      rw [this]
    · have wi : w i = b i := by simpa [hji.symm] using hws i
      rw [wi, vi, abs_lt] at hi
      have h1 : (a i : ℝ) < b i := by linarith
      have h2 : (b i : ℝ) < a i + 1 := by linarith
      have h1' : a i < b i := by exact_mod_cast h1
      have h2' : b i < a i + 1 := by exact_mod_cast h2
      omega
  refine ⟨δ, hδ0, Metric.ball v δ ∩ {w | v j < w j}, Metric.ball v δ ∩ {w | w j < v j},
    ((convex_ball v δ).inter (convex_halfSpace_gt hlin _)).isPreconnected,
    ((convex_ball v δ).inter (convex_halfSpace_lt hlin _)).isPreconnected, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨v + (δ / 2) • EuclideanSpace.single j 1, ?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
        PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith
    · simp; linarith
  · refine ⟨v - (δ / 2) • EuclideanSpace.single j 1, ?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul,
        PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith
    · simp; linarith
  · rw [Set.disjoint_left]
    rintro w ⟨hw, hwj⟩ hws
    exact (hskel w hw hws).not_gt hwj
  · rw [Set.disjoint_left]
    rintro w ⟨hw, hwj⟩ hws
    exact (hskel w hw hws).not_lt hwj
  · intro w hw
    rcases lt_trichotomy (v j) (w j) with hlt | heq | hgt
    · exact Or.inl (Or.inl ⟨hw, hlt⟩)
    · right
      have hi := abs_coord_sub_lt hw i
      rw [vi, abs_lt] at hi
      refine mem_edgeSegment_add_unit.2 ⟨w i - a i, ⟨by linarith, by linarith⟩, fun k => ?_⟩
      rcases hk k with rfl | rfl
      · simp
      · simp [hji, ← heq, vj]
    · exact Or.inl (Or.inr ⟨hw, hgt⟩)

/-! ### The square `[-R, R]²` and the lattice points -/

/-- The closed square `[-R, R]²` of the plane. -/
def realCube (R : ℕ) : Set Plane := {v | ∀ k, |v k| ≤ R}

theorem convex_realCube (R : ℕ) : Convex ℝ (realCube R) := by
  have : realCube R = ⋂ k, (fun v : Plane => v k) ⁻¹' Icc (-(R : ℝ)) R := by
    ext v; simp [realCube, abs_le]
  rw [this]
  exact convex_iInter fun k => (convex_Icc _ _).is_linear_preimage ⟨fun _ _ => rfl, fun _ _ => rfl⟩

theorem abs_intCast_le_iff {m : ℤ} {R : ℕ} : |(m : ℝ)| ≤ R ↔ |m| ≤ (R : ℤ) := by
  rw [← Int.cast_abs, ← Int.cast_natCast (R := ℝ), Int.cast_le]

theorem latticePoint_mem_realCube {x : Vertex 2} {R : ℕ} (hx : ∀ k, |x k| ≤ (R : ℤ)) :
    latticePoint x ∈ realCube R := fun k => by
  rw [latticePoint_apply]
  exact abs_intCast_le_iff.2 (hx k)

/-- A unit lattice segment between vertices outside `Q_R` misses the square `[-R, R]²`. -/
theorem disjoint_edgeSegment_realCube {x y : Vertex 2} (h : (nearestNeighborGraph 2).Adj x y)
    {R : ℕ} (hx : ¬ ∀ k, |x k| ≤ (R : ℤ)) (hy : ¬ ∀ k, |y k| ≤ (R : ℤ)) :
    Disjoint (edgeSegment x y) (realCube R) := by
  obtain ⟨a, i, hxy, hs⟩ := exists_unit_of_adj h
  have ha : ¬ ∀ k, |a k| ≤ (R : ℤ) := by rcases hxy with ⟨rfl, -⟩ | ⟨-, rfl⟩ <;> assumption
  have ha' : ¬ ∀ k, |(a + unit i) k| ≤ (R : ℤ) := by
    rcases hxy with ⟨-, rfl⟩ | ⟨rfl, -⟩ <;> assumption
  rw [hs, Set.disjoint_left]
  intro w hw hwc
  obtain ⟨t, ⟨t0, t1⟩, hwt⟩ := mem_edgeSegment_add_unit.1 hw
  have hoff : ∀ k, k ≠ i → |a k| ≤ (R : ℤ) := by
    intro k hk
    have := hwc k
    rw [hwt k, if_neg hk, add_zero] at this
    exact abs_intCast_le_iff.1 this
  push Not at ha ha'
  obtain ⟨k, hk⟩ := ha
  obtain ⟨k', hk'⟩ := ha'
  have hki : k = i := by by_contra hne; exact (hoff k hne).not_gt hk
  have hki' : k' = i := by
    by_contra hne
    simp only [Pi.add_apply, unit_apply, if_neg hne, add_zero] at hk'
    exact (hoff k' hne).not_gt hk'
  have hA : (R : ℤ) < |a i| := hki ▸ hk
  have hB : (R : ℤ) < |a i + 1| := by
    have := hki' ▸ hk'
    simpa [unit_apply] using this
  have hwi := hwc i
  rw [hwt i, if_pos rfl, abs_le] at hwi
  have h1 : (a i : ℝ) ≤ R := by linarith
  have h2 : -(R : ℝ) ≤ a i + 1 := by linarith
  have h1' : a i ≤ R := by exact_mod_cast h1
  have h2' : -(R : ℤ) ≤ a i + 1 := by exact_mod_cast h2
  rw [lt_abs] at hA hB
  omega

theorem isConnected_compl_range_latticePoint : IsConnected (range latticePoint)ᶜ :=
  (countable_range _).isConnected_compl_of_one_lt_rank
    (by rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]; norm_num)

theorem dense_compl_range_latticePoint : Dense (range latticePoint)ᶜ :=
  (countable_range latticePoint).dense_compl ℝ

/-- The lattice points of infinitely many distinct vertices form an unbounded set. -/
theorem not_isBounded_image {g : ℤ → Vertex 2} (hg : Function.Injective g) {T : Set ℤ}
    (hT : T.Infinite) : ¬ Bornology.IsBounded ((latticePoint ∘ g) '' T) := by
  intro hb
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_ball (latticePoint 0)).1 hb
  refine hT (Set.Finite.of_finite_image ?_ hg.injOn)
  refine (finite_latticeEuclideanBall (0 : Vertex 2) r).subset ?_
  rintro _ ⟨n, hn, rfl⟩
  exact hr ⟨n, hn, rfl⟩

/-! ### Lattice points on lattice segments -/

/-- A lattice point on a unit lattice segment is one of its endpoints. -/
theorem eq_of_latticePoint_mem_edgeSegment {x y z : Vertex 2}
    (h : (nearestNeighborGraph 2).Adj x y) (hz : latticePoint z ∈ edgeSegment x y) :
    z = x ∨ z = y := by
  obtain ⟨a, i, hxy, hs⟩ := exists_unit_of_adj h
  rw [hs] at hz
  obtain ⟨t, ⟨t0, t1⟩, hzt⟩ := mem_edgeSegment_add_unit.1 hz
  have hi := hzt i
  rw [if_pos rfl, latticePoint_apply] at hi
  have hm : ((z i - a i : ℤ) : ℝ) = t := by push_cast; linarith
  have hoff : ∀ k, k ≠ i → z k = a k := fun k hk => by
    have := hzt k
    rw [if_neg hk, add_zero, latticePoint_apply] at this
    exact Int.cast_injective this
  rcases int_eq_zero_or_one hm t0 t1 with e | e
  · have hza : z = a := by
      funext k
      by_cases hk : k = i
      · rw [hk]; omega
      · exact hoff k hk
    rcases hxy with ⟨rfl, -⟩ | ⟨-, rfl⟩
    · exact Or.inl hza
    · exact Or.inr hza
  · have hza : z = a + unit i := by
      funext k
      by_cases hk : k = i
      · rw [hk, Pi.add_apply, unit_apply, if_pos rfl]; omega
      · rw [Pi.add_apply, unit_apply, if_neg hk, add_zero]; exact hoff k hk
    rcases hxy with ⟨-, rfl⟩ | ⟨rfl, -⟩
    · exact Or.inr hza
    · exact Or.inl hza

/-- The interpolation of a lattice chain meets a lattice point only at an integer, where it is
the vertex of the chain. -/
theorem polyline_eq_latticePoint {g : ℤ → Vertex 2} {s : ℝ} {z : Vertex 2}
    (hadj : (nearestNeighborGraph 2).Adj (g ⌊s⌋) (g (⌊s⌋ + 1)))
    (hz : polyline (latticePoint ∘ g) s = latticePoint z) : z = g ⌊s⌋ ∧ Int.fract s = 0 := by
  have hne : latticePoint (g ⌊s⌋) ≠ latticePoint (g (⌊s⌋ + 1)) :=
    fun h => hadj.ne (latticePoint_injective h)
  have hm := polyline_mem_edgeSegment g s
  rw [hz] at hm
  rcases eq_of_latticePoint_mem_edgeSegment hadj hm with rfl | rfl
  · refine ⟨rfl, AffineMap.lineMap_injective ℝ hne ?_⟩
    simpa [polyline] using hz
  · exfalso
    have : Int.fract s = 1 :=
      AffineMap.lineMap_injective ℝ hne (by simpa [polyline] using hz)
    exact (Int.fract_lt_one s).ne this

theorem latticePoint_mem_chainTrace {g : ℤ → Vertex 2} {S : Set ℤ}
    (hg : ∀ n ∈ S, (nearestNeighborGraph 2).Adj (g n) (g (n + 1))) {z : Vertex 2}
    (hz : latticePoint z ∈ chainTrace g S) : z ∈ chainVerts g S := by
  simp only [chainTrace, mem_iUnion] at hz
  obtain ⟨n, hn, hz⟩ := hz
  exact ⟨n, hn, eq_of_latticePoint_mem_edgeSegment (hg n hn) hz⟩

theorem chainTrace_subset_latticeSkeleton {g : ℤ → Vertex 2} {S : Set ℤ}
    (hg : ∀ n ∈ S, (nearestNeighborGraph 2).Adj (g n) (g (n + 1))) :
    chainTrace g S ⊆ latticeSkeleton := by
  intro v hv
  simp only [chainTrace, mem_iUnion] at hv
  obtain ⟨n, hn, hv⟩ := hv
  exact mem_iUnion.2 ⟨g n, mem_iUnion.2 ⟨g (n + 1), mem_iUnion.2 ⟨hg n hn, hv⟩⟩⟩

/-- An edge whose segment meets a component of the complement of the trace of a lattice chain,
with an endpoint `y` off the chain, has `y` in that component (lattice segments meet only at
lattice points). -/
theorem latticePoint_mem_connectedComponentIn {g : ℤ → Vertex 2} {S : Set ℤ}
    (hg : ∀ n ∈ S, (nearestNeighborGraph 2).Adj (g n) (g (n + 1))) {x y : Vertex 2}
    (hxy : (nearestNeighborGraph 2).Adj x y) (hy : y ∉ chainVerts g S) {z₀ v : Plane}
    (hv : v ∈ edgeSegment x y) (hvD : v ∈ connectedComponentIn (chainTrace g S)ᶜ z₀) :
    latticePoint y ∈ connectedComponentIn (chainTrace g S)ᶜ z₀ := by
  have hvT : v ∉ chainTrace g S := connectedComponentIn_subset _ _ hvD
  have hsub : segment ℝ v (latticePoint y) ⊆ (chainTrace g S)ᶜ := by
    intro w hw hwT
    have hw' : w ∈ edgeSegment x y :=
      (convex_segment _ _).segment_subset hv (right_mem_edgeSegment x y) hw
    have hwT' := hwT
    simp only [chainTrace, mem_iUnion] at hwT'
    obtain ⟨n, hn, hwn⟩ := hwT'
    rcases edgeSegment_inter hxy (hg n hn) hw' hwn with ⟨-, h⟩ | ⟨-, h⟩ | ⟨z, hwz, hz, hz'⟩
    · exact hy ⟨n, hn, Or.inr h⟩
    · exact hy ⟨n, hn, Or.inl h⟩
    · rcases hz with hzx | hzy
      · rw [hwz, hzx] at hw hwT
        have h1 : Wbtw ℝ (latticePoint x) v (latticePoint y) := mem_segment_iff_wbtw.1 hv
        have h2 : Wbtw ℝ v (latticePoint x) (latticePoint y) := mem_segment_iff_wbtw.1 hw
        have hvx : latticePoint x = v := (wbtw_swap_left_iff ℝ (latticePoint y)).1 ⟨h1, h2⟩
        exact hvT (hvx ▸ hwT)
      · exact hy ⟨n, hn, hzy ▸ hz'⟩
  have := (convex_segment v (latticePoint y)).isPreconnected.subset_connectedComponentIn
    (left_mem_segment ℝ _ _) hsub
  rw [← connectedComponentIn_eq hvD] at this
  exact this (right_mem_segment ℝ _ _)

end Rigidity.Proofs.Section5
