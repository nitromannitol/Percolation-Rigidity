import Rigidity.Steps.Section5.InfiniteDisjointPaths

/-!
# Proposition 5.12: edges leaving a side of a planar lattice path

This file proves `TraceCrossingStep` (Proposition 5.12, the planar trace used in
step:5.12-jordan, corrected draft L2112-2121). No literature input is used.

* `endpoint_eq_of_mem_unitSegment`: two unit lattice segments `[c, c + eᵢ]`, `[c', c' + eⱼ]` of
  `ℝ²` which meet share an endpoint. Writing the common point as `c + t eᵢ = c' + t' eⱼ` with
  `t, t' ∈ [0, 1]` gives `-eⱼ ≤ c' - c ≤ eᵢ` coordinatewise, and `c' - c ∈ ℤ²`.
* `traceCrossingStep`: let `y ∼ x` in `𝒞_∞` with `y` in a component `D` of `ℝ² \ π` and `x ∉ D`.
  The point `y` is off the trace, so `y` is no vertex of `π`. If `x` were no vertex of `π`, the
  segment `[y, x]` would meet no segment of `π` (they would share an endpoint), so the connected
  set `[y, x]` would lie in `D`.
-/

open LatticeProb LatticeProb.Percolation Rigidity.Section5 Rigidity.Steps.Section5

namespace Rigidity.Proofs.Section5

/-- The coordinates of an embedded lattice point. -/
theorem latticeEuclideanEmbedding_apply (x : Vertex 2) (k : Fin 2) :
    latticeEuclideanEmbedding x k = (x k : ℝ) := rfl

/-- A point of the unit lattice segment `[c, c + eᵢ]` is `c + t eᵢ` with `0 ≤ t ≤ 1`. -/
theorem exists_eq_of_mem_unitSegment {c : Vertex 2} {i : Fin 2} {z : EuclideanSpace ℝ (Fin 2)}
    (hz : z ∈ segment ℝ (latticeEuclideanEmbedding c) (latticeEuclideanEmbedding (c + unit i))) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ ∀ k, z k = c k + t * (unit i k : ℤ) := by
  rw [segment_eq_image'] at hz
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hz
  refine ⟨t, ht0, ht1, fun k => ?_⟩
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, latticeEuclideanEmbedding_apply,
    smul_eq_mul, Pi.add_apply, Int.cast_add]
  ring

/-- The coordinates of a unit vector of `ℤ²` are `0` or `1` and add up to `1`. -/
theorem unit_coord (l : Fin 2) :
    (0 ≤ unit l 0 ∧ unit l 0 ≤ 1) ∧ (0 ≤ unit l 1 ∧ unit l 1 ≤ 1) ∧ unit l 0 + unit l 1 = 1 := by
  fin_cases l <;> simp [unit]

/-- Two unit lattice segments `[c, c + eᵢ]` and `[c', c' + eⱼ]` of `ℝ²` which meet share an
endpoint. -/
theorem endpoint_eq_of_mem_unitSegment {c c' : Vertex 2} {i j : Fin 2}
    {z : EuclideanSpace ℝ (Fin 2)}
    (hz : z ∈ segment ℝ (latticeEuclideanEmbedding c) (latticeEuclideanEmbedding (c + unit i)))
    (hz' : z ∈ segment ℝ (latticeEuclideanEmbedding c')
      (latticeEuclideanEmbedding (c' + unit j))) :
    c = c' ∨ c = c' + unit j ∨ c + unit i = c' ∨ c + unit i = c' + unit j := by
  obtain ⟨t, ht0, ht1, ht⟩ := exists_eq_of_mem_unitSegment hz
  obtain ⟨t', ht0', ht1', ht'⟩ := exists_eq_of_mem_unitSegment hz'
  have hnn : ∀ (l k : Fin 2), (0 : ℝ) ≤ (unit l k : ℤ) := fun l k => by
    have := unit_coord l
    fin_cases k <;> simp only [Fin.zero_eta, Fin.mk_one] <;> exact_mod_cast (by omega)
  -- `-eⱼ ≤ c' - c ≤ eᵢ` coordinatewise
  have hb : ∀ k, -unit j k ≤ c' k - c k ∧ c' k - c k ≤ unit i k := by
    intro k
    have h := (ht k).symm.trans (ht' k)
    have hi := hnn i k
    have hj := hnn j k
    constructor
    · have : ((-unit j k : ℤ) : ℝ) ≤ ((c' k - c k : ℤ) : ℝ) := by
        push_cast
        nlinarith [mul_nonneg ht0 hi, mul_nonneg (sub_nonneg.2 ht1') hj]
      exact_mod_cast this
    · have : ((c' k - c k : ℤ) : ℝ) ≤ ((unit i k : ℤ) : ℝ) := by
        push_cast
        nlinarith [mul_nonneg ht0' hj, mul_nonneg (sub_nonneg.2 ht1) hi]
      exact_mod_cast this
  have e : ∀ a b : Vertex 2, a = b ↔ a 0 = b 0 ∧ a 1 = b 1 := fun a b =>
    ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun ⟨h0, h1⟩ => funext fun k => by fin_cases k <;> assumption⟩
  have h0 := hb 0
  have h1 := hb 1
  have ui := unit_coord i
  have uj := unit_coord j
  simp only [e, Pi.add_apply]
  omega

/-- Two unit lattice segments `[y, x]` and `[a, b]` of `ℝ²` which meet share an endpoint. -/
theorem eq_or_eq_of_mem_segment_inter {y x a b : Vertex 2} (hyx : (lattice 2).Adj y x)
    (hab : (lattice 2).Adj a b) {z : EuclideanSpace ℝ (Fin 2)}
    (hz : z ∈ segment ℝ (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding x))
    (hz' : z ∈ segment ℝ (latticeEuclideanEmbedding a) (latticeEuclideanEmbedding b)) :
    y = a ∨ y = b ∨ x = a ∨ x = b := by
  obtain ⟨i, rfl | rfl⟩ := hyx <;> obtain ⟨j, rfl | rfl⟩ := hab
  · rcases endpoint_eq_of_mem_unitSegment hz hz' with h | h | h | h <;> tauto
  · rw [segment_symm] at hz'
    rcases endpoint_eq_of_mem_unitSegment hz hz' with h | h | h | h <;> tauto
  · rw [segment_symm] at hz
    rcases endpoint_eq_of_mem_unitSegment hz hz' with h | h | h | h <;> tauto
  · rw [segment_symm] at hz hz'
    rcases endpoint_eq_of_mem_unitSegment hz hz' with h | h | h | h <;> tauto

/-- `TraceCrossingStep`: an edge of `𝒞_∞` leaving a connected component of the complement of the
trace of a bi-infinite path `π` ends on `π`. -/
theorem traceCrossingStep : TraceCrossingStep := by
  intro ω C π hπ w y x hyx hy hx
  by_contra hne
  push Not at hne
  apply hx
  have hyc : latticeEuclideanEmbedding y.val ∉ pathTrace π := connectedComponentIn_subset _ _ hy
  have hmem : ∀ m, latticeEuclideanEmbedding (π m).val ∈ pathTrace π := fun m =>
    Set.mem_iUnion.2 ⟨m, left_mem_segment _ _ _⟩
  have hlat : ∀ {a b : C}, (componentGraph C).Adj a b → (lattice 2).Adj a.val b.val :=
    fun h => openGraph_le ω ((C.toSimpleGraph_adj _ _).1 h)
  have hseg : segment ℝ (latticeEuclideanEmbedding y.val) (latticeEuclideanEmbedding x.val) ⊆
      (pathTrace π)ᶜ := by
    intro z hz hzπ
    obtain ⟨m, hm⟩ := Set.mem_iUnion.1 hzπ
    rcases eq_or_eq_of_mem_segment_inter (hlat hyx) (hlat (hπ m)) hz hm with h | h | h | h
    · exact hyc (h ▸ hmem m)
    · exact hyc (h ▸ hmem (m + 1))
    · exact hne m (Subtype.ext h)
    · exact hne (m + 1) (Subtype.ext h)
  have hsub := (convex_segment _ _).isPreconnected.subset_connectedComponentIn
    (left_mem_segment ℝ _ _) hseg
  rw [← connectedComponentIn_eq hy] at hsub
  exact hsub (right_mem_segment _ _ _)

end Rigidity.Proofs.Section5
