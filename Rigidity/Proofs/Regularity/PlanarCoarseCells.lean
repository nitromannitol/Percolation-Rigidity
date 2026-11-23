import Rigidity.Proofs.Percolation.PlanarPartition
import Rigidity.Draft.Section3Statements
import Rigidity.Percolation.IntegerCubeCoalescenceScales
import Rigidity.Proofs.Regularity.LatticeHarmonicExcessTwo

/-!
# Cells and anchors of the planar partition

On the planar partition event, the anchor `planarCoarseAnchor ω x` of the partition cube of `x`
lies in that cube (`planarCoarseAnchor_mem`), so the cube is determined by its anchor
(`planarPartCube_eq_of_anchor_eq`) and the points with a given anchor lie in one cube of
`9^{scale}` points (`card_filter_anchor_eq_le`). The anchors of neighbouring vertices are joined by
open paths (`TriadicCube.reachIn_planarAnchor_of_near`, the cubes of neighbouring vertices having
comparable scales), hence all anchors lie in one open cluster, which meets infinitely many cubes:
when the infinite open cluster is unique, every anchor belongs to it
(`planarCoarseAnchor_mem_uniqueInfiniteComponent`; Armstrong and Dario, arXiv:1609.09431v2,
§2.3: the maximal crossing clusters of the cubes of the partition lie in `𝒞_∞`). The coarsening
`coarseAtAnchor C u`, the value at the anchor of `u` extended by `0` off `C` (the function
`planarCoarse` of the statement of Lemma 7.1 in dimension two), is on this cluster the value of
`u` at the anchor (`coarseAtAnchor_eq`).

The weighted Cauchy–Schwarz inequality `sq_sum_abs_comp_le` bounds `(∑_{x ∈ B} |f(a(x))|)²` by
`(∑_{x ∈ B} W(x)) ∑_{y ∈ a(B)} f(y)²` whenever `W(x)` bounds the number of points of `B` with the
anchor of `x`: the `ℓ¹` step of the proof of Lemma 7.3 of Armstrong and Dario.
-/

namespace Rigidity.Proofs.Regularity

open Finset LatticeProb LatticeProb.Percolation Rigidity.Percolation Rigidity.External
open Rigidity.Proofs.Section5

variable {ω : Configuration 2}

/-- The coarsening `[u]_𝒫`: the value at the anchor of the partition cube of `u`, extended by `0`
off the component. -/
noncomputable def coarseAtAnchor (C : OpenComponent ω) (u : C → ℝ) : Vertex 2 → ℝ :=
  fun y => Rigidity.Section3.extend C u (planarCoarseAnchor ω y)

theorem planarCoarseAnchor_mem (hP : PlanarPartitionEvent ω) (x : Vertex 2) :
    planarCoarseAnchor ω x ∈ (planarPartCube ω x).vertices :=
  (TriadicCube.planarAnchor_spec (planarPartCube_meshed hP x).1 (planarPartCube_large hP x)).1

theorem planarPartCube_planarCoarseAnchor (hP : PlanarPartitionEvent ω) (x : Vertex 2) :
    planarPartCube ω (planarCoarseAnchor ω x) = planarPartCube ω x :=
  planarPartCube_eq_of_mem hP (planarCoarseAnchor_mem hP x)

theorem planarPartCube_eq_of_anchor_eq (hP : PlanarPartitionEvent ω) {x y : Vertex 2}
    (h : planarCoarseAnchor ω x = planarCoarseAnchor ω y) :
    planarPartCube ω x = planarPartCube ω y := by
  rw [← planarPartCube_planarCoarseAnchor hP x, h, planarPartCube_planarCoarseAnchor hP y]

theorem mem_planarPartCube_of_anchor_eq (hP : PlanarPartitionEvent ω) {x y : Vertex 2}
    (h : planarCoarseAnchor ω y = planarCoarseAnchor ω x) :
    y ∈ (planarPartCube ω x).vertices := by
  rw [← planarPartCube_eq_of_anchor_eq hP h]
  exact (planarPartCube_spec hP y).1

/-- The anchor of `x` is less than a side of the cube of `x` away from `x`. -/
theorem abs_coarseAnchor_sub_lt (hP : PlanarPartitionEvent ω) (x : Vertex 2) (i : Fin 2) :
    |planarCoarseAnchor ω x i - x i| < (planarPartCube ω x).side :=
  TriadicCube.abs_coord_sub_lt_side (planarCoarseAnchor_mem hP x) (planarPartCube_spec hP x).1 i

/-- The number of points of a finite set with the anchor of `x` is at most `9^{scale}`. -/
theorem card_filter_anchor_eq_le (hP : PlanarPartitionEvent ω) (B : Finset (Vertex 2))
    (x : Vertex 2) :
    ((B.filter fun x' => planarCoarseAnchor ω x' = planarCoarseAnchor ω x).card : ℝ) ≤
      ((3 : ℝ) ^ (planarPartCube ω x).scale) ^ 2 := by
  classical
  have hsub : B.filter (fun x' => planarCoarseAnchor ω x' = planarCoarseAnchor ω x) ⊆
      (planarPartCube ω x).toIntegerCube.vertices := by
    intro y hy
    rw [mem_filter] at hy
    rw [TriadicCube.mem_toIntegerCube_vertices]
    exact mem_planarPartCube_of_anchor_eq hP hy.2
  have h := card_le_card hsub
  rw [IntegerCube.card_vertices] at h
  have e : (planarPartCube ω x).toIntegerCube.size = 3 ^ (planarPartCube ω x).scale := rfl
  rw [e] at h
  exact_mod_cast h

theorem reachable_coarseAnchor_of_near (hP : PlanarPartitionEvent ω) {x y : Vertex 2}
    (hnear : ∀ i, |x i - y i| ≤ 1) :
    (openGraph ω).Reachable (planarCoarseAnchor ω x) (planarCoarseAnchor ω y) := by
  obtain ⟨h1, h2⟩ := planarPartCube_scales_close hP hnear
  rcases le_total (planarPartCube ω x).scale (planarPartCube ω y).scale with h | h
  · exact (TriadicCube.reachIn_planarAnchor_of_near (planarPartCube_meshed hP x).1
      (planarPartCube_meshed hP y).1 (planarPartCube_large hP x) h h2
      (planarPartCube_spec hP x).1 (planarPartCube_spec hP y).1 hnear).reachable
  · have hnear' : ∀ i, |y i - x i| ≤ 1 := fun i => by rw [abs_sub_comm]; exact hnear i
    exact (TriadicCube.reachIn_planarAnchor_of_near (planarPartCube_meshed hP y).1
      (planarPartCube_meshed hP x).1 (planarPartCube_large hP y) h h1
      (planarPartCube_spec hP y).1 (planarPartCube_spec hP x).1 hnear').reachable.symm

theorem reachable_coarseAnchor_shift (hP : PlanarPartitionEvent ω) (y : Vertex 2) (i : Fin 2)
    (k : ℤ) :
    (openGraph ω).Reachable (planarCoarseAnchor ω y) (planarCoarseAnchor ω (y + k • unit i)) := by
  induction k using Int.induction_on with
  | zero => simp only [zero_smul, add_zero]; exact SimpleGraph.Reachable.refl _
  | succ n ih =>
    refine ih.trans (reachable_coarseAnchor_of_near hP fun j => ?_)
    rw [add_smul_unit_apply, add_smul_unit_apply]
    split_ifs <;> simp
  | pred n ih =>
    refine ih.trans (reachable_coarseAnchor_of_near hP fun j => ?_)
    rw [add_smul_unit_apply, add_smul_unit_apply]
    split_ifs <;> simp

/-- All anchors are joined by open paths. -/
theorem reachable_coarseAnchor (hP : PlanarPartitionEvent ω) (x : Vertex 2) :
    (openGraph ω).Reachable (planarCoarseAnchor ω 0) (planarCoarseAnchor ω x) := by
  have h1 := reachable_coarseAnchor_shift hP 0 0 (x 0)
  have h2 := reachable_coarseAnchor_shift hP (0 + x 0 • unit 0) 1 (x 1)
  have e : 0 + x 0 • unit 0 + x 1 • unit 1 = x := by
    funext j
    fin_cases j <;> simp [unit]
  rw [e] at h2
  exact h1.trans h2

/-- **The anchors lie in the infinite cluster.** -/
theorem planarCoarseAnchor_mem_uniqueInfiniteComponent (hP : PlanarPartitionEvent ω)
    (h : HasUniqueInfiniteOpenComponent ω) (x : Vertex 2) :
    planarCoarseAnchor ω x ∈ (uniqueInfiniteComponent h).supp := by
  classical
  set K : OpenComponent ω := (openGraph ω).connectedComponentMk (planarCoarseAnchor ω 0) with hK
  have hmem : ∀ y, planarCoarseAnchor ω y ∈ K.supp := fun y => by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff, hK, SimpleGraph.ConnectedComponent.eq]
    exact (reachable_coarseAnchor hP y).symm
  have hinf : K.supp.Infinite := by
    intro hfin
    apply Set.infinite_univ (α := Vertex 2)
    refine (hfin.biUnion fun a _ =>
      ((planarPartCube ω a).toIntegerCube.vertices.finite_toSet)).subset ?_
    intro y _
    refine Set.mem_biUnion (hmem y) ?_
    rw [Finset.mem_coe, TriadicCube.mem_toIntegerCube_vertices,
      planarPartCube_planarCoarseAnchor hP y]
    exact (planarPartCube_spec hP y).1
  have hKeq : K = uniqueInfiniteComponent h := (eq_uniqueInfiniteComponent_iff h K).2 hinf
  rw [← hKeq]
  exact hmem x

/-- On the infinite cluster, the coarsening is the value at the anchor. -/
theorem coarseAtAnchor_eq (hP : PlanarPartitionEvent ω) (h : HasUniqueInfiniteOpenComponent ω)
    (u : uniqueInfiniteComponent h → ℝ) (x : Vertex 2) :
    coarseAtAnchor (uniqueInfiniteComponent h) u x =
      u ⟨planarCoarseAnchor ω x, planarCoarseAnchor_mem_uniqueInfiniteComponent hP h x⟩ := by
  rw [coarseAtAnchor, Rigidity.Section3.extend,
    dif_pos (planarCoarseAnchor_mem_uniqueInfiniteComponent hP h x)]

/-- **Weighted Cauchy–Schwarz over the fibres of a map.** If `W x` bounds the number of points of
`B` with the image of `x`, then `(∑_{x ∈ B} |f(a x)|)² ≤ (∑_{x ∈ B} W x) ∑_{y ∈ a(B)} f(y)²`. -/
theorem sq_sum_abs_comp_le {α β : Type*} [DecidableEq β] (B : Finset α) (a : α → β)
    (W : α → ℝ) (f : β → ℝ)
    (hW : ∀ x ∈ B, ((B.filter fun x' => a x' = a x).card : ℝ) ≤ W x) :
    (∑ x ∈ B, |f (a x)|) ^ 2 ≤ (∑ x ∈ B, W x) * ∑ y ∈ B.image a, f y ^ 2 := by
  classical
  set n : β → ℝ := fun y => ((B.filter fun x' => a x' = y).card : ℝ) with hn
  have hn1 : ∀ x ∈ B, 1 ≤ n (a x) := fun x hx => by
    have : 0 < (B.filter fun x' => a x' = a x).card :=
      Finset.card_pos.2 ⟨x, mem_filter.2 ⟨hx, rfl⟩⟩
    simp only [hn]; exact_mod_cast this
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq B (fun x => |f (a x)| / Real.sqrt (n (a x)))
    (fun x => Real.sqrt (n (a x)))
  have e1 : ∀ x ∈ B, |f (a x)| / Real.sqrt (n (a x)) * Real.sqrt (n (a x)) = |f (a x)| :=
    fun x hx => div_mul_cancel₀ _ (Real.sqrt_pos.2 (by linarith [hn1 x hx])).ne'
  rw [sum_congr rfl e1] at hcs
  have e2 : ∀ x ∈ B, (|f (a x)| / Real.sqrt (n (a x))) ^ 2 = f (a x) ^ 2 / n (a x) :=
    fun x hx => by rw [div_pow, sq_abs, Real.sq_sqrt (by linarith [hn1 x hx])]
  have e3 : ∀ x ∈ B, Real.sqrt (n (a x)) ^ 2 = n (a x) :=
    fun x hx => Real.sq_sqrt (by linarith [hn1 x hx])
  rw [sum_congr rfl e2, sum_congr rfl e3] at hcs
  have hfib : ∑ x ∈ B, f (a x) ^ 2 / n (a x) = ∑ y ∈ B.image a, f y ^ 2 := by
    rw [sum_comp (fun y => f y ^ 2 / n y) a]
    refine sum_congr rfl fun y hy => ?_
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hy
    have h1 := hn1 x hx
    rw [nsmul_eq_mul]
    change n (a x) * (f (a x) ^ 2 / n (a x)) = _
    field_simp
  rw [hfib] at hcs
  have hnW : ∑ x ∈ B, n (a x) ≤ ∑ x ∈ B, W x := sum_le_sum fun x hx => hW x hx
  have hf0 : 0 ≤ ∑ y ∈ B.image a, f y ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  calc (∑ x ∈ B, |f (a x)|) ^ 2 ≤ (∑ y ∈ B.image a, f y ^ 2) * ∑ x ∈ B, n (a x) := hcs
    _ ≤ (∑ y ∈ B.image a, f y ^ 2) * ∑ x ∈ B, W x := mul_le_mul_of_nonneg_left hnW hf0
    _ = _ := mul_comm _ _

/-- **Sum over the fibres.** If every fibre of `a` on `B` has at most `W₀` points, then
`∑_{x ∈ B} f(a x)² ≤ W₀ ∑_{y ∈ a(B)} f(y)²`. -/
theorem sum_sq_comp_le {α β : Type*} [DecidableEq β] (B : Finset α) (a : α → β) {W₀ : ℝ}
    (f : β → ℝ) (hW : ∀ x ∈ B, ((B.filter fun x' => a x' = a x).card : ℝ) ≤ W₀) :
    ∑ x ∈ B, f (a x) ^ 2 ≤ W₀ * ∑ y ∈ B.image a, f y ^ 2 := by
  classical
  rw [sum_comp (fun y => f y ^ 2) a, mul_sum]
  refine sum_le_sum fun y hy => ?_
  obtain ⟨x, hx, rfl⟩ := mem_image.1 hy
  rw [nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (hW x hx) (sq_nonneg _)

end Rigidity.Proofs.Regularity
