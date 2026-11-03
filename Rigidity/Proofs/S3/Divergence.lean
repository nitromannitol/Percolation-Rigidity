import Rigidity.Steps.S3.NotLipschitz
import LatticeProb.Graph.Zd

/-!
# `step:3.2-divergence`: the divergence identity on `L(Q_N)`

Step `step:3.2-divergence` of Proposition 3.2 (eq. (divergence-theorem-flux) of the corrected
draft). For a function `f` on oriented pairs of vertices which is antisymmetric and whose sum over
the `2d` neighbours of every vertex vanishes, the sum of `f` over the oriented edges leaving
`L(Q_N)` vanishes: summing the vanishing neighbour sums over `L(Q_N)`, direction by direction, the
edges with both endpoints in `L(Q_N)` cancel in pairs (`x ↦ x - e_i` is a bijection between the
two orientations), and the outward edges in direction `±e_i` start exactly at the points of the
corresponding face: `center(Q_N)` for `+e₁`, `left(Q_N)` for `-e₁`, and the sides `x_j = ±N` for
`±e_j`, `j ≠ 1`.

The discrete normal derivative `edgeDifference C u` of a function `u` on a cluster is antisymmetric,
and its neighbour sum at a vertex of the cluster is minus the Laplacian of `u` there, so the
identity applies to harmonic functions.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Rigidity.Proofs.S3

open LatticeProb LatticeProb.Percolation Rigidity.Section3 Rigidity.Steps.S3 Classical

variable {d : ℕ}

/-! ### The faces of `L(Q_N)` as the starting points of the outward edges -/

section Faces

variable [NeZero d] {N : ℕ}

theorem mem_halfCube_iff {x : Vertex d} :
    x ∈ halfCube d N ↔ (∀ j, -(N : ℤ) ≤ x j ∧ x j ≤ N) ∧ x 0 ≤ 0 := by
  simp [halfCube, latticeCube, Fintype.mem_piFinset, Finset.mem_Icc]

omit [NeZero d] in
theorem add_unit_apply (x : Vertex d) (i j : Fin d) :
    (x + unit i) j = if j = i then x j + 1 else x j := by
  by_cases h : j = i
  · subst h
    simp [unit]
  · simp [unit, h]

omit [NeZero d] in
theorem sub_unit_apply (x : Vertex d) (i j : Fin d) :
    (x - unit i) j = if j = i then x j - 1 else x j := by
  by_cases h : j = i
  · subst h
    simp [unit]
  · simp [unit, h]

theorem add_unit_mem_halfCube_iff {x : Vertex d} (hx : x ∈ halfCube d N) (i : Fin d) :
    x + unit i ∈ halfCube d N ↔ x i < N ∧ (i = 0 → x 0 < 0) := by
  rw [mem_halfCube_iff] at hx ⊢
  obtain ⟨hb, h0⟩ := hx
  constructor
  · rintro ⟨hb', h0'⟩
    refine ⟨?_, fun hi => ?_⟩
    · have h := (hb' i).2
      rw [add_unit_apply, if_pos rfl] at h
      omega
    · subst hi
      rw [add_unit_apply, if_pos rfl] at h0'
      omega
  · rintro ⟨hN, hi0⟩
    refine ⟨fun j => ?_, ?_⟩
    · rw [add_unit_apply]
      split_ifs with hj
      · subst hj
        have h := hb j
        omega
      · exact hb j
    · rw [add_unit_apply]
      split_ifs with hj
      · have h := hi0 hj.symm
        omega
      · exact h0

theorem sub_unit_mem_halfCube_iff {x : Vertex d} (hx : x ∈ halfCube d N) (i : Fin d) :
    x - unit i ∈ halfCube d N ↔ -(N : ℤ) < x i := by
  rw [mem_halfCube_iff] at hx ⊢
  obtain ⟨hb, h0⟩ := hx
  constructor
  · rintro ⟨hb', -⟩
    have h := (hb' i).1
    rw [sub_unit_apply, if_pos rfl] at h
    omega
  · intro hN
    refine ⟨fun j => ?_, ?_⟩
    · rw [sub_unit_apply]
      split_ifs with hj
      · subst hj
        have h := hb j
        omega
      · exact hb j
    · rw [sub_unit_apply]
      split_ifs <;> omega

/-- The outward edges of `L(Q_N)` in direction `+e₁` start at `center(Q_N)`. -/
theorem filter_add_unit_zero_not_mem_halfCube :
    (halfCube d N).filter (fun x => x + unit 0 ∉ halfCube d N) = centerFace d N := by
  ext x
  rw [Finset.mem_filter, centerFace, Finset.mem_filter]
  constructor
  · rintro ⟨hx, hn⟩
    rw [add_unit_mem_halfCube_iff hx] at hn
    have h0 := (mem_halfCube_iff.mp hx).2
    refine ⟨(Finset.mem_filter.mp hx).1, ?_⟩
    by_contra hne
    exact hn ⟨by omega, fun _ => by omega⟩
  · rintro ⟨hc, h0⟩
    have hx : x ∈ halfCube d N := Finset.mem_filter.mpr ⟨hc, h0.le⟩
    refine ⟨hx, fun h => ?_⟩
    have h' := ((add_unit_mem_halfCube_iff hx 0).mp h).2 rfl
    omega

/-- The outward edges of `L(Q_N)` in direction `-e₁` start at `left(Q_N)`. -/
theorem filter_sub_unit_zero_not_mem_halfCube :
    (halfCube d N).filter (fun x => x - unit 0 ∉ halfCube d N) = leftFace d N := by
  ext x
  rw [Finset.mem_filter, leftFace, Finset.mem_filter]
  constructor
  · rintro ⟨hx, hn⟩
    rw [sub_unit_mem_halfCube_iff hx] at hn
    have h0 := ((mem_halfCube_iff.mp hx).1 0).1
    exact ⟨(Finset.mem_filter.mp hx).1, by omega⟩
  · rintro ⟨hc, h0⟩
    have hx : x ∈ halfCube d N := Finset.mem_filter.mpr ⟨hc, by omega⟩
    refine ⟨hx, fun h => ?_⟩
    have h' := (sub_unit_mem_halfCube_iff hx 0).mp h
    omega

/-- The outward edges of `L(Q_N)` in direction `+e_j`, `j ≠ 1`, start at the side `x_j = N`. -/
theorem filter_add_unit_not_mem_halfCube {j : Fin d} (hj : j ≠ 0) :
    (halfCube d N).filter (fun x => x + unit j ∉ halfCube d N) = upperSide j N := by
  ext x
  rw [Finset.mem_filter, upperSide, Finset.mem_filter]
  refine and_congr_right fun hx => ?_
  rw [add_unit_mem_halfCube_iff hx]
  have h := ((mem_halfCube_iff.mp hx).1 j).2
  constructor
  · intro hn
    by_contra hne
    exact hn ⟨by omega, fun h0 => absurd h0 hj⟩
  · intro hN hlt
    omega

/-- The outward edges of `L(Q_N)` in direction `-e_j` start at the side `x_j = -N`. -/
theorem filter_sub_unit_not_mem_halfCube (j : Fin d) :
    (halfCube d N).filter (fun x => x - unit j ∉ halfCube d N) = lowerSide j N := by
  ext x
  rw [Finset.mem_filter, lowerSide, Finset.mem_filter]
  refine and_congr_right fun hx => ?_
  rw [sub_unit_mem_halfCube_iff hx]
  have h := ((mem_halfCube_iff.mp hx).1 j).1
  omega

end Faces

/-! ### The divergence identity -/

/-- The sum over the oriented edges `(x, x ± e_i)` with `x ∈ L(Q_N)` in a fixed direction `i` is the
sum over the outward ones. -/
theorem sum_halfCube_dir_eq (N : ℕ) [NeZero d] (f : Vertex d → Vertex d → ℝ)
    (hanti : ∀ x y, f y x = - f x y) (i : Fin d) :
    ∑ x ∈ halfCube d N, (f x (x + unit i) + f x (x - unit i)) =
      ∑ x ∈ (halfCube d N).filter (fun x => x + unit i ∉ halfCube d N), f x (x + unit i) +
        ∑ x ∈ (halfCube d N).filter (fun x => x - unit i ∉ halfCube d N), f x (x - unit i) := by
  set A := halfCube d N
  have hcancel : ∑ x ∈ A.filter (fun x => x - unit i ∈ A), f x (x - unit i) =
      - ∑ x ∈ A.filter (fun x => x + unit i ∈ A), f x (x + unit i) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_nbij' (fun x => x - unit i) (fun x => x + unit i) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨hx.2, by rw [sub_add_cancel]; exact hx.1⟩
    · intro x hx
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨hx.2, by rw [add_sub_cancel_right]; exact hx.1⟩
    · intro x _
      exact sub_add_cancel x (unit i)
    · intro x _
      exact add_sub_cancel_right x (unit i)
    · intro x _
      rw [sub_add_cancel]
      exact hanti _ _
  rw [Finset.sum_add_distrib,
    ← Finset.sum_filter_add_sum_filter_not A (fun x => x + unit i ∈ A) (fun x => f x (x + unit i)),
    ← Finset.sum_filter_add_sum_filter_not A (fun x => x - unit i ∈ A) (fun x => f x (x - unit i)),
    hcancel]
  ring

/-- The divergence identity on `L(Q_N)`: an antisymmetric `f` whose neighbour sums vanish has zero
total flux out of `L(Q_N)` through `left(Q_N)`, `sides(Q_N)` and `center(Q_N)`. -/
theorem leftSum_add_sidesSum_add_centerSum_eq_zero [NeZero d] (f : Vertex d → Vertex d → ℝ)
    (hanti : ∀ x y, f y x = - f x y)
    (hharm : ∀ x, ∑ i, (f x (x + unit i) + f x (x - unit i)) = 0) (N : ℕ) :
    leftSum f N + sidesSum f N + centerSum f N = 0 := by
  have htot : ∑ i, (∑ x ∈ (halfCube d N).filter (fun x => x + unit i ∉ halfCube d N),
      f x (x + unit i) +
        ∑ x ∈ (halfCube d N).filter (fun x => x - unit i ∉ halfCube d N), f x (x - unit i)) =
      0 := by
    rw [← Finset.sum_congr rfl fun i _ => sum_halfCube_dir_eq N f hanti i, Finset.sum_comm]
    exact Finset.sum_eq_zero fun x _ => hharm x
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin d)),
    filter_add_unit_zero_not_mem_halfCube, filter_sub_unit_zero_not_mem_halfCube] at htot
  have hsides : sidesSum f N = ∑ j ∈ Finset.univ.erase (0 : Fin d),
      (∑ x ∈ (halfCube d N).filter (fun x => x + unit j ∉ halfCube d N), f x (x + unit j) +
        ∑ x ∈ (halfCube d N).filter (fun x => x - unit j ∉ halfCube d N), f x (x - unit j)) := by
    rw [sidesSum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [filter_add_unit_not_mem_halfCube (Finset.ne_of_mem_erase hj),
      filter_sub_unit_not_mem_halfCube]
  rw [leftSum, centerSum, hsides]
  linarith

/-! ### The discrete normal derivative of a harmonic function -/

/-- The discrete normal derivative is antisymmetric. -/
theorem edgeDifference_antisymm {ω : Configuration d} (C : OpenComponent ω) (u : C → ℝ)
    (x y : Vertex d) : edgeDifference C u y x = - edgeDifference C u x y := by
  unfold edgeDifference
  by_cases hxy : x ∈ C.supp ∧ (openGraph ω).Adj x y
  · rw [if_pos hxy, if_pos ⟨C.mem_supp_of_adj_mem_supp hxy.1 hxy.2, hxy.2.symm⟩]
    ring
  · rw [if_neg hxy, if_neg, neg_zero]
    rintro ⟨hy, hyx⟩
    exact hxy ⟨C.mem_supp_of_adj_mem_supp hy hyx, hyx.symm⟩

/-- The sum of `f` over the lattice neighbours of `x` is the sum over the `2d` directions. -/
theorem sum_lattice_neighborFinset_eq_nbrSum [NeZero d] (f : Vertex d → ℝ) (x : Vertex d) :
    ∑ y ∈ (lattice d).neighborFinset x, f y = nbrSum f x := by
  have hw := Graph.Zd.walkOp_eq f x
  have hd0 : (2 * (d : ℝ)) ≠ 0 := by
    have : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
    positivity
  rw [Graph.walkOp, LatticeProb.walkOp, Graph.Zd.degree_eq] at hw
  push_cast at hw
  exact (div_left_inj' hd0).mp hw

/-- The Laplacian on a cluster as a sum over the lattice neighbours. -/
theorem componentLaplacian_eq_sum_lattice {ω : Configuration d} (C : OpenComponent ω)
    (u : C → ℝ) (x : Vertex d) (hx : x ∈ C.supp) :
    componentLaplacian C u ⟨x, hx⟩ = ∑ z ∈ (lattice d).neighborFinset x,
      if (openGraph ω).Adj x z then extend C u z - extend C u x else 0 := by
  rw [← Finset.sum_filter]
  have hset : ((lattice d).neighborFinset x).filter (fun z => (openGraph ω).Adj x z) =
      ((componentGraph C).neighborFinset ⟨x, hx⟩).map (Function.Embedding.subtype _) := by
    ext z
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset, Finset.mem_map,
      Function.Embedding.coe_subtype]
    constructor
    · rintro ⟨-, hz⟩
      exact ⟨⟨z, C.mem_supp_of_adj_mem_supp hx hz⟩, hz, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨openGraph_le ω hy, hy⟩
  rw [hset, Finset.sum_map, componentLaplacian]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp [extend, hx]

/-- The neighbour sum of the discrete normal derivative of a harmonic function vanishes. -/
theorem edgeDifference_nbrSum_eq_zero [NeZero d] {ω : Configuration d} (C : OpenComponent ω)
    (u : C → ℝ) (hu : ∀ x, componentLaplacian C u x = 0) (x : Vertex d) :
    ∑ i, (edgeDifference C u x (x + unit i) + edgeDifference C u x (x - unit i)) = 0 := by
  by_cases hx : x ∈ C.supp
  · have hL := hu ⟨x, hx⟩
    rw [componentLaplacian_eq_sum_lattice C u x hx, sum_lattice_neighborFinset_eq_nbrSum,
      nbrSum] at hL
    rw [← neg_eq_zero, ← Finset.sum_neg_distrib, ← hL]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [edgeDifference, hx, true_and]
    split_ifs <;> ring
  · refine Finset.sum_eq_zero fun i _ => ?_
    simp [edgeDifference, hx]

/-- `step:3.2-divergence`. -/
theorem divergenceStep [NeZero d] : DivergenceStep d := by
  intro ω C u hu N
  exact leftSum_add_sidesSum_add_centerSum_eq_zero _ (edgeDifference_antisymm C u)
    (edgeDifference_nbrSum_eq_zero C u hu) N

end Rigidity.Proofs.S3
