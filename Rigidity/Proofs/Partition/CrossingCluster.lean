import Rigidity.Percolation.TriadicThreeQuarterCube
import Rigidity.Percolation.TriadicBoundary
import Rigidity.Percolation.CoalescenceCover

/-!
# The crossing cluster of a well-connected triadic cube

A triadic cube `Q` of side `s = 3ⁿ` is well-connected relative to its rounded three-quarter cube
(`TriadicCube.wellConnectedIn`) when it has a root whose open component in `Q` meets all faces of
`Q`, every test cube is crossable, and every open path of a test cube with a coordinate
displacement of at least `s / 10` is joined inside the test cube to the component of the root.
The crossing cluster `C_*(Q)` is the union of the open components of `Q` which meet all faces of
`Q` (Armstrong and Dario, Definition 2.5).

For `n ≥ 2`, every open walk in `Q` with a coordinate displacement of at least `s / 10` starts in
the component of the root: its initial segment up to the first exit from the box of radius
`⌈s / 10⌉` around its start lies in a test cube of side `(s - 1) / 2` contained in `Q`. Hence
`C_*(Q)` is the component of the root, so it is the unique maximal crossing cluster of `Q`, and it
contains the crossing cluster of every child of `Q`.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation Rigidity.External

variable {d : ℕ}

/-- A root witnessing that a triadic cube is well-connected relative to its rounded three-quarter
cube. -/
def TriadicCube.IsWellConnectedRoot (ω : Configuration d) (Q : TriadicCube d) (root : Vertex d) :
    Prop :=
  IsCrossingRoot ω Q.vertices (fun i => ↑(Q.toIntegerCube.lowerFace i))
      (fun i => ↑(Q.toIntegerCube.upperFace i)) root ∧
    ∀ R ∈ Q.testCubes Q.threeQuarterCube.vertices,
      CrossableRegion ω ↑R.vertices (fun i => ↑(R.lowerFace i)) (fun i => ↑(R.upperFace i)) ∧
        ConnectsSelectedPaths ω ↑R.vertices Q.vertices root Q.largePath

/-- Well-connectedness relative to the rounded three-quarter cube is the existence of a root. -/
theorem TriadicCube.wellConnectedIn_threeQuarter_iff (ω : Configuration d) (Q : TriadicCube d) :
    Q.wellConnectedIn Q.threeQuarterCube.vertices ω ↔ ∃ root, Q.IsWellConnectedRoot ω root :=
  Q.wellConnectedIn_iff _ ω

/-- The crossing cluster `C_*(Q)` of a triadic cube: the vertices joined inside `Q` to a vertex
whose open component in `Q` meets every face of `Q`. -/
def TriadicCube.crossingCluster (ω : Configuration d) (Q : TriadicCube d) : Set (Vertex d) :=
  {y | ∃ root, IsCrossingRoot ω Q.vertices (fun i => ↑(Q.toIntegerCube.lowerFace i))
      (fun i => ↑(Q.toIntegerCube.upperFace i)) root ∧ (openIn ω Q.vertices).Reachable root y}

/-- Reachability inside a region stays in the region. -/
theorem mem_of_reachable_openIn_of_mem {ω : Configuration d} {B : Set (Vertex d)}
    {x y : Vertex d} (hx : x ∈ B) (h : (openIn ω B).Reachable x y) : y ∈ B := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact hx
  | cons hadj _ ih => exact ih hadj.2.2

/-- An open edge changes every coordinate by at most one. -/
theorem abs_sub_le_one_of_openIn_adj {ω : Configuration d} {B : Set (Vertex d)} {x y : Vertex d}
    (h : (openIn ω B).Adj x y) (i : Fin d) : |y i - x i| ≤ 1 := by
  obtain ⟨⟨⟨j, hj | hj⟩, -⟩, -⟩ := h <;> subst hj <;>
    by_cases hij : i = j <;> simp [LatticeProb.unit, hij]

/-- **First exit.** An open walk inside `B` started in `S` either stays in `S` up to its end, or
leaves `S` along an open edge of `B` from a vertex joined to its start inside `B ∩ S`. -/
theorem exists_reachable_inter_of_reachable_openIn {ω : Configuration d} {B S : Set (Vertex d)}
    {a b : Vertex d} (h : (openIn ω B).Reachable a b) (ha : a ∈ S) :
    ∃ u, (openIn ω (B ∩ S)).Reachable a u ∧
      (u = b ∨ ∃ v, v ∉ S ∧ (openIn ω B).Adj u v) := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact ⟨_, SimpleGraph.Reachable.refl _, Or.inl rfl⟩
  | @cons x y z hxy w ih =>
    by_cases hy : y ∈ S
    · obtain ⟨u, hu, hub⟩ := ih hy
      exact ⟨u, (SimpleGraph.Adj.reachable
        (G := openIn ω (B ∩ S)) ⟨hxy.1, ⟨hxy.2.1, ha⟩, ⟨hxy.2.2, hy⟩⟩).trans hu, hub⟩
    · exact ⟨x, SimpleGraph.Reachable.refl _, Or.inr ⟨y, hy, hxy⟩⟩

/-- An open walk inside a test region whose endpoints are a selected distance apart is joined
inside the region to the component of the root. -/
theorem ConnectsSelectedPaths.exists_of_reachable {ω : Configuration d} {R C : Set (Vertex d)}
    {root : Vertex d} {Q : TriadicCube d} (h : ConnectsSelectedPaths ω R C root Q.largePath)
    {a u : Vertex d} (ha : a ∈ R) (hau : (openIn ω R).Reachable a u) {i : Fin d}
    (hi : Q.side ≤ 10 * |a i - u i|) :
    ∃ z ∈ R, (openIn ω R).Reachable a z ∧ (openIn ω C).Reachable root z := by
  obtain ⟨w⟩ := hau
  have hl : Q.largePath w.length (fun j => w.getVert j) :=
    ⟨0, Fin.last _, i, by
      simpa only [Fin.val_zero, SimpleGraph.Walk.getVert_zero, Fin.val_last,
        SimpleGraph.Walk.getVert_length] using hi⟩
  obtain ⟨z, hz, h1, h2⟩ := h w.length (fun j => w.getVert j) hl
    (by simpa only [Fin.val_zero, SimpleGraph.Walk.getVert_zero] using ha)
    (fun j => by
      simpa only [Fin.val_castSucc, Fin.val_succ] using w.adj_getVert_succ j.isLt)
  exact ⟨z, hz, by simpa only [Fin.val_zero, SimpleGraph.Walk.getVert_zero] using h1, h2⟩

/-- The side of a triadic cube as the cast of a natural number. -/
theorem TriadicCube.natCast_three_pow_scale (Q : TriadicCube d) :
    ((3 ^ Q.scale : ℕ) : ℤ) = Q.side := by
  simp only [TriadicCube.side, Nat.cast_pow, Nat.cast_ofNat]

/-- Membership in the integer cube of a triadic cube, in coordinates. -/
theorem TriadicCube.mem_vertices_iff_coord (Q : TriadicCube d) (x : Vertex d) :
    x ∈ Q.vertices ↔ ∀ i, Q.center i - Q.radius ≤ x i ∧ x i ≤ Q.center i + Q.radius := by
  rw [Q.mem_vertices_iff]
  exact forall_congr' fun i => abs_sub_le_iff.trans (by constructor <;> intro h <;> constructor <;>
    omega)

/-- **Absorption of large walks.** In a well-connected triadic cube of scale at least two, every
open walk inside the cube with a coordinate displacement of at least a tenth of the side starts in
the component of the root. -/
theorem TriadicCube.IsWellConnectedRoot.reachable_of_reachable {ω : Configuration d}
    {Q : TriadicCube d} {root : Vertex d} (hroot : Q.IsWellConnectedRoot ω root)
    (hs : 2 ≤ Q.scale) {a b : Vertex d} (ha : a ∈ Q.vertices)
    (hab : (openIn ω Q.vertices).Reachable a b) (k : Fin d) (hk : Q.side ≤ 10 * |b k - a k|) :
    (openIn ω Q.vertices).Reachable root a := by
  set N : ℕ := 3 ^ Q.scale
  have hNdef : N = 3 ^ Q.scale := rfl
  have hN : (N : ℤ) = Q.side := Q.natCast_three_pow_scale
  have hN9 : 9 ≤ N := by
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ Q.scale := Nat.pow_le_pow_right (by norm_num) hs
  have hsr := Q.side_eq_two_mul_radius_add_one
  set ρ : ℤ := (Q.side + 9) / 10 with hρdef
  set box : Set (Vertex d) := {y | ∀ i, |y i - a i| ≤ ρ} with hboxdef
  have habox : a ∈ box := by
    rw [hboxdef, Set.mem_setOf_eq]
    intro i
    rw [sub_self, abs_zero]
    omega
  obtain ⟨u, hau, hu⟩ := exists_reachable_inter_of_reachable_openIn hab habox
  -- the displacement of the segment
  obtain ⟨i, hi⟩ : ∃ i, Q.side ≤ 10 * |a i - u i| := by
    rcases hu with rfl | ⟨v, hv, huv⟩
    · exact ⟨k, by rw [abs_sub_comm]; exact hk⟩
    · simp only [hboxdef, Set.mem_setOf_eq, not_forall, not_le] at hv
      obtain ⟨i, hi⟩ := hv
      have h1 := abs_sub_le_one_of_openIn_adj huv i
      have h2 := abs_sub_le (v i) (u i) (a i)
      refine ⟨i, ?_⟩
      rw [abs_sub_comm]
      omega
  -- the test cube
  let c : Vertex d := fun j => max (Q.center j - Q.radius) (min (a j - ρ) (Q.center j + 1))
  let R : IntegerCube d := ⟨c, N / 2⟩
  have hL : ((N / 2 : ℕ) : ℤ) = Q.radius := by omega
  have hc (j : Fin d) : Q.center j - Q.radius ≤ c j ∧ c j ≤ Q.center j + 1 ∧
      min (a j - ρ) (Q.center j + 1) ≤ c j ∧
      (c j = Q.center j - Q.radius ∨ c j = min (a j - ρ) (Q.center j + 1)) ∧
      (min (a j - ρ) (Q.center j + 1) = a j - ρ ∨
        min (a j - ρ) (Q.center j + 1) = Q.center j + 1) ∧
      min (a j - ρ) (Q.center j + 1) ≤ a j - ρ :=
    ⟨le_max_left _ _, max_le (by omega) (min_le_right _ _), le_max_right _ _,
      max_choice _ _, min_choice _ _, min_le_left _ _⟩
  have hmemR (y : Vertex d) : y ∈ R.vertices ↔ ∀ j, c j ≤ y j ∧ y j < c j + Q.radius := by
    rw [IntegerCube.mem_vertices]
    change (∀ j, c j ≤ y j ∧ y j < c j + ((N / 2 : ℕ) : ℤ)) ↔ _
    rw [hL]
  have haQ := (Q.mem_vertices_iff_coord a).1 ha
  have hRQ : (↑R.vertices : Set (Vertex d)) ⊆ Q.vertices := by
    intro y hy
    rw [Finset.mem_coe, hmemR] at hy
    rw [Q.mem_vertices_iff_coord]
    intro j
    have := hc j
    have := hy j
    omega
  have hboxR : Q.vertices ∩ box ⊆ ↑R.vertices := by
    rintro y ⟨hyQ, hyb⟩
    rw [Finset.mem_coe, hmemR]
    intro j
    have h1 := (Q.mem_vertices_iff_coord y).1 hyQ j
    have h2 := abs_le.mp (hyb j)
    have h3 := hc j
    have h4 := haQ j
    omega
  have hR : R ∈ Q.testCubes Q.threeQuarterCube.vertices := by
    refine ⟨by change Q.side ≤ 10 * ((N / 2 : ℕ) : ℤ); omega,
      by change 2 * ((N / 2 : ℕ) : ℤ) ≤ Q.side; omega, ?_⟩
    set K : ℕ := 3 * 3 ^ Q.scale / 4 with hKdef
    have hK : (K : ℤ) = 3 * Q.side / 4 := by rw [hKdef]; omega
    refine ⟨fun j => max (c j) (Q.center j - (K : ℤ) / 2), ?_, ?_⟩
    · rw [hmemR]
      intro j
      have := hc j
      exact ⟨le_max_left _ _, max_lt (by omega) (by omega)⟩
    · rw [Finset.mem_coe, IntegerCube.mem_vertices]
      intro j
      have := hc j
      change Q.center j - (K : ℤ) / 2 ≤ max (c j) (Q.center j - (K : ℤ) / 2) ∧
        max (c j) (Q.center j - (K : ℤ) / 2) < Q.center j - (K : ℤ) / 2 + (K : ℤ)
      exact ⟨le_max_right _ _, max_lt (by omega) (by omega)⟩
  obtain ⟨-, hconn⟩ := hroot.2 R hR
  have haR : a ∈ (↑R.vertices : Set (Vertex d)) := hboxR ⟨ha, habox⟩
  obtain ⟨z, -, haz, hrz⟩ := hconn.exists_of_reachable haR (reachable_openIn_mono hboxR hau) hi
  exact hrz.trans (reachable_openIn_mono hRQ haz).symm

/-- A point of the lower face of the integer cube of a triadic cube. -/
theorem TriadicCube.coord_of_mem_lowerFace {Q : TriadicCube d} {k : Fin d} {y : Vertex d}
    (hy : y ∈ (↑(Q.toIntegerCube.lowerFace k) : Set (Vertex d))) :
    y k = Q.center k - Q.radius := by
  rw [Finset.mem_coe, IntegerCube.mem_lowerFace] at hy
  exact hy.2

/-- A point of the upper face of the integer cube of a triadic cube. -/
theorem TriadicCube.coord_of_mem_upperFace {Q : TriadicCube d} {k : Fin d} {y : Vertex d}
    (hy : y ∈ (↑(Q.toIntegerCube.upperFace k) : Set (Vertex d))) :
    y k = Q.center k + Q.radius := by
  rw [Finset.mem_coe, IntegerCube.mem_upperFace] at hy
  have h := hy.2
  have hN := Q.natCast_three_pow_scale
  have hsr := Q.side_eq_two_mul_radius_add_one
  change y k + 1 = Q.side * Q.index k - Q.side / 2 + ((3 ^ Q.scale : ℕ) : ℤ) at h
  change y k = Q.side * Q.index k + Q.side / 2
  rw [hN] at h
  unfold TriadicCube.radius at hsr
  omega

/-- A crossing root is joined inside the cube to points of opposite faces in every direction, at
distance one less than the side. -/
theorem IsCrossingRoot.exists_reachable_face {ω : Configuration d} {Q : TriadicCube d}
    {r : Vertex d}
    (hr : IsCrossingRoot ω Q.vertices (fun i => ↑(Q.toIntegerCube.lowerFace i))
      (fun i => ↑(Q.toIntegerCube.upperFace i)) r) (k : Fin d) :
    ∃ a ∈ Q.vertices, ∃ b, (openIn ω Q.vertices).Reachable r a ∧
      (openIn ω Q.vertices).Reachable a b ∧ b k - a k = Q.side - 1 := by
  obtain ⟨⟨a, haQ, haf, hra⟩, ⟨b, -, hbf, hrb⟩⟩ := hr.2 k
  refine ⟨a, haQ, b, hra, hra.symm.trans hrb, ?_⟩
  rw [TriadicCube.coord_of_mem_lowerFace haf, TriadicCube.coord_of_mem_upperFace hbf]
  have := Q.side_eq_two_mul_radius_add_one
  omega

/-- **Uniqueness of the crossing cluster.** In a well-connected triadic cube of scale at least
two, every crossing root is joined inside the cube to the root. -/
theorem TriadicCube.IsWellConnectedRoot.reachable_of_isCrossingRoot (hd : 0 < d)
    {ω : Configuration d} {Q : TriadicCube d} {root : Vertex d}
    (hroot : Q.IsWellConnectedRoot ω root) (hs : 2 ≤ Q.scale) {r : Vertex d}
    (hr : IsCrossingRoot ω Q.vertices (fun i => ↑(Q.toIntegerCube.lowerFace i))
      (fun i => ↑(Q.toIntegerCube.upperFace i)) r) :
    (openIn ω Q.vertices).Reachable root r := by
  obtain ⟨a, haQ, b, hra, hab, hba⟩ := hr.exists_reachable_face ⟨0, hd⟩
  have hside : 9 ≤ Q.side := by
    rw [← Q.natCast_three_pow_scale]
    have : 9 ≤ 3 ^ Q.scale := by
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ Q.scale := Nat.pow_le_pow_right (by norm_num) hs
    exact_mod_cast this
  have hk : Q.side ≤ 10 * |b ⟨0, hd⟩ - a ⟨0, hd⟩| := by
    rw [hba, abs_of_nonneg (by omega)]
    omega
  exact (hroot.reachable_of_reachable hs haQ hab _ hk).trans hra.symm

/-- **The crossing cluster of a well-connected cube** is the open component of the root inside the
cube; in particular it is the unique maximal crossing cluster of the cube. -/
theorem TriadicCube.IsWellConnectedRoot.crossingCluster_eq (hd : 0 < d) {ω : Configuration d}
    {Q : TriadicCube d} {root : Vertex d} (hroot : Q.IsWellConnectedRoot ω root)
    (hs : 2 ≤ Q.scale) :
    Q.crossingCluster ω = {y | (openIn ω Q.vertices).Reachable root y} := by
  ext y
  constructor
  · rintro ⟨r, hr, hry⟩
    exact (hroot.reachable_of_isCrossingRoot hd hs hr).trans hry
  · intro hy
    exact ⟨root, hroot.1, hy⟩

/-- The root of a well-connected cube belongs to its crossing cluster. -/
theorem TriadicCube.IsWellConnectedRoot.mem_crossingCluster {ω : Configuration d}
    {Q : TriadicCube d} {root : Vertex d} (hroot : Q.IsWellConnectedRoot ω root) :
    root ∈ Q.crossingCluster ω :=
  ⟨root, hroot.1, SimpleGraph.Reachable.refl _⟩

/-- The crossing cluster lies in the cube. -/
theorem TriadicCube.crossingCluster_subset (ω : Configuration d) (Q : TriadicCube d) :
    Q.crossingCluster ω ⊆ Q.vertices := by
  rintro y ⟨r, hr, hry⟩
  exact mem_of_reachable_openIn_of_mem hr.1 hry

/-- Two points of the crossing cluster of a well-connected cube of scale at least two are joined
inside the cube. -/
theorem TriadicCube.IsWellConnectedRoot.reachable_of_mem_crossingCluster (hd : 0 < d)
    {ω : Configuration d} {Q : TriadicCube d} {root : Vertex d}
    (hroot : Q.IsWellConnectedRoot ω root) (hs : 2 ≤ Q.scale) {x y : Vertex d}
    (hx : x ∈ Q.crossingCluster ω) (hy : y ∈ Q.crossingCluster ω) :
    (openIn ω Q.vertices).Reachable x y := by
  rw [hroot.crossingCluster_eq hd hs] at hx hy
  exact hx.symm.trans hy

/-- **Children.** The crossing cluster of every child of a well-connected cube of scale at least
two is contained in the component of the root. -/
theorem TriadicCube.IsWellConnectedRoot.crossingCluster_child_subset (hd : 0 < d)
    {ω : Configuration d} {Q : TriadicCube d} {root : Vertex d}
    (hroot : Q.IsWellConnectedRoot ω root) (hs : 2 ≤ Q.scale) (digits : Fin d → Fin 3) :
    (Q.child digits).crossingCluster ω ⊆ {y | (openIn ω Q.vertices).Reachable root y} := by
  rintro y ⟨r, hr, hry⟩
  have hsub := Q.vertices_child_subset digits (by omega)
  obtain ⟨a, haQ, b, hra, hab, hba⟩ := hr.exists_reachable_face ⟨0, hd⟩
  have hside : 3 * (Q.child digits).side = Q.side := by
    rw [← TriadicCube.side_parent, TriadicCube.child_parent _ _ (by omega)]
  have hcside : 3 ≤ (Q.child digits).side := by
    rw [TriadicCube.three_le_side_iff]
    change 0 < Q.scale - 1
    omega
  have hk : Q.side ≤ 10 * |b ⟨0, hd⟩ - a ⟨0, hd⟩| := by
    rw [hba, abs_of_nonneg (by omega)]
    omega
  have h1 := hroot.reachable_of_reachable hs (hsub haQ) (reachable_openIn_mono hsub hab) _ hk
  exact h1.trans (reachable_openIn_mono hsub (hra.symm.trans hry))

/-- **Children.** The crossing cluster of every child of a well-connected cube of scale at least
two is contained in the crossing cluster of the cube. -/
theorem TriadicCube.IsWellConnectedRoot.crossingCluster_child_subset_crossingCluster (hd : 0 < d)
    {ω : Configuration d} {Q : TriadicCube d} {root : Vertex d}
    (hroot : Q.IsWellConnectedRoot ω root) (hs : 2 ≤ Q.scale) (digits : Fin d → Fin 3) :
    (Q.child digits).crossingCluster ω ⊆ Q.crossingCluster ω := by
  rw [hroot.crossingCluster_eq hd hs]
  exact hroot.crossingCluster_child_subset hd hs digits

end Rigidity.Percolation
