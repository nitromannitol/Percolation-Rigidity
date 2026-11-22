import Rigidity.Proofs.Percolation.PlanarWindows

/-!
# Windows of meshed planar cubes inside an integer square

The windows of `Rigidity.Proofs.Percolation.PlanarWindows` are taken inside a triadic cube `U`, but
only the square of `U` enters. Here the same windows are taken inside an arbitrary integer square
`B`, such as the triple `3□'` of a triadic cube `□'` (Armstrong and Dario, proof of Proposition 3.8)
or a triadic cube with a boundary layer removed (proof of Lemma 5.5). Let `Q` be a meshed planar
cube of side `s ≥ 1000` inside `B`. Its window in `B` is `B` itself if `B` has side less than
`5s`, and otherwise the square of side `5s` inside `B` containing the `2s`-neighbourhood of `Q`
within `B`; it is a surrounding square of `Q`. An open edge leaving the window towards a vertex of
`B` starts at distance at least `2s` from `Q`.

Consequently a vertex `x` of `Q` joined to the anchor of `Q` by an open path inside a set `S` is
joined to it inside the window, provided that every vertex of `B` with a lattice neighbour in
`S \ B` lies at distance at least `s/100` from `x` in some coordinate (this holds when `S ⊆ B`, and
when `x` lies far inside `B`). The anchors of two adjacent meshed cubes inside `B` of the same or
consecutive scales are joined inside a square of side `4s` contained in `B`, or inside `B` itself if
its side is less than `4s`.
-/

open LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped Classical

namespace Rigidity.Percolation

variable {ω : Configuration 2}

/-- A triadic cube inside an integer square has its corners inside the square. -/
theorem TriadicCube.corner_bounds_of_subset_box {Q : TriadicCube 2} {B : IntegerCube 2}
    (h : Q.vertices ⊆ ↑B.vertices) (i : Fin 2) :
    B.corner i ≤ Q.toIntegerCube.corner i ∧
      Q.toIntegerCube.corner i + 3 ^ Q.scale ≤ B.corner i + (B.size : ℤ) := by
  have hpos : (1 : ℤ) ≤ 3 ^ Q.scale := one_le_pow₀ (by norm_num)
  have h0 : Q.toIntegerCube.corner ∈ B.vertices :=
    h (TriadicCube.mem_of_corner_le fun j => ⟨le_rfl, by omega⟩)
  have h1 : (fun j => Q.toIntegerCube.corner j + 3 ^ Q.scale - 1) ∈ B.vertices :=
    h (TriadicCube.mem_of_corner_le fun j => ⟨by omega, by omega⟩)
  have h0' := ((IntegerCube.mem_vertices _ _).1 h0) i
  have h1' := ((IntegerCube.mem_vertices _ _).1 h1) i
  constructor <;> omega

/-- A triadic cube inside an integer square has side at most the side of the square. -/
theorem TriadicCube.three_pow_scale_le_size_of_subset_box {Q : TriadicCube 2} {B : IntegerCube 2}
    (h : Q.vertices ⊆ ↑B.vertices) : (3 : ℤ) ^ Q.scale ≤ (B.size : ℤ) := by
  have hb := TriadicCube.corner_bounds_of_subset_box h 0
  omega

/-- The clamped position of an interval of length `5t` inside `[A, A + L)` around `[b, b + t)`,
for `5t ≤ L`. -/
theorem clamp_window_facts_of_five_le {A L b t : ℤ} (ht : 1 ≤ t) (hL : 5 * t ≤ L) (hA : A ≤ b)
    (hB : b + t ≤ A + L) :
    A ≤ min (max (b - 2 * t) A) (A + L - 5 * t) ∧
      min (max (b - 2 * t) A) (A + L - 5 * t) + 5 * t ≤ A + L ∧
      b - 4 * t ≤ min (max (b - 2 * t) A) (A + L - 5 * t) ∧
      min (max (b - 2 * t) A) (A + L - 5 * t) ≤ b ∧
      (min (max (b - 2 * t) A) (A + L - 5 * t) = A ∨
        min (max (b - 2 * t) A) (A + L - 5 * t) + 2 * t ≤ b) ∧
      (min (max (b - 2 * t) A) (A + L - 5 * t) + 5 * t = A + L ∨
        b + 3 * t ≤ min (max (b - 2 * t) A) (A + L - 5 * t) + 5 * t) := by
  simp only [min_def, max_def]
  split_ifs <;> omega

/-- The clamped position of an interval of length `4t` inside `[A, A + L)` containing two
adjacent intervals `[b, b + t)` and `[b', b' + t')` with `t' ≤ 3t`, for `4t ≤ L`. -/
theorem clamp_pairWindow_facts_of_four_le {A L b b' t t' : ℤ} (ht' : t' ≤ 3 * t)
    (hL : 4 * t ≤ L) (hA : A ≤ b) (hA' : A ≤ b') (hB : b + t ≤ A + L) (hB' : b' + t' ≤ A + L)
    (hn : b' ≤ b + t) (hn' : b ≤ b' + t') :
    A ≤ min (min b b') (A + L - 4 * t) ∧ min (min b b') (A + L - 4 * t) + 4 * t ≤ A + L ∧
      b - 3 * t ≤ min (min b b') (A + L - 4 * t) ∧ min (min b b') (A + L - 4 * t) ≤ b ∧
      min (min b b') (A + L - 4 * t) ≤ b' ∧ b + t ≤ min (min b b') (A + L - 4 * t) + 4 * t ∧
      b' + t' ≤ min (min b b') (A + L - 4 * t) + 4 * t := by
  simp only [min_def]
  split_ifs <;> omega

/-- The window of a cube `Q` inside an integer square `B`. -/
def TriadicCube.boxWindow (Q : TriadicCube 2) (B : IntegerCube 2) : IntegerCube 2 :=
  if B.size < 5 * 3 ^ Q.scale then B else
    ⟨fun i => min (max (Q.toIntegerCube.corner i - 2 * 3 ^ Q.scale) (B.corner i))
      (B.corner i + (B.size : ℤ) - 5 * 3 ^ Q.scale), 5 * 3 ^ Q.scale⟩

theorem TriadicCube.boxWindow_of_lt {Q : TriadicCube 2} {B : IntegerCube 2}
    (hn : B.size < 5 * 3 ^ Q.scale) : Q.boxWindow B = B := by
  unfold TriadicCube.boxWindow
  rw [if_pos hn]

theorem TriadicCube.boxWindow_of_not_lt {Q : TriadicCube 2} {B : IntegerCube 2}
    (hn : ¬ B.size < 5 * 3 ^ Q.scale) :
    (Q.boxWindow B).corner = (fun i => min (max (Q.toIntegerCube.corner i - 2 * 3 ^ Q.scale)
      (B.corner i)) (B.corner i + (B.size : ℤ) - 5 * 3 ^ Q.scale)) ∧
    (((Q.boxWindow B).size : ℕ) : ℤ) = 5 * 3 ^ Q.scale := by
  unfold TriadicCube.boxWindow
  rw [if_neg hn]
  refine ⟨rfl, ?_⟩
  change ((5 * 3 ^ Q.scale : ℕ) : ℤ) = _
  push_cast
  ring

/-- Coordinates of the window of a cube inside an integer square. -/
theorem TriadicCube.boxWindow_corner_facts {Q : TriadicCube 2} {B : IntegerCube 2}
    (hsub : Q.vertices ⊆ ↑B.vertices) (hn : ¬ B.size < 5 * 3 ^ Q.scale) (i : Fin 2) :
    B.corner i ≤ (Q.boxWindow B).corner i ∧
      (Q.boxWindow B).corner i + 5 * 3 ^ Q.scale ≤ B.corner i + (B.size : ℤ) ∧
      Q.toIntegerCube.corner i - 4 * 3 ^ Q.scale ≤ (Q.boxWindow B).corner i ∧
      (Q.boxWindow B).corner i ≤ Q.toIntegerCube.corner i ∧
      ((Q.boxWindow B).corner i = B.corner i ∨
        (Q.boxWindow B).corner i + 2 * 3 ^ Q.scale ≤ Q.toIntegerCube.corner i) ∧
      ((Q.boxWindow B).corner i + 5 * 3 ^ Q.scale = B.corner i + (B.size : ℤ) ∨
        Q.toIntegerCube.corner i + 3 * 3 ^ Q.scale ≤
          (Q.boxWindow B).corner i + 5 * 3 ^ Q.scale) := by
  have hb := TriadicCube.corner_bounds_of_subset_box hsub i
  have ht : (1 : ℤ) ≤ 3 ^ Q.scale := one_le_pow₀ (by norm_num)
  have hL : 5 * (3 : ℤ) ^ Q.scale ≤ (B.size : ℤ) := by
    have : 5 * 3 ^ Q.scale ≤ B.size := not_lt.1 hn
    exact_mod_cast this
  rw [(TriadicCube.boxWindow_of_not_lt hn).1]
  exact clamp_window_facts_of_five_le ht hL hb.1 hb.2

/-- The window of a cube inside an integer square is one of its surrounding squares. -/
theorem TriadicCube.boxWindow_mem_planarSquares {Q : TriadicCube 2} {B : IntegerCube 2}
    (hsub : Q.vertices ⊆ ↑B.vertices) : Q.boxWindow B ∈ Q.planarSquares := by
  have hr := Q.two_mul_ninefoldRadius
  have hge := TriadicCube.three_pow_scale_le_size_of_subset_box hsub
  rw [TriadicCube.mem_planarSquares]
  by_cases hn : B.size < 5 * 3 ^ Q.scale
  · rw [TriadicCube.boxWindow_of_lt hn]
    have hgeN : 3 ^ Q.scale ≤ B.size := by exact_mod_cast hge
    have hnZ : (B.size : ℤ) < 5 * 3 ^ Q.scale := by exact_mod_cast hn
    refine ⟨hgeN, by omega, fun i => ?_⟩
    have hb := TriadicCube.corner_bounds_of_subset_box hsub i
    have hc := Q.two_mul_center_sub_corner i
    constructor <;> omega
  · obtain ⟨-, hsize⟩ := TriadicCube.boxWindow_of_not_lt (Q := Q) (B := B) hn
    have hsizeN : (Q.boxWindow B).size = 5 * 3 ^ Q.scale := by exact_mod_cast hsize
    rw [hsizeN]
    refine ⟨by omega, by omega, fun i => ?_⟩
    have hf := TriadicCube.boxWindow_corner_facts hsub hn i
    have hc := Q.two_mul_center_sub_corner i
    have hcast : ((5 * 3 ^ Q.scale : ℕ) : ℤ) = 5 * 3 ^ Q.scale := by push_cast; ring
    rw [hcast]
    constructor <;> omega

/-- The window of a cube contains the cube. -/
theorem TriadicCube.subset_boxWindow {Q : TriadicCube 2} {B : IntegerCube 2}
    (hsub : Q.vertices ⊆ ↑B.vertices) : Q.vertices ⊆ ↑(Q.boxWindow B).vertices := by
  intro x hx
  rw [Finset.mem_coe, IntegerCube.mem_vertices]
  intro i
  have hx' := TriadicCube.corner_le_of_mem hx i
  have hb := TriadicCube.corner_bounds_of_subset_box hsub i
  by_cases hn : B.size < 5 * 3 ^ Q.scale
  · rw [TriadicCube.boxWindow_of_lt hn]
    constructor <;> omega
  · rw [(TriadicCube.boxWindow_of_not_lt hn).2]
    have hf := TriadicCube.boxWindow_corner_facts hsub hn i
    constructor <;> omega

/-- The window of a cube inside an integer square lies in the square. -/
theorem TriadicCube.boxWindow_subset {Q : TriadicCube 2} {B : IntegerCube 2}
    (hsub : Q.vertices ⊆ ↑B.vertices) : (Q.boxWindow B).vertices ⊆ B.vertices := by
  intro x hx
  rw [IntegerCube.mem_vertices] at hx ⊢
  intro i
  have hxi := hx i
  by_cases hn : B.size < 5 * 3 ^ Q.scale
  · rw [TriadicCube.boxWindow_of_lt hn] at hxi
    exact hxi
  · rw [(TriadicCube.boxWindow_of_not_lt hn).2] at hxi
    have hf := TriadicCube.boxWindow_corner_facts hsub hn i
    constructor <;> omega

/-- **Exits from a window.** An open edge leaving the window of `Q` inside `B` towards a vertex of
`B` starts at distance at least `2s` from every vertex of `Q` in some coordinate. -/
theorem TriadicCube.boxWindow_exit {Q : TriadicCube 2} {B : IntegerCube 2}
    (hsub : Q.vertices ⊆ ↑B.vertices) (hn : ¬ B.size < 5 * 3 ^ Q.scale)
    {u v x : Vertex 2} (hu : u ∈ (Q.boxWindow B).vertices) (hv : v ∈ B.vertices)
    (hvw : v ∉ (Q.boxWindow B).vertices) (huv : ∀ i, |v i - u i| ≤ 1) (hx : x ∈ Q.vertices) :
    ∃ k, x k + 2 * 3 ^ Q.scale ≤ u k ∨ u k + 2 * 3 ^ Q.scale ≤ x k := by
  rw [IntegerCube.mem_vertices, (TriadicCube.boxWindow_of_not_lt hn).2] at hu hvw
  push Not at hvw
  obtain ⟨k, hk⟩ := hvw
  refine ⟨k, ?_⟩
  have huk := hu k
  have hvk := (IntegerCube.mem_vertices _ _).1 hv k
  have hxk := TriadicCube.corner_le_of_mem hx k
  have hf := TriadicCube.boxWindow_corner_facts hsub hn k
  have hadj := huv k
  rw [abs_le] at hadj
  omega

/-- **Local connection inside a window.** Let `Q` be a meshed cube of side `s ≥ 1000` inside an
integer square `B`, and `x ∈ Q` joined to the anchor of `Q` by an open path inside a set `S`. If
every vertex of `B` with a lattice neighbour in `S` outside `B` is at distance at least `⌊s/100⌋`
from `x` in some coordinate, then `x` is joined to the anchor inside the window of `Q` in `B`. -/
theorem TriadicCube.reachIn_boxWindow_of_reachIn {Q : TriadicCube 2} {B : IntegerCube 2}
    (hQ : Q.planarMeshed ω) (hs : 1000 ≤ 3 ^ Q.scale) (hsub : Q.vertices ⊆ ↑B.vertices)
    {x : Vertex 2} (hx : x ∈ Q.vertices) {S : Set (Vertex 2)}
    (hdeep : ∀ u ∈ B.vertices, ∀ v ∈ S, v ∉ B.vertices → (∀ i, |v i - u i| ≤ 1) →
      ∃ k, ((3 ^ Q.scale / 100 : ℕ) : ℤ) ≤ |x k - u k|)
    (h : ReachIn ω S x (Q.planarAnchor ω)) :
    ReachIn ω ↑(Q.boxWindow B).vertices (Q.planarAnchor ω) x := by
  set R : Set (Vertex 2) := ↑(Q.boxWindow B).vertices with hR
  have hxR : x ∈ R := Q.subset_boxWindow hsub hx
  obtain ⟨W, hW⟩ := h
  by_cases hall : ∀ z ∈ W.support, z ∈ R
  · exact ReachIn.symm (show ReachIn ω R x (Q.planarAnchor ω) from ⟨W, hall⟩)
  push Not at hall
  obtain ⟨z, hzW, hzR⟩ := hall
  obtain ⟨u, v, hxu, huv, hvR, hvW⟩ :=
    exists_exit_of_walk_mem_support hxR hzR (W.takeUntil z hzW)
  have hvS : v ∈ S := hW v (W.support_takeUntil_subset_support hzW hvW)
  have huR : u ∈ (Q.boxWindow B).vertices := Finset.mem_coe.1 hxu.end_mem
  have huB : u ∈ B.vertices := Q.boxWindow_subset hsub huR
  have hadj : ∀ i, |v i - u i| ≤ 1 := fun i =>
    Rigidity.Proofs.S3.abs_coord_sub_le_one_of_adj (openGraph_le ω huv) i
  have hlong : ∃ k, ((3 ^ Q.scale / 100 : ℕ) : ℤ) ≤ |x k - u k| := by
    by_cases hvB : v ∈ B.vertices
    · have hn : ¬ B.size < 5 * 3 ^ Q.scale := by
        intro hn
        rw [hR, TriadicCube.boxWindow_of_lt hn] at hvR
        exact hvR hvB
      obtain ⟨k, hk⟩ := Q.boxWindow_exit hsub hn huR hvB hvR hadj hx
      have hw100 : 100 * ((3 ^ Q.scale / 100 : ℕ) : ℤ) ≤ 3 ^ Q.scale := by
        have := Nat.mul_div_le (3 ^ Q.scale) 100
        have hc : ((3 ^ Q.scale : ℕ) : ℤ) = 3 ^ Q.scale := by push_cast; rfl
        omega
      have hpos : (1 : ℤ) ≤ 3 ^ Q.scale := one_le_pow₀ (by norm_num)
      refine ⟨k, ?_⟩
      rcases hk with hk | hk
      · rw [abs_sub_comm, abs_of_nonneg (by omega)]
        omega
      · rw [abs_of_nonneg (by omega)]
        omega
    · exact hdeep u huB v hvS hvB hadj
  obtain ⟨k, hk⟩ := hlong
  exact Q.reachIn_planarAnchor_of_long hQ hs (Q.boxWindow_mem_planarSquares hsub)
    (Q.subset_boxWindow hsub) hxu hk

/-- The square of side `4s` inside `B` containing two adjacent cubes `Q` and `Q'`, or `B` itself
when its side is less than `4s`. -/
def TriadicCube.boxPairWindow (Q Q' : TriadicCube 2) (B : IntegerCube 2) : IntegerCube 2 :=
  if B.size < 4 * 3 ^ Q.scale then B else
    ⟨fun i => min (min (Q.toIntegerCube.corner i) (Q'.toIntegerCube.corner i))
      (B.corner i + (B.size : ℤ) - 4 * 3 ^ Q.scale), 4 * 3 ^ Q.scale⟩

theorem TriadicCube.boxPairWindow_of_not_lt {Q Q' : TriadicCube 2} {B : IntegerCube 2}
    (hn : ¬ B.size < 4 * 3 ^ Q.scale) :
    (Q.boxPairWindow Q' B).corner = (fun i => min (min (Q.toIntegerCube.corner i)
      (Q'.toIntegerCube.corner i)) (B.corner i + (B.size : ℤ) - 4 * 3 ^ Q.scale)) ∧
    (((Q.boxPairWindow Q' B).size : ℕ) : ℤ) = 4 * 3 ^ Q.scale := by
  unfold TriadicCube.boxPairWindow
  rw [if_neg hn]
  refine ⟨rfl, ?_⟩
  change ((4 * 3 ^ Q.scale : ℕ) : ℤ) = _
  push_cast
  ring

/-- The pair window of two adjacent cubes inside `B` is a surrounding square of the first cube
containing both cubes and contained in `B`. -/
theorem TriadicCube.boxPairWindow_spec {Q Q' : TriadicCube 2} {B : IntegerCube 2}
    (hsub : Q.vertices ⊆ ↑B.vertices) (hsub' : Q'.vertices ⊆ ↑B.vertices)
    (hscale : Q.scale ≤ Q'.scale) (hscale' : Q'.scale ≤ Q.scale + 1) {x y : Vertex 2}
    (hx : x ∈ Q.vertices) (hy : y ∈ Q'.vertices) (hnear : ∀ i, |x i - y i| ≤ 1) :
    Q.boxPairWindow Q' B ∈ Q.planarSquares ∧ Q.vertices ⊆ ↑(Q.boxPairWindow Q' B).vertices ∧
      Q'.vertices ⊆ ↑(Q.boxPairWindow Q' B).vertices ∧
      (Q.boxPairWindow Q' B).vertices ⊆ B.vertices := by
  by_cases hn : B.size < 4 * 3 ^ Q.scale
  · have hw : Q.boxPairWindow Q' B = B := by
      unfold TriadicCube.boxPairWindow
      rw [if_pos hn]
    rw [hw]
    have hmem := Q.boxWindow_mem_planarSquares hsub
    rw [TriadicCube.boxWindow_of_lt (by omega)] at hmem
    exact ⟨hmem, hsub, hsub', Finset.Subset.refl _⟩
  have hL : 4 * (3 : ℤ) ^ Q.scale ≤ (B.size : ℤ) := by
    have : 4 * 3 ^ Q.scale ≤ B.size := not_lt.1 hn
    exact_mod_cast this
  have hr := Q.two_mul_ninefoldRadius
  obtain ⟨hcor, hsize⟩ := TriadicCube.boxPairWindow_of_not_lt (Q' := Q') (B := B) hn
  have hfacts : ∀ i, B.corner i ≤ (Q.boxPairWindow Q' B).corner i ∧
      (Q.boxPairWindow Q' B).corner i + 4 * 3 ^ Q.scale ≤ B.corner i + (B.size : ℤ) ∧
      Q.toIntegerCube.corner i - 3 * 3 ^ Q.scale ≤ (Q.boxPairWindow Q' B).corner i ∧
      (Q.boxPairWindow Q' B).corner i ≤ Q.toIntegerCube.corner i ∧
      (Q.boxPairWindow Q' B).corner i ≤ Q'.toIntegerCube.corner i ∧
      Q.toIntegerCube.corner i + 3 ^ Q.scale ≤
        (Q.boxPairWindow Q' B).corner i + 4 * 3 ^ Q.scale ∧
      Q'.toIntegerCube.corner i + 3 ^ Q'.scale ≤
        (Q.boxPairWindow Q' B).corner i + 4 * 3 ^ Q.scale := by
    intro i
    have hb := TriadicCube.corner_bounds_of_subset_box hsub i
    have hb' := TriadicCube.corner_bounds_of_subset_box hsub' i
    have hnr := TriadicCube.corner_bounds_of_near hscale hscale' hx hy hnear i
    rw [hcor]
    exact clamp_pairWindow_facts_of_four_le hnr.2.2.2 hL hb.1 hb'.1 hb.2 hb'.2 hnr.1 hnr.2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [TriadicCube.mem_planarSquares]
    have hsizeN : (Q.boxPairWindow Q' B).size = 4 * 3 ^ Q.scale := by exact_mod_cast hsize
    rw [hsizeN]
    refine ⟨by omega, by omega, fun i => ?_⟩
    have hf := hfacts i
    have hc := Q.two_mul_center_sub_corner i
    have hcast : ((4 * 3 ^ Q.scale : ℕ) : ℤ) = 4 * 3 ^ Q.scale := by push_cast; ring
    rw [hcast]
    constructor <;> omega
  · intro z hz
    rw [Finset.mem_coe, IntegerCube.mem_vertices, hsize]
    intro i
    have hz' := TriadicCube.corner_le_of_mem hz i
    have hf := hfacts i
    constructor <;> omega
  · intro z hz
    rw [Finset.mem_coe, IntegerCube.mem_vertices, hsize]
    intro i
    have hz' := TriadicCube.corner_le_of_mem hz i
    have hf := hfacts i
    constructor <;> omega
  · intro z hz
    rw [IntegerCube.mem_vertices, hsize] at hz
    rw [IntegerCube.mem_vertices]
    intro i
    have hzi := hz i
    have hf := hfacts i
    constructor <;> omega

/-- **Adjacent anchors inside an integer square.** The anchors of two adjacent meshed cubes inside
`B`, the second of the same or the next scale, are joined inside their pair window. -/
theorem TriadicCube.reachIn_planarAnchor_boxPairWindow {Q Q' : TriadicCube 2} {B : IntegerCube 2}
    (hQ : Q.planarMeshed ω) (hQ' : Q'.planarMeshed ω) (hs : 1000 ≤ 3 ^ Q.scale)
    (hsub : Q.vertices ⊆ ↑B.vertices) (hsub' : Q'.vertices ⊆ ↑B.vertices)
    (hscale : Q.scale ≤ Q'.scale) (hscale' : Q'.scale ≤ Q.scale + 1) {x y : Vertex 2}
    (hx : x ∈ Q.vertices) (hy : y ∈ Q'.vertices) (hnear : ∀ i, |x i - y i| ≤ 1) :
    ReachIn ω ↑(Q.boxPairWindow Q' B).vertices (Q.planarAnchor ω) (Q'.planarAnchor ω) := by
  obtain ⟨hR, hQR, hQ'R, -⟩ := Q.boxPairWindow_spec hsub hsub' hscale hscale' hx hy hnear
  have hs' : 1000 ≤ 3 ^ Q'.scale := hs.trans (Nat.pow_le_pow_right (by norm_num) hscale)
  obtain ⟨-, hA', -⟩ := Q'.planarAnchor_spec hQ' hs'
  set w' := 3 ^ Q'.scale / 100
  have hw' : 100 * w' ≤ 3 ^ Q'.scale := Nat.mul_div_le _ _
  have hwQ' : w' + 1 ≤ Q'.toIntegerCube.size := by
    change w' + 1 ≤ 3 ^ Q'.scale
    omega
  obtain ⟨_hub, -, -, hfaces⟩ := (hQ' _ Q'.toIntegerCube_mem_planarSquares).exists_hub hwQ'
  obtain ⟨⟨yl, -, hylf, hhl⟩, ⟨yu, -, hyuf, hhu⟩⟩ := hfaces 0
  have hyl0 := (IntegerCube.mem_lowerFace_coe.1 hylf).2
  have hyu0 := (IntegerCube.mem_upperFace_coe.1 hyuf).2
  have hcross : ReachIn ω Q'.vertices yl yu :=
    Q'.coe_toIntegerCube_vertices ▸ (hhl.symm.trans hhu)
  have hsz := Q'.cast_toIntegerCube_size
  have hw'Z : 100 * (w' : ℤ) ≤ 3 ^ Q'.scale := by exact_mod_cast hw'
  have hpos' : (1000 : ℤ) ≤ 3 ^ Q'.scale := by exact_mod_cast hs'
  have hge : (3 : ℤ) ^ Q.scale ≤ 3 ^ Q'.scale := pow_le_pow_right₀ (by norm_num) hscale
  have hw100 : 100 * ((3 ^ Q.scale / 100 : ℕ) : ℤ) ≤ 3 ^ Q.scale := by
    have := Nat.mul_div_le (3 ^ Q.scale) 100
    have hc : ((3 ^ Q.scale : ℕ) : ℤ) = 3 ^ Q.scale := by push_cast; rfl
    omega
  have hA'yl : ReachIn ω Q'.vertices (Q'.planarAnchor ω) yl := hA' yl yu 0 hcross (by omega)
  have hlong : ((3 ^ Q.scale / 100 : ℕ) : ℤ) ≤ |yl 0 - yu 0| := by
    rw [abs_sub_comm, abs_of_nonneg (by omega)]
    omega
  have hAyl := Q.reachIn_planarAnchor_of_long hQ hs hR hQR (hcross.mono hQ'R) hlong
  exact hAyl.trans (hA'yl.mono hQ'R).symm

end Rigidity.Percolation
