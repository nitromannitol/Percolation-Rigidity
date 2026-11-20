import Rigidity.Proofs.Percolation.PlanarPartition

/-!
# Windows of meshed planar cubes inside a triadic cube

Let `Q` be a meshed planar cube of side `s ≥ 1000` inside a triadic cube `U`. Its *window* in `U`
is an integer square containing `Q`, contained in `U` and in the square of side `9s` around `Q`,
with side between `s` and `9s`: it is `U` itself if `U` has scale at most one more than `Q`, and
otherwise the square of side `5s` inside `U` containing the `2s`-neighbourhood of `Q` within `U`.
An open path inside `U` leaving the window does so at distance at least `2s` from `Q`.

Consequently, a vertex of `Q` joined inside `U` to the anchor of `Q` is joined to it inside the
window, and the anchors of two adjacent meshed cubes inside `U` of the same or consecutive scales
are joined inside a square of side `4s` contained in `U`. These replace the local paths of
Armstrong and Dario (Lemma 3.2), which are asserted to stay inside the neighbours of the
partition cube; the windows lie in `U` and in the square of side `9s` around the cube.
-/

open LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped Classical

namespace Rigidity.Percolation

variable {ω : Configuration 2}

/-- The centre of a triadic cube is `(s - 1) / 2` above the corner of its integer square. -/
theorem TriadicCube.two_mul_center_sub_corner (Q : TriadicCube 2) (i : Fin 2) :
    2 * (Q.center i - Q.toIntegerCube.corner i) + 1 = 3 ^ Q.scale := by
  have ho : (3 : ℤ) ^ Q.scale % 2 = 1 :=
    Int.odd_iff.mp ((show Odd (3 : ℤ) from ⟨1, by norm_num⟩).pow)
  change 2 * (Q.side * Q.index i - (Q.side * Q.index i - Q.side / 2)) + 1 = 3 ^ Q.scale
  have hs : Q.side = 3 ^ Q.scale := rfl
  rw [hs]
  omega

theorem TriadicCube.cast_toIntegerCube_size (Q : TriadicCube 2) :
    ((Q.toIntegerCube.size : ℕ) : ℤ) = 3 ^ Q.scale := by
  change ((3 ^ Q.scale : ℕ) : ℤ) = _
  push_cast
  rfl

/-- Coordinates of the vertices of a triadic cube lie between the corner and the opposite
corner. -/
theorem TriadicCube.corner_le_of_mem {Q : TriadicCube 2} {x : Vertex 2} (hx : x ∈ Q.vertices)
    (i : Fin 2) :
    Q.toIntegerCube.corner i ≤ x i ∧ x i < Q.toIntegerCube.corner i + 3 ^ Q.scale := by
  have h := ((IntegerCube.mem_vertices _ x).1 ((Q.mem_toIntegerCube_vertices x).2 hx)) i
  rw [Q.cast_toIntegerCube_size] at h
  exact h

theorem TriadicCube.mem_of_corner_le {Q : TriadicCube 2} {x : Vertex 2}
    (h : ∀ i, Q.toIntegerCube.corner i ≤ x i ∧ x i < Q.toIntegerCube.corner i + 3 ^ Q.scale) :
    x ∈ Q.vertices := by
  rw [← Q.mem_toIntegerCube_vertices, IntegerCube.mem_vertices, Q.cast_toIntegerCube_size]
  exact h

/-- A triadic cube inside another one has its corners inside the other one. -/
theorem TriadicCube.corner_bounds_of_subset {Q U : TriadicCube 2}
    (h : Q.vertices ⊆ U.vertices) (i : Fin 2) :
    U.toIntegerCube.corner i ≤ Q.toIntegerCube.corner i ∧
      Q.toIntegerCube.corner i + 3 ^ Q.scale ≤ U.toIntegerCube.corner i + 3 ^ U.scale := by
  have hpos : (1 : ℤ) ≤ 3 ^ Q.scale := one_le_pow₀ (by norm_num)
  have h0 : Q.toIntegerCube.corner ∈ U.vertices :=
    h (TriadicCube.mem_of_corner_le fun j => ⟨le_rfl, by omega⟩)
  have h1 : (fun j => Q.toIntegerCube.corner j + 3 ^ Q.scale - 1) ∈ U.vertices :=
    h (TriadicCube.mem_of_corner_le fun j => ⟨by omega, by omega⟩)
  have h0' := TriadicCube.corner_le_of_mem h0 i
  have h1' := TriadicCube.corner_le_of_mem h1 i
  constructor <;> omega

/-- An open walk from inside a region to outside it leaves the region along an open edge whose
outer vertex lies on the walk. -/
theorem exists_exit_of_walk_mem_support {S : Set (Vertex 2)} {x y : Vertex 2} (hx : x ∈ S)
    (hy : y ∉ S) (W : (openGraph ω).Walk x y) :
    ∃ u v, ReachIn ω S x u ∧ (openGraph ω).Adj u v ∧ v ∉ S ∧ v ∈ W.support := by
  induction W with
  | nil => exact absurd hx hy
  | @cons a b c hab W ih =>
    by_cases hb : b ∈ S
    · obtain ⟨u, v, hu, huv, hv, hvW⟩ := ih hb hy
      refine ⟨u, v, ?_, huv, hv, List.mem_cons_of_mem _ hvW⟩
      obtain ⟨P, hP⟩ := hu
      refine ⟨SimpleGraph.Walk.cons hab P, fun z hz => ?_⟩
      rcases List.mem_cons.1 hz with rfl | hz
      exacts [hx, hP z hz]
    · refine ⟨a, b, ⟨SimpleGraph.Walk.nil, fun z hz => ?_⟩, hab, hb, ?_⟩
      · simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
        exact hz ▸ hx
      · rw [SimpleGraph.Walk.support_cons]
        exact List.mem_cons_of_mem _ W.start_mem_support

/-- **Long paths reach the anchor.** If a meshed cube `Q` of side at least `1000` lies in one of
its surrounding squares `R`, then every vertex joined inside `R` to a vertex at distance at least
`⌊s / 100⌋` in some coordinate is joined inside `R` to the anchor of `Q`. -/
theorem TriadicCube.reachIn_planarAnchor_of_long {Q : TriadicCube 2} (hQ : Q.planarMeshed ω)
    (hs : 1000 ≤ 3 ^ Q.scale) {R : IntegerCube 2} (hR : R ∈ Q.planarSquares)
    (hQR : Q.vertices ⊆ ↑R.vertices) {c d : Vertex 2} {k : Fin 2}
    (hcd : ReachIn ω ↑R.vertices c d) (hk : ((3 ^ Q.scale / 100 : ℕ) : ℤ) ≤ |c k - d k|) :
    ReachIn ω ↑R.vertices (Q.planarAnchor ω) c := by
  set w := 3 ^ Q.scale / 100 with hwdef
  obtain ⟨-, hA, -⟩ := Q.planarAnchor_spec hQ hs
  have hw100 : 100 * w ≤ 3 ^ Q.scale := Nat.mul_div_le _ _
  have hRs := ((TriadicCube.mem_planarSquares).1 hR).1
  have hwR : w + 1 ≤ R.size := by omega
  obtain ⟨hub, -, hhub, -⟩ := (hQ R hR).exists_hub hwR
  have hwQ : w + 1 ≤ Q.toIntegerCube.size := by
    change w + 1 ≤ 3 ^ Q.scale
    omega
  obtain ⟨_hub, -, -, hfaces⟩ := (hQ _ Q.toIntegerCube_mem_planarSquares).exists_hub hwQ
  obtain ⟨⟨yl, -, hylf, hhl⟩, ⟨yu, -, hyuf, hhu⟩⟩ := hfaces 0
  have hyl0 := (IntegerCube.mem_lowerFace_coe.1 hylf).2
  have hyu0 := (IntegerCube.mem_upperFace_coe.1 hyuf).2
  have hQset := Q.coe_toIntegerCube_vertices
  have hcross : ReachIn ω Q.vertices yl yu := hQset ▸ (hhl.symm.trans hhu)
  have hsz : ((Q.toIntegerCube.size : ℕ) : ℤ) = 3 ^ Q.scale := Q.cast_toIntegerCube_size
  have hw100' : 100 * (w : ℤ) ≤ 3 ^ Q.scale := by exact_mod_cast hw100
  have hpos : (1000 : ℤ) ≤ 3 ^ Q.scale := by exact_mod_cast hs
  have hdisp : yl 0 + (w : ℤ) ≤ yu 0 := by omega
  have h1 : ReachIn ω ↑R.vertices (Q.planarAnchor ω) yl := (hA yl yu 0 hcross hdisp).mono hQR
  have h2 : ReachIn ω ↑R.vertices hub yl := hhub yl yu 0 (hcross.mono hQR) hdisp
  have h3 : ReachIn ω ↑R.vertices hub c := by
    rcases le_abs'.1 hk with hk' | hk'
    · exact hhub c d k hcd (by omega)
    · exact (hhub d c k hcd.symm (by omega)).trans hcd.symm
  exact (h1.trans h2.symm).trans h3

/-- The window of a cube `Q` inside a triadic cube `U`. -/
def TriadicCube.window (Q U : TriadicCube 2) : IntegerCube 2 :=
  if U.scale ≤ Q.scale + 1 then U.toIntegerCube else
    ⟨fun i => min (max (Q.toIntegerCube.corner i - 2 * 3 ^ Q.scale) (U.toIntegerCube.corner i))
      (U.toIntegerCube.corner i + 3 ^ U.scale - 5 * 3 ^ Q.scale), 5 * 3 ^ Q.scale⟩

theorem three_pow_le_three_mul_of_le {j n : ℕ} (h : n ≤ j + 1) :
    (3 : ℤ) ^ n ≤ 3 * 3 ^ j := by
  calc (3 : ℤ) ^ n ≤ 3 ^ (j + 1) := pow_le_pow_right₀ (by norm_num) h
    _ = 3 * 3 ^ j := by ring

theorem nine_mul_three_pow_le_of_lt {j n : ℕ} (h : ¬ n ≤ j + 1) :
    9 * (3 : ℤ) ^ j ≤ 3 ^ n := by
  calc 9 * (3 : ℤ) ^ j = 3 ^ (j + 2) := by ring
    _ ≤ 3 ^ n := pow_le_pow_right₀ (by norm_num) (by omega)

/-- The clamped position of an interval of length `5t` inside `[A, A + L)` around `[b, b + t)`. -/
theorem clamp_window_facts {A L b t : ℤ} (ht : 1 ≤ t) (hL : 9 * t ≤ L) (hA : A ≤ b)
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
adjacent intervals `[b, b + t)` and `[b', b' + t')` with `t ≤ t' ≤ 3t`. -/
theorem clamp_pairWindow_facts {A L b b' t t' : ℤ} (ht : t ≤ t') (ht' : t' ≤ 3 * t)
    (hL : 9 * t ≤ L) (hA : A ≤ b) (hA' : A ≤ b') (hB : b + t ≤ A + L) (hB' : b' + t' ≤ A + L)
    (hn : b' ≤ b + t) (hn' : b ≤ b' + t') :
    A ≤ min (min b b') (A + L - 4 * t) ∧ min (min b b') (A + L - 4 * t) + 4 * t ≤ A + L ∧
      b - 3 * t ≤ min (min b b') (A + L - 4 * t) ∧ min (min b b') (A + L - 4 * t) ≤ b ∧
      min (min b b') (A + L - 4 * t) ≤ b' ∧ b + t ≤ min (min b b') (A + L - 4 * t) + 4 * t ∧
      b' + t' ≤ min (min b b') (A + L - 4 * t) + 4 * t := by
  simp only [min_def]
  split_ifs <;> omega

theorem TriadicCube.window_of_le {Q U : TriadicCube 2} (hU : U.scale ≤ Q.scale + 1) :
    Q.window U = U.toIntegerCube := by
  unfold TriadicCube.window
  rw [if_pos hU]

theorem TriadicCube.window_of_not_le {Q U : TriadicCube 2} (hU : ¬ U.scale ≤ Q.scale + 1) :
    (Q.window U).corner = (fun i => min (max (Q.toIntegerCube.corner i - 2 * 3 ^ Q.scale)
      (U.toIntegerCube.corner i)) (U.toIntegerCube.corner i + 3 ^ U.scale - 5 * 3 ^ Q.scale)) ∧
    (((Q.window U).size : ℕ) : ℤ) = 5 * 3 ^ Q.scale := by
  unfold TriadicCube.window
  rw [if_neg hU]
  refine ⟨rfl, ?_⟩
  change ((5 * 3 ^ Q.scale : ℕ) : ℤ) = _
  push_cast
  ring

/-- Coordinates of the window of a cube inside a triadic cube. -/
theorem TriadicCube.window_corner_facts {Q U : TriadicCube 2} (hsub : Q.vertices ⊆ U.vertices)
    (hU : ¬ U.scale ≤ Q.scale + 1) (i : Fin 2) :
    U.toIntegerCube.corner i ≤ (Q.window U).corner i ∧
      (Q.window U).corner i + 5 * 3 ^ Q.scale ≤ U.toIntegerCube.corner i + 3 ^ U.scale ∧
      Q.toIntegerCube.corner i - 4 * 3 ^ Q.scale ≤ (Q.window U).corner i ∧
      (Q.window U).corner i ≤ Q.toIntegerCube.corner i ∧
      ((Q.window U).corner i = U.toIntegerCube.corner i ∨
        (Q.window U).corner i + 2 * 3 ^ Q.scale ≤ Q.toIntegerCube.corner i) ∧
      ((Q.window U).corner i + 5 * 3 ^ Q.scale = U.toIntegerCube.corner i + 3 ^ U.scale ∨
        Q.toIntegerCube.corner i + 3 * 3 ^ Q.scale ≤ (Q.window U).corner i + 5 * 3 ^ Q.scale) := by
  have hb := TriadicCube.corner_bounds_of_subset hsub i
  have ht : (1 : ℤ) ≤ 3 ^ Q.scale := one_le_pow₀ (by norm_num)
  rw [(TriadicCube.window_of_not_le hU).1]
  exact clamp_window_facts ht (nine_mul_three_pow_le_of_lt hU) hb.1 hb.2

/-- The window of a cube inside a larger triadic cube is one of its surrounding squares. -/
theorem TriadicCube.window_mem_planarSquares {Q U : TriadicCube 2} (hsc : Q.scale ≤ U.scale)
    (hsub : Q.vertices ⊆ U.vertices) : Q.window U ∈ Q.planarSquares := by
  have hr := Q.two_mul_ninefoldRadius
  have hgeN : 3 ^ Q.scale ≤ 3 ^ U.scale := Nat.pow_le_pow_right (by norm_num) hsc
  rw [TriadicCube.mem_planarSquares]
  by_cases hU : U.scale ≤ Q.scale + 1
  · rw [TriadicCube.window_of_le hU]
    have hle := three_pow_le_three_mul_of_le hU
    have hleN : 3 ^ U.scale ≤ 3 * 3 ^ Q.scale := by exact_mod_cast hle
    refine ⟨hgeN, by change 3 ^ U.scale ≤ 9 * 3 ^ Q.scale; omega, fun i => ?_⟩
    have hb := TriadicCube.corner_bounds_of_subset hsub i
    have hc := Q.two_mul_center_sub_corner i
    rw [U.cast_toIntegerCube_size]
    constructor <;> omega
  · obtain ⟨-, hsize⟩ := TriadicCube.window_of_not_le (Q := Q) hU
    have hsizeN : (Q.window U).size = 5 * 3 ^ Q.scale := by exact_mod_cast hsize
    rw [hsizeN]
    refine ⟨by omega, by omega, fun i => ?_⟩
    have hf := TriadicCube.window_corner_facts hsub hU i
    have hc := Q.two_mul_center_sub_corner i
    have hcast : ((5 * 3 ^ Q.scale : ℕ) : ℤ) = 5 * 3 ^ Q.scale := by push_cast; ring
    rw [hcast]
    constructor <;> omega

/-- The window of a cube contains the cube. -/
theorem TriadicCube.subset_window {Q U : TriadicCube 2} (hsub : Q.vertices ⊆ U.vertices) :
    Q.vertices ⊆ ↑(Q.window U).vertices := by
  intro x hx
  rw [Finset.mem_coe, IntegerCube.mem_vertices]
  intro i
  have hx' := TriadicCube.corner_le_of_mem hx i
  have hb := TriadicCube.corner_bounds_of_subset hsub i
  by_cases hU : U.scale ≤ Q.scale + 1
  · rw [TriadicCube.window_of_le hU, U.cast_toIntegerCube_size]
    constructor <;> omega
  · rw [(TriadicCube.window_of_not_le hU).2]
    have hf := TriadicCube.window_corner_facts hsub hU i
    constructor <;> omega

/-- The window of a cube inside a triadic cube lies in that triadic cube. -/
theorem TriadicCube.window_subset {Q U : TriadicCube 2} (hsub : Q.vertices ⊆ U.vertices) :
    ↑(Q.window U).vertices ⊆ U.vertices := by
  intro x hx
  rw [Finset.mem_coe, IntegerCube.mem_vertices] at hx
  apply TriadicCube.mem_of_corner_le
  intro i
  have hxi := hx i
  by_cases hU : U.scale ≤ Q.scale + 1
  · rw [TriadicCube.window_of_le hU, U.cast_toIntegerCube_size] at hxi
    exact hxi
  · rw [(TriadicCube.window_of_not_le hU).2] at hxi
    have hf := TriadicCube.window_corner_facts hsub hU i
    constructor <;> omega

/-- **Exits from a window.** An open edge leaving the window of `Q` inside `U` towards a vertex of
`U` starts at distance at least `2s` from every vertex of `Q` in some coordinate. -/
theorem TriadicCube.window_exit {Q U : TriadicCube 2} (hsub : Q.vertices ⊆ U.vertices)
    (hU : ¬ U.scale ≤ Q.scale + 1) {u v x : Vertex 2} (hu : u ∈ (Q.window U).vertices)
    (hv : v ∈ U.vertices) (hvw : v ∉ (Q.window U).vertices) (huv : ∀ i, |v i - u i| ≤ 1)
    (hx : x ∈ Q.vertices) :
    ∃ k, x k + 2 * 3 ^ Q.scale ≤ u k ∨ u k + 2 * 3 ^ Q.scale ≤ x k := by
  rw [IntegerCube.mem_vertices, (TriadicCube.window_of_not_le hU).2] at hu hvw
  push Not at hvw
  obtain ⟨k, hk⟩ := hvw
  refine ⟨k, ?_⟩
  have huk := hu k
  have hvk := TriadicCube.corner_le_of_mem hv k
  have hxk := TriadicCube.corner_le_of_mem hx k
  have hf := TriadicCube.window_corner_facts hsub hU k
  have hadj := huv k
  rw [abs_le] at hadj
  omega

/-- **Local connection inside a window.** A vertex of a meshed cube `Q` of side at least `1000`
inside a triadic cube `U`, joined inside `U` to the anchor of `Q`, is joined to it inside the
window. -/
theorem TriadicCube.reachIn_window_of_reachIn {Q U : TriadicCube 2} (hQ : Q.planarMeshed ω)
    (hs : 1000 ≤ 3 ^ Q.scale) (hsc : Q.scale ≤ U.scale) (hsub : Q.vertices ⊆ U.vertices)
    {x : Vertex 2} (hx : x ∈ Q.vertices) (h : ReachIn ω U.vertices x (Q.planarAnchor ω)) :
    ReachIn ω ↑(Q.window U).vertices (Q.planarAnchor ω) x := by
  by_cases hU : U.scale ≤ Q.scale + 1
  · have hw : Q.window U = U.toIntegerCube := by
      unfold TriadicCube.window
      rw [if_pos hU]
    rw [hw, U.coe_toIntegerCube_vertices]
    exact h.symm
  set S : Set (Vertex 2) := ↑(Q.window U).vertices with hS
  have hxS : x ∈ S := Q.subset_window hsub hx
  obtain ⟨W, hW⟩ := h
  by_cases hall : ∀ z ∈ W.support, z ∈ S
  · exact ReachIn.symm (show ReachIn ω S x (Q.planarAnchor ω) from ⟨W, hall⟩)
  push Not at hall
  obtain ⟨z, hzW, hzS⟩ := hall
  obtain ⟨u, v, hxu, huv, hvS, hvW⟩ :=
    exists_exit_of_walk_mem_support hxS hzS (W.takeUntil z hzW)
  have hvU : v ∈ U.vertices := hW v (W.support_takeUntil_subset_support hzW hvW)
  have huS : u ∈ (Q.window U).vertices := Finset.mem_coe.1 hxu.end_mem
  have hadj : ∀ i, |v i - u i| ≤ 1 := fun i =>
    Rigidity.Proofs.S3.abs_coord_sub_le_one_of_adj (openGraph_le ω huv) i
  obtain ⟨k, hk⟩ := Q.window_exit hsub hU huS hvU hvS hadj hx
  have hw100 : 100 * ((3 ^ Q.scale / 100 : ℕ) : ℤ) ≤ 3 ^ Q.scale := by
    have := Nat.mul_div_le (3 ^ Q.scale) 100
    have hc : ((3 ^ Q.scale : ℕ) : ℤ) = 3 ^ Q.scale := by push_cast; rfl
    omega
  have hpos : (1 : ℤ) ≤ 3 ^ Q.scale := one_le_pow₀ (by norm_num)
  have hlong : ((3 ^ Q.scale / 100 : ℕ) : ℤ) ≤ |x k - u k| := by
    rcases hk with hk | hk
    · rw [abs_sub_comm, abs_of_nonneg (by omega)]
      omega
    · rw [abs_of_nonneg (by omega)]
      omega
  exact Q.reachIn_planarAnchor_of_long hQ hs (Q.window_mem_planarSquares hsc hsub)
    (Q.subset_window hsub) hxu hlong

/-- The square of side `4s` inside `U` containing two adjacent cubes `Q` and `Q'`, or `U` itself
when `U` has scale at most one more than `Q`. -/
def TriadicCube.pairWindow (Q Q' U : TriadicCube 2) : IntegerCube 2 :=
  if U.scale ≤ Q.scale + 1 then U.toIntegerCube else
    ⟨fun i => min (min (Q.toIntegerCube.corner i) (Q'.toIntegerCube.corner i))
      (U.toIntegerCube.corner i + 3 ^ U.scale - 4 * 3 ^ Q.scale), 4 * 3 ^ Q.scale⟩

/-- Coordinates of two adjacent cubes, the second of the same or the next scale. -/
theorem TriadicCube.corner_bounds_of_near {Q Q' : TriadicCube 2} (hscale : Q.scale ≤ Q'.scale)
    (hscale' : Q'.scale ≤ Q.scale + 1) {x y : Vertex 2} (hx : x ∈ Q.vertices)
    (hy : y ∈ Q'.vertices) (hnear : ∀ i, |x i - y i| ≤ 1) (i : Fin 2) :
    Q'.toIntegerCube.corner i ≤ Q.toIntegerCube.corner i + 3 ^ Q.scale ∧
      Q.toIntegerCube.corner i ≤ Q'.toIntegerCube.corner i + 3 ^ Q'.scale ∧
      (3 : ℤ) ^ Q.scale ≤ 3 ^ Q'.scale ∧ (3 : ℤ) ^ Q'.scale ≤ 3 * 3 ^ Q.scale := by
  have hx' := TriadicCube.corner_le_of_mem hx i
  have hy' := TriadicCube.corner_le_of_mem hy i
  have h := hnear i
  rw [abs_le] at h
  refine ⟨by omega, by omega, pow_le_pow_right₀ (by norm_num) hscale,
    three_pow_le_three_mul_of_le hscale'⟩

theorem TriadicCube.pairWindow_of_not_le {Q Q' U : TriadicCube 2}
    (hU : ¬ U.scale ≤ Q.scale + 1) :
    (Q.pairWindow Q' U).corner = (fun i => min (min (Q.toIntegerCube.corner i)
      (Q'.toIntegerCube.corner i)) (U.toIntegerCube.corner i + 3 ^ U.scale - 4 * 3 ^ Q.scale)) ∧
    (((Q.pairWindow Q' U).size : ℕ) : ℤ) = 4 * 3 ^ Q.scale := by
  unfold TriadicCube.pairWindow
  rw [if_neg hU]
  refine ⟨rfl, ?_⟩
  change ((4 * 3 ^ Q.scale : ℕ) : ℤ) = _
  push_cast
  ring

/-- The pair window of two adjacent cubes inside `U` is a surrounding square of the first cube
containing both cubes and contained in `U`. -/
theorem TriadicCube.pairWindow_spec {Q Q' U : TriadicCube 2} (hsc : Q.scale ≤ U.scale)
    (hsub : Q.vertices ⊆ U.vertices) (hsub' : Q'.vertices ⊆ U.vertices)
    (hscale : Q.scale ≤ Q'.scale) (hscale' : Q'.scale ≤ Q.scale + 1) {x y : Vertex 2}
    (hx : x ∈ Q.vertices) (hy : y ∈ Q'.vertices) (hnear : ∀ i, |x i - y i| ≤ 1) :
    Q.pairWindow Q' U ∈ Q.planarSquares ∧ Q.vertices ⊆ ↑(Q.pairWindow Q' U).vertices ∧
      Q'.vertices ⊆ ↑(Q.pairWindow Q' U).vertices ∧
      ↑(Q.pairWindow Q' U).vertices ⊆ U.vertices := by
  by_cases hU : U.scale ≤ Q.scale + 1
  · have hw : Q.pairWindow Q' U = U.toIntegerCube := by
      unfold TriadicCube.pairWindow
      rw [if_pos hU]
    rw [hw, U.coe_toIntegerCube_vertices, ← TriadicCube.window_of_le hU]
    exact ⟨Q.window_mem_planarSquares hsc hsub, hsub, hsub', le_rfl⟩
  have hlt := nine_mul_three_pow_le_of_lt hU
  have hr := Q.two_mul_ninefoldRadius
  obtain ⟨hcor, hsize⟩ := TriadicCube.pairWindow_of_not_le (Q' := Q') hU
  have hfacts : ∀ i, U.toIntegerCube.corner i ≤ (Q.pairWindow Q' U).corner i ∧
      (Q.pairWindow Q' U).corner i + 4 * 3 ^ Q.scale ≤ U.toIntegerCube.corner i + 3 ^ U.scale ∧
      Q.toIntegerCube.corner i - 3 * 3 ^ Q.scale ≤ (Q.pairWindow Q' U).corner i ∧
      (Q.pairWindow Q' U).corner i ≤ Q.toIntegerCube.corner i ∧
      (Q.pairWindow Q' U).corner i ≤ Q'.toIntegerCube.corner i ∧
      Q.toIntegerCube.corner i + 3 ^ Q.scale ≤ (Q.pairWindow Q' U).corner i + 4 * 3 ^ Q.scale ∧
      Q'.toIntegerCube.corner i + 3 ^ Q'.scale ≤
        (Q.pairWindow Q' U).corner i + 4 * 3 ^ Q.scale := by
    intro i
    have hb := TriadicCube.corner_bounds_of_subset hsub i
    have hb' := TriadicCube.corner_bounds_of_subset hsub' i
    have hn := TriadicCube.corner_bounds_of_near hscale hscale' hx hy hnear i
    rw [hcor]
    exact clamp_pairWindow_facts hn.2.2.1 hn.2.2.2 hlt hb.1 hb'.1 hb.2 hb'.2 hn.1 hn.2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [TriadicCube.mem_planarSquares]
    have hsizeN : (Q.pairWindow Q' U).size = 4 * 3 ^ Q.scale := by exact_mod_cast hsize
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
    rw [Finset.mem_coe, IntegerCube.mem_vertices, hsize] at hz
    apply TriadicCube.mem_of_corner_le
    intro i
    have hzi := hz i
    have hf := hfacts i
    constructor <;> omega

/-- **Adjacent anchors inside a triadic cube.** The anchors of two adjacent meshed cubes inside
`U`, the second of the same or the next scale, are joined inside their pair window. -/
theorem TriadicCube.reachIn_planarAnchor_pairWindow {Q Q' U : TriadicCube 2}
    (hQ : Q.planarMeshed ω) (hQ' : Q'.planarMeshed ω) (hs : 1000 ≤ 3 ^ Q.scale)
    (hsc : Q.scale ≤ U.scale) (hsub : Q.vertices ⊆ U.vertices)
    (hsub' : Q'.vertices ⊆ U.vertices) (hscale : Q.scale ≤ Q'.scale)
    (hscale' : Q'.scale ≤ Q.scale + 1) {x y : Vertex 2} (hx : x ∈ Q.vertices)
    (hy : y ∈ Q'.vertices) (hnear : ∀ i, |x i - y i| ≤ 1) :
    ReachIn ω ↑(Q.pairWindow Q' U).vertices (Q.planarAnchor ω) (Q'.planarAnchor ω) := by
  obtain ⟨hR, hQR, hQ'R, -⟩ := Q.pairWindow_spec hsc hsub hsub' hscale hscale' hx hy hnear
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
