import Rigidity.Proofs.Percolation.PlanarGoodCubes

/-!
# Local connectivity at the scale of meshed planar cubes

Let `Q` be a meshed triadic cube of side `s ≥ 1000`. The hub of the mesh of `Q` is an anchor
`a ∈ Q`: inside `Q` it is joined to every open walk of `Q` whose endpoints differ by at least
`⌊s/100⌋` in some coordinate, and the same holds inside the square of side `9s` around `Q`. Hence
every vertex of `Q` in an infinite open cluster is joined to the anchor inside the square of side
`9s`, and the anchors of two adjacent meshed cubes, the second at most three times larger than the
first, are joined inside the square of side `9s` around the first.
-/

open LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5

namespace Rigidity.Percolation

variable {ω : Configuration 2}

/-- The square of side `9s` around a triadic cube of side `s`. -/
def TriadicCube.ninefold (Q : TriadicCube 2) : IntegerCube 2 :=
  ⟨fun i => Q.center i - Q.ninefoldRadius, 9 * 3 ^ Q.scale⟩

theorem TriadicCube.two_mul_ninefoldRadius (Q : TriadicCube 2) :
    2 * Q.ninefoldRadius + 1 = 9 * 3 ^ Q.scale := by
  have ho : (9 * 3 ^ Q.scale : ℤ) % 2 = 1 := by
    have : Odd ((9 : ℤ) * 3 ^ Q.scale) :=
      (show Odd (9 : ℤ) from ⟨4, by norm_num⟩).mul
        ((show Odd (3 : ℤ) from ⟨1, by norm_num⟩).pow)
    exact Int.odd_iff.mp this
  unfold TriadicCube.ninefoldRadius
  omega

theorem TriadicCube.mem_ninefold {Q : TriadicCube 2} {x : Vertex 2} :
    x ∈ (↑Q.ninefold.vertices : Set (Vertex 2)) ↔
      ∀ i, |x i - Q.center i| ≤ Q.ninefoldRadius := by
  have h := Q.two_mul_ninefoldRadius
  rw [Finset.mem_coe, IntegerCube.mem_vertices]
  refine forall_congr' fun i => ?_
  change Q.center i - Q.ninefoldRadius ≤ x i ∧
    x i < Q.center i - Q.ninefoldRadius + ((9 * 3 ^ Q.scale : ℕ) : ℤ) ↔ _
  push_cast
  rw [abs_le]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> omega

theorem TriadicCube.ninefold_mem_planarSquares (Q : TriadicCube 2) :
    Q.ninefold ∈ Q.planarSquares := by
  have h := Q.two_mul_ninefoldRadius
  rw [TriadicCube.mem_planarSquares]
  refine ⟨by change 3 ^ Q.scale ≤ 9 * 3 ^ Q.scale; omega, le_rfl, fun i => ⟨le_rfl, ?_⟩⟩
  change Q.center i - Q.ninefoldRadius + ((9 * 3 ^ Q.scale : ℕ) : ℤ) ≤ _
  push_cast
  omega

/-- A vertex of a triadic cube lies within `(s-1)/2` of its centre in each coordinate. -/
theorem TriadicCube.abs_sub_center_le {Q : TriadicCube 2} {x : Vertex 2} (hx : x ∈ Q.vertices)
    (i : Fin 2) : 2 * |x i - Q.center i| + 1 ≤ 3 ^ Q.scale := by
  have h := hx i
  have hs : Q.side = 3 ^ Q.scale := rfl
  change |2 * (x i - Q.side * Q.index i)| < Q.side at h
  change 2 * |x i - Q.side * Q.index i| + 1 ≤ 3 ^ Q.scale
  rw [abs_mul, abs_two] at h
  have ho : Q.side % 2 = 1 := by
    have : Odd Q.side := by
      rw [hs]; exact (show Odd (3 : ℤ) from ⟨1, by norm_num⟩).pow
    exact Int.odd_iff.mp this
  omega

theorem TriadicCube.toIntegerCube_mem_planarSquares (Q : TriadicCube 2) :
    Q.toIntegerCube ∈ Q.planarSquares := by
  have h := Q.two_mul_ninefoldRadius
  have hs : Q.side = 3 ^ Q.scale := rfl
  have ho : Q.side % 2 = 1 := by
    have : Odd Q.side := by
      rw [hs]; exact (show Odd (3 : ℤ) from ⟨1, by norm_num⟩).pow
    exact Int.odd_iff.mp this
  have hpos : (1 : ℤ) ≤ 3 ^ Q.scale := one_le_pow₀ (by norm_num)
  rw [TriadicCube.mem_planarSquares]
  refine ⟨le_rfl, by change 3 ^ Q.scale ≤ 9 * 3 ^ Q.scale; omega, fun i => ?_⟩
  change Q.center i - Q.ninefoldRadius ≤ Q.side * Q.index i - Q.side / 2 ∧
    Q.side * Q.index i - Q.side / 2 + ((3 ^ Q.scale : ℕ) : ℤ) ≤ Q.center i + Q.ninefoldRadius + 1
  have hc : Q.center i = Q.side * Q.index i := rfl
  push_cast
  rw [hc]
  constructor <;> omega

/-- An open walk from inside a region to outside it leaves the region along an open edge from a
vertex joined to its start inside the region. -/
theorem exists_reachIn_exit_of_walk {S : Set (Vertex 2)} {x y : Vertex 2} (hx : x ∈ S) (hy : y ∉ S)
    (W : (openGraph ω).Walk x y) :
    ∃ u v, ReachIn ω S x u ∧ (openGraph ω).Adj u v ∧ v ∉ S := by
  induction W with
  | nil => exact absurd hx hy
  | @cons a b c hab W ih =>
    by_cases hb : b ∈ S
    · obtain ⟨u, v, hu, huv, hv⟩ := ih hb hy
      refine ⟨u, v, ?_, huv, hv⟩
      obtain ⟨P, hP⟩ := hu
      refine ⟨SimpleGraph.Walk.cons hab P, fun z hz => ?_⟩
      rcases List.mem_cons.1 hz with rfl | hz
      exacts [hx, hP z hz]
    · exact ⟨a, b, ⟨SimpleGraph.Walk.nil, fun z hz => by
        simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
        exact hz ▸ hx⟩, hab, hb⟩

/-- **The anchor of a meshed cube.** -/
theorem TriadicCube.exists_planar_anchor {Q : TriadicCube 2} (hQ : Q.planarMeshed ω)
    (hs : 1000 ≤ 3 ^ Q.scale) :
    ∃ a ∈ Q.vertices,
      (∀ (c d : Vertex 2) (k : Fin 2), ReachIn ω Q.vertices c d →
        c k + ((3 ^ Q.scale / 100 : ℕ) : ℤ) ≤ d k → ReachIn ω Q.vertices a c) ∧
      (∀ (c d : Vertex 2) (k : Fin 2), ReachIn ω ↑Q.ninefold.vertices c d →
        c k + ((3 ^ Q.scale / 100 : ℕ) : ℤ) ≤ d k → ReachIn ω ↑Q.ninefold.vertices a c) := by
  set w := 3 ^ Q.scale / 100 with hwdef
  have hQm := hQ _ Q.toIntegerCube_mem_planarSquares
  have hNm := hQ _ Q.ninefold_mem_planarSquares
  have hwQ : w + 1 ≤ Q.toIntegerCube.size := by change w + 1 ≤ 3 ^ Q.scale; omega
  have hwN : w + 1 ≤ Q.ninefold.size := by change w + 1 ≤ 9 * 3 ^ Q.scale; omega
  obtain ⟨a, haQ, habs, hfaces⟩ := hQm.exists_hub hwQ
  obtain ⟨b, -, hbabs, -⟩ := hNm.exists_hub hwN
  have hQset := Q.coe_toIntegerCube_vertices
  have hQsub : (↑Q.toIntegerCube.vertices : Set (Vertex 2)) ⊆ ↑Q.ninefold.vertices := by
    intro x hx
    rw [hQset] at hx
    rw [TriadicCube.mem_ninefold]
    intro i
    have h1 := Q.abs_sub_center_le hx i
    have h2 := Q.two_mul_ninefoldRadius
    have hpos : (1 : ℤ) ≤ 3 ^ Q.scale := one_le_pow₀ (by norm_num)
    omega
  -- the hub of `Q` is joined to the hub of the large square
  obtain ⟨⟨yl, hyl, hylf, hayl⟩, ⟨yu, hyu, hyuf, hayu⟩⟩ := hfaces 0
  have hyl0 := (IntegerCube.mem_lowerFace_coe.1 hylf).2
  have hyu0 := (IntegerCube.mem_upperFace_coe.1 hyuf).2
  have hcross : ReachIn ω ↑Q.ninefold.vertices yl yu := ((hayl.symm.trans hayu).mono hQsub)
  have hdisp : yl 0 + (w : ℤ) ≤ yu 0 := by
    have : (Q.toIntegerCube.size : ℤ) = 3 ^ Q.scale := by
      change ((3 ^ Q.scale : ℕ) : ℤ) = _; push_cast; ring
    have hw100 : 100 * (w : ℤ) ≤ 3 ^ Q.scale := by
      have := Nat.mul_div_le (3 ^ Q.scale) 100
      have h' : ((100 * w : ℕ) : ℤ) ≤ ((3 ^ Q.scale : ℕ) : ℤ) := by exact_mod_cast this
      push_cast at h'
      linarith
    omega
  have hba : ReachIn ω ↑Q.ninefold.vertices b a :=
    (hbabs yl yu 0 hcross hdisp).trans (hayl.mono hQsub).symm
  refine ⟨a, hQset ▸ haQ, fun c d k hcd hk => ?_, fun c d k hcd hk => ?_⟩
  · rw [← hQset] at hcd ⊢
    exact habs c d k hcd hk
  · exact hba.symm.trans (hbabs c d k hcd hk)

/-- Any open walk in the large square from a vertex of `Q` to a vertex at distance at least
`⌊s/100⌋` in some coordinate is joined to the anchor; in particular so is every vertex of `Q` in an
infinite open cluster. -/
theorem TriadicCube.reachIn_anchor_of_infinite {Q : TriadicCube 2} {a : Vertex 2}
    (habs : ∀ (c d : Vertex 2) (k : Fin 2), ReachIn ω ↑Q.ninefold.vertices c d →
        c k + ((3 ^ Q.scale / 100 : ℕ) : ℤ) ≤ d k → ReachIn ω ↑Q.ninefold.vertices a c)
    {x : Vertex 2} (hx : x ∈ Q.vertices)
    (hinf : ((openGraph ω).connectedComponentMk x).supp.Infinite) :
    ReachIn ω ↑Q.ninefold.vertices a x := by
  set N := (↑Q.ninefold.vertices : Set (Vertex 2))
  have hxN : x ∈ N := by
    rw [TriadicCube.mem_ninefold]
    intro i
    have h1 := Q.abs_sub_center_le hx i
    have h2 := Q.two_mul_ninefoldRadius
    have hpos : (1 : ℤ) ≤ 3 ^ Q.scale := one_le_pow₀ (by norm_num)
    omega
  have hNfin : N.Finite := Q.ninefold.vertices.finite_toSet
  obtain ⟨y, hy, hyN⟩ := (hinf.sdiff hNfin).nonempty
  have hr : (openGraph ω).Reachable x y :=
    (SimpleGraph.ConnectedComponent.eq.mp
      ((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp hy)).symm
  obtain ⟨W⟩ := hr
  obtain ⟨u, v, hxu, huv, hv⟩ := exists_reachIn_exit_of_walk hxN hyN W
  have huN : u ∈ N := hxu.end_mem
  rw [TriadicCube.mem_ninefold] at huN hv
  push Not at hv
  obtain ⟨k, hk⟩ := hv
  have hadj := Rigidity.Proofs.S3.abs_coord_sub_le_one_of_adj (openGraph_le ω huv) k
  have hu := huN k
  have hxk := Q.abs_sub_center_le hx k
  have h2 := Q.two_mul_ninefoldRadius
  have hw100 : 100 * ((3 ^ Q.scale / 100 : ℕ) : ℤ) ≤ 3 ^ Q.scale := by
    have := Nat.mul_div_le (3 ^ Q.scale) 100
    have hc : ((3 ^ Q.scale : ℕ) : ℤ) = 3 ^ Q.scale := by push_cast; rfl
    omega
  rw [abs_le] at hu hadj
  have h3 := le_abs_self (x k - Q.center k)
  have h4 := neg_abs_le (x k - Q.center k)
  rcases lt_abs.mp hk with hvk | hvk
  · exact habs x u k hxu (by omega)
  · exact (habs u x k hxu.symm (by omega)).trans hxu.symm

/-- The anchor property of a vertex of a triadic cube: inside the cube and inside the square of
side `9s` around it, the vertex is joined to every open walk whose endpoints differ by at least
`⌊s/100⌋` in some coordinate. -/
def TriadicCube.IsPlanarAnchor (ω : Configuration 2) (Q : TriadicCube 2) (a : Vertex 2) : Prop :=
  a ∈ Q.vertices ∧
    (∀ (c d : Vertex 2) (k : Fin 2), ReachIn ω Q.vertices c d →
      c k + ((3 ^ Q.scale / 100 : ℕ) : ℤ) ≤ d k → ReachIn ω Q.vertices a c) ∧
    (∀ (c d : Vertex 2) (k : Fin 2), ReachIn ω ↑Q.ninefold.vertices c d →
      c k + ((3 ^ Q.scale / 100 : ℕ) : ℤ) ≤ d k → ReachIn ω ↑Q.ninefold.vertices a c)

open Classical in
/-- The anchor of a triadic cube: for a meshed cube of side at least `1000`, a vertex given by
`exists_planar_anchor`, and its centre otherwise. The vertex is chosen through its displacement
from the centre, so that anchors move with translations. -/
noncomputable def TriadicCube.planarAnchor (ω : Configuration 2) (Q : TriadicCube 2) : Vertex 2 :=
  if Q.planarMeshed ω ∧ 1000 ≤ 3 ^ Q.scale then
    Q.center + Classical.epsilon fun e => Q.IsPlanarAnchor ω (Q.center + e)
  else Q.center

theorem TriadicCube.planarAnchor_spec {Q : TriadicCube 2} (hQ : Q.planarMeshed ω)
    (hs : 1000 ≤ 3 ^ Q.scale) :
    Q.planarAnchor ω ∈ Q.vertices ∧
      (∀ (c d : Vertex 2) (k : Fin 2), ReachIn ω Q.vertices c d →
        c k + ((3 ^ Q.scale / 100 : ℕ) : ℤ) ≤ d k → ReachIn ω Q.vertices (Q.planarAnchor ω) c) ∧
      (∀ (c d : Vertex 2) (k : Fin 2), ReachIn ω ↑Q.ninefold.vertices c d →
        c k + ((3 ^ Q.scale / 100 : ℕ) : ℤ) ≤ d k →
          ReachIn ω ↑Q.ninefold.vertices (Q.planarAnchor ω) c) := by
  have h : Q.planarMeshed ω ∧ 1000 ≤ 3 ^ Q.scale := ⟨hQ, hs⟩
  obtain ⟨a, ha, hspec⟩ := Q.exists_planar_anchor hQ hs
  have hex : ∃ e, Q.IsPlanarAnchor ω (Q.center + e) :=
    ⟨a - Q.center, by rw [add_sub_cancel]; exact ⟨ha, hspec⟩⟩
  unfold TriadicCube.planarAnchor
  rw [if_pos h]
  exact Classical.epsilon_spec hex

/-- **Adjacent anchors.** If a meshed cube `Q'` touches a meshed cube `Q` and has the same or the
next scale, their anchors are joined inside the square of side `9s` around `Q`. -/
theorem TriadicCube.reachIn_planarAnchor_of_near {Q Q' : TriadicCube 2} (hQ : Q.planarMeshed ω)
    (hQ' : Q'.planarMeshed ω) (hs : 1000 ≤ 3 ^ Q.scale) (hscale : Q.scale ≤ Q'.scale)
    (hscale' : Q'.scale ≤ Q.scale + 1) {x y : Vertex 2} (hx : x ∈ Q.vertices)
    (hy : y ∈ Q'.vertices) (hnear : ∀ i, |x i - y i| ≤ 1) :
    ReachIn ω ↑Q.ninefold.vertices (Q.planarAnchor ω) (Q'.planarAnchor ω) := by
  have hs' : 1000 ≤ 3 ^ Q'.scale :=
    hs.trans (Nat.pow_le_pow_right (by norm_num) hscale)
  obtain ⟨-, -, hB⟩ := Q.planarAnchor_spec hQ hs
  obtain ⟨-, hA', -⟩ := Q'.planarAnchor_spec hQ' hs'
  have hpow : 3 ^ Q'.scale ≤ 3 * 3 ^ Q.scale := by
    calc 3 ^ Q'.scale ≤ 3 ^ (Q.scale + 1) := Nat.pow_le_pow_right (by norm_num) hscale'
      _ = 3 * 3 ^ Q.scale := by ring
  have hpow' : 3 ^ Q.scale ≤ 3 ^ Q'.scale := Nat.pow_le_pow_right (by norm_num) hscale
  have hc : ((3 ^ Q.scale : ℕ) : ℤ) = 3 ^ Q.scale := by push_cast; rfl
  have hc' : ((3 ^ Q'.scale : ℕ) : ℤ) = 3 ^ Q'.scale := by push_cast; rfl
  have hpowZ : (3 : ℤ) ^ Q'.scale ≤ 3 * 3 ^ Q.scale := by
    have := (Nat.cast_le (α := ℤ)).2 hpow
    push_cast at this
    exact this
  have hpos : (1 : ℤ) ≤ 3 ^ Q.scale := one_le_pow₀ (by norm_num)
  have h2 := Q.two_mul_ninefoldRadius
  -- the cube `Q'` lies in the square of side `9s` around `Q`
  have hsub : Q'.vertices ⊆ ↑Q.ninefold.vertices := by
    intro z hz
    rw [TriadicCube.mem_ninefold]
    intro i
    have h1 := Q.abs_sub_center_le hx i
    have h3 := Q'.abs_sub_center_le hz i
    have h4 := Q'.abs_sub_center_le hy i
    have h5 := hnear i
    have h6 := abs_sub_le (z i) (Q'.center i) (y i)
    have h7 := abs_sub_le (z i) (y i) (x i)
    have h8 := abs_sub_le (z i) (x i) (Q.center i)
    rw [abs_sub_comm (Q'.center i) (y i)] at h6
    rw [abs_sub_comm (y i) (x i)] at h7
    omega
  have hmem : Q'.toIntegerCube ∈ Q.planarSquares := by
    rw [TriadicCube.mem_planarSquares]
    refine ⟨hpow', by change 3 ^ Q'.scale ≤ 9 * 3 ^ Q.scale; omega, fun i => ?_⟩
    have hsz : (Q'.toIntegerCube.size : ℤ) = 3 ^ Q'.scale := by
      change ((3 ^ Q'.scale : ℕ) : ℤ) = _; push_cast; rfl
    -- the two extreme vertices of `Q'` in coordinate `i` lie in the large square
    have hlow : (fun j => if j = i then Q'.toIntegerCube.corner i else y j) ∈ Q'.vertices := by
      rw [← Q'.coe_toIntegerCube_vertices, Finset.mem_coe, IntegerCube.mem_vertices]
      intro j
      by_cases hj : j = i
      · subst hj
        simp only [if_true]
        rw [hsz]
        have hpos' : (1 : ℤ) ≤ 3 ^ Q'.scale := one_le_pow₀ (by norm_num)
        constructor <;> omega
      · simp only [hj, if_false]
        have := (IntegerCube.mem_vertices _ y).1
          ((Q'.mem_toIntegerCube_vertices y).2 hy) j
        exact this
    have hhigh : (fun j => if j = i then Q'.toIntegerCube.corner i + 3 ^ Q'.scale - 1
        else y j) ∈ Q'.vertices := by
      rw [← Q'.coe_toIntegerCube_vertices, Finset.mem_coe, IntegerCube.mem_vertices]
      intro j
      by_cases hj : j = i
      · subst hj
        simp only [if_true]
        rw [hsz]
        have hpos' : (1 : ℤ) ≤ 3 ^ Q'.scale := one_le_pow₀ (by norm_num)
        constructor <;> omega
      · simp only [hj, if_false]
        exact (IntegerCube.mem_vertices _ y).1 ((Q'.mem_toIntegerCube_vertices y).2 hy) j
    have hl := (TriadicCube.mem_ninefold.1 (hsub hlow)) i
    have hh := (TriadicCube.mem_ninefold.1 (hsub hhigh)) i
    simp only [if_true] at hl hh
    rw [abs_le] at hl hh
    rw [hsz]
    constructor <;> omega
  have hmesh := hQ _ hmem
  set w := 3 ^ Q.scale / 100 with hwdef
  have hwsize : w + 1 ≤ Q'.toIntegerCube.size := by
    change w + 1 ≤ 3 ^ Q'.scale; omega
  obtain ⟨hub, -, -, hfaces⟩ := hmesh.exists_hub hwsize
  obtain ⟨⟨yl, hyl, hylf, hhl⟩, ⟨yu, hyu, hyuf, hhu⟩⟩ := hfaces 0
  have hyl0 := (IntegerCube.mem_lowerFace_coe.1 hylf).2
  have hyu0 := (IntegerCube.mem_upperFace_coe.1 hyuf).2
  have hQ'set := Q'.coe_toIntegerCube_vertices
  have hcross : ReachIn ω Q'.vertices yl yu := hQ'set ▸ (hhl.symm.trans hhu)
  have hsz : (Q'.toIntegerCube.size : ℤ) = 3 ^ Q'.scale := by
    change ((3 ^ Q'.scale : ℕ) : ℤ) = _; push_cast; rfl
  have hw100 : 100 * (w : ℤ) ≤ 3 ^ Q.scale := by
    have := Nat.mul_div_le (3 ^ Q.scale) 100
    omega
  have hw' : 100 * ((3 ^ Q'.scale / 100 : ℕ) : ℤ) ≤ 3 ^ Q'.scale := by
    have := Nat.mul_div_le (3 ^ Q'.scale) 100
    omega
  have hd1 : yl 0 + ((3 ^ Q'.scale / 100 : ℕ) : ℤ) ≤ yu 0 := by omega
  have hd2 : yl 0 + (w : ℤ) ≤ yu 0 := by omega
  have ha'yl := hA' yl yu 0 hcross hd1
  have hayl := hB yl yu 0 (hcross.mono hsub) hd2
  exact hayl.trans (ha'yl.mono hsub).symm

end Rigidity.Percolation
