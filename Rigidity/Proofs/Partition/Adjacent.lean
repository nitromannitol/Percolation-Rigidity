import Rigidity.Proofs.Partition.CrossingCluster

/-!
# Joined clusters of adjacent good cubes

Armstrong and Dario, Lemma 2.8: two good triadic cubes of comparable sizes at distance one have
crossing clusters joined by open paths inside their union.

Let `A` be a well-connected triadic cube of side `s = 3ⁿ`, `n ≥ 3`, and `B` the cube of the same
scale following it in direction `k`. The test cube of `A` of side `(s - 1) / 2`, reaching
`⌊s / 5⌋` into `A` across the common face, is crossable in direction `k`; the crossing path first
reaches the common face after a displacement `⌊s / 5⌋` inside `A`, and last leaves it before a
displacement `(s - 1) / 2 - ⌊s / 5⌋ - 2` inside `B`. Both are at least `s / 10`, so the two ends of
the crossing path lie in the components of the roots of `A` and `B`.

Here the good cubes are the cubes whose children are well-connected relative to their rounded
three-quarter cubes and of scale at least two; they have scale at least three. This lower bound
is a departure from Armstrong and Dario, who allow good cubes of side three, for which the
statement fails.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation Rigidity.External

variable {d : ℕ}

/-- The triadic cube of the same scale following `Q` in direction `k`. -/
def TriadicCube.neighbor (Q : TriadicCube d) (k : Fin d) : TriadicCube d :=
  ⟨Q.scale, Q.index + Pi.single k 1⟩

theorem TriadicCube.neighbor_scale (Q : TriadicCube d) (k : Fin d) :
    (Q.neighbor k).scale = Q.scale := rfl

theorem TriadicCube.neighbor_side (Q : TriadicCube d) (k : Fin d) :
    (Q.neighbor k).side = Q.side := rfl

theorem TriadicCube.neighbor_radius (Q : TriadicCube d) (k : Fin d) :
    (Q.neighbor k).radius = Q.radius := rfl

theorem TriadicCube.neighbor_center (Q : TriadicCube d) (k i : Fin d) :
    (Q.neighbor k).center i = Q.center i + if i = k then Q.side else 0 := by
  change Q.side * (Q.index i + (Pi.single k (1 : ℤ) : Fin d → ℤ) i) = Q.side * Q.index i + _
  rw [Pi.single_apply]
  split_ifs <;> ring

/-- **Adjacent well-connected cubes of the same scale.** For a well-connected cube of scale at
least three and the well-connected cube following it in some direction, the roots are joined
inside the union of the two cubes. -/
theorem TriadicCube.IsWellConnectedRoot.reachable_neighbor {ω : Configuration d}
    {A : TriadicCube d} {k : Fin d} {rA rB : Vertex d} (hA : A.IsWellConnectedRoot ω rA)
    (hB : (A.neighbor k).IsWellConnectedRoot ω rB) (hs : 3 ≤ A.scale) :
    (openIn ω (A.vertices ∪ (A.neighbor k).vertices)).Reachable rA rB := by
  set N : ℕ := 3 ^ A.scale
  have hNdef : N = 3 ^ A.scale := rfl
  have hN : (N : ℤ) = A.side := A.natCast_three_pow_scale
  have hN27 : 27 ≤ N := by
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ A.scale := Nat.pow_le_pow_right (by norm_num) hs
  have hsr := A.side_eq_two_mul_radius_add_one
  set a : ℤ := A.side / 5 with hadef
  -- the test cube across the common face
  let c : Vertex d := fun i =>
    if i = k then A.center k + A.radius - a else A.center i - A.radius
  let R : IntegerCube d := ⟨c, N / 2⟩
  have hL : ((N / 2 : ℕ) : ℤ) = A.radius := by omega
  have hmemR (y : Vertex d) : y ∈ R.vertices ↔ ∀ j, c j ≤ y j ∧ y j < c j + A.radius := by
    rw [IntegerCube.mem_vertices]
    change (∀ j, c j ≤ y j ∧ y j < c j + ((N / 2 : ℕ) : ℤ)) ↔ _
    rw [hL]
  have hck : c k = A.center k + A.radius - a := if_pos rfl
  have hcj (j : Fin d) (hj : j ≠ k) : c j = A.center j - A.radius := if_neg hj
  have hR : R ∈ A.testCubes A.threeQuarterCube.vertices := by
    refine ⟨by change A.side ≤ 10 * ((N / 2 : ℕ) : ℤ); omega,
      by change 2 * ((N / 2 : ℕ) : ℤ) ≤ A.side; omega, ?_⟩
    set K : ℕ := 3 * 3 ^ A.scale / 4 with hKdef
    have hK : (K : ℤ) = 3 * A.side / 4 := by rw [hKdef]; omega
    refine ⟨fun j => max (c j) (A.center j - (K : ℤ) / 2), ?_, ?_⟩
    · rw [hmemR]
      intro j
      refine ⟨le_max_left _ _, max_lt (by omega) ?_⟩
      rcases eq_or_ne j k with rfl | hj
      · rw [hck]; omega
      · rw [hcj j hj]; omega
    · rw [Finset.mem_coe, IntegerCube.mem_vertices]
      intro j
      change A.center j - (K : ℤ) / 2 ≤ max (c j) (A.center j - (K : ℤ) / 2) ∧
        max (c j) (A.center j - (K : ℤ) / 2) < A.center j - (K : ℤ) / 2 + (K : ℤ)
      refine ⟨le_max_right _ _, max_lt ?_ (by omega)⟩
      rcases eq_or_ne j k with rfl | hj
      · rw [hck]; omega
      · rw [hcj j hj]; omega
  have hcenter (j : Fin d) (hj : j ≠ k) : (A.neighbor k).center j = A.center j := by
    rw [A.neighbor_center, if_neg hj, add_zero]
  have hcenterk : (A.neighbor k).center k = A.center k + A.side := by
    rw [A.neighbor_center, if_pos rfl]
  -- the two halves of the test cube
  set f : ℤ := A.center k + A.radius with hfdef
  have hlow : (↑R.vertices : Set (Vertex d)) ∩ {z | z k ≤ f} ⊆ A.vertices := by
    rintro z ⟨hz, hzf⟩
    rw [Finset.mem_coe, hmemR] at hz
    rw [A.mem_vertices_iff_coord]
    intro j
    have := hz j
    rcases eq_or_ne j k with rfl | hj
    · have hzf' : z j ≤ f := hzf
      rw [hck] at this; omega
    · rw [hcj j hj] at this; omega
  have hhigh : (↑R.vertices : Set (Vertex d)) ∩ {z | f + 1 ≤ z k} ⊆ (A.neighbor k).vertices := by
    rintro z ⟨hz, hzf⟩
    rw [Finset.mem_coe, hmemR] at hz
    rw [(A.neighbor k).mem_vertices_iff_coord, A.neighbor_radius]
    intro j
    have := hz j
    rcases eq_or_ne j k with rfl | hj
    · have hzf' : f + 1 ≤ z j := hzf
      rw [hck] at this; rw [hcenterk]; omega
    · rw [hcj j hj] at this; rw [hcenter j hj]; omega
  have hunion : (↑R.vertices : Set (Vertex d)) ⊆ A.vertices ∪ (A.neighbor k).vertices := by
    intro z hz
    by_cases hzf : z k ≤ f
    · exact Or.inl (hlow ⟨hz, hzf⟩)
    · exact Or.inr (hhigh ⟨hz, by change f + 1 ≤ z k; omega⟩)
  -- a crossing path of the test cube in direction `k`
  obtain ⟨hcross, -⟩ := hA.2 R hR
  obtain ⟨x, hxR, y, hyR, hxf, hyf, hxy⟩ := hcross k
  have hxk : x k = A.center k + A.radius - a := by
    rw [Finset.mem_coe, IntegerCube.mem_lowerFace] at hxf
    rw [← hck]; exact hxf.2
  have hyk : y k = A.center k + 2 * A.radius - a - 1 := by
    rw [Finset.mem_coe, IntegerCube.mem_upperFace] at hyf
    have h := hyf.2
    change y k + 1 = c k + ((N / 2 : ℕ) : ℤ) at h
    rw [hck, hL] at h
    omega
  -- the part inside `A`
  have hxS : x ∈ {z : Vertex d | z k ≤ f} := by
    change x k ≤ f; omega
  obtain ⟨u, hxu, hu⟩ := exists_reachable_inter_of_reachable_openIn hxy hxS
  have huS : u ∈ (↑R.vertices : Set (Vertex d)) ∩ {z | z k ≤ f} :=
    mem_of_reachable_openIn_of_mem ⟨hxR, hxS⟩ hxu
  have huk : u k = f := by
    rcases hu with rfl | ⟨v, hv, huv⟩
    · have := huS.2
      change u k ≤ f at this
      omega
    · have h1 := abs_le.mp (abs_sub_le_one_of_openIn_adj huv k)
      have h2 : u k ≤ f := huS.2
      change ¬ v k ≤ f at hv
      omega
  have hrAx : (openIn ω A.vertices).Reachable rA x := by
    refine hA.reachable_of_reachable (by omega) (hlow ⟨hxR, hxS⟩)
      (reachable_openIn_mono hlow hxu) k ?_
    rw [huk, hxk, abs_of_nonneg (by omega)]
    omega
  -- the part inside the neighbour
  have hyS : y ∈ {z : Vertex d | f + 1 ≤ z k} := by
    change f + 1 ≤ y k; omega
  obtain ⟨u', hyu, hu'⟩ := exists_reachable_inter_of_reachable_openIn hxy.symm hyS
  have huS' : u' ∈ (↑R.vertices : Set (Vertex d)) ∩ {z | f + 1 ≤ z k} :=
    mem_of_reachable_openIn_of_mem ⟨hyR, hyS⟩ hyu
  have huk' : u' k = f + 1 := by
    rcases hu' with rfl | ⟨v, hv, huv⟩
    · have := huS'.2
      change f + 1 ≤ u' k at this
      omega
    · have h1 := abs_le.mp (abs_sub_le_one_of_openIn_adj huv k)
      have h2 : f + 1 ≤ u' k := huS'.2
      change ¬ f + 1 ≤ v k at hv
      omega
  have hrBy : (openIn ω (A.neighbor k).vertices).Reachable rB y := by
    refine hB.reachable_of_reachable (by rw [A.neighbor_scale]; omega) (hhigh ⟨hyR, hyS⟩)
      (reachable_openIn_mono hhigh hyu) k ?_
    rw [huk', hyk, A.neighbor_side, abs_of_nonpos (by omega)]
    omega
  exact ((reachable_openIn_mono Set.subset_union_left hrAx).trans
    (reachable_openIn_mono hunion hxy)).trans
    (reachable_openIn_mono Set.subset_union_right hrBy).symm

/-- The cubes of scale at least two which are well-connected relative to their rounded
three-quarter cubes. -/
def TriadicCube.wellConnectedCubes (ω : Configuration d) : Set (TriadicCube d) :=
  {Q | 2 ≤ Q.scale ∧ Q.wellConnectedIn Q.threeQuarterCube.vertices ω}

/-- The good cubes (Armstrong and Dario, Definition 2.6): a cube is good when it and all its
children are well-connected cubes of scale at least two. -/
def TriadicCube.goodCubes (ω : Configuration d) : Set (TriadicCube d) :=
  goodOfWellConnected (wellConnectedCubes ω)

/-- Good cubes have scale at least three. -/
theorem TriadicCube.three_le_scale_of_mem_goodCubes {ω : Configuration d} {Q : TriadicCube d}
    (hQ : Q ∈ goodCubes ω) : 3 ≤ Q.scale := by
  have h := (hQ.2.2 fun _ => 0).1
  change 2 ≤ Q.scale - 1 at h
  omega

/-- A lattice neighbour outside a triadic cube of a vertex of the cube lies in the cube of the
same scale following it, or in the cube of the same scale preceding it, in some direction. -/
theorem TriadicCube.exists_neighbor_of_adj {Q : TriadicCube d} {x y : Vertex d}
    (hx : x ∈ Q.vertices) (hy : y ∉ Q.vertices) (hxy : (nearestNeighborGraph d).Adj x y) :
    ∃ k : Fin d, y ∈ (Q.neighbor k).vertices ∨
      ∃ P : TriadicCube d, P.neighbor k = Q ∧ y ∈ P.vertices := by
  have hxQ := (Q.mem_vertices_iff_coord x).1 hx
  have hsr := Q.side_eq_two_mul_radius_add_one
  obtain ⟨k, hk | hk⟩ := hxy
  · have hyi (i : Fin d) : y i = x i + if i = k then 1 else 0 := by
      rw [hk]; simp only [Pi.add_apply, LatticeProb.unit, Pi.single_apply]
    have hxk : x k = Q.center k + Q.radius := by
      by_contra hne
      apply hy
      rw [Q.mem_vertices_iff_coord]
      intro i
      have := hxQ i
      have hi := hyi i
      split_ifs at hi with hik
      · subst hik; omega
      · omega
    refine ⟨k, Or.inl ?_⟩
    rw [(Q.neighbor k).mem_vertices_iff_coord, Q.neighbor_radius]
    intro i
    have := hxQ i
    have hi := hyi i
    rw [Q.neighbor_center]
    split_ifs at hi ⊢ with hik
    · subst hik; omega
    · omega
  · have hxi (i : Fin d) : x i = y i + if i = k then 1 else 0 := by
      rw [hk]; simp only [Pi.add_apply, LatticeProb.unit, Pi.single_apply]
    have hxk : x k = Q.center k - Q.radius := by
      by_contra hne
      apply hy
      rw [Q.mem_vertices_iff_coord]
      intro i
      have := hxQ i
      have hi := hxi i
      split_ifs at hi with hik
      · subst hik; omega
      · omega
    let P : TriadicCube d := ⟨Q.scale, Q.index - Pi.single k 1⟩
    have hP : P.neighbor k = Q :=
      TriadicCube.ext_iff.2 ⟨rfl, sub_add_cancel Q.index (Pi.single k 1)⟩
    refine ⟨k, Or.inr ⟨P, hP, ?_⟩⟩
    have hPc (i : Fin d) : Q.center i = P.center i + if i = k then Q.side else 0 := by
      have h := P.neighbor_center k i
      rw [hP] at h
      exact h
    have hPr : P.radius = Q.radius := rfl
    rw [P.mem_vertices_iff_coord, hPr]
    intro i
    have := hxQ i
    have hi := hxi i
    have hc := hPc i
    split_ifs at hi hc with hik
    · subst hik; omega
    · omega

/-- **Armstrong and Dario, Lemma 2.8.** Let `Q` and `Q'` be good cubes containing lattice
neighbours, the scale of `Q'` being that of `Q` or one more. Then any two points of their crossing
clusters are joined by an open path inside `Q ∪ Q'`. -/
theorem TriadicCube.reachable_of_mem_goodCubes (hd : 0 < d) {ω : Configuration d}
    {Q Q' : TriadicCube d} (hQ : Q ∈ goodCubes ω) (hQ' : Q' ∈ goodCubes ω)
    (hle : Q.scale ≤ Q'.scale) (hle' : Q'.scale ≤ Q.scale + 1) {x y : Vertex d}
    (hx : x ∈ Q.vertices) (hy : y ∈ Q'.vertices) (hxy : (nearestNeighborGraph d).Adj x y)
    {u v : Vertex d} (hu : u ∈ Q.crossingCluster ω) (hv : v ∈ Q'.crossingCluster ω) :
    (openIn ω (Q.vertices ∪ Q'.vertices)).Reachable u v := by
  have h3 := three_le_scale_of_mem_goodCubes hQ
  obtain ⟨rQ, hrQ⟩ := (Q.wellConnectedIn_threeQuarter_iff ω).1 hQ.2.1.2
  obtain ⟨rQ', hrQ'⟩ := (Q'.wellConnectedIn_threeQuarter_iff ω).1 hQ'.2.1.2
  have hs' : 2 ≤ Q'.scale := hQ'.2.1.1
  -- the cube of the scale of `Q` containing `y`
  obtain ⟨T, ⟨hTs, hyT⟩, -⟩ := existsUnique_mem d Q.scale y
  have hTQ' : T.vertices ⊆ Q'.vertices :=
    vertices_subset_of_mem_of_scale_le hyT hy (by omega)
  have hT : T ∈ wellConnectedCubes ω ∧ T.crossingCluster ω ⊆ Q'.crossingCluster ω := by
    rcases Nat.eq_or_lt_of_le hle with h | h
    · have hTQ' : T = Q' := eq_of_mem_of_scale_eq (hTs.trans h) hyT hy
      rw [hTQ']
      exact ⟨hQ'.2.1, subset_rfl⟩
    · have hpar : T.parent = Q' :=
        eq_of_mem_of_scale_eq (by change T.scale + 1 = Q'.scale; omega)
          (T.vertices_subset_parent hyT) hy
      have hTc : Q'.child T.digit = T := by rw [← hpar]; exact T.parent_child
      rw [← hTc]
      exact ⟨hQ'.2.2 _, hrQ'.crossingCluster_child_subset_crossingCluster hd hs' _⟩
  obtain ⟨rT, hrT⟩ := (T.wellConnectedIn_threeQuarter_iff ω).1 hT.1.2
  have hvT : (openIn ω Q'.vertices).Reachable rT v :=
    hrQ'.reachable_of_mem_crossingCluster hd hs' (hT.2 hrT.mem_crossingCluster) hv
  have hrQu : (openIn ω Q.vertices).Reachable rQ u := by
    have h := hu
    rw [hrQ.crossingCluster_eq hd (by omega)] at h
    exact h
  by_cases hxT : x ∈ T.vertices
  · have hTQ : T = Q := eq_of_mem_of_scale_eq hTs hxT hx
    rw [hTQ] at hT
    exact reachable_openIn_mono Set.subset_union_right
      (hrQ'.reachable_of_mem_crossingCluster hd hs' (hT.2 hu) hv)
  · have hyQ : y ∉ Q.vertices := fun hyQ => hxT ((eq_of_mem_of_scale_eq hTs hyT hyQ) ▸ hx)
    have hjoin : (openIn ω (Q.vertices ∪ T.vertices)).Reachable rQ rT := by
      obtain ⟨k, hk | ⟨P, hP, hyP⟩⟩ := exists_neighbor_of_adj hx hyQ hxy
      · have hTn : T = Q.neighbor k := eq_of_mem_of_scale_eq hTs hyT hk
        rw [hTn] at hrT ⊢
        exact hrQ.reachable_neighbor hrT h3
      · have hTP : T = P := eq_of_mem_of_scale_eq (by rw [hTs, ← hP, neighbor_scale]) hyT hyP
        have h3' : 3 ≤ P.scale := by rw [← hTP, hTs]; exact h3
        rw [hTP] at hrT ⊢
        have hrQ'' : (P.neighbor k).IsWellConnectedRoot ω rQ := by rw [hP]; exact hrQ
        have h := hrT.reachable_neighbor hrQ'' h3'
        rw [hP, Set.union_comm] at h
        exact h.symm
    exact ((reachable_openIn_mono Set.subset_union_left hrQu.symm).trans
      (reachable_openIn_mono (Set.union_subset_union_right _ hTQ') hjoin)).trans
      (reachable_openIn_mono Set.subset_union_right hvT)

/-- **Armstrong and Dario, Lemma 2.8**, in the form of the source: under the assumptions of
`TriadicCube.reachable_of_mem_goodCubes`, an open cluster of `Q ∪ Q'` contains the crossing
clusters of both cubes. -/
theorem TriadicCube.exists_cluster_of_mem_goodCubes (hd : 0 < d) {ω : Configuration d}
    {Q Q' : TriadicCube d} (hQ : Q ∈ goodCubes ω) (hQ' : Q' ∈ goodCubes ω)
    (hle : Q.scale ≤ Q'.scale) (hle' : Q'.scale ≤ Q.scale + 1) {x y : Vertex d}
    (hx : x ∈ Q.vertices) (hy : y ∈ Q'.vertices) (hxy : (nearestNeighborGraph d).Adj x y) :
    ∃ C : Set (Vertex d), Q.crossingCluster ω ∪ Q'.crossingCluster ω ⊆ C ∧
      C ⊆ Q.vertices ∪ Q'.vertices ∧
      ∀ u ∈ C, ∀ v ∈ C, (openIn ω (Q.vertices ∪ Q'.vertices)).Reachable u v := by
  obtain ⟨rQ, hrQ⟩ := (Q.wellConnectedIn_threeQuarter_iff ω).1 hQ.2.1.2
  have hr := hrQ.mem_crossingCluster
  have h2 : 2 ≤ Q.scale := hQ.2.1.1
  refine ⟨{z | (openIn ω (Q.vertices ∪ Q'.vertices)).Reachable rQ z}, ?_, ?_, ?_⟩
  · rintro z (hz | hz)
    · exact reachable_openIn_mono Set.subset_union_left
        (hrQ.reachable_of_mem_crossingCluster hd h2 hr hz)
    · exact reachable_of_mem_goodCubes hd hQ hQ' hle hle' hx hy hxy hr hz
  · intro z hz
    exact mem_of_reachable_openIn_of_mem (Or.inl (hrQ.1.1)) hz
  · intro u hu v hv
    exact hu.symm.trans hv

end Rigidity.Percolation
