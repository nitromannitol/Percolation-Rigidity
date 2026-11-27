import Rigidity.Proofs.Corrector.GeneralResamplePartition
import PercolationClusterHomogenization.Percolation.TriadicLocalizationGeometry
import PercolationClusterHomogenization.Percolation.TriadicStableAncestors
import PercolationClusterHomogenization.Percolation.TriadicThreeQuarterCube
import PercolationClusterHomogenization.Percolation.TriadicWellConnectedEvent
import PercolationClusterHomogenization.Proofs.Cluster.GeneralMuLocality

/-!
# Lemma 3.5 of Dario, corrected, for the partition into good cubes of `ℤᵈ`

Lemma 3.5 of Dario compares the partitions into good cubes of two configurations `ω, ω'` that
differ at one bond `e`. As printed, its scale is the side `s` of the partition cube of an endpoint
`x` of `e` for `ω`; with that scale the lemma fails in dimension `d ≥ 3` (one bond can destroy the
goodness of arbitrarily large cubes while the partition of `ω` has side 27 everywhere). The
corrected form uses the scale `S = max(side □_{𝒫(ω)}(x), side □_{𝒫(ω')}(x))`, and is proved here
with no hypothesis.

* `TriadicCube.eq_of_isMaximalStopping_of_agree`: two maximal stopping cubes containing a point,
  for two collections of good cubes which agree on the influence sets of the two cubes and of their
  children, coincide;
* `goodCubes_iff_of_far` (Dario's ingredient 1): changing a bond with an endpoint outside the
  centred triple `{v : |v - c_T|_∞ < 3 side(T)/2}` of a cube `T` does not change its goodness
  (`Rigidity.Percolation.TriadicCube.mem_goodCubes_iff_of_adj_iff`);
* `scale_partitionCube_le_of_near` (Dario's ingredient 5): if `|z - x|_∞ < 3^a side(□_𝒫(x))`, then
  `scale(□_𝒫(z)) ≤ scale(□_𝒫(x)) + a + 1`;
* `mem_stableGood_of_mem_centeredTriple`: every cube of side at least `9 side(□_𝒫(x))` whose centred
  triple contains `x` is stable;
* `goodCubes_iff_of_flip`: hence the cubes of side at least `9S` have the same goodness for `ω` and
  `ω'`;
* `resamplePartition_max_bound`: **Lemma 3.5, corrected**, with `C₀ = 81` and `C = 243`: the
  partition cubes for `ω'` of the points `z` with `|z - x|_∞ < 81 S` have side at most `243 S`, and
  the partition cubes and their anchors of the other points are the same for `ω` and `ω'`.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation Rigidity.External

variable {d : ℕ}

/-- Stopping cubes for two collections of good cubes which agree on the influence sets of the cube
and of its children coincide. -/
theorem TriadicCube.isStopping_iff_of_agree {G H : Set (TriadicCube d)} {Q : TriadicCube d}
    (hQ : ∀ T ∈ Q.influence, (T ∈ G ↔ T ∈ H))
    (hch : 0 < Q.scale → ∀ digits, ∀ T ∈ (Q.child digits).influence, (T ∈ G ↔ T ∈ H)) :
    Q.IsStopping G ↔ Q.IsStopping H := by
  have hs : ∀ S : TriadicCube d, (∀ T ∈ S.influence, (T ∈ G ↔ T ∈ H)) →
      (S ∈ stableGood G ↔ S ∈ stableGood H) :=
    fun S hS => ⟨fun h T hT => (hS T hT).1 (h hT), fun h T hT => (hS T hT).2 (h hT)⟩
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(hs Q hQ).1 h1, ?_⟩
    rcases h2 with h | ⟨dg, hdg⟩
    · exact Or.inl h
    · rcases Nat.eq_zero_or_pos Q.scale with h0 | h0
      · exact Or.inl h0
      · exact Or.inr ⟨dg, fun h' => hdg ((hs _ (hch h0 dg)).2 h')⟩
  · rintro ⟨h1, h2⟩
    refine ⟨(hs Q hQ).2 h1, ?_⟩
    rcases h2 with h | ⟨dg, hdg⟩
    · exact Or.inl h
    · rcases Nat.eq_zero_or_pos Q.scale with h0 | h0
      · exact Or.inl h0
      · exact Or.inr ⟨dg, fun h' => hdg ((hs _ (hch h0 dg)).1 h')⟩

/-- **Two partitions agree where their good cubes agree**: maximal stopping cubes containing `x`
for collections `G` and `H` which agree on the influence sets of both cubes and of their children
coincide. -/
theorem TriadicCube.eq_of_isMaximalStopping_of_agree {G H : Set (TriadicCube d)}
    {Q R : TriadicCube d} {x : Vertex d} (hxQ : x ∈ Q.vertices) (hxR : x ∈ R.vertices)
    (hQ : Q.IsMaximalStopping G) (hR : R.IsMaximalStopping H)
    (hagQ : ∀ T ∈ Q.influence, (T ∈ G ↔ T ∈ H)) (hagR : ∀ T ∈ R.influence, (T ∈ G ↔ T ∈ H))
    (hchQ : 0 < Q.scale → ∀ digits, ∀ T ∈ (Q.child digits).influence, (T ∈ G ↔ T ∈ H))
    (hchR : 0 < R.scale → ∀ digits, ∀ T ∈ (R.child digits).influence, (T ∈ G ↔ T ∈ H)) :
    Q = R := by
  have hQH : Q.IsStopping H := (isStopping_iff_of_agree hagQ hchQ).1 hQ.1
  have hRG : R.IsStopping G := (isStopping_iff_of_agree hagR hchR).2 hR.1
  rcases le_total Q.scale R.scale with h | h
  · have hle := hQ.2 R hRG (vertices_subset_of_mem_of_scale_le hxQ hxR h)
    exact eq_of_mem_of_scale_eq (le_antisymm h hle) hxQ hxR
  · have hle := hR.2 Q hQH (vertices_subset_of_mem_of_scale_le hxR hxQ h)
    exact eq_of_mem_of_scale_eq (le_antisymm hle h) hxQ hxR

/-- Two cubes of the same scale whose indices differ by at most one in every coordinate have points
at `ℓ∞` distance at most one. -/
theorem TriadicCube.exists_near_of_index {S S' : TriadicCube d} (hs : S.scale = S'.scale)
    (hι : ∀ i, -1 ≤ S'.index i - S.index i ∧ S'.index i - S.index i ≤ 1) :
    ∃ a' ∈ S.vertices, ∃ b' ∈ S'.vertices, ∀ i, |a' i - b' i| ≤ 1 := by
  have hss : S'.side = S.side := by simp only [side, hs]
  have hpos := S.side_pos
  have hr := S.side_eq_two_mul_radius_add_one
  have hr0 : 0 ≤ S.radius := by omega
  refine ⟨fun i => S.side * S.index i + S.radius * (S'.index i - S.index i), ?_,
    fun i => S.side * S'.index i - S.radius * (S'.index i - S.index i), ?_, fun i => ?_⟩
  · intro i
    obtain ⟨h1, h2⟩ := hι i
    have e : 2 * (S.side * S.index i + S.radius * (S'.index i - S.index i) - S.side * S.index i) =
        2 * S.radius * (S'.index i - S.index i) := by ring
    rw [e, abs_lt]
    constructor <;> nlinarith
  · intro i
    obtain ⟨h1, h2⟩ := hι i
    rw [hss]
    have e : 2 * (S.side * S'.index i - S.radius * (S'.index i - S.index i) - S.side * S'.index i) =
        -(2 * S.radius * (S'.index i - S.index i)) := by ring
    rw [e, abs_neg, abs_lt]
    constructor <;> nlinarith
  · have e : S.side * S.index i + S.radius * (S'.index i - S.index i) -
        (S.side * S'.index i - S.radius * (S'.index i - S.index i)) =
        -(S'.index i - S.index i) := by rw [hr]; ring
    rw [e, abs_neg, abs_le]
    exact hι i

/-- Two cubes of the same scale with points at `ℓ∞` distance at most their side have points at
`ℓ∞` distance at most one. -/
theorem TriadicCube.exists_near_of_abs_sub_le {S S' : TriadicCube d} (hs : S.scale = S'.scale)
    {a b : Vertex d} (ha : a ∈ S.vertices) (hb : b ∈ S'.vertices)
    (hab : ∀ i, |a i - b i| ≤ S.side) :
    ∃ a' ∈ S.vertices, ∃ b' ∈ S'.vertices, ∀ i, |a' i - b' i| ≤ 1 := by
  have hss : S'.side = S.side := by simp only [side, hs]
  have hpos := S.side_pos
  refine exists_near_of_index hs fun i => ?_
  have h1 := abs_lt.mp (ha i)
  have h2 := abs_lt.mp (hb i)
  rw [hss] at h2
  have h3 := abs_le.mp (hab i)
  have hlt : S.side * (S'.index i - S.index i) < S.side * 2 := by linarith
  have hgt : S.side * (-2) < S.side * (S'.index i - S.index i) := by linarith
  have e1 := lt_of_mul_lt_mul_left hlt hpos.le
  have e2 := lt_of_mul_lt_mul_left hgt hpos.le
  constructor <;> omega

/-- A cube whose centred triple contains a point of a cube of the same scale is that cube or one of
its neighbours: their indices differ by at most one in every coordinate. -/
theorem TriadicCube.index_sub_of_mem_centeredTriple {E T : TriadicCube d} (hs : E.scale = T.scale)
    {x : Vertex d} (hxE : x ∈ E.vertices) (hxT : x ∈ T.centeredTriple) (i : Fin d) :
    -1 ≤ T.index i - E.index i ∧ T.index i - E.index i ≤ 1 := by
  have hss : T.side = E.side := by simp only [side, hs]
  have hpos := E.side_pos
  have h1 := abs_lt.mp (hxE i)
  have h2 := abs_lt.mp (hxT i)
  change -(3 * T.side) < 2 * (x i - T.side * T.index i) ∧
    2 * (x i - T.side * T.index i) < 3 * T.side at h2
  rw [hss] at h2
  have hlt : E.side * (T.index i - E.index i) < E.side * 2 := by linarith
  have hgt : E.side * (-2) < E.side * (T.index i - E.index i) := by linarith
  have e1 := lt_of_mul_lt_mul_left hlt hpos.le
  have e2 := lt_of_mul_lt_mul_left hgt hpos.le
  constructor <;> omega

end Rigidity.Percolation

namespace Rigidity.Corrector.GeneralDim

open LatticeProb.Percolation Rigidity.Percolation

variable {d : ℕ}

/-- **Dario, Lemma 3.5, ingredient 1, for one bond**: changing one bond with an endpoint outside
the centred triple of a cube does not change its goodness. -/
theorem goodCubes_iff_of_far {e : Bond d} {ω ω' : Configuration d}
    (hagree : ∀ b, b ≠ e → ω' b = ω b) {x : Vertex d} (hx : x ∈ e.1) {T : TriadicCube d}
    (hfar : x ∉ T.centeredTriple) :
    T ∈ TriadicCube.goodCubes ω ↔ T ∈ TriadicCube.goodCubes ω' := by
  refine TriadicCube.mem_goodCubes_iff_of_adj_iff fun u hu v hv => ?_
  have h := openGraph_adj_iff_of_localBonds (S := T.centeredTriple) (ω := ω) (ω' := ω')
    (fun b hb => (hagree b fun hbe => hfar (hb x (hbe ▸ hx))).symm) u hu v hv
  exact h.symm

/-- **Dario, Lemma 3.5, ingredient 5**: partition cubes of nearby points have comparable sizes:
if `|z - x|_∞ < 3^a side(□_𝒫(x))`, then `scale(□_𝒫(z)) ≤ scale(□_𝒫(x)) + a + 1`. -/
theorem scale_partitionCube_le_of_near {ω : Configuration d} (hP : PartitionEvent ω)
    {x z : Vertex d} {a : ℕ}
    (hz : ∀ i, |z i - x i| < (3 : ℤ) ^ a * 3 ^ (partitionCube ω x).scale) :
    (partitionCube ω z).scale ≤ (partitionCube ω x).scale + a + 1 := by
  set R₀ := partitionCube ω x with hR₀def
  set Q := partitionCube ω z with hQdef
  by_contra hlt
  push Not at hlt
  have hR₀ : R₀ ∈ TriadicCube.stableGood (TriadicCube.goodCubes ω) :=
    (partitionCube_spec hP x).2.1.1
  set A := R₀.ancestor (Q.scale - 2 - R₀.scale) with hAdef
  have hA := TriadicCube.ancestor_mem_stableGood hR₀ (Q.scale - 2 - R₀.scale)
  have hAscale : A.scale = Q.scale - 2 := by
    rw [hAdef, TriadicCube.scale_ancestor]
    omega
  have hxA : x ∈ A.vertices := R₀.vertices_subset_ancestor _ (mem_partitionCube hP x)
  obtain ⟨S', ⟨hS'scale, hzS'⟩, -⟩ := TriadicCube.existsUnique_mem d (Q.scale - 2) z
  have hS'Q : S'.vertices ⊆ Q.vertices :=
    TriadicCube.vertices_subset_of_mem_of_scale_le hzS' (mem_partitionCube hP z) (by omega)
  have hnear : ∀ i, |x i - z i| ≤ A.side := by
    intro i
    have h1 := hz i
    rw [abs_sub_comm] at h1
    have h2 : (3 : ℤ) ^ a * 3 ^ R₀.scale ≤ A.side := by
      rw [← pow_add, TriadicCube.side, hAscale]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  obtain ⟨a', ha', b', hb', hab⟩ :=
    TriadicCube.exists_near_of_abs_sub_le (hAscale.trans hS'scale.symm) hxA hzS' hnear
  have hQpos : 0 < Q.scale := by omega
  have hchild : ∀ dg, Q.child dg ∈ TriadicCube.stableGood (TriadicCube.goodCubes ω) := by
    intro dg
    have hstep : A.InfluenceStep (Q.child dg) := by
      refine ⟨?_, a', ha', b', ?_, hab⟩
      · change Q.scale - 1 = A.scale + 1
        omega
      · rw [TriadicCube.child_parent _ _ hQpos]
        exact hS'Q hb'
    exact TriadicCube.influence_subset_stableGood hA (Relation.ReflTransGen.single hstep)
  rcases (show Q.IsMaximalStopping _ from (partitionCube_spec hP z).2).1.2 with h0 | ⟨dg, hdg⟩
  · omega
  · exact hdg (hchild dg)

/-- **The grid observation**: if the partition cube of `x` has scale at most `n - 2`, every cube of
scale `n` whose centred triple contains `x` (the cube of scale `n` containing `x` and its
neighbours) is stable: the ancestor of scale `n - 2` of the partition cube influences every child of
the cube of `x`, and a child touching the cube influences it. -/
theorem mem_stableGood_of_mem_centeredTriple {ω : Configuration d} (hP : PartitionEvent ω)
    {x : Vertex d} {T : TriadicCube d} (hT : (partitionCube ω x).scale + 2 ≤ T.scale)
    (hxT : x ∈ T.centeredTriple) : T ∈ TriadicCube.stableGood (TriadicCube.goodCubes ω) := by
  set R₀ := partitionCube ω x with hR₀def
  have hR₀ : R₀ ∈ TriadicCube.stableGood (TriadicCube.goodCubes ω) :=
    (partitionCube_spec hP x).2.1.1
  set A := R₀.ancestor (T.scale - 2 - R₀.scale) with hAdef
  have hA := TriadicCube.ancestor_mem_stableGood hR₀ (T.scale - 2 - R₀.scale)
  have hAscale : A.scale = T.scale - 2 := by
    rw [hAdef, TriadicCube.scale_ancestor]
    omega
  have hxA : x ∈ A.vertices := R₀.vertices_subset_ancestor _ (mem_partitionCube hP x)
  obtain ⟨E, ⟨hEscale, hxE⟩, -⟩ := TriadicCube.existsUnique_mem d T.scale x
  obtain ⟨a', ha'E, b', hb'T, hab⟩ := TriadicCube.exists_near_of_index (S := E) (S' := T) hEscale
    (TriadicCube.index_sub_of_mem_centeredTriple hEscale hxE hxT)
  obtain ⟨W, ⟨hWscale, ha'W⟩, -⟩ := TriadicCube.existsUnique_mem d (T.scale - 1) a'
  have hWE : W.parent = E := TriadicCube.eq_of_mem_of_scale_eq
    (by change W.scale + 1 = E.scale; omega) (W.vertices_subset_parent ha'W) ha'E
  have h1 : A.InfluenceStep W := by
    refine ⟨by omega, x, hxA, x, ?_, fun i => by simp⟩
    rw [hWE]
    exact hxE
  have h2 : W.InfluenceStep T :=
    ⟨by omega, a', ha'W, b', T.vertices_subset_parent hb'T, hab⟩
  exact TriadicCube.influence_subset_stableGood hA
    (Relation.ReflTransGen.tail (Relation.ReflTransGen.single h1) h2)

/-- **The large-cube equivalence** (the corrected form of Dario's ingredients 3 and 4): for
configurations equal off a bond `e` and an endpoint `x` of `e`, every cube of scale at least
`max(k, k') + 2`, `k` and `k'` the scales of the partition cubes of `x` for `ω` and `ω'`, is good for
`ω` if and only if it is good for `ω'`. -/
theorem goodCubes_iff_of_flip {e : Bond d} {ω ω' : Configuration d}
    (hagree : ∀ b, b ≠ e → ω' b = ω b) (hP : PartitionEvent ω) (hP' : PartitionEvent ω')
    {x : Vertex d} (hx : x ∈ e.1) {T : TriadicCube d}
    (hT : max (partitionCube ω x).scale (partitionCube ω' x).scale + 2 ≤ T.scale) :
    T ∈ TriadicCube.goodCubes ω ↔ T ∈ TriadicCube.goodCubes ω' := by
  by_cases hxT : x ∈ T.centeredTriple
  · exact iff_of_true
      (TriadicCube.stableGood_subset _ (mem_stableGood_of_mem_centeredTriple hP
        (le_trans (by omega) hT) hxT))
      (TriadicCube.stableGood_subset _ (mem_stableGood_of_mem_centeredTriple hP'
        (le_trans (by omega) hT) hxT))
  · exact goodCubes_iff_of_far hagree hx hxT

/-- **Dario, Lemma 3.5, corrected**: let `ω, ω'` be equal off a bond `e`, both on the partition
event, `x` an endpoint of `e` and `S = max(side □_{𝒫(ω)}(x), side □_{𝒫(ω')}(x))`. The partition
cubes for `ω'` of the points `z` with `|z - x|_∞ < 81 S` have side at most `243 S`, and the partition
cubes and their anchors of the other points are the same for `ω` and `ω'`. -/
theorem resamplePartition_max_bound {e : Bond d} {ω ω' : Configuration d}
    (hag : ∀ b, b ≠ e → ω' b = ω b) (hP : PartitionEvent ω) (hP' : PartitionEvent ω')
    {x : Vertex d} (hx : x ∈ e.1) (z : Vertex d) :
    ((∀ i, |z i - x i| < ((81 : ℕ) : ℤ) *
        ((max (3 ^ (partitionCube ω x).scale) (3 ^ (partitionCube ω' x).scale) : ℕ) : ℤ)) →
      3 ^ (partitionCube ω' z).scale ≤
        243 * max (3 ^ (partitionCube ω x).scale) (3 ^ (partitionCube ω' x).scale)) ∧
    (¬ (∀ i, |z i - x i| < ((81 : ℕ) : ℤ) *
        ((max (3 ^ (partitionCube ω x).scale) (3 ^ (partitionCube ω' x).scale) : ℕ) : ℤ)) →
      partitionCube ω' z = partitionCube ω z ∧ partitionAnchor ω' z = partitionAnchor ω z) := by
  set k := (partitionCube ω x).scale with hk
  set k' := (partitionCube ω' x).scale with hk'
  set K := max k k' with hK
  have hS : max (3 ^ k) (3 ^ k') = 3 ^ K := by
    rcases le_total k k' with h | h
    · rw [hK, max_eq_right h, max_eq_right (Nat.pow_le_pow_right (by norm_num) h)]
    · rw [hK, max_eq_left h, max_eq_left (Nat.pow_le_pow_right (by norm_num) h)]
  rw [hS]
  have hchg : ∀ T : TriadicCube d, ¬ (T ∈ TriadicCube.goodCubes ω ↔ T ∈ TriadicCube.goodCubes ω') →
      T.scale < K + 2 ∧ ∀ i, |x i - T.center i| < 3 * T.side := by
    intro T hT
    refine ⟨?_, ?_⟩
    · by_contra hs
      push Not at hs
      exact hT (goodCubes_iff_of_flip hag hP hP' hx hs)
    · by_contra hfar
      refine hT (goodCubes_iff_of_far hag hx fun hxT => hfar fun i => ?_)
      exact TriadicCube.abs_coord_sub_center_lt_of_mem_centeredTriple hxT i
  constructor
  · intro hball
    have hcomp := scale_partitionCube_le_of_near hP' (x := x) (z := z) (a := 4 + (K - k'))
      fun i => by
        have h := hball i
        have e : (3 : ℤ) ^ (4 + (K - k')) * 3 ^ k' = ((81 : ℕ) : ℤ) * ((3 ^ K : ℕ) : ℤ) := by
          rw [← pow_add, show 4 + (K - k') + k' = 4 + K by omega, pow_add]
          push_cast
          ring
        rw [e]
        exact h
    calc 3 ^ (partitionCube ω' z).scale ≤ 3 ^ (K + 5) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 243 * 3 ^ K := by ring
  · intro hnot
    push Not at hnot
    obtain ⟨i₀, hi₀⟩ := hnot
    push_cast at hi₀
    have hun : ∀ S T : TriadicCube d, z ∈ S.parent.vertices → T ∈ S.influence →
        (T ∈ TriadicCube.goodCubes ω ↔ T ∈ TriadicCube.goodCubes ω') := by
      intro S T hzS hT
      by_contra hne
      obtain ⟨hTs, hTx⟩ := hchg T hne
      have h1 := TriadicCube.abs_coord_sub_lt_of_mem_parent_of_mem_influence hzS hT
        T.center_mem i₀
      have h2 := hTx i₀
      have hside : T.side ≤ 3 * (3 : ℤ) ^ K := by
        rw [TriadicCube.side, ← pow_succ']
        exact pow_le_pow_right₀ (by norm_num) (by omega)
      have h3 : |z i₀ - x i₀| ≤ |z i₀ - T.center i₀| + |x i₀ - T.center i₀| := by
        have := abs_sub_le (z i₀) (T.center i₀) (x i₀)
        rwa [abs_sub_comm (T.center i₀) (x i₀)] at this
      have h1' : |z i₀ - T.center i₀| < 12 * T.side := h1
      have hKpos : (0 : ℤ) < 3 ^ K := by positivity
      linarith
    set Q := partitionCube ω z with hQdef
    set R := partitionCube ω' z with hRdef
    have hQspec := partitionCube_spec hP z
    have hRspec := partitionCube_spec hP' z
    have hQR : Q = R := TriadicCube.eq_of_isMaximalStopping_of_agree hQspec.1 hRspec.1
      hQspec.2 hRspec.2
      (fun T hT => hun Q T (Q.vertices_subset_parent hQspec.1) hT)
      (fun T hT => hun R T (R.vertices_subset_parent hRspec.1) hT)
      (fun h0 dg T hT => hun _ T (by rw [TriadicCube.child_parent _ _ h0]; exact hQspec.1) hT)
      (fun h0 dg T hT => hun _ T (by rw [TriadicCube.child_parent _ _ h0]; exact hRspec.1) hT)
    have hxQ : x ∉ Q.vertices := by
      intro hxQ
      have hxeq : partitionCube ω x = Q := partitionCube_eq_of_mem hP hxQ
      have h1 := TriadicCube.abs_coord_sub_lt_side hQspec.1 hxQ i₀
      have h2 : Q.side = (3 : ℤ) ^ k := by rw [hk, hxeq]; rfl
      have h3 : (3 : ℤ) ^ k ≤ 3 ^ K := pow_le_pow_right₀ (by norm_num) (le_max_left _ _)
      have h4 : (0 : ℤ) < 3 ^ K := by positivity
      linarith
    refine ⟨hQR.symm, ?_⟩
    have hanchor : Q.anchor ω = Q.anchor ω' := TriadicCube.anchor_eq_of_adj_iff fun u hu v hv =>
      (openGraph_adj_iff_of_localBonds (S := Q.vertices) (ω := ω) (ω' := ω')
        (fun b hb => (hag b fun hbe => hxQ (hb x (hbe ▸ hx))).symm) u hu v hv).symm
    change (partitionCube ω' z).anchor ω' = (partitionCube ω z).anchor ω
    rw [← hRdef, ← hQR, hanchor]

end Rigidity.Corrector.GeneralDim
