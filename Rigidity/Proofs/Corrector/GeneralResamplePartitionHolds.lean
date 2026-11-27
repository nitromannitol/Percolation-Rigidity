import Rigidity.Proofs.Corrector.GeneralResamplePartition
import PercolationClusterHomogenization.Percolation.TriadicLocalizationGeometry
import PercolationClusterHomogenization.Percolation.TriadicStableAncestors
import PercolationClusterHomogenization.Percolation.TriadicThreeQuarterCube
import PercolationClusterHomogenization.Percolation.TriadicWellConnectedEvent
import PercolationClusterHomogenization.Proofs.Cluster.GeneralMuLocality

/-!
# Lemma 3.5 of Dario from the one-bond stability of good cubes

Dario's proof of Lemma 3.5 combines five ingredients. This file proves, for the partition into good
cubes of `ℤᵈ`, all of the argument except the one-bond stability of good cubes at large scales,
which is the named hypothesis `GoodFlipStable c`: for configurations equal off a bond `e`, every
cube of scale at least `k + c`, `k` the scale of the partition cube of an endpoint of `e`, is good
for one configuration if and only if it is good for the other.

* `TriadicCube.eq_of_isMaximalStopping_of_agree`: two maximal stopping cubes containing a point,
  for two collections of good cubes which agree on the influence sets of the two cubes and of their
  children, coincide;
* `goodCubes_iff_of_far` (Dario's ingredient 1): changing a bond with an endpoint outside the
  centred triple `{v : |v - c_T|_∞ < 3 side(T)/2}` of a cube `T` does not change its goodness
  (`Rigidity.Percolation.TriadicCube.mem_goodCubes_iff_of_adj_iff`);
* `scale_partitionCube_le_of_near` (Dario's ingredient 5): if `|z - x|_∞ < 3^a side(□_𝒫(x))`, then
  `scale(□_𝒫(z)) ≤ scale(□_𝒫(x)) + a + 1`;
* `resamplePartitionBound_of_goodFlipStable`: `GoodFlipStable c` gives Lemma 3.5 in the form
  `ResamplePartitionBound (3^{c+2}) (3^{c+4})`, with the partition cubes and their anchors equal
  outside the ball;
* `darioResamplePartitionThree_of_goodFlipStable`: `DarioResamplePartitionThree` from the stability
  in every dimension `d ≥ 3` (`DarioGoodFlipStableThree`).
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

/-- Two cubes of the same scale with points at `ℓ∞` distance at most their side have points at
`ℓ∞` distance at most one. -/
theorem TriadicCube.exists_near_of_abs_sub_le {S S' : TriadicCube d} (hs : S.scale = S'.scale)
    {a b : Vertex d} (ha : a ∈ S.vertices) (hb : b ∈ S'.vertices)
    (hab : ∀ i, |a i - b i| ≤ S.side) :
    ∃ a' ∈ S.vertices, ∃ b' ∈ S'.vertices, ∀ i, |a' i - b' i| ≤ 1 := by
  have hss : S'.side = S.side := by simp only [side, hs]
  have hpos := S.side_pos
  have hr := S.side_eq_two_mul_radius_add_one
  have hr0 : 0 ≤ S.radius := by omega
  have hι : ∀ i, -1 ≤ S'.index i - S.index i ∧ S'.index i - S.index i ≤ 1 := by
    intro i
    have h1 := abs_lt.mp (ha i)
    have h2 := abs_lt.mp (hb i)
    rw [hss] at h2
    have h3 := abs_le.mp (hab i)
    have hlt : S.side * (S'.index i - S.index i) < S.side * 2 := by linarith
    have hgt : S.side * (-2) < S.side * (S'.index i - S.index i) := by linarith
    have e1 := lt_of_mul_lt_mul_left hlt hpos.le
    have e2 := lt_of_mul_lt_mul_left hgt hpos.le
    constructor <;> omega
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

/-- **The one-bond stability of good cubes at large scales** (the step of Dario's proof of Lemma
3.5 stated there without proof, ingredients 3 and 4): for configurations equal off a bond `e`,
both on the partition event, an endpoint `x` of `e` and `k` the scale of the partition cube of `x`
for `ω`, every triadic cube of scale at least `k + c` is good for `ω` if and only if it is good
for `ω'`. -/
def GoodFlipStable (c : ℕ) : Prop :=
  ∀ (e : Bond d) (ω ω' : Configuration d), (∀ b, b ≠ e → ω' b = ω b) →
    PartitionEvent ω → PartitionEvent ω' → ∀ x ∈ e.1, ∀ T : TriadicCube d,
      (partitionCube ω x).scale + c ≤ T.scale →
        (T ∈ TriadicCube.goodCubes ω ↔ T ∈ TriadicCube.goodCubes ω')

/-- The one-bond stability of good cubes in every dimension `d ≥ 3` (hypothesis). -/
def DarioGoodFlipStableThree : Prop :=
  ∀ (d : ℕ) [NeZero d], 3 ≤ d → ∃ c : ℕ, GoodFlipStable (d := d) c

/-- **Dario, Lemma 3.5, from the one-bond stability of good cubes**: with `C₀ = 3^{c+2}` and
`C = 3^{c+4}`, the partition cubes of points in the ball `|z - x|_∞ < C₀ side(□_𝒫(x))` have side at
most `C side(□_𝒫(x))` after the change, and the partition cubes and their anchors of the other points
do not change. -/
theorem resamplePartitionBound_of_goodFlipStable {c : ℕ} (h : GoodFlipStable (d := d) c) :
    ResamplePartitionBound (d := d) (3 ^ (c + 2)) (3 ^ (c + 4)) := by
  intro e ω ω' hag hP hP' x hx z
  set k := (partitionCube ω x).scale with hk
  have hchg : ∀ T : TriadicCube d, ¬ (T ∈ TriadicCube.goodCubes ω ↔ T ∈ TriadicCube.goodCubes ω') →
      T.scale < k + c ∧ ∀ i, |x i - T.center i| < 3 * T.side := by
    intro T hT
    refine ⟨?_, ?_⟩
    · by_contra hs
      push Not at hs
      exact hT (h e ω ω' hag hP hP' x hx T hs)
    · by_contra hfar
      refine hT (goodCubes_iff_of_far hag hx fun hxT => hfar fun i => ?_)
      exact TriadicCube.abs_coord_sub_center_lt_of_mem_centeredTriple hxT i
  constructor
  · intro hball
    set R := partitionCube ω' z with hRdef
    have hRspec := partitionCube_spec hP' z
    by_contra hbig
    have hm : k + c + 4 < R.scale := by
      by_contra hle
      push Not at hle
      apply hbig
      rw [← pow_add]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have hagR : ∀ T ∈ R.influence,
        (T ∈ TriadicCube.goodCubes ω ↔ T ∈ TriadicCube.goodCubes ω') := fun T hT =>
      h e ω ω' hag hP hP' x hx T (by have := TriadicCube.scale_le_of_mem_influence hT; omega)
    have hchR : 0 < R.scale → ∀ dg, ∀ T ∈ (R.child dg).influence,
        (T ∈ TriadicCube.goodCubes ω ↔ T ∈ TriadicCube.goodCubes ω') := fun _ dg T hT =>
      h e ω ω' hag hP hP' x hx T (by
        have := TriadicCube.scale_le_of_mem_influence hT
        change R.scale - 1 ≤ T.scale at this
        omega)
    have hRstop : R.IsStopping (TriadicCube.goodCubes ω) :=
      (TriadicCube.isStopping_iff_of_agree hagR hchR).2 hRspec.2.1
    have hQspec := partitionCube_spec hP z
    have hge : R.scale ≤ (partitionCube ω z).scale := by
      rcases le_total (partitionCube ω z).scale R.scale with hl | hl
      · exact hQspec.2.2 R hRstop
          (TriadicCube.vertices_subset_of_mem_of_scale_le hQspec.1 hRspec.1 hl)
      · exact hl
    have hcomp := scale_partitionCube_le_of_near hP (z := z) (a := c + 2) fun i => by
      have := hball i
      push_cast at this
      exact this
    omega
  · intro hnot
    have hfar : ∃ i, ((3 ^ (c + 2) : ℕ) : ℤ) * 3 ^ k ≤ |z i - x i| := by
      unfold InResampleBall at hnot
      push Not at hnot
      exact hnot
    obtain ⟨i₀, hi₀⟩ := hfar
    push_cast at hi₀
    have hun : ∀ S T : TriadicCube d, z ∈ S.parent.vertices → T ∈ S.influence →
        (T ∈ TriadicCube.goodCubes ω ↔ T ∈ TriadicCube.goodCubes ω') := by
      intro S T hzS hT
      by_contra hne
      obtain ⟨hTs, hTx⟩ := hchg T hne
      have h1 := TriadicCube.abs_coord_sub_lt_of_mem_parent_of_mem_influence hzS hT
        T.center_mem i₀
      have h2 := hTx i₀
      have hside : 3 * T.side ≤ (3 : ℤ) ^ c * 3 ^ k := by
        rw [← pow_add, TriadicCube.side, ← pow_succ']
        exact pow_le_pow_right₀ (by norm_num) (by omega)
      have h3 : |z i₀ - x i₀| ≤ |z i₀ - T.center i₀| + |x i₀ - T.center i₀| := by
        have := abs_sub_le (z i₀) (T.center i₀) (x i₀)
        rwa [abs_sub_comm (T.center i₀) (x i₀)] at this
      have hc : (3 : ℤ) ^ (c + 2) * 3 ^ k = 9 * ((3 : ℤ) ^ c * 3 ^ k) := by ring
      have h1' : |z i₀ - T.center i₀| < 12 * T.side := h1
      have hTpos := T.side_pos
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
      have h3 : (3 : ℤ) ^ k ≤ (3 : ℤ) ^ (c + 2) * 3 ^ k :=
        le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num))
      linarith
    refine ⟨hQR.symm, ?_⟩
    have hanchor : Q.anchor ω = Q.anchor ω' := TriadicCube.anchor_eq_of_adj_iff fun u hu v hv =>
      (openGraph_adj_iff_of_localBonds (S := Q.vertices) (ω := ω) (ω' := ω')
        (fun b hb => (hag b fun hbe => hxQ (hb x (hbe ▸ hx))).symm) u hu v hv).symm
    change (partitionCube ω' z).anchor ω' = (partitionCube ω z).anchor ω
    rw [← hRdef, ← hQR, hanchor]

/-- **Dario, Lemma 3.5, in dimension `d ≥ 3`**, from the one-bond stability of good cubes. -/
theorem darioResamplePartitionThree_of_goodFlipStable (h : DarioGoodFlipStableThree) :
    DarioResamplePartitionThree := by
  intro d _ hd
  obtain ⟨c, hc⟩ := h d hd
  exact ⟨3 ^ (c + 2), 3 ^ (c + 4), by positivity, resamplePartitionBound_of_goodFlipStable hc⟩

end Rigidity.Corrector.GeneralDim
