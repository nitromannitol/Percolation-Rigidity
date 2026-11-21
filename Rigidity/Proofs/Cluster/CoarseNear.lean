import Rigidity.Proofs.Cluster.CoarseInequalities

/-!
# Bounded overlap from neighbouring partition cubes

In Armstrong and Dario (Lemmas 3.2 and 3.3) the open path from a vertex `x` of the cluster to its
anchor stays in the partition cubes at distance at most one from `□_𝒫(x)`, and the open path
between the anchors of two neighbouring partition cubes stays in their union. Together with
Proposition 2.1 (ii), neighbouring partition cubes have sizes within a factor of three, this gives
the bounded overlap of the regions used in Lemmas 3.2 and 3.3, with constants depending only on
the dimension:
* `CoarseData.regionOverlap_of_near`: `K = 7^d`, `N = 21^d`, `m = 1`;
* `CoarseData.pairOverlap_of_mem`: `K = 1 + 3^d`, `N = 21^d`, `m = 1`.

The count `N = 21^d` comes from disjointness: the partition cubes near a partition cube of scale
`n` and of scale at least `n - 1` are disjoint and lie in the box of side `7 · 3^n` around it.
-/

open LatticeProb.Percolation
open scoped Classical

namespace Rigidity.Percolation

variable {d : ℕ}

/-- Two triadic cubes are near when they contain vertices at sup-distance at most one. -/
def TriadicCube.Near (Q Q' : TriadicCube d) : Prop :=
  ∃ a ∈ Q.vertices, ∃ b ∈ Q'.vertices, ∀ i, |a i - b i| ≤ 1

theorem TriadicCube.Near.symm {Q Q' : TriadicCube d} (h : Q.Near Q') : Q'.Near Q := by
  obtain ⟨a, ha, b, hb, hab⟩ := h
  exact ⟨b, hb, a, ha, fun i => by rw [abs_sub_comm]; exact hab i⟩

theorem TriadicCube.near_self_of_mem {Q : TriadicCube d} {x : Vertex d} (hx : x ∈ Q.vertices) :
    Q.Near Q :=
  ⟨x, hx, x, hx, fun i => by simp⟩

/-- The integer cube of side `7 · 3^n` around a triadic cube of scale `n`. -/
def TriadicCube.nearBox (Q : TriadicCube d) : IntegerCube d where
  corner i := Q.toIntegerCube.corner i - 3 * (Q.toIntegerCube.size : ℤ)
  size := 7 * Q.toIntegerCube.size

theorem TriadicCube.card_nearBox (Q : TriadicCube d) :
    Q.nearBox.vertices.card = 7 ^ d * 3 ^ (Q.scale * d) := by
  rw [IntegerCube.card_vertices_eq]
  change (7 * 3 ^ Q.scale) ^ d = _
  rw [mul_pow, pow_mul]

/-- A triadic cube near `Q`, of scale at most one more, lies in the box around `Q`. -/
theorem TriadicCube.subset_nearBox {Q Q' : TriadicCube d} (h : Q.Near Q')
    (hsc : Q'.scale ≤ Q.scale + 1) : Q'.toIntegerCube.vertices ⊆ Q.nearBox.vertices := by
  obtain ⟨a, ha, b, hb, hab⟩ := h
  rw [← Q.mem_toIntegerCube_vertices, IntegerCube.mem_vertices] at ha
  rw [← Q'.mem_toIntegerCube_vertices, IntegerCube.mem_vertices] at hb
  have hs : Q'.toIntegerCube.size ≤ 3 * Q.toIntegerCube.size := by
    change 3 ^ Q'.scale ≤ 3 * 3 ^ Q.scale
    calc 3 ^ Q'.scale ≤ 3 ^ (Q.scale + 1) := Nat.pow_le_pow_right (by norm_num) hsc
      _ = 3 * 3 ^ Q.scale := by ring
  have hs' : (Q'.toIntegerCube.size : ℤ) ≤ 3 * (Q.toIntegerCube.size : ℤ) := by exact_mod_cast hs
  intro z hz
  rw [IntegerCube.mem_vertices] at hz
  rw [IntegerCube.mem_vertices]
  intro i
  have h1 := ha i
  have h2 := hb i
  have h3 := hz i
  have h4 := abs_le.1 (hab i)
  change Q.toIntegerCube.corner i - 3 * (Q.toIntegerCube.size : ℤ) ≤ z i ∧
    z i < Q.toIntegerCube.corner i - 3 * (Q.toIntegerCube.size : ℤ) +
      ((7 * Q.toIntegerCube.size : ℕ) : ℤ)
  push_cast
  constructor <;> omega

namespace CoarseData

variable {ω : Configuration d} (P : CoarseData d ω)

/-- **Counting neighbouring partition cubes.** At most `21^d` partition cubes are near a given
triadic cube of scale `n` and have scales between `n - 1` and `n + 1`. -/
theorem card_le_of_near (I : Finset (TriadicCube d)) (hI : ∀ Q ∈ I, ∃ x ∈ P.domain, P.part x = Q)
    {Q₀ : TriadicCube d} (hnear : ∀ Q ∈ I, Q.Near Q₀)
    (hsc : ∀ Q ∈ I, Q₀.scale ≤ Q.scale + 1 ∧ Q.scale ≤ Q₀.scale + 1) : I.card ≤ 21 ^ d := by
  have hdisj : (I : Set (TriadicCube d)).PairwiseDisjoint fun Q => Q.toIntegerCube.vertices := by
    intro Q hQ Q' hQ' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro y hy hy'
    obtain ⟨x, hx, rfl⟩ := hI Q hQ
    obtain ⟨x', hx', rfl⟩ := hI Q' hQ'
    have hy₁ : y ∈ (P.part x).vertices := (TriadicCube.mem_toIntegerCube_vertices _ _).1 hy
    have hy₂ : y ∈ (P.part x').vertices := (TriadicCube.mem_toIntegerCube_vertices _ _).1 hy'
    exact hne ((P.part_eq_of_mem x hx y hy₁).symm.trans (P.part_eq_of_mem x' hx' y hy₂))
  have hsub : I.biUnion (fun Q => Q.toIntegerCube.vertices) ⊆ Q₀.nearBox.vertices := by
    intro y hy
    obtain ⟨Q, hQ, hyQ⟩ := Finset.mem_biUnion.1 hy
    exact Q₀.subset_nearBox (hnear Q hQ).symm (hsc Q hQ).2 hyQ
  have hcard := (Finset.card_biUnion hdisj).symm.le.trans (Finset.card_le_card hsub)
  rw [Q₀.card_nearBox] at hcard
  have hlow : I.card * 3 ^ ((Q₀.scale - 1) * d) ≤
      ∑ Q ∈ I, Q.toIntegerCube.vertices.card := by
    calc I.card * 3 ^ ((Q₀.scale - 1) * d) = ∑ _Q ∈ I, 3 ^ ((Q₀.scale - 1) * d) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum fun Q hQ => ?_
    rw [IntegerCube.card_vertices_eq]
    change 3 ^ ((Q₀.scale - 1) * d) ≤ (3 ^ Q.scale) ^ d
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num)
      (Nat.mul_le_mul_right d (by have := (hsc Q hQ).1; omega))
  have hup : 7 ^ d * 3 ^ (Q₀.scale * d) ≤ 21 ^ d * 3 ^ ((Q₀.scale - 1) * d) := by
    calc 7 ^ d * 3 ^ (Q₀.scale * d) ≤ 7 ^ d * 3 ^ ((Q₀.scale - 1 + 1) * d) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num)
            (Nat.mul_le_mul_right d (by omega)))
      _ = 21 ^ d * 3 ^ ((Q₀.scale - 1) * d) := by
          rw [add_mul, one_mul, pow_add, show (21 : ℕ) = 7 * 3 by norm_num, mul_pow]
          ring
  have hpos : 0 < 3 ^ ((Q₀.scale - 1) * d) := by positivity
  exact Nat.le_of_mul_le_mul_right ((hlow.trans hcard).trans hup) hpos

/-- **Regions in neighbouring partition cubes** (Armstrong and Dario, proof of Lemma 3.2): if the
region of each vertex of the cluster meets the cluster only in partition cubes near its own, and
near partition cubes differ by at most one scale (Proposition 2.1 (ii)), the regions have bounded
overlap with constants `7^d`, `21^d` and `1`. -/
theorem regionOverlap_of_near
    (hreg : ∀ x ∈ P.cluster, ∀ z ∈ P.region x ∩ P.cluster, (P.part x).Near (P.part z))
    (hsc : ∀ x ∈ P.domain, ∀ y ∈ P.domain, (P.part x).Near (P.part y) →
      (P.part x).scale ≤ (P.part y).scale + 1) :
    P.RegionOverlap (7 ^ d) (21 ^ d) 1 where
  card_region_le x hx := by
    have hsub : P.region x ∩ P.cluster ⊆ (P.part x).nearBox.vertices := by
      intro z hz
      have hzC := (Finset.mem_inter.1 hz).2
      have hn := hreg x hx z hz
      refine (P.part x).subset_nearBox hn
        (hsc z (P.cluster_subset hzC) x (P.cluster_subset hx) hn.symm) ?_
      rw [TriadicCube.mem_toIntegerCube_vertices]
      exact P.mem_part z (P.cluster_subset hzC)
    exact (Finset.card_le_card hsub).trans (P.part x).card_nearBox.le
  scale_le x hx z hz :=
    hsc x (P.cluster_subset hx) z (P.cluster_subset (Finset.mem_inter.1 hz).2) (hreg x hx z hz)
  card_image_le z hz := by
    refine P.card_le_of_near _ (fun Q hQ => ?_) (Q₀ := P.part z) (fun Q hQ => ?_)
      (fun Q hQ => ?_)
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hQ
      exact ⟨x, P.cluster_subset (Finset.mem_filter.1 hx).1, rfl⟩
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hQ
      rw [Finset.mem_filter] at hx
      exact hreg x hx.1 z (Finset.mem_inter.2 ⟨hx.2, hz⟩)
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hQ
      rw [Finset.mem_filter] at hx
      have hn := hreg x hx.1 z (Finset.mem_inter.2 ⟨hx.2, hz⟩)
      exact ⟨hsc z (P.cluster_subset hz) x (P.cluster_subset hx.1) hn.symm,
        hsc x (P.cluster_subset hx.1) z (P.cluster_subset hz) hn⟩

private theorem near_abs_sub_le_one_of_adj {u v : Vertex d}
    (h : (nearestNeighborGraph d).Adj u v) (k : Fin d) : |u k - v k| ≤ 1 := by
  obtain ⟨l, hl | hl⟩ := h <;> subst hl <;> by_cases hkl : k = l <;> simp [LatticeProb.unit, hkl]

theorem near_of_mem_edgesAcross {q : Vertex d × Vertex d} (hq : q ∈ P.edgesAcross) :
    (P.part q.1).Near (P.part q.2) := by
  rw [edgesAcross, Finset.mem_filter, Finset.mem_product] at hq
  exact ⟨q.1, P.mem_part _ hq.1.1, q.2, P.mem_part _ hq.1.2, near_abs_sub_le_one_of_adj hq.2.1⟩

/-- **Pair regions in two neighbouring partition cubes** (Armstrong and Dario, proof of
Lemma 3.3): if the region of two lattice neighbours meets the cluster only in their two partition
cubes, and near partition cubes differ by at most one scale (Proposition 2.1 (ii)), the pair
regions have bounded overlap with constants `1 + 3^d`, `21^d` and `1`. -/
theorem pairOverlap_of_mem
    (hpair : ∀ q ∈ P.edgesAcross, ∀ z ∈ P.pairRegion q.1 q.2 ∩ P.cluster,
      z ∈ (P.part q.1).vertices ∨ z ∈ (P.part q.2).vertices)
    (hsc : ∀ x ∈ P.domain, ∀ y ∈ P.domain, (P.part x).Near (P.part y) →
      (P.part x).scale ≤ (P.part y).scale + 1) :
    P.PairOverlap (1 + 3 ^ d) (21 ^ d) 1 where
  card_pairRegion_le q hq := by
    have hq' := hq
    rw [edgesAcross, Finset.mem_filter, Finset.mem_product] at hq'
    have hsub : P.pairRegion q.1 q.2 ∩ P.cluster ⊆
        (P.part q.1).toIntegerCube.vertices ∪ (P.part q.2).toIntegerCube.vertices := by
      intro z hz
      rw [Finset.mem_union, TriadicCube.mem_toIntegerCube_vertices,
        TriadicCube.mem_toIntegerCube_vertices]
      exact hpair q hq z hz
    have hs := hsc q.2 hq'.1.2 q.1 hq'.1.1 (P.near_of_mem_edgesAcross hq).symm
    have h2 : (P.part q.2).toIntegerCube.vertices.card ≤
        3 ^ d * 3 ^ ((P.part q.1).scale * d) := by
      rw [IntegerCube.card_vertices_eq]
      change (3 ^ (P.part q.2).scale) ^ d ≤ _
      rw [← pow_mul, ← pow_add]
      refine Nat.pow_le_pow_right (by norm_num) ?_
      calc (P.part q.2).scale * d ≤ ((P.part q.1).scale + 1) * d := Nat.mul_le_mul_right d hs
        _ = d + (P.part q.1).scale * d := by ring
    have h1 : (P.part q.1).toIntegerCube.vertices.card = 3 ^ ((P.part q.1).scale * d) := by
      rw [IntegerCube.card_vertices_eq]
      change (3 ^ (P.part q.1).scale) ^ d = _
      rw [← pow_mul]
    calc (P.pairRegion q.1 q.2 ∩ P.cluster).card
        ≤ ((P.part q.1).toIntegerCube.vertices ∪ (P.part q.2).toIntegerCube.vertices).card :=
          Finset.card_le_card hsub
      _ ≤ (P.part q.1).toIntegerCube.vertices.card + (P.part q.2).toIntegerCube.vertices.card :=
          Finset.card_union_le _ _
      _ ≤ 3 ^ ((P.part q.1).scale * d) + 3 ^ d * 3 ^ ((P.part q.1).scale * d) := by
          rw [h1]; exact Nat.add_le_add_left h2 _
      _ = (1 + 3 ^ d) * 3 ^ ((P.part q.1).scale * d) := by ring
  scale_le q hq z hz := by
    have hq' := hq
    rw [edgesAcross, Finset.mem_filter, Finset.mem_product] at hq'
    rcases hpair q hq z hz with h | h
    · rw [P.part_eq_of_mem q.1 hq'.1.1 z h]
      omega
    · rw [P.part_eq_of_mem q.2 hq'.1.2 z h]
      exact hsc q.1 hq'.1.1 q.2 hq'.1.2 (P.near_of_mem_edgesAcross hq)
  card_image_le z hz := by
    have key : ∀ q ∈ P.edgesAcross.filter (fun q => z ∈ P.pairRegion q.1 q.2),
        (P.part q.1).Near (P.part z) := by
      intro q hq
      rw [Finset.mem_filter] at hq
      have hq' := hq.1
      rw [edgesAcross, Finset.mem_filter, Finset.mem_product] at hq'
      rcases hpair q hq.1 z (Finset.mem_inter.2 ⟨hq.2, hz⟩) with h | h
      · rw [P.part_eq_of_mem q.1 hq'.1.1 z h]
        exact TriadicCube.near_self_of_mem (P.mem_part q.1 hq'.1.1)
      · rw [P.part_eq_of_mem q.2 hq'.1.2 z h]
        exact P.near_of_mem_edgesAcross hq.1
    have hdom : ∀ q ∈ P.edgesAcross.filter (fun q => z ∈ P.pairRegion q.1 q.2),
        q.1 ∈ P.domain := by
      intro q hq
      have hq' := (Finset.mem_filter.1 hq).1
      rw [edgesAcross, Finset.mem_filter, Finset.mem_product] at hq'
      exact hq'.1.1
    refine P.card_le_of_near _ (fun Q hQ => ?_) (Q₀ := P.part z) (fun Q hQ => ?_)
      (fun Q hQ => ?_)
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hQ
      exact ⟨q.1, hdom q hq, rfl⟩
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hQ
      exact key q hq
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hQ
      have hn := key q hq
      exact ⟨hsc z (P.cluster_subset hz) q.1 (hdom q hq) hn.symm,
        hsc q.1 (hdom q hq) z (P.cluster_subset hz) hn⟩

end CoarseData

end Rigidity.Percolation
