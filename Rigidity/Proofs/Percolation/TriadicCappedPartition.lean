import Rigidity.Percolation.TriadicLocalizationGeometry
import Rigidity.Percolation.TriadicInfluenceBounds

/-!
# Capped stopping partitions and translations

Declaring every triadic cube of scale at least `n` good caps the stopping partition at scale `n`:
every lattice point lies in a unique maximal stopping cube, of scale at most `n`. A translation by
a vector of `3ⁿ ℤᵈ` moves the triadic cubes of scale at most `n` to triadic cubes, and the capped
partition moves with it when the good cubes of scale below `n` do. Where the capped partition
differs from the stopping partition of the original good cubes, a bad cube of scale at least `n`
lies nearby.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation

variable {d : ℕ}

/-- The triadic cube moved by a vector `c`. It represents the translate of the cube when the side
divides every coordinate of `c`. -/
def TriadicCube.shift (Q : TriadicCube d) (c : Vertex d) : TriadicCube d where
  scale := Q.scale
  index i := Q.index i + c i / Q.side

@[simp] theorem TriadicCube.scale_shift (Q : TriadicCube d) (c : Vertex d) :
    (Q.shift c).scale = Q.scale := rfl

@[simp] theorem TriadicCube.side_shift (Q : TriadicCube d) (c : Vertex d) :
    (Q.shift c).side = Q.side := rfl

/-- The side of a cube of scale at most `n` divides every coordinate of a vector of `3ⁿ ℤᵈ`. -/
theorem TriadicCube.side_dvd_of_scale_le {n : ℕ} {c : Vertex d} (hc : ∀ i, (3 : ℤ) ^ n ∣ c i)
    {Q : TriadicCube d} (hQ : Q.scale ≤ n) (i : Fin d) : Q.side ∣ c i :=
  (pow_dvd_pow 3 hQ).trans (hc i)

/-- Translating a point moves it into the shifted cube exactly when it was in the cube. -/
theorem TriadicCube.add_mem_shift_iff {Q : TriadicCube d} {c : Vertex d}
    (hc : ∀ i, Q.side ∣ c i) (x : Vertex d) :
    x + c ∈ (Q.shift c).vertices ↔ x ∈ Q.vertices := by
  have h : ∀ i, (x + c) i - (Q.shift c).side * (Q.shift c).index i =
      x i - Q.side * Q.index i := by
    intro i
    change x i + c i - Q.side * (Q.index i + c i / Q.side) = _
    rw [mul_add, Int.mul_ediv_cancel' (hc i)]
    ring
  show (∀ i, |2 * ((x + c) i - (Q.shift c).side * (Q.shift c).index i)| < (Q.shift c).side) ↔
    ∀ i, |2 * (x i - Q.side * Q.index i)| < Q.side
  refine forall_congr' fun i => ?_
  rw [h i]
  exact Iff.rfl

/-- Membership in the shifted cube. -/
theorem TriadicCube.mem_shift_iff {Q : TriadicCube d} {c : Vertex d}
    (hc : ∀ i, Q.side ∣ c i) (y : Vertex d) :
    y ∈ (Q.shift c).vertices ↔ y - c ∈ Q.vertices := by
  rw [← add_mem_shift_iff hc (y - c), sub_add_cancel]

/-- Shifting back undoes a shift. -/
theorem TriadicCube.shift_shift_neg {Q : TriadicCube d} {c : Vertex d}
    (hc : ∀ i, Q.side ∣ c i) : (Q.shift c).shift (-c) = Q := by
  apply TriadicCube.ext
  · rfl
  funext i
  change Q.index i + c i / Q.side + (-c i) / Q.side = Q.index i
  rw [Int.neg_ediv_of_dvd (hc i)]
  ring

/-- Shifting forward undoes a backward shift. -/
theorem TriadicCube.shift_neg_shift {Q : TriadicCube d} {c : Vertex d}
    (hc : ∀ i, Q.side ∣ c i) : (Q.shift (-c)).shift c = Q := by
  have hc' : ∀ i, Q.side ∣ (-c) i := fun i => (dvd_neg.2 (hc i))
  simpa only [neg_neg] using shift_shift_neg hc'

/-- The shifted cube of a shifted cube's parent. -/
theorem TriadicCube.parent_shift {Q : TriadicCube d} {c : Vertex d}
    (hc : ∀ i, Q.parent.side ∣ c i) : (Q.shift c).parent = Q.parent.shift c := by
  apply TriadicCube.ext
  · rfl
  funext i
  obtain ⟨t, ht⟩ := hc i
  have hs := Q.side_pos
  rw [side_parent] at ht
  change (Q.index i + c i / Q.side + 1) / 3 = (Q.index i + 1) / 3 + c i / Q.parent.side
  rw [side_parent, ht, show 3 * Q.side * t = Q.side * (3 * t) by ring,
    Int.mul_ediv_cancel_left _ hs.ne', show Q.side * (3 * t) = (3 * Q.side) * t by ring,
    Int.mul_ediv_cancel_left _ (by positivity),
    show Q.index i + 3 * t + 1 = Q.index i + 1 + t * 3 by ring,
    Int.add_mul_ediv_right _ _ (by norm_num)]

/-- The side of a child is a third of the side of a positive-scale cube. -/
theorem TriadicCube.three_mul_side_child (Q : TriadicCube d) (digits : Fin d → Fin 3)
    (hQ : 0 < Q.scale) : 3 * (Q.child digits).side = Q.side := by
  rw [← side_parent, child_parent _ _ hQ]

/-- Children of a shifted cube are the shifted children. -/
theorem TriadicCube.child_shift {Q : TriadicCube d} {c : Vertex d} (hQ : 0 < Q.scale)
    (hc : ∀ i, Q.side ∣ c i) (digits : Fin d → Fin 3) :
    (Q.shift c).child digits = (Q.child digits).shift c := by
  apply TriadicCube.ext
  · rfl
  funext i
  obtain ⟨t, ht⟩ := hc i
  have hside := Q.three_mul_side_child digits hQ
  have hs := (Q.child digits).side_pos
  change 3 * (Q.index i + c i / Q.side) + (digits i : ℤ) - 1 =
    3 * Q.index i + (digits i : ℤ) - 1 + c i / (Q.child digits).side
  rw [ht, Int.mul_ediv_cancel_left _ Q.side_pos.ne', ← hside,
    show 3 * (Q.child digits).side * t = (Q.child digits).side * (3 * t) by ring,
    Int.mul_ediv_cancel_left _ hs.ne']
  ring

/-- Shifts preserve inclusions between cubes whose sides divide the vector. -/
theorem TriadicCube.shift_vertices_subset_iff {Q R : TriadicCube d} {c : Vertex d}
    (hQ : ∀ i, Q.side ∣ c i) (hR : ∀ i, R.side ∣ c i) :
    (Q.shift c).vertices ⊆ (R.shift c).vertices ↔ Q.vertices ⊆ R.vertices := by
  constructor
  · intro h x hx
    exact (add_mem_shift_iff hR x).1 (h ((add_mem_shift_iff hQ x).2 hx))
  · intro h y hy
    exact (mem_shift_iff hR y).2 (h ((mem_shift_iff hQ y).1 hy))

/-- Influence steps move with shifts. -/
theorem TriadicCube.influenceStep_shift_iff {Q R : TriadicCube d} {c : Vertex d}
    (hQ : ∀ i, Q.side ∣ c i) (hR : ∀ i, R.parent.side ∣ c i) :
    (Q.shift c).InfluenceStep (R.shift c) ↔ Q.InfluenceStep R := by
  unfold InfluenceStep
  rw [parent_shift hR]
  constructor
  · rintro ⟨hscale, a, ha, b, hb, hab⟩
    refine ⟨hscale, a - c, (mem_shift_iff hQ a).1 ha, b - c, (mem_shift_iff hR b).1 hb, ?_⟩
    intro i
    simpa only [Pi.sub_apply, sub_sub_sub_cancel_right] using hab i
  · rintro ⟨hscale, a, ha, b, hb, hab⟩
    refine ⟨hscale, a + c, (add_mem_shift_iff hQ a).2 ha, b + c,
      (add_mem_shift_iff hR b).2 hb, ?_⟩
    intro i
    simpa only [Pi.add_apply, add_sub_add_right_eq_sub] using hab i

/-- Influence between cubes of scale below `n` moves with a shift in `3ⁿ ℤᵈ`. -/
theorem TriadicCube.shift_mem_influence_of_mem {n : ℕ} {c : Vertex d}
    (hc : ∀ i, (3 : ℤ) ^ n ∣ c i) {Q R : TriadicCube d} (hR : R.scale < n)
    (h : R ∈ Q.influence) : R.shift c ∈ (Q.shift c).influence := by
  induction h with
  | refl => exact mem_influence_self _
  | @tail S T hQS hST ih =>
    have hS : S.scale < n := by
      have := hST.1
      omega
    refine Relation.ReflTransGen.tail (ih hS) ?_
    refine (influenceStep_shift_iff (side_dvd_of_scale_le hc hS.le) ?_).2 hST
    exact side_dvd_of_scale_le hc (by simp only [parent]; omega)

/-- Influence between cubes of scale below `n` is invariant under shifts in `3ⁿ ℤᵈ`. -/
theorem TriadicCube.shift_mem_influence_iff {n : ℕ} {c : Vertex d}
    (hc : ∀ i, (3 : ℤ) ^ n ∣ c i) {Q R : TriadicCube d} (hR : R.scale < n) :
    R.shift c ∈ (Q.shift c).influence ↔ R ∈ Q.influence := by
  refine ⟨fun h => ?_, shift_mem_influence_of_mem hc hR⟩
  have hc' : ∀ i, (3 : ℤ) ^ n ∣ (-c) i := fun i => dvd_neg.2 (hc i)
  have h1 : (Q.shift c).scale ≤ (R.shift c).scale := scale_le_of_mem_influence h
  have hQ : Q.scale < n := lt_of_le_of_lt h1 hR
  have h' := shift_mem_influence_of_mem hc' (Q := Q.shift c) (R := R.shift c) hR h
  rwa [shift_shift_neg (side_dvd_of_scale_le hc hR.le),
    shift_shift_neg (side_dvd_of_scale_le hc hQ.le)] at h'

/-- The good cubes with every cube of scale at least `n` declared good. -/
def TriadicCube.capped (G : Set (TriadicCube d)) (n : ℕ) : Set (TriadicCube d) :=
  G ∪ {Q | n ≤ Q.scale}

theorem TriadicCube.subset_capped (G : Set (TriadicCube d)) (n : ℕ) : G ⊆ capped G n :=
  Set.subset_union_left

theorem TriadicCube.mem_capped_of_le {G : Set (TriadicCube d)} {n : ℕ} {Q : TriadicCube d}
    (hQ : n ≤ Q.scale) : Q ∈ capped G n :=
  Or.inr hQ

/-- Cubes of scale at least `n` are stable for a family containing them all. -/
theorem TriadicCube.mem_stableGood_of_le_scale {G : Set (TriadicCube d)} {n : ℕ}
    (hbig : ∀ R : TriadicCube d, n ≤ R.scale → R ∈ G) {Q : TriadicCube d}
    (hQ : n ≤ Q.scale) : Q ∈ stableGood G := fun R hR =>
  hbig R (hQ.trans (scale_le_of_mem_influence hR))

/-- Stopping cubes of a family containing all cubes of scale at least `n` have scale at most
`n`. -/
theorem TriadicCube.IsStopping.scale_le {G : Set (TriadicCube d)} {n : ℕ}
    (hbig : ∀ R : TriadicCube d, n ≤ R.scale → R ∈ G) {Q : TriadicCube d}
    (hQ : Q.IsStopping G) : Q.scale ≤ n := by
  by_contra hlt
  replace hlt := Nat.lt_of_not_le hlt
  rcases hQ.2 with h0 | ⟨digits, hchild⟩
  · omega
  · exact hchild (mem_stableGood_of_le_scale hbig (by simp only [child]; omega))

section Shift

variable {G G' : Set (TriadicCube d)} {n : ℕ} {c : Vertex d}

/-- Stability moves with a shift in `3ⁿ ℤᵈ` when the good cubes of scale below `n` do and all
cubes of scale at least `n` are good. -/
theorem TriadicCube.shift_mem_stableGood_iff (hc : ∀ i, (3 : ℤ) ^ n ∣ c i)
    (hG : ∀ R : TriadicCube d, R.scale < n → (R.shift c ∈ G' ↔ R ∈ G))
    (hbig : ∀ R : TriadicCube d, n ≤ R.scale → R ∈ G)
    (hbig' : ∀ R : TriadicCube d, n ≤ R.scale → R ∈ G') (Q : TriadicCube d) :
    Q.shift c ∈ stableGood G' ↔ Q ∈ stableGood G := by
  constructor
  · intro h R hR
    by_cases hn : n ≤ R.scale
    · exact hbig R hn
    · replace hn := Nat.lt_of_not_le hn
      exact (hG R hn).1 (h ((shift_mem_influence_iff hc hn).2 hR))
  · intro h S hS
    by_cases hn : n ≤ S.scale
    · exact hbig' S hn
    · replace hn := Nat.lt_of_not_le hn
      have hS' : S = (S.shift (-c)).shift c :=
        (shift_neg_shift (side_dvd_of_scale_le hc hn.le)).symm
      rw [hS'] at hS ⊢
      exact (hG (S.shift (-c)) hn).2 (h ((shift_mem_influence_iff hc (R := S.shift (-c)) hn).1 hS))

/-- Stopping cubes move with a shift in `3ⁿ ℤᵈ`. -/
theorem TriadicCube.shift_isStopping_iff (hc : ∀ i, (3 : ℤ) ^ n ∣ c i)
    (hG : ∀ R : TriadicCube d, R.scale < n → (R.shift c ∈ G' ↔ R ∈ G))
    (hbig : ∀ R : TriadicCube d, n ≤ R.scale → R ∈ G)
    (hbig' : ∀ R : TriadicCube d, n ≤ R.scale → R ∈ G') {Q : TriadicCube d}
    (hQ : Q.scale ≤ n) : (Q.shift c).IsStopping G' ↔ Q.IsStopping G := by
  have hst := shift_mem_stableGood_iff hc hG hbig hbig'
  have hdiv := side_dvd_of_scale_le hc hQ
  unfold IsStopping
  rw [hst Q, scale_shift]
  by_cases h0 : Q.scale = 0
  · simp only [h0, true_or, and_true]
  · have hpos : 0 < Q.scale := Nat.pos_of_ne_zero h0
    simp only [h0, false_or]
    refine and_congr Iff.rfl ⟨fun ⟨digits, hd⟩ => ⟨digits, fun h => hd ?_⟩,
      fun ⟨digits, hd⟩ => ⟨digits, fun h => hd ?_⟩⟩
    · rw [child_shift hpos hdiv, hst]
      exact h
    · rw [child_shift hpos hdiv, hst] at h
      exact h

/-- Maximal stopping cubes move with a shift in `3ⁿ ℤᵈ`. -/
theorem TriadicCube.shift_isMaximalStopping_iff (hc : ∀ i, (3 : ℤ) ^ n ∣ c i)
    (hG : ∀ R : TriadicCube d, R.scale < n → (R.shift c ∈ G' ↔ R ∈ G))
    (hbig : ∀ R : TriadicCube d, n ≤ R.scale → R ∈ G)
    (hbig' : ∀ R : TriadicCube d, n ≤ R.scale → R ∈ G') {Q : TriadicCube d}
    (hQ : Q.scale ≤ n) : (Q.shift c).IsMaximalStopping G' ↔ Q.IsMaximalStopping G := by
  have hstop := fun {R : TriadicCube d} (hR : R.scale ≤ n) =>
    shift_isStopping_iff hc hG hbig hbig' hR
  have hdiv := side_dvd_of_scale_le hc hQ
  unfold IsMaximalStopping
  rw [hstop hQ, scale_shift]
  refine and_congr Iff.rfl ⟨fun h R hR hsub => ?_, fun h S hS hsub => ?_⟩
  · have hRn := hR.scale_le hbig
    have hRdiv := side_dvd_of_scale_le hc hRn
    exact h (R.shift c) ((hstop hRn).2 hR) ((shift_vertices_subset_iff hdiv hRdiv).2 hsub)
  · have hSn := hS.scale_le hbig'
    have hSdiv := side_dvd_of_scale_le hc hSn
    have hS' : S = (S.shift (-c)).shift c := (shift_neg_shift hSdiv).symm
    rw [hS'] at hS hsub ⊢
    have hRdiv : ∀ i, (S.shift (-c)).side ∣ c i := hSdiv
    exact h (S.shift (-c)) ((hstop (R := S.shift (-c)) hSn).1 hS) ((shift_vertices_subset_iff hdiv hRdiv).1 hsub)

end Shift

/-- The unique maximal stopping cube of the capped family at a point. -/
theorem TriadicCube.existsUnique_isMaximalStopping_capped (G : Set (TriadicCube d)) (n : ℕ)
    (x : Vertex d) : ∃! Q : TriadicCube d, x ∈ Q.vertices ∧ Q.IsMaximalStopping (capped G n) := by
  obtain ⟨Q, hQ, -⟩ := existsUnique_mem d n x
  exact existsUnique_isMaximalStopping_of_mem_stableGood
    (mem_stableGood_of_le_scale (fun R hR => mem_capped_of_le hR) hQ.1.ge) hQ.2

/-- The cube of the capped partition at a point. -/
noncomputable def TriadicCube.cappedCube (G : Set (TriadicCube d)) (n : ℕ) (x : Vertex d) :
    TriadicCube d :=
  (existsUnique_isMaximalStopping_capped G n x).exists.choose

theorem TriadicCube.cappedCube_spec (G : Set (TriadicCube d)) (n : ℕ) (x : Vertex d) :
    x ∈ (cappedCube G n x).vertices ∧ (cappedCube G n x).IsMaximalStopping (capped G n) :=
  (existsUnique_isMaximalStopping_capped G n x).exists.choose_spec

theorem TriadicCube.cappedCube_eq {G : Set (TriadicCube d)} {n : ℕ} {x : Vertex d}
    {Q : TriadicCube d} (hx : x ∈ Q.vertices) (hQ : Q.IsMaximalStopping (capped G n)) :
    cappedCube G n x = Q :=
  eq_of_isMaximalStopping_of_mem (cappedCube_spec G n x).2 hQ (cappedCube_spec G n x).1 hx

/-- The cubes of the capped partition have scale at most `n`. -/
theorem TriadicCube.scale_cappedCube_le (G : Set (TriadicCube d)) (n : ℕ) (x : Vertex d) :
    (cappedCube G n x).scale ≤ n :=
  (cappedCube_spec G n x).2.1.scale_le fun _ hR => mem_capped_of_le hR

/-- **Translation of the capped partition.** If the good cubes of scale below `n` move with a
translation by a vector of `3ⁿ ℤᵈ`, so does the capped partition. -/
theorem TriadicCube.cappedCube_add {G G' : Set (TriadicCube d)} {n : ℕ} {c : Vertex d}
    (hc : ∀ i, (3 : ℤ) ^ n ∣ c i)
    (hG : ∀ R : TriadicCube d, R.scale < n → (R.shift c ∈ G' ↔ R ∈ G)) (x : Vertex d) :
    cappedCube G' n (x + c) = (cappedCube G n x).shift c := by
  have hcap : ∀ R : TriadicCube d, R.scale < n → (R.shift c ∈ capped G' n ↔ R ∈ capped G n) := by
    intro R hR
    have h1 : ¬ n ≤ (R.shift c).scale := by simp only [scale_shift]; omega
    have h2 : ¬ n ≤ R.scale := by omega
    simp only [capped, Set.mem_union, Set.mem_setOf_eq, h1, h2, or_false]
    exact hG R hR
  have hQ := cappedCube_spec G n x
  have hle := scale_cappedCube_le G n x
  apply cappedCube_eq ((add_mem_shift_iff (side_dvd_of_scale_le hc hle) x).2 hQ.1)
  exact (shift_isMaximalStopping_iff hc hcap (fun _ hR => mem_capped_of_le hR)
    (fun _ hR => mem_capped_of_le hR) hle).2 hQ.2

/-- **Discrepancy with the capped partition.** If a maximal stopping cube of `G` at `x` differs
from the capped cube, some cube of scale at least `n` which is not in `G` lies within twelve of its
side lengths from `x`. -/
theorem TriadicCube.exists_bad_of_ne_cappedCube {G : Set (TriadicCube d)} {n : ℕ} {x : Vertex d}
    {Q : TriadicCube d} (hx : x ∈ Q.vertices) (hQ : Q.IsMaximalStopping G)
    (hne : Q ≠ cappedCube G n x) :
    ∃ T : TriadicCube d, T ∉ G ∧ n ≤ T.scale ∧
      ∀ y ∈ T.vertices, ∀ i, |x i - y i| < 12 * T.side := by
  obtain ⟨T, hTG, hTH, hnear⟩ := exists_new_good_near_of_stopping_ne (subset_capped G n) hx
    (cappedCube_spec G n x).1 hQ (cappedCube_spec G n x).2 hne
  rcases hTH with h | h
  · exact absurd h hTG
  · exact ⟨T, hTG, h, hnear⟩

end Rigidity.Percolation
