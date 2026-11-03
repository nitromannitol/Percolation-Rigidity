import Rigidity.Steps.Section5.LongPathRenormalized
import Rigidity.Proofs.Section5.Peierls

/-!
# Proposition 5.24: the walk steps

This file proves the steps `OneDependentWalkStep` and `SiteWalkStep` of Proposition 5.24
(`Rigidity/Steps/Section5/LongPathRenormalized.lean`; corrected draft L2280-2339, step
`step:5.24-crossings`): outside an event of
probability `C exp(-c N₀)`, every lazy walk of `ℤ²` from the origin to a site `z` with
`|z|₁ ≥ N₀` visits at least `|z|₁ / 8` distinct sites of the infinite open clusters. Both follow
from one Peierls bound, valid for every `1`-dependent site field (for the `ℓ^∞` distance) whose
sites are closed with probability at most `ε₀ = 144⁻¹⁸`; for Bernoulli site percolation the
exceptional event is the complement of a measurable increasing event.

**Enclosure.** A site `x` is enclosed by a set `K` (`enclosedBy`) when its nearest-neighbour
component in `ℤ² ∖ K` is finite. A site outside the infinite open clusters is enclosed by a
closed `*`-cluster (`exists_enclosedBy_of_not_inInfinite`): a closed site by its own, an open
site `x` by the closed `*`-cluster of the outer endpoints of the component `Γ` of the dual
boundary graph of its open cluster used in `exists_closedStarWalk`, since the parity of the
crossings of `Γ` by a horizontal ray is `1` at `x`, changes only across `Γ`, and vanishes off
a box. A site of the infinite open clusters is enclosed by no closed set, and a site enclosed by
`K` with a nearest neighbour that is not lies in `K`. Two closed `*`-clusters `K, K'` with a site
of `K ∖ K'` enclosed by `K'` have nested enclosures (`enclosedBy_starCluster_subset`): a
diagonal step of `K` turns about a corner outside `K'`. Hence a nearest-neighbour walk of sites
outside the infinite open clusters stays enclosed by a single closed `*`-cluster
(`exists_enclosedBy_step`), which contains the first and last sites of the walk when these have
a neighbour in an infinite open cluster.

**The `*`-path** (`longStarPath_of_walk`). Let `w` be a lazy walk from the origin to `z` and
`M = |z|₁`. Replacing each excursion of `w` outside the infinite open clusters by a `*`-path of
the closed `*`-cluster enclosing it, and the initial excursion by a `*`-path from the first site
`(j, 0)` of the enclosing cluster on the horizontal ray from the origin, gives a self-avoiding
`*`-path from `(j, 0)` of length `L ≥ max(j, M / 4)` whose open sites are sites of the infinite
open clusters visited by `w` (when `4 j > M`, the `*`-path joins `(j, 0)` to a site of the
cluster on the opposite ray). If `w` visits fewer than `M / 8` such sites, at most `L / 2` sites
of the `*`-path are open.

**Counting.** There are at most `(L + 1) 9ᴸ` such `*`-paths of length `L`, at most `2ᴸ⁺¹` sets
of their sites containing the closed ones, and at least `L / 18` sites of such a set at pairwise
`ℓ^∞` distance at least `2`, all closed with probability at most `ε₀^{L/18} = 144⁻ᴸ`
(`measure_countP_le`). Summing over `L ≥ N₀ / 4` gives `4 exp(-(log 2 / 4) N₀)`.
-/

open MeasureTheory ProbabilityTheory LatticeProb.Percolation Rigidity.Steps.Section5

noncomputable section

open Classical

namespace Rigidity.Proofs.Section5

/-! ### Enclosure by a set of sites -/

/-- The nearest-neighbour graph of `ℤ²` on the sites outside `K`. -/
def avoidGraph (K : Set PlanarCarrier) : SimpleGraph PlanarCarrier where
  Adj a b := |a.1 - b.1| + |a.2 - b.2| = 1 ∧ a ∉ K ∧ b ∉ K
  symm := ⟨fun a b h => ⟨by rw [abs_sub_comm b.1, abs_sub_comm b.2]; exact h.1, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun a h => by simp at h⟩

/-- The sites enclosed by `K`: those whose nearest-neighbour component in `ℤ² ∖ K` is finite.
They include the sites of `K`. -/
def enclosedBy (K : Set PlanarCarrier) : Set PlanarCarrier :=
  {x | {y | (avoidGraph K).Reachable x y}.Finite}

/-- The closed `*`-cluster of the site `c`. -/
def starCluster (η : PlanarCarrier → Bool) (c : PlanarCarrier) : Set PlanarCarrier :=
  {d | (closedStarGraph η).Reachable c d}

/-- The `*`-graph on the sites of `A`: two distinct sites of `A` are adjacent when they are at
`ℓ^∞` distance `1`. -/
def starGraphOn (A : Set PlanarCarrier) : SimpleGraph PlanarCarrier where
  Adj s t := s ≠ t ∧ |s.1 - t.1| ≤ 1 ∧ |s.2 - t.2| ≤ 1 ∧ s ∈ A ∧ t ∈ A
  symm := ⟨fun s t h => ⟨h.1.symm, by rw [abs_sub_comm]; exact h.2.1,
    by rw [abs_sub_comm]; exact h.2.2.1, h.2.2.2.2, h.2.2.2.1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem mem_enclosedBy_of_mem {K : Set PlanarCarrier} {x : PlanarCarrier} (hx : x ∈ K) :
    x ∈ enclosedBy K := by
  refine (Set.finite_singleton x).subset fun y hy => ?_
  obtain ⟨p⟩ := hy
  cases p with
  | nil => exact Set.mem_singleton _
  | cons h _ => exact absurd hx h.2.1

/-- A site of an infinite open cluster is enclosed by no set of closed sites. -/
theorem notMem_enclosedBy_of_inInfinite {η : PlanarCarrier → Bool} {K : Set PlanarCarrier}
    (hK : ∀ s ∈ K, η s = false) {g : PlanarCarrier} (hg : InInfiniteSiteCluster η g) :
    g ∉ enclosedBy K := fun hfin => by
  have hle : siteOpenGraph η ≤ avoidGraph K := fun a b h =>
    ⟨h.1, fun ha => absurd ((hK a ha).symm.trans h.2.1) (by decide),
      fun hb => absurd ((hK b hb).symm.trans h.2.2) (by decide)⟩
  exact hg.2 (hfin.subset fun w hw => SimpleGraph.Reachable.mono hle hw)

/-- A site enclosed by `K` with a nearest neighbour not enclosed by `K` lies in `K`. -/
theorem mem_of_mem_enclosedBy_of_adj {K : Set PlanarCarrier} {x y : PlanarCarrier}
    (hx : x ∈ enclosedBy K) (hy : y ∉ enclosedBy K) (hxy : |x.1 - y.1| + |x.2 - y.2| = 1) :
    x ∈ K := by
  by_contra hxK
  have hyK : y ∉ K := fun h => hy (mem_enclosedBy_of_mem h)
  have hr : (avoidGraph K).Reachable x y := SimpleGraph.Adj.reachable ⟨hxy, hxK, hyK⟩
  exact hy (hx.subset fun z hz => hr.trans hz)

/-- Every ray of `ℤ²` from a site enclosed by `K` meets `K`. -/
theorem exists_mem_ray {K : Set PlanarCarrier} {x : PlanarCarrier} (hx : x ∈ enclosedBy K)
    {d₁ d₂ : ℤ} (hd : |d₁| + |d₂| = 1) : ∃ j : ℕ, (x.1 + j * d₁, x.2 + j * d₂) ∈ K := by
  by_contra h
  push Not at h
  have hreach : ∀ j : ℕ, (avoidGraph K).Reachable x (x.1 + j * d₁, x.2 + j * d₂) := by
    intro j
    induction j with
    | zero =>
      simp only [Nat.cast_zero, zero_mul, add_zero]
      exact SimpleGraph.Reachable.refl _
    | succ j ih =>
      refine ih.trans (SimpleGraph.Adj.reachable ⟨?_, h j, h (j + 1)⟩)
      have e1 : x.1 + (j : ℤ) * d₁ - (x.1 + ((j + 1 : ℕ) : ℤ) * d₁) = -d₁ := by push_cast; ring
      have e2 : x.2 + (j : ℤ) * d₂ - (x.2 + ((j + 1 : ℕ) : ℤ) * d₂) = -d₂ := by push_cast; ring
      simp only [e1, e2, abs_neg]
      exact hd
  have hinj : Function.Injective fun j : ℕ => ((x.1 + j * d₁, x.2 + j * d₂) : PlanarCarrier) := by
    intro i j hij
    simp only [Prod.mk.injEq, add_right_inj] at hij
    by_contra hne
    have hne' : (i : ℤ) - j ≠ 0 := by omega
    have h1 : ((i : ℤ) - j) * d₁ = 0 := by rw [sub_mul]; linarith [hij.1]
    have h2 : ((i : ℤ) - j) * d₂ = 0 := by rw [sub_mul]; linarith [hij.2]
    have h1' := (mul_eq_zero.mp h1).resolve_left hne'
    have h2' := (mul_eq_zero.mp h2).resolve_left hne'
    simp [h1', h2'] at hd
  exact Set.infinite_of_injective_forall_mem hinj hreach hx

theorem exists_mem_right {K : Set PlanarCarrier} {x : PlanarCarrier} (hx : x ∈ enclosedBy K) :
    ∃ j : ℕ, ((x.1 + j, x.2) : PlanarCarrier) ∈ K := by
  obtain ⟨j, hj⟩ := exists_mem_ray hx (d₁ := 1) (d₂ := 0) (by norm_num)
  exact ⟨j, by simpa using hj⟩

theorem exists_mem_left {K : Set PlanarCarrier} {x : PlanarCarrier} (hx : x ∈ enclosedBy K) :
    ∃ j : ℕ, ((x.1 - j, x.2) : PlanarCarrier) ∈ K := by
  obtain ⟨j, hj⟩ := exists_mem_ray hx (d₁ := -1) (d₂ := 0) (by norm_num)
  exact ⟨j, by simpa [sub_eq_add_neg] using hj⟩

theorem exists_mem_up {K : Set PlanarCarrier} {x : PlanarCarrier} (hx : x ∈ enclosedBy K) :
    ∃ j : ℕ, ((x.1, x.2 + j) : PlanarCarrier) ∈ K := by
  obtain ⟨j, hj⟩ := exists_mem_ray hx (d₁ := 0) (d₂ := 1) (by norm_num)
  exact ⟨j, by simpa using hj⟩

theorem exists_mem_down {K : Set PlanarCarrier} {x : PlanarCarrier} (hx : x ∈ enclosedBy K) :
    ∃ j : ℕ, ((x.1, x.2 - j) : PlanarCarrier) ∈ K := by
  obtain ⟨j, hj⟩ := exists_mem_ray hx (d₁ := 0) (d₂ := -1) (by norm_num)
  exact ⟨j, by simpa [sub_eq_add_neg] using hj⟩

/-- A set enclosing `z` has a site `k` with `|z|₁ ≤ 2 |k.1|` or `|z|₁ ≤ 2 |k.2|`. -/
theorem exists_mem_far {K : Set PlanarCarrier} {z : PlanarCarrier} (hz : z ∈ enclosedBy K) :
    ∃ k ∈ K, |z.1| + |z.2| ≤ 2 * |k.1| ∨ |z.1| + |z.2| ≤ 2 * |k.2| := by
  rcases le_total |z.2| |z.1| with h | h
  · rcases le_total 0 z.1 with h1 | h1
    · obtain ⟨j, hj⟩ := exists_mem_right hz
      refine ⟨_, hj, Or.inl ?_⟩
      show _ ≤ 2 * |z.1 + (j : ℤ)|
      rw [abs_of_nonneg h1] at h ⊢
      rw [abs_of_nonneg (show 0 ≤ z.1 + (j : ℤ) by omega)]
      omega
    · obtain ⟨j, hj⟩ := exists_mem_left hz
      refine ⟨_, hj, Or.inl ?_⟩
      show _ ≤ 2 * |z.1 - (j : ℤ)|
      rw [abs_of_nonpos h1] at h ⊢
      rw [abs_of_nonpos (show z.1 - (j : ℤ) ≤ 0 by omega)]
      omega
  · rcases le_total 0 z.2 with h2 | h2
    · obtain ⟨j, hj⟩ := exists_mem_up hz
      refine ⟨_, hj, Or.inr ?_⟩
      show _ ≤ 2 * |z.2 + (j : ℤ)|
      rw [abs_of_nonneg h2] at h ⊢
      rw [abs_of_nonneg (show 0 ≤ z.2 + (j : ℤ) by omega)]
      omega
    · obtain ⟨j, hj⟩ := exists_mem_down hz
      refine ⟨_, hj, Or.inr ?_⟩
      show _ ≤ 2 * |z.2 - (j : ℤ)|
      rw [abs_of_nonpos h2] at h ⊢
      rw [abs_of_nonpos (show z.2 - (j : ℤ) ≤ 0 by omega)]
      omega

/-! ### Closed `*`-clusters -/

theorem mem_starCluster_self (η : PlanarCarrier → Bool) (c : PlanarCarrier) :
    c ∈ starCluster η c :=
  SimpleGraph.Reachable.refl c

theorem starCluster_eq {η : PlanarCarrier → Bool} {c c' d : PlanarCarrier}
    (h : d ∈ starCluster η c) (h' : d ∈ starCluster η c') :
    starCluster η c = starCluster η c' := by
  ext y
  exact ⟨fun hy => SimpleGraph.Reachable.trans h' (h.symm.trans hy),
    fun hy => SimpleGraph.Reachable.trans h (SimpleGraph.Reachable.trans h'.symm hy)⟩

theorem closed_of_mem_starCluster {η : PlanarCarrier → Bool} {c d : PlanarCarrier}
    (hc : η c = false) (h : d ∈ starCluster η c) : η d = false := by
  have h' := (SimpleGraph.reachable_iff_reflTransGen _ _).mp h
  clear h
  induction h' with
  | refl => exact hc
  | tail _ hadj _ => exact hadj.2.2.2.2

theorem closedStarGraph_le_starGraphOn {η : PlanarCarrier → Bool} {A : Set PlanarCarrier}
    (hA : ∀ s, η s = false → s ∈ A) : closedStarGraph η ≤ starGraphOn A :=
  fun s t h => ⟨h.1, h.2.1, h.2.2.1, hA s h.2.2.2.1, hA t h.2.2.2.2⟩

theorem reachable_of_mem_starCluster {η : PlanarCarrier → Bool} {A : Set PlanarCarrier}
    (hA : ∀ s, η s = false → s ∈ A) {c r a : PlanarCarrier} (hr : r ∈ starCluster η c)
    (ha : a ∈ starCluster η c) : (starGraphOn A).Reachable r a :=
  SimpleGraph.Reachable.mono (closedStarGraph_le_starGraphOn hA)
    (SimpleGraph.Reachable.trans (SimpleGraph.Reachable.symm hr) ha)

theorem ne_of_nn {a b : PlanarCarrier} (hab : |a.1 - b.1| + |a.2 - b.2| = 1) : a ≠ b := by
  rintro rfl
  simp at hab

theorem abs_fst_le_one_of_nn {a b : PlanarCarrier} (hab : |a.1 - b.1| + |a.2 - b.2| = 1) :
    |a.1 - b.1| ≤ 1 := by
  linarith [abs_nonneg (a.2 - b.2)]

theorem abs_snd_le_one_of_nn {a b : PlanarCarrier} (hab : |a.1 - b.1| + |a.2 - b.2| = 1) :
    |a.2 - b.2| ≤ 1 := by
  linarith [abs_nonneg (a.1 - b.1)]

/-- Two nearest-neighbour closed sites lie in the same closed `*`-cluster. -/
theorem mem_starCluster_of_nn {η : PlanarCarrier → Bool} {c a b : PlanarCarrier}
    (hc : η c = false) (ha : a ∈ starCluster η c) (hb : η b = false)
    (hab : |a.1 - b.1| + |a.2 - b.2| = 1) : b ∈ starCluster η c :=
  SimpleGraph.Reachable.trans ha (SimpleGraph.Adj.reachable ⟨ne_of_nn hab,
    abs_fst_le_one_of_nn hab, abs_snd_le_one_of_nn hab, closed_of_mem_starCluster hc ha, hb⟩)

theorem abs_eq_one_of_diag {a b : ℤ} (h1 : |a| ≤ 1) (h2 : |b| ≤ 1) (hnn : |a| + |b| ≠ 1)
    (hne : a ≠ 0 ∨ b ≠ 0) : |a| = 1 ∧ |b| = 1 := by
  rcases abs_cases a with ⟨ea, _⟩ | ⟨ea, _⟩ <;> rcases abs_cases b with ⟨eb, _⟩ | ⟨eb, _⟩ <;>
    rw [ea, eb] at hnn ⊢ <;> rw [ea] at h1 <;> rw [eb] at h2 <;> omega

/-- **Nesting.** If a site `a` of the closed `*`-cluster `K` not in the closed `*`-cluster `K'`
is enclosed by `K'`, every site enclosed by `K` is enclosed by `K'`. -/
theorem enclosedBy_starCluster_subset {η : PlanarCarrier → Bool} {c c' a : PlanarCarrier}
    (hc : η c = false) (hc' : η c' = false) (ha : a ∈ starCluster η c)
    (ha' : a ∈ enclosedBy (starCluster η c')) (hna : a ∉ starCluster η c') :
    enclosedBy (starCluster η c) ⊆ enclosedBy (starCluster η c') := by
  set K := starCluster η c with hKdef
  set K' := starCluster η c' with hK'def
  have hdisj : ∀ d ∈ K, d ∉ K' := fun d hd hd' => hna (by
    rw [hK'def, starCluster_eq hd' hd]
    exact ha)
  -- a step of `K` is joined outside `K'`, turning about a corner for a diagonal step
  have hstep : ∀ s t, s ∈ K → (closedStarGraph η).Adj s t → (avoidGraph K').Reachable s t := by
    intro s t hs hst
    have ht : t ∈ K := SimpleGraph.Reachable.trans hs hst.reachable
    have hsK' := hdisj s hs
    have htK' := hdisj t ht
    obtain ⟨hne, h1, h2, hηs, hηt⟩ := hst
    by_cases hnn : |s.1 - t.1| + |s.2 - t.2| = 1
    · exact SimpleGraph.Adj.reachable ⟨hnn, hsK', htK'⟩
    · have hne' : s.1 - t.1 ≠ 0 ∨ s.2 - t.2 ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hne (Prod.ext (by omega) (by omega))
      obtain ⟨hd1, hd2⟩ := abs_eq_one_of_diag h1 h2 hnn hne'
      set u : PlanarCarrier := (s.1, t.2) with hu
      have hsu : |s.1 - u.1| + |s.2 - u.2| = 1 := by simp [u, hd2]
      have hut : |u.1 - t.1| + |u.2 - t.2| = 1 := by simp [u, hd1]
      have huK' : u ∉ K' := by
        intro huK'
        exact hdisj u (mem_starCluster_of_nn hc hs (closed_of_mem_starCluster hc' huK') hsu) huK'
      exact (SimpleGraph.Adj.reachable (G := avoidGraph K') ⟨hsu, hsK', huK'⟩).trans
        (SimpleGraph.Adj.reachable ⟨hut, huK', htK'⟩)
  have hreachK : ∀ k, (closedStarGraph η).Reachable a k → (avoidGraph K').Reachable a k := by
    intro k hk
    have h' := (SimpleGraph.reachable_iff_reflTransGen _ _).mp hk
    clear hk
    induction h' with
    | refl => exact SimpleGraph.Reachable.refl _
    | @tail b d hab hbd ih =>
      exact ih.trans (hstep b d (SimpleGraph.Reachable.trans ha
        ((SimpleGraph.reachable_iff_reflTransGen _ _).mpr hab)) hbd)
  have hKenc : ∀ k ∈ K, k ∈ enclosedBy K' := fun k hk => by
    have hr := hreachK k (SimpleGraph.Reachable.trans (SimpleGraph.Reachable.symm ha) hk)
    exact ha'.subset fun y hy => hr.trans hy
  intro x hx
  by_contra hinf
  by_cases hmeet : ∃ k ∈ K, (avoidGraph K').Reachable x k
  · obtain ⟨k, hk, hxk⟩ := hmeet
    exact hinf ((hKenc k hk).subset fun y hy => hxk.symm.trans hy)
  · push Not at hmeet
    apply hinf
    refine hx.subset fun y hy => ?_
    have h' := (SimpleGraph.reachable_iff_reflTransGen _ _).mp hy
    clear hy
    induction h' with
    | refl => exact SimpleGraph.Reachable.refl _
    | @tail b d hab hbd ih =>
      have hb : (avoidGraph K').Reachable x b := (SimpleGraph.reachable_iff_reflTransGen _ _).mpr hab
      have hd : (avoidGraph K').Reachable x d := hb.trans hbd.reachable
      exact ih.trans (SimpleGraph.Adj.reachable
        ⟨hbd.1, fun h => hmeet b h hb, fun h => hmeet d h hd⟩)

/-! ### Enclosure of the sites outside the infinite open clusters -/

theorem rowCount_of_le (Γ : Set (PlanarCarrier × Bool)) {R : ℤ} {a : PlanarCarrier}
    (h : R ≤ a.1) : rowCount Γ R a = 0 := by
  unfold rowCount
  rw [show (R - a.1).toNat = 0 by omega, Finset.sum_range_zero]

theorem outerEnd_cases (C : Set PlanarCarrier) (e : PlanarCarrier × Bool) :
    outerEnd C e = e.1 ∨ outerEnd C e = edgeTip e := by
  unfold outerEnd
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- **Duality.** An open site `z` with a finite open cluster is enclosed by a closed `*`-cluster:
that of the outer endpoints of the component `Γ` of the dual boundary graph of its cluster
through the edge leaving the cluster on the horizontal ray from `z`. -/
theorem exists_enclosedBy_of_finite (η : PlanarCarrier → Bool) (z : PlanarCarrier)
    (hz : η z = true) (hfin : {w | (siteOpenGraph η).Reachable z w}.Finite) :
    ∃ c, η c = false ∧ z ∈ enclosedBy (starCluster η c) := by
  set C := {w | (siteOpenGraph η).Reachable z w} with hCdef
  have hzC : z ∈ C := SimpleGraph.Reachable.refl z
  obtain ⟨B, hB⟩ : ∃ B : ℤ, ∀ c ∈ C, |c.1| ≤ B ∧ |c.2| ≤ B := by
    obtain ⟨B, hB⟩ := (hfin.image fun c : PlanarCarrier => max |c.1| |c.2|).bddAbove
    exact ⟨B, fun c hc => by
      have := hB (Set.mem_image_of_mem _ hc)
      exact ⟨(le_max_left _ _).trans this, (le_max_right _ _).trans this⟩⟩
  have hB' : ∀ c ∈ C, -B ≤ c.1 ∧ c.1 ≤ B ∧ -B ≤ c.2 ∧ c.2 ≤ B := fun c hc =>
    ⟨(abs_le.mp (hB c hc).1).1, (abs_le.mp (hB c hc).1).2, (abs_le.mp (hB c hc).2).1,
      (abs_le.mp (hB c hc).2).2⟩
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB z hzC).1
  have hnot : ∀ s : PlanarCarrier, (B < s.1 ∨ s.1 < -B ∨ B < s.2 ∨ s.2 < -B) → s ∉ C :=
    fun s hs hsC => by have := hB' s hsC; omega
  -- the last site `u = z + (k₀, 0)` of `C` on the horizontal ray from `z`
  have hrowfin : {k : ℕ | ((z.1 + k, z.2) : PlanarCarrier) ∈ C}.Finite :=
    hfin.preimage (f := fun k : ℕ => ((z.1 + k, z.2) : PlanarCarrier))
      (fun a _ b _ h => by simpa using h)
  set K := hrowfin.toFinset
  have hK0 : 0 ∈ K := by simpa [K] using hzC
  set k₀ := K.max' ⟨0, hK0⟩
  have hk₀C : ((z.1 + k₀, z.2) : PlanarCarrier) ∈ C := by
    have := K.max'_mem ⟨0, hK0⟩
    simpa [K] using this
  have hk₀max : ∀ j : ℕ, k₀ < j → ((z.1 + j, z.2) : PlanarCarrier) ∉ C := fun j hj hjC => by
    have : j ≤ k₀ := K.le_max' j (by simpa [K] using hjC)
    omega
  set D₀ : PlanarCarrier × Bool := ((z.1 + k₀, z.2), false) with hD₀
  have hD : IsBoundaryEdge C D₀ := by
    refine Or.inl ⟨hk₀C, ?_⟩
    have := hk₀max (k₀ + 1) (by omega)
    push_cast at this
    simpa [D₀, ← add_assoc] using this
  set Γ := boundaryComponent C D₀ with hΓ
  set R := B + 1 with hRdef
  have hR : ∀ y', ((R, y'), true) ∉ Γ := fun y' =>
    notMem_boundaryComponent_of_both_notMem hD (hnot _ (by simp; omega))
      (hnot _ (by simp; omega))
  have heven := plaquette_sum_eq_zero hD
  -- `rowCount` is constant on `C`
  have hadj : ∀ s t : PlanarCarrier, s ∈ C → t ∈ C → |s.1 - t.1| + |s.2 - t.2| = 1 →
      rowCount Γ R s = rowCount Γ R t := by
    rintro ⟨s1, s2⟩ ⟨t1, t2⟩ hs ht hd
    have hs' := hB' _ hs
    have ht' := hB' _ ht
    simp only at hd hs' ht'
    rcases unit_step_cases hd with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain rfl : t1 = s1 + 1 := by omega
      obtain rfl : s2 = t2 := by omega
      rw [rowCount_succ_fst Γ s2 (R := R) (x := s1) (by omega),
        edgeInd_of_notMem (notMem_boundaryComponent_of_both_mem (e := ((s1, s2), false)) hD hs ht),
        zero_add]
    · obtain rfl : s1 = t1 + 1 := by omega
      obtain rfl : s2 = t2 := by omega
      rw [rowCount_succ_fst Γ s2 (R := R) (x := t1) (by omega),
        edgeInd_of_notMem (notMem_boundaryComponent_of_both_mem (e := ((t1, s2), false)) hD ht hs),
        zero_add]
    · obtain rfl : t1 = s1 := by omega
      obtain rfl : t2 = s2 + 1 := by omega
      have := rowCount_add_succ_snd Γ s2 (R := R) (x := t1) (by omega) hR heven
      rw [edgeInd_of_notMem
        (notMem_boundaryComponent_of_both_mem (e := ((t1, s2), true)) hD hs ht)] at this
      linear_combination this - rowCount Γ R (t1, s2 + 1) * two_eq_zero_zmod
    · obtain rfl : t1 = s1 := by omega
      obtain rfl : s2 = t2 + 1 := by omega
      have := rowCount_add_succ_snd Γ t2 (R := R) (x := t1) (by omega) hR heven
      rw [edgeInd_of_notMem
        (notMem_boundaryComponent_of_both_mem (e := ((t1, t2), true)) hD ht hs)] at this
      linear_combination this - rowCount Γ R (t1, t2) * two_eq_zero_zmod
  have hconst : ∀ s ∈ C, rowCount Γ R s = rowCount Γ R z := by
    intro s hs
    have hs' := (SimpleGraph.reachable_iff_reflTransGen _ _).mp hs
    clear hs
    induction hs' with
    | refl => rfl
    | @tail a b hab hab' ih =>
      have haC : a ∈ C := (SimpleGraph.reachable_iff_reflTransGen _ _).mpr hab
      have hbC : b ∈ C := (SimpleGraph.reachable_iff_reflTransGen _ _).mpr (hab.tail hab')
      rw [← ih, hadj b a hbC haC]
      rw [abs_sub_comm b.1, abs_sub_comm b.2]
      exact hab'.1
  -- `rowCount` is `1` on `C`
  have hFw : rowCount Γ R (z.1 + k₀ + 1, z.2) = 0 := by
    refine Finset.sum_eq_zero fun i _ => edgeInd_of_notMem ?_
    refine notMem_boundaryComponent_of_both_notMem hD ?_ ?_
    · have := hk₀max (k₀ + 1 + i) (by omega)
      push_cast at this
      simpa [add_assoc] using this
    · have := hk₀max (k₀ + 1 + i + 1) (by omega)
      push_cast at this
      simpa [add_assoc] using this
  have hFz : rowCount Γ R z = 1 := by
    rw [← hconst _ hk₀C, rowCount_succ_fst Γ z.2 (by have := hB' _ hk₀C; simp at this; omega),
      hFw, edgeInd_of_mem (SimpleGraph.Reachable.refl _), add_zero]
  have hcl : ∀ e, IsBoundaryEdge C e → η (outerEnd C e) = false := by
    intro e he
    by_contra hη
    rw [Bool.not_eq_false] at hη
    rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [outerEnd, if_pos h1] at hη
      exact h2 (SimpleGraph.Reachable.trans h1 (SimpleGraph.Adj.reachable
        ⟨edgeTip_dist e, open_of_reachable hz h1, hη⟩))
    · rw [outerEnd, if_neg h1] at hη
      refine h1 (SimpleGraph.Reachable.trans h2 (SimpleGraph.Adj.reachable
        ⟨?_, open_of_reachable hz h2, hη⟩))
      rw [abs_sub_comm, abs_sub_comm (edgeTip e).2]
      exact edgeTip_dist e
  set c := outerEnd C D₀ with hc
  refine ⟨c, hcl D₀ hD, ?_⟩
  set W := starCluster η c with hW
  have hWΓ : ∀ e ∈ Γ, outerEnd C e ∈ W := fun e he => reachable_outerEnd η hcl he
  -- an edge of `Γ` has an endpoint in `W`
  have hnotΓ : ∀ e : PlanarCarrier × Bool, e.1 ∉ W → edgeTip e ∉ W → e ∉ Γ := by
    intro e h1 h2 he
    rcases outerEnd_cases C e with h | h
    · exact h1 (h ▸ hWΓ e he)
    · exact h2 (h ▸ hWΓ e he)
  -- `F` vanishes off the box `(-B - 2, R) × [-B, B]`
  have hrow : ∀ y : ℤ, (y < -B ∨ B < y) → ∀ x : ℤ, rowCount Γ R (x, y) = 0 := by
    intro y hy x
    refine Finset.sum_eq_zero fun i _ => edgeInd_of_notMem ?_
    exact notMem_boundaryComponent_of_both_notMem hD (hnot _ (by simp; omega))
      (hnot _ (by simp; omega))
  have hcol : ∀ y : ℤ, rowCount Γ R (-B - 2, y) = 0 := by
    intro y
    rcases lt_or_ge y (-B) with hy | hy
    · exact hrow y (Or.inl hy) _
    have h2 : ∀ m : ℕ, rowCount Γ R (-B - 2, -B - 2 + m) = 0 := by
      intro m
      induction m with
      | zero =>
        refine Finset.sum_eq_zero fun i _ => edgeInd_of_notMem ?_
        exact notMem_boundaryComponent_of_both_notMem hD (hnot _ (by simp))
          (hnot _ (by simp))
      | succ m ih =>
        have := rowCount_add_succ_snd Γ (-B - 2 + m) (x := -B - 2) (R := R) (by omega) hR heven
        rw [edgeInd_of_notMem (notMem_boundaryComponent_of_both_notMem hD (hnot _ (by simp))
          (hnot _ (by simp))), ih] at this
        push_cast
        rw [← add_assoc]
        linear_combination this
    have := h2 (y + B + 2).toNat
    rwa [Int.toNat_of_nonneg (by omega), show -B - 2 + (y + B + 2) = y by ring] at this
  have hleftF : ∀ (m : ℕ) (y : ℤ), rowCount Γ R (-B - 2 - m, y) = 0 := by
    intro m y
    induction m with
    | zero => simpa using hcol y
    | succ m ih =>
      have := rowCount_succ_fst Γ y (x := -B - 2 - (m + 1 : ℕ)) (R := R) (by omega)
      rw [edgeInd_of_notMem (notMem_boundaryComponent_of_both_notMem hD (hnot _ (by simp; omega))
        (hnot _ (by simp; omega))), zero_add] at this
      rw [this, ← ih]
      congr 2
      push_cast
      ring
  have hbox : ∀ y : PlanarCarrier, rowCount Γ R y = 1 → -B - 2 < y.1 ∧ y.1 < R ∧ -B ≤ y.2 ∧ y.2 ≤ B := by
    rintro ⟨y1, y2⟩ hy
    have h10 : (1 : ZMod 2) ≠ 0 := by decide
    refine ⟨?_, ?_, ?_, ?_⟩
    · by_contra h
      have := hleftF (-B - 2 - y1).toNat y2
      rw [show -B - 2 - ((-B - 2 - y1).toNat : ℤ) = y1 by omega] at this
      exact h10 (hy.symm.trans this)
    · by_contra h
      exact h10 (hy.symm.trans (rowCount_of_le Γ (by simp; omega)))
    · by_contra h
      exact h10 (hy.symm.trans (hrow y2 (Or.inl (by omega)) y1))
    · by_contra h
      exact h10 (hy.symm.trans (hrow y2 (Or.inr (by omega)) y1))
  -- `F` is constant along the nearest-neighbour walks of `ℤ² ∖ W` from `z`
  have hstep : ∀ a b : PlanarCarrier, rowCount Γ R a = 1 → (avoidGraph W).Adj a b → rowCount Γ R b = 1 := by
    rintro ⟨a1, a2⟩ ⟨b1, b2⟩ ha ⟨hab, haW, hbW⟩
    have haR := (hbox _ ha).2.1
    simp only at hab haR
    rcases unit_step_cases (show |b1 - a1| + |b2 - a2| = 1 by
      rw [abs_sub_comm, abs_sub_comm b2]; exact hab) with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain rfl : b1 = a1 - 1 := by omega
      obtain rfl : a2 = b2 := by omega
      have := rowCount_succ_fst Γ a2 (R := R) (x := a1 - 1) (by omega)
      rw [edgeInd_of_notMem (hnotΓ _ hbW (by simpa using haW)), zero_add,
        show a1 - 1 + 1 = a1 by ring] at this
      rw [this]
      exact ha
    · obtain rfl : b1 = a1 + 1 := by omega
      obtain rfl : a2 = b2 := by omega
      have := rowCount_succ_fst Γ a2 (R := R) (x := a1) (by omega)
      rw [edgeInd_of_notMem (hnotΓ _ haW (by simpa using hbW)), zero_add] at this
      rw [← this]
      exact ha
    · obtain rfl : a1 = b1 := by omega
      obtain rfl : b2 = a2 - 1 := by omega
      have := rowCount_add_succ_snd Γ (a2 - 1) (x := a1) (R := R) (by omega) hR heven
      rw [edgeInd_of_notMem (hnotΓ _ hbW (by simpa using haW)),
        show a2 - 1 + 1 = a2 by ring] at this
      linear_combination this - ha - two_eq_zero_zmod
    · obtain rfl : a1 = b1 := by omega
      obtain rfl : b2 = a2 + 1 := by omega
      have := rowCount_add_succ_snd Γ a2 (x := a1) (R := R) (by omega) hR heven
      rw [edgeInd_of_notMem (hnotΓ _ haW (by simpa using hbW))] at this
      linear_combination this - ha - two_eq_zero_zmod
  have hreachF : ∀ y, (avoidGraph W).Reachable z y → rowCount Γ R y = 1 := by
    intro y hy
    have h' := (SimpleGraph.reachable_iff_reflTransGen _ _).mp hy
    clear hy
    induction h' with
    | refl => exact hFz
    | tail _ hadj ih => exact hstep _ _ ih hadj
  refine ((Set.finite_Ioo (-B - 2) R).prod (Set.finite_Icc (-B) B)).subset fun y hy => ?_
  obtain ⟨h1, h2, h3, h4⟩ := hbox y (hreachF y hy)
  exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩

/-- A site outside the infinite open clusters is enclosed by a closed `*`-cluster. -/
theorem exists_enclosedBy_of_not_inInfinite {η : PlanarCarrier → Bool} {x : PlanarCarrier}
    (hx : ¬InInfiniteSiteCluster η x) :
    ∃ c, η c = false ∧ x ∈ enclosedBy (starCluster η c) := by
  by_cases hη : η x = true
  · exact exists_enclosedBy_of_finite η x hη (by
      by_contra h
      exact hx ⟨hη, h⟩)
  · exact ⟨x, by simpa using hη, mem_enclosedBy_of_mem (mem_starCluster_self η x)⟩

/-- A site outside the infinite open clusters with a nearest neighbour in one is closed. -/
theorem closed_of_adj_inInfinite {η : PlanarCarrier → Bool} {g b : PlanarCarrier}
    (hg : InInfiniteSiteCluster η g) (hb : ¬InInfiniteSiteCluster η b)
    (hgb : |g.1 - b.1| + |g.2 - b.2| = 1) : η b = false := by
  by_contra hη
  rw [Bool.not_eq_false] at hη
  have hr : (siteOpenGraph η).Reachable b g := SimpleGraph.Adj.reachable
    ⟨by rw [abs_sub_comm, abs_sub_comm b.2]; exact hgb, hη, hg.1⟩
  exact hb ⟨hη, fun hfin => hg.2 (hfin.subset fun w hw => hr.trans hw)⟩

/-- **The enclosing cluster of an excursion.** If `a` is enclosed by the closed `*`-cluster of
`c` and its nearest neighbour `b` is outside the infinite open clusters, `b` is enclosed by a
closed `*`-cluster enclosing every site enclosed by that of `c`. -/
theorem exists_enclosedBy_step {η : PlanarCarrier → Bool} {c a b : PlanarCarrier}
    (hc : η c = false) (ha : a ∈ enclosedBy (starCluster η c))
    (hb : ¬InInfiniteSiteCluster η b) (hab : |a.1 - b.1| + |a.2 - b.2| = 1) :
    ∃ c₂, η c₂ = false ∧ b ∈ enclosedBy (starCluster η c₂) ∧
      enclosedBy (starCluster η c) ⊆ enclosedBy (starCluster η c₂) := by
  by_cases hbK : b ∈ enclosedBy (starCluster η c)
  · exact ⟨c, hc, hbK, subset_rfl⟩
  obtain ⟨cb, hcb, hbcb⟩ := exists_enclosedBy_of_not_inInfinite hb
  have haK : a ∈ starCluster η c := mem_of_mem_enclosedBy_of_adj ha hbK hab
  by_cases hacb : a ∈ enclosedBy (starCluster η cb)
  · have hna : a ∉ starCluster η cb := fun h => hbK (by
      rw [starCluster_eq haK h]
      exact hbcb)
    exact ⟨cb, hcb, hbcb, enclosedBy_starCluster_subset hc hcb haK hacb hna⟩
  · have hba : |b.1 - a.1| + |b.2 - a.2| = 1 := by
      rw [abs_sub_comm, abs_sub_comm b.2]
      exact hab
    have hbcb' : b ∈ starCluster η cb := mem_of_mem_enclosedBy_of_adj hbcb hacb hba
    exact absurd (mem_enclosedBy_of_mem (mem_starCluster_of_nn hc haK
      (closed_of_mem_starCluster hcb hbcb') hab)) hbK

/-- A site lying in every closed `*`-cluster enclosing it. -/
def IsExposed (η : PlanarCarrier → Bool) (r : PlanarCarrier) : Prop :=
  ∀ c, η c = false → r ∈ enclosedBy (starCluster η c) → r ∈ starCluster η c

theorem isExposed_of_adj {η : PlanarCarrier → Bool} {r g : PlanarCarrier}
    (hg : InInfiniteSiteCluster η g) (hrg : |r.1 - g.1| + |r.2 - g.2| = 1) : IsExposed η r :=
  fun _ hc hr => mem_of_mem_enclosedBy_of_adj hr
    (notMem_enclosedBy_of_inInfinite (fun _ hs => closed_of_mem_starCluster hc hs) hg) hrg

/-! ### The `*`-path of a deficient walk -/

theorem starGraphOn_adj_of_nn {A : Set PlanarCarrier} {a b : PlanarCarrier} (ha : a ∈ A)
    (hb : b ∈ A) (hab : |a.1 - b.1| + |a.2 - b.2| = 1) : (starGraphOn A).Adj a b :=
  ⟨ne_of_nn hab, abs_fst_le_one_of_nn hab, abs_snd_le_one_of_nn hab, ha, hb⟩

theorem abs_sub_le_length_starGraphOn {A : Set PlanarCarrier} {u v : PlanarCarrier}
    (p : (starGraphOn A).Walk u v) : |u.1 - v.1| ≤ p.length ∧ |u.2 - v.2| ≤ p.length := by
  induction p with
  | nil => simp
  | @cons a b c h p ih =>
    simp only [SimpleGraph.Walk.length_cons]
    push_cast
    exact ⟨(abs_sub_le a.1 b.1 c.1).trans (by linarith [h.2.1, ih.1]),
      (abs_sub_le a.2 b.2 c.2).trans (by linarith [h.2.2.1, ih.2])⟩

/-- A self-avoiding `*`-walk through `A` from a site `(j, 0)`, `j ≥ 0`, of length at least `j`
and at least `M / 4`. -/
def LongStarPath (A : Set PlanarCarrier) (M : ℤ) : Prop :=
  ∃ (j : ℕ) (v : PlanarCarrier) (p : (starGraphOn A).Walk ((j : ℤ), 0) v),
    p.IsPath ∧ M ≤ 4 * (p.length : ℤ) ∧ j ≤ p.length

theorem longStarPath_of_reachable {A : Set PlanarCarrier} {M : ℤ} {j : ℕ} {v : PlanarCarrier}
    (h : (starGraphOn A).Reachable ((j : ℤ), 0) v) (hj : 4 * (j : ℤ) ≤ M)
    (hv : M ≤ 2 * |v.1| ∨ M ≤ 2 * |v.2|) : LongStarPath A M := by
  obtain ⟨p⟩ := h
  obtain ⟨h1, h2⟩ := abs_sub_le_length_starGraphOn p.bypass
  simp only at h1 h2
  have hM : M ≤ 4 * (p.bypass.length : ℤ) := by
    rcases hv with hv | hv
    · rcases abs_cases ((j : ℤ) - v.1) with ⟨e, _⟩ | ⟨e, _⟩ <;>
        rcases abs_cases v.1 with ⟨e', _⟩ | ⟨e', _⟩ <;> rw [e] at h1 <;> rw [e'] at hv <;> omega
    · rcases abs_cases ((0 : ℤ) - v.2) with ⟨e, _⟩ | ⟨e, _⟩ <;>
        rcases abs_cases v.2 with ⟨e', _⟩ | ⟨e', _⟩ <;> rw [e] at h2 <;> rw [e'] at hv <;> omega
  exact ⟨j, v, p.bypass, p.bypass_isPath, hM, by omega⟩

theorem longStarPath_of_rays {η : PlanarCarrier → Bool} {A : Set PlanarCarrier}
    (hA : ∀ s, η s = false → s ∈ A) {c : PlanarCarrier} {M : ℤ} {j j' : ℕ}
    (hj : ((j : ℤ), (0 : ℤ)) ∈ starCluster η c) (hj' : (-(j' : ℤ), (0 : ℤ)) ∈ starCluster η c)
    (hM : M < 4 * (j : ℤ)) : LongStarPath A M := by
  obtain ⟨p⟩ := reachable_of_mem_starCluster hA hj hj'
  obtain ⟨h1, -⟩ := abs_sub_le_length_starGraphOn p.bypass
  simp only at h1
  rw [abs_of_nonneg (by omega)] at h1
  exact ⟨j, _, p.bypass, p.bypass_isPath, by omega, by omega⟩

/-- The invariant along a lazy walk from the origin: the current site `a` and the origin are
enclosed by one closed `*`-cluster and no site of an infinite open cluster was met; or a
`*`-path through `A` joins a site `(j, 0)` with `4 j ≤ M` to `a` (if `a` lies in an infinite
open cluster) or to an exposed site of a closed `*`-cluster enclosing `a`; or the conclusion
holds. -/
def WalkState (η : PlanarCarrier → Bool) (A : Set PlanarCarrier) (M : ℤ) (a : PlanarCarrier) :
    Prop :=
  (¬InInfiniteSiteCluster η a ∧ ∃ c, η c = false ∧
      (0 : PlanarCarrier) ∈ enclosedBy (starCluster η c) ∧ a ∈ enclosedBy (starCluster η c)) ∨
  (∃ j : ℕ, 4 * (j : ℤ) ≤ M ∧
    ((InInfiniteSiteCluster η a ∧ (starGraphOn A).Reachable ((j : ℤ), 0) a) ∨
     (¬InInfiniteSiteCluster η a ∧ ∃ c r, η c = false ∧ a ∈ enclosedBy (starCluster η c) ∧
        r ∈ starCluster η c ∧ (starGraphOn A).Reachable ((j : ℤ), 0) r ∧ IsExposed η r))) ∨
  LongStarPath A M

theorem walkState_zero {η : PlanarCarrier → Bool} {A : Set PlanarCarrier} {M : ℤ}
    (hM : 0 ≤ M) :
    WalkState η A M 0 := by
  by_cases hg : InInfiniteSiteCluster η 0
  · refine Or.inr (Or.inl ⟨0, by simpa using hM, Or.inl ⟨hg, ?_⟩⟩)
    have : (((0 : ℕ) : ℤ), (0 : ℤ)) = (0 : PlanarCarrier) := by ext <;> simp
    rw [this]
  · obtain ⟨c, hc, h0⟩ := exists_enclosedBy_of_not_inInfinite hg
    exact Or.inl ⟨hg, c, hc, h0, h0⟩

theorem walkState_step {η : PlanarCarrier → Bool} {A : Set PlanarCarrier} {M : ℤ}
    {a b : PlanarCarrier} (hA : ∀ s, η s = false → s ∈ A)
    (haA : InInfiniteSiteCluster η a → a ∈ A) (hbA : InInfiniteSiteCluster η b → b ∈ A)
    (hab : a = b ∨ |a.1 - b.1| + |a.2 - b.2| = 1) (h : WalkState η A M a) :
    WalkState η A M b := by
  rcases hab with rfl | hab
  · exact h
  have hba : |b.1 - a.1| + |b.2 - a.2| = 1 := by
    rw [abs_sub_comm, abs_sub_comm b.2]
    exact hab
  have hclK : ∀ {c}, η c = false → ∀ s ∈ starCluster η c, η s = false :=
    fun hc _ hs => closed_of_mem_starCluster hc hs
  rcases h with ⟨hag, c, hc, h0, haK⟩ |
      ⟨j, hj, ⟨hag, hreach⟩ | ⟨hag, c, r, hc, haK, hrK, hreach, hexp⟩⟩ | hfin
  · by_cases hbg : InInfiniteSiteCluster η b
    · have haK' : a ∈ starCluster η c := mem_of_mem_enclosedBy_of_adj haK
        (notMem_enclosedBy_of_inInfinite (hclK hc) hbg) hab
      obtain ⟨j, hjK⟩ := exists_mem_right h0
      obtain ⟨j', hj'K⟩ := exists_mem_left h0
      simp only [Prod.fst_zero, Prod.snd_zero, zero_add, zero_sub] at hjK hj'K
      by_cases hjM : 4 * (j : ℤ) ≤ M
      · refine Or.inr (Or.inl ⟨j, hjM, Or.inl ⟨hbg, ?_⟩⟩)
        exact (reachable_of_mem_starCluster hA hjK haK').trans (SimpleGraph.Adj.reachable
          (starGraphOn_adj_of_nn (hA a (closed_of_mem_starCluster hc haK')) (hbA hbg) hab))
      · exact Or.inr (Or.inr (longStarPath_of_rays hA hjK hj'K (by omega)))
    · obtain ⟨c₂, hc₂, hbK₂, hsub⟩ := exists_enclosedBy_step hc haK hbg hab
      exact Or.inl ⟨hbg, c₂, hc₂, hsub h0, hbK₂⟩
  · by_cases hbg : InInfiniteSiteCluster η b
    · exact Or.inr (Or.inl ⟨j, hj, Or.inl ⟨hbg, hreach.trans (SimpleGraph.Adj.reachable
        (starGraphOn_adj_of_nn (haA hag) (hbA hbg) hab))⟩⟩)
    · have hηb := closed_of_adj_inInfinite hag hbg hab
      exact Or.inr (Or.inl ⟨j, hj, Or.inr ⟨hbg, b, b, hηb,
        mem_enclosedBy_of_mem (mem_starCluster_self η b), mem_starCluster_self η b,
        hreach.trans (SimpleGraph.Adj.reachable
          (starGraphOn_adj_of_nn (haA hag) (hA b hηb) hab)),
        isExposed_of_adj hag hba⟩⟩)
  · by_cases hbg : InInfiniteSiteCluster η b
    · have haK' : a ∈ starCluster η c := mem_of_mem_enclosedBy_of_adj haK
        (notMem_enclosedBy_of_inInfinite (hclK hc) hbg) hab
      exact Or.inr (Or.inl ⟨j, hj, Or.inl ⟨hbg,
        (hreach.trans (reachable_of_mem_starCluster hA hrK haK')).trans
          (SimpleGraph.Adj.reachable (starGraphOn_adj_of_nn
            (hA a (closed_of_mem_starCluster hc haK')) (hbA hbg) hab))⟩⟩)
    · obtain ⟨c₂, hc₂, hbK₂, hsub⟩ := exists_enclosedBy_step hc haK hbg hab
      exact Or.inr (Or.inl ⟨j, hj, Or.inr ⟨hbg, c₂, r, hc₂, hbK₂,
        hexp c₂ hc₂ (hsub (mem_enclosedBy_of_mem hrK)), hreach, hexp⟩⟩)
  · exact Or.inr (Or.inr hfin)

theorem longStarPath_of_walkState {η : PlanarCarrier → Bool} {A : Set PlanarCarrier}
    (hA : ∀ s, η s = false → s ∈ A) {z : PlanarCarrier}
    (h : WalkState η A (|z.1| + |z.2|) z) : LongStarPath A (|z.1| + |z.2|) := by
  rcases h with ⟨-, c, -, h0, hzK⟩ | ⟨j, hj, ⟨-, hreach⟩ | ⟨-, c, r, -, hzK, hrK, hreach, -⟩⟩ |
      hfin
  · obtain ⟨j, hjK⟩ := exists_mem_right h0
    obtain ⟨j', hj'K⟩ := exists_mem_left h0
    simp only [Prod.fst_zero, Prod.snd_zero, zero_add, zero_sub] at hjK hj'K
    by_cases hjM : 4 * (j : ℤ) ≤ |z.1| + |z.2|
    · obtain ⟨k, hkK, hk⟩ := exists_mem_far hzK
      exact longStarPath_of_reachable (reachable_of_mem_starCluster hA hjK hkK) hjM hk
    · exact longStarPath_of_rays hA hjK hj'K (by omega)
  · refine longStarPath_of_reachable hreach hj ?_
    rcases le_total |z.2| |z.1| with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · obtain ⟨k, hkK, hk⟩ := exists_mem_far hzK
    exact longStarPath_of_reachable (hreach.trans (reachable_of_mem_starCluster hA hrK hkK)) hj hk
  · exact hfin

/-- The sites of the infinite open clusters visited by the walk `w`. -/
def visitedClusterSites (η : PlanarCarrier → Bool) {n : ℕ} (w : Fin (n + 1) → PlanarCarrier) :
    Finset PlanarCarrier :=
  (Finset.univ.filter fun i => InInfiniteSiteCluster η (w i)).image w

theorem lazy_step_cases {a b : PlanarCarrier} (h : |b.1 - a.1| + |b.2 - a.2| ≤ 1) :
    a = b ∨ |a.1 - b.1| + |a.2 - b.2| = 1 := by
  rw [abs_sub_comm b.1, abs_sub_comm b.2] at h
  have h1 := abs_nonneg (a.1 - b.1)
  have h2 := abs_nonneg (a.2 - b.2)
  by_cases hz : |a.1 - b.1| + |a.2 - b.2| = 0
  · have e1 : |a.1 - b.1| = 0 := by omega
    have e2 : |a.2 - b.2| = 0 := by omega
    rw [abs_eq_zero, sub_eq_zero] at e1 e2
    exact Or.inl (Prod.ext e1 e2)
  · exact Or.inr (by omega)

/-- **The `*`-path of a lazy walk.** A lazy walk `w` from the origin to `z` gives a
self-avoiding `*`-path from a site `(j, 0)` of length `L ≥ max(j, |z|₁ / 4)`, whose sites are
closed or sites of the infinite open clusters visited by `w`. -/
theorem longStarPath_of_walk (η : PlanarCarrier → Bool) {n : ℕ} (w : Fin (n + 1) → PlanarCarrier)
    (hw : IsLazyWalk w) (h0 : w 0 = 0) :
    LongStarPath ({s | η s = false} ∪ ↑(visitedClusterSites η w))
      (|(w (Fin.last n)).1| + |(w (Fin.last n)).2|) := by
  set A : Set PlanarCarrier := {s | η s = false} ∪ ↑(visitedClusterSites η w) with hAdef
  have hA : ∀ s, η s = false → s ∈ A := fun s hs => Or.inl hs
  have hgA : ∀ i, InInfiniteSiteCluster η (w i) → w i ∈ A := fun i hi => Or.inr (by
    simp only [visitedClusterSites, Finset.coe_image, Finset.coe_filter, Finset.mem_univ,
      true_and]
    exact ⟨i, hi, rfl⟩)
  have hinv : ∀ i : Fin (n + 1),
      WalkState η A (|(w (Fin.last n)).1| + |(w (Fin.last n)).2|) (w i) := by
    intro i
    induction i using Fin.induction with
    | zero =>
      rw [h0]
      exact walkState_zero (by positivity)
    | succ i ih => exact walkState_step hA (hgA _) (hgA _) (lazy_step_cases (hw i)) ih
  exact longStarPath_of_walkState hA (hinv (Fin.last n))

/-! ### The Peierls event -/

theorem support_mem_starWalkLists_of_starGraphOn {A : Set PlanarCarrier} {w v : PlanarCarrier}
    (p : (starGraphOn A).Walk w v) : p.support ∈ starWalkLists p.length w := by
  induction p with
  | nil => simp [starWalkLists]
  | @cons u v' _ h p ih =>
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.length_cons, starWalkLists,
      Finset.mem_biUnion, Finset.mem_image]
    refine ⟨v' - u, ?_, p.support, by rwa [add_sub_cancel], rfl⟩
    have h1 := abs_le.mp h.2.1
    have h2 := abs_le.mp h.2.2.1
    simp only [starOffsets, Finset.mem_product, Finset.mem_Icc, Prod.fst_sub, Prod.snd_sub]
    omega

theorem mem_of_mem_support_starGraphOn {A : Set PlanarCarrier} {u v : PlanarCarrier}
    (p : (starGraphOn A).Walk u v) : ∀ s ∈ p.support, s = u ∨ s ∈ A := by
  induction p with
  | nil =>
    intro s hs
    exact Or.inl (by simpa using hs)
  | @cons a b c h q ih =>
    intro s hs
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hs
    rcases hs with rfl | hs
    · exact Or.inl rfl
    · rcases ih s hs with rfl | h'
      · exact Or.inr h.2.2.2.2
      · exact Or.inr h'

/-- The open sites of a self-avoiding `*`-path through the closed sites and `G` lie in `G`. -/
theorem countP_support_le {η : PlanarCarrier → Bool} {G : Finset PlanarCarrier}
    {u v : PlanarCarrier} (p : (starGraphOn ({s | η s = false} ∪ ↑G)).Walk u v) (hp : p.IsPath)
    (hlen : 0 < p.length) : p.support.countP η ≤ G.card := by
  have hu : u ∈ ({s | η s = false} ∪ ↑G : Set PlanarCarrier) := by
    cases p with
    | nil => simp at hlen
    | cons h _ => exact h.2.2.2.1
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hp.support_nodup.filter _)]
  refine Finset.card_le_card fun s hs => ?_
  rw [List.mem_toFinset, List.mem_filter] at hs
  have hsA : s ∈ ({s | η s = false} ∪ ↑G : Set PlanarCarrier) := by
    rcases mem_of_mem_support_starGraphOn p s hs.1 with rfl | h
    · exact hu
    · exact h
  rcases hsA with h | h
  · rw [Set.mem_setOf_eq] at h
    rw [h] at hs
    exact absurd hs.2 (by decide)
  · exact h

/-- The Peierls event of Proposition 5.24: some self-avoiding `*`-path from a site `(j, 0)`, of
length `L ≥ j` with `4 L ≥ N₀`, has at most `L / 2` open sites. -/
def walkPeierlsEvent (N₀ : ℝ) : Set (PlanarCarrier → Bool) :=
  ⋃ L : ℕ, ⋃ (_ : N₀ ≤ 4 * (L : ℝ)), ⋃ j ∈ Finset.range (L + 1),
    ⋃ l ∈ starWalkLists L ((j : ℤ), 0), {η | l.Nodup ∧ 2 * l.countP η ≤ L}

/-- A lazy walk from the origin to `|z|₁ ≥ N₀` visiting fewer than `|z|₁ / 8` sites of the
infinite open clusters gives the Peierls event. -/
theorem renormWalkDeficient_subset {N₀ : ℝ} (hN₀ : 1 ≤ N₀) :
    RenormWalkDeficient (1 / 8) N₀ ⊆ walkPeierlsEvent N₀ := by
  rintro η ⟨n, w, hw, h0, hN, hcount⟩
  obtain ⟨j, v, p, hp, hM, hj⟩ := longStarPath_of_walk η w hw h0
  set M : ℤ := |(w (Fin.last n)).1| + |(w (Fin.last n)).2| with hMdef
  have hMR : (M : ℝ) ≤ 4 * (p.length : ℝ) := by exact_mod_cast hM
  have hM4 : N₀ ≤ 4 * (p.length : ℝ) := by linarith
  have hlen : 0 < p.length := by
    have : (0 : ℝ) < p.length := by linarith
    exact_mod_cast this
  have hcnt := countP_support_le p hp hlen
  have hcs : clusterSiteCount η w = (visitedClusterSites η w).card := rfl
  have h2 : 2 * p.support.countP η ≤ p.length := by
    have h1 : ((p.support.countP η : ℕ) : ℝ) ≤ (visitedClusterSites η w).card := by
      exact_mod_cast hcnt
    have h3 : ((2 * p.support.countP η : ℕ) : ℝ) < p.length := by
      rw [hcs] at hcount
      push_cast
      linarith
    exact_mod_cast h3.le
  simp only [walkPeierlsEvent, Set.mem_iUnion, Set.mem_setOf_eq]
  exact ⟨p.length, hM4, j, Finset.mem_range.mpr (by omega), p.support,
    support_mem_starWalkLists_of_starGraphOn p, hp.support_nodup, h2⟩

theorem measurable_countP (l : List PlanarCarrier) :
    Measurable fun η : PlanarCarrier → Bool => l.countP η := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.countP_cons]
    exact ih.add ((Measurable.of_discrete (f := fun b : Bool => if b = true then 1 else 0)).comp
      (measurable_pi_apply a))

theorem measurableSet_walkPeierlsEvent (N₀ : ℝ) : MeasurableSet (walkPeierlsEvent N₀) := by
  refine MeasurableSet.iUnion fun L => MeasurableSet.iUnion fun _ =>
    Finset.measurableSet_biUnion _ fun j _ => Finset.measurableSet_biUnion _ fun l _ => ?_
  by_cases hnd : l.Nodup
  · simp only [hnd, true_and]
    exact measurable_countP l (MeasurableSet.of_discrete (s := {k : ℕ | 2 * k ≤ L}))
  · simp [hnd]

/-- The Peierls event is decreasing: its complement is increasing. -/
theorem isIncreasingSet_compl_walkPeierlsEvent (N₀ : ℝ) :
    LatticeProb.StrassenAux.IsIncreasingSet (walkPeierlsEvent N₀)ᶜ := by
  intro ω ω' hω hωω' hω'
  apply hω
  simp only [walkPeierlsEvent, Set.mem_iUnion, Set.mem_setOf_eq] at hω' ⊢
  obtain ⟨L, hL, j, hj, l, hl, hnd, hc⟩ := hω'
  exact ⟨L, hL, j, hj, l, hl, hnd,
    le_trans (Nat.mul_le_mul_left 2 (List.countP_mono_left fun s _ hs => hωω' s hs)) hc⟩

theorem countP_add_countP_not (η : PlanarCarrier → Bool) (l : List PlanarCarrier) :
    l.countP η + l.countP (fun s => !η s) = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => cases h : η a <;> simp [h] <;> omega

/-- A self-avoiding `*`-path of length `L` has at most `L / 2` open sites with probability at
most `2ᴸ⁺¹ 144⁻ᴸ`. -/
theorem measure_countP_le {ν : Measure (PlanarCarrier → Bool)} [IsProbabilityMeasure ν]
    (hν : KDependentPlanar 1 ν)
    (hcl : ∀ z, ν {η | η z = false} ≤ ENNReal.ofReal ((1 / 144 : ℝ) ^ 18))
    {L : ℕ} {l : List PlanarCarrier} (hlen : l.length = L + 1) :
    ν {η | l.Nodup ∧ 2 * l.countP η ≤ L} ≤ ENNReal.ofReal (2 ^ (L + 1) * (1 / 144 : ℝ) ^ L) := by
  by_cases hnd : l.Nodup
  swap
  · have : {η : PlanarCarrier → Bool | l.Nodup ∧ 2 * l.countP η ≤ L} = ∅ := by
      ext η
      simp [hnd]
    rw [this, measure_empty]
    exact zero_le
  set 𝒯 := l.toFinset.powerset.filter fun T => L ≤ 2 * T.card with h𝒯
  have hsub : {η : PlanarCarrier → Bool | l.Nodup ∧ 2 * l.countP η ≤ L} ⊆
      ⋃ T ∈ 𝒯, {η | ∀ s ∈ T, η s = false} := by
    rintro η ⟨-, hη⟩
    simp only [Set.mem_iUnion]
    set T := (l.filter fun s => !η s).toFinset with hT
    have hTc : T.card = l.countP fun s => !η s := by
      rw [hT, List.toFinset_card_of_nodup (hnd.filter _), List.countP_eq_length_filter]
    have hsum := countP_add_countP_not η l
    refine ⟨T, ?_, fun s hs => ?_⟩
    · rw [h𝒯, Finset.mem_filter, Finset.mem_powerset]
      refine ⟨fun s hs => ?_, by omega⟩
      rw [hT, List.mem_toFinset, List.mem_filter] at hs
      exact List.mem_toFinset.mpr hs.1
    · rw [hT, List.mem_toFinset, List.mem_filter] at hs
      simpa using hs.2
  have hT : ∀ T ∈ 𝒯, ν {η | ∀ s ∈ T, η s = false} ≤ ENNReal.ofReal ((1 / 144 : ℝ) ^ L) := by
    intro T hT
    have hLT := (Finset.mem_filter.mp hT).2
    obtain ⟨S, hST, hcard, hsep⟩ := exists_separated_subset T
    calc ν {η | ∀ s ∈ T, η s = false} ≤ ν {η | ∀ s ∈ S, η s = false} :=
          measure_mono fun η hη s hs => hη s (hST hs)
      _ ≤ ENNReal.ofReal ((1 / 144 : ℝ) ^ 18) ^ S.card := measure_forall_closed_le hν hcl S hsep
      _ = ENNReal.ofReal (((1 / 144 : ℝ) ^ 18) ^ S.card) :=
          (ENNReal.ofReal_pow (by positivity) _).symm
      _ ≤ ENNReal.ofReal ((1 / 144 : ℝ) ^ L) := ENNReal.ofReal_le_ofReal (by
          rw [← pow_mul]
          exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega))
  have hcard𝒯 : 𝒯.card ≤ 2 ^ (L + 1) := (Finset.card_filter_le _ _).trans (by
    rw [Finset.card_powerset, List.toFinset_card_of_nodup hnd, hlen])
  calc ν {η | l.Nodup ∧ 2 * l.countP η ≤ L}
      ≤ ν (⋃ T ∈ 𝒯, {η | ∀ s ∈ T, η s = false}) := measure_mono hsub
    _ ≤ ∑ T ∈ 𝒯, ν {η | ∀ s ∈ T, η s = false} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _T ∈ 𝒯, ENNReal.ofReal ((1 / 144 : ℝ) ^ L) := Finset.sum_le_sum hT
    _ = 𝒯.card • ENNReal.ofReal ((1 / 144 : ℝ) ^ L) := Finset.sum_const _
    _ ≤ (2 ^ (L + 1)) • ENNReal.ofReal ((1 / 144 : ℝ) ^ L) := nsmul_le_nsmul_left zero_le hcard𝒯
    _ = ENNReal.ofReal (2 ^ (L + 1) * (1 / 144 : ℝ) ^ L) := by
        rw [nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
          show (2 : ℝ) ^ (L + 1) = ((2 ^ (L + 1) : ℕ) : ℝ) by norm_cast, ENNReal.ofReal_natCast]

/-- **Peierls bound for the walk steps.** For a `1`-dependent site field on `ℤ²` (for the
`ℓ^∞` distance) whose sites are closed with probability at most `144⁻¹⁸`, the Peierls event has
probability at most `4 exp(-(log 2 / 4) N₀)`. -/
theorem measure_walkPeierlsEvent_le {ν : Measure (PlanarCarrier → Bool)} [IsProbabilityMeasure ν]
    (hν : KDependentPlanar 1 ν)
    (hcl : ∀ z, ν {η | η z = false} ≤ ENNReal.ofReal ((1 / 144 : ℝ) ^ 18)) (N₀ : ℝ) :
    ν (walkPeierlsEvent N₀) ≤ ENNReal.ofReal (4 * Real.exp (-(Real.log 2 / 4 * N₀))) := by
  have hterm : ∀ L : ℕ, ν (⋃ j ∈ Finset.range (L + 1), ⋃ l ∈ starWalkLists L ((j : ℤ), 0),
      {η | l.Nodup ∧ 2 * l.countP η ≤ L}) ≤ ENNReal.ofReal (2 * (1 / 4 : ℝ) ^ L) := by
    intro L
    calc _ ≤ ∑ j ∈ Finset.range (L + 1), ν (⋃ l ∈ starWalkLists L ((j : ℤ), 0),
          {η | l.Nodup ∧ 2 * l.countP η ≤ L}) := measure_biUnion_finset_le _ _
      _ ≤ ∑ j ∈ Finset.range (L + 1), ∑ l ∈ starWalkLists L ((j : ℤ), 0),
          ν {η | l.Nodup ∧ 2 * l.countP η ≤ L} :=
          Finset.sum_le_sum fun j _ => measure_biUnion_finset_le _ _
      _ ≤ ∑ _j ∈ Finset.range (L + 1),
          (9 ^ L) • ENNReal.ofReal (2 ^ (L + 1) * (1 / 144 : ℝ) ^ L) :=
          Finset.sum_le_sum fun j _ =>
            (Finset.sum_le_card_nsmul _ _ _ fun l hl =>
              measure_countP_le hν hcl (length_of_mem_starWalkLists hl)).trans
              (nsmul_le_nsmul_left zero_le (card_starWalkLists_le L _))
      _ = ENNReal.ofReal (((L : ℝ) + 1) * 9 ^ L * (2 ^ (L + 1) * (1 / 144 : ℝ) ^ L)) := by
          have ha : ENNReal.ofReal (((L : ℝ) + 1) * 9 ^ L) = ((L + 1) * 9 ^ L : ℕ) := by
            rw [← ENNReal.ofReal_natCast]
            norm_num
          rw [Finset.sum_const, Finset.card_range, smul_smul, nsmul_eq_mul,
            ENNReal.ofReal_mul (p := ((L : ℝ) + 1) * 9 ^ L) (by positivity), ha]
      _ ≤ ENNReal.ofReal (2 * (1 / 4 : ℝ) ^ L) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have h2L : ((L : ℝ) + 1) ≤ 2 ^ L := by exact_mod_cast Nat.lt_two_pow_self
          calc ((L : ℝ) + 1) * 9 ^ L * (2 ^ (L + 1) * (1 / 144 : ℝ) ^ L)
              ≤ 2 ^ L * 9 ^ L * (2 ^ (L + 1) * (1 / 144 : ℝ) ^ L) := by gcongr
            _ = 2 * (2 * 9 * 2 * (1 / 144 : ℝ)) ^ L := by
                rw [mul_pow, mul_pow, mul_pow, pow_succ]
                ring
            _ = 2 * (1 / 4 : ℝ) ^ L := by norm_num
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hexp : ∀ L : ℕ, N₀ ≤ 4 * (L : ℝ) →
      2 * (1 / 4 : ℝ) ^ L ≤ 2 * Real.exp (-(Real.log 2 / 4 * N₀)) * (1 / 2) ^ L := by
    intro L hL
    have hhalf : (1 / 2 : ℝ) ^ L = Real.exp (-(L * Real.log 2)) := by
      rw [← mul_neg, Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by norm_num)]
      norm_num
    have hq : (1 / 4 : ℝ) ^ L = (1 / 2) ^ L * (1 / 2) ^ L := by
      rw [← mul_pow]
      norm_num
    have hle : (1 / 2 : ℝ) ^ L ≤ Real.exp (-(Real.log 2 / 4 * N₀)) := by
      rw [hhalf]
      exact Real.exp_le_exp.mpr (by nlinarith)
    rw [hq]
    have h0 : (0 : ℝ) ≤ (1 / 2) ^ L := by positivity
    nlinarith
  have hU : walkPeierlsEvent N₀ = ⋃ L : ℕ, ⋃ (_ : N₀ ≤ 4 * (L : ℝ)),
      ⋃ j ∈ Finset.range (L + 1), ⋃ l ∈ starWalkLists L ((j : ℤ), 0),
        {η : PlanarCarrier → Bool | l.Nodup ∧ 2 * l.countP η ≤ L} := rfl
  rw [hU]
  calc _ ≤ ∑' L : ℕ, ν (⋃ (_ : N₀ ≤ 4 * (L : ℝ)), ⋃ j ∈ Finset.range (L + 1),
        ⋃ l ∈ starWalkLists L ((j : ℤ), 0),
          {η : PlanarCarrier → Bool | l.Nodup ∧ 2 * l.countP η ≤ L}) := measure_iUnion_le _
    _ ≤ ∑' L : ℕ, ENNReal.ofReal (2 * Real.exp (-(Real.log 2 / 4 * N₀)) * (1 / 2) ^ L) := by
        refine ENNReal.tsum_le_tsum fun L => ?_
        by_cases hL : N₀ ≤ 4 * (L : ℝ)
        · exact (measure_mono (Set.iUnion_subset fun _ => subset_rfl)).trans
            ((hterm L).trans (ENNReal.ofReal_le_ofReal (hexp L hL)))
        · rw [Set.iUnion_eq_empty.mpr fun h => absurd h hL, measure_empty]
          exact zero_le
    _ = ENNReal.ofReal (∑' L : ℕ, 2 * Real.exp (-(Real.log 2 / 4 * N₀)) * (1 / 2) ^ L) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun L => by positivity)
          (summable_geometric_two.mul_left _)).symm
    _ = ENNReal.ofReal (4 * Real.exp (-(Real.log 2 / 4 * N₀))) := by
        rw [tsum_mul_left, tsum_geometric_two]
        congr 1
        ring

/-! ### The steps -/

/-- Step `step:5.24-crossings` for `1`-dependent fields, with `ε₀ = 144⁻¹⁸`, `c₂ = 1 / 8`,
`C = 4` and `c = log 2 / 4`. -/
theorem oneDependentWalkStep : OneDependentWalkStep := by
  refine ⟨(1 / 144 : ℝ) ^ 18, by positivity, 1 / 8, 4, Real.log 2 / 4, by norm_num, by norm_num,
    div_pos (Real.log_pos one_lt_two) (by norm_num), ?_⟩
  intro ν hν hdep hcl N₀ hN₀
  haveI := hν
  exact (measure_mono (renormWalkDeficient_subset hN₀)).trans
    (measure_walkPeierlsEvent_le hdep hcl N₀)

/-- Step `step:5.24-crossings` for Bernoulli site percolation, with `q₀ = 1 - 144⁻¹⁸`,
`c₂ = 1 / 8`, `C = 4` and `c = log 2 / 4`; the increasing event is the complement of the Peierls
event. -/
theorem siteWalkStep : SiteWalkStep := by
  have hε : (0 : ℝ) < (1 / 144 : ℝ) ^ 18 := by positivity
  refine ⟨1 - (1 / 144 : ℝ) ^ 18, by linarith, 1 / 8, 4, Real.log 2 / 4, by norm_num, by norm_num,
    div_pos (Real.log_pos one_lt_two) (by norm_num), ?_⟩
  intro q hq hq₀ N₀ hN₀
  refine ⟨(walkPeierlsEvent N₀)ᶜ, (measurableSet_walkPeierlsEvent N₀).compl,
    isIncreasingSet_compl_walkPeierlsEvent N₀,
    Set.compl_subset_compl.mpr (renormWalkDeficient_subset hN₀), ?_⟩
  rw [compl_compl]
  refine measure_walkPeierlsEvent_le (kDependentPlanar_bernoulliFieldPlanar 1 q hq)
    (fun z => ?_) N₀
  have hmeas : MeasurableSet {η : PlanarCarrier → Bool | η z = true} :=
    (measurable_pi_apply z : Measurable fun η : PlanarCarrier → Bool => η z)
      (measurableSet_singleton true)
  have hcompl : {η : PlanarCarrier → Bool | η z = false} = {η | η z = true}ᶜ := by
    ext η
    simp
  rw [hcompl, prob_compl_eq_one_sub hmeas, bernoulliFieldPlanar_oneSite, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub _ (NNReal.coe_nonneg q)]
  exact ENNReal.ofReal_le_ofReal (by linarith)

end Rigidity.Proofs.Section5
