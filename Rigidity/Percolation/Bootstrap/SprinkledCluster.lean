import Rigidity.Percolation.Bootstrap.Composition

/-!
# Clusters at bond-dependent levels

A bond-dependent level `β` opens the bond `e` when its mark is at most `β e`. The cluster of a set
`γ` inside a finite region `W` at level `β` equals a set `S'` with `γ ⊆ S' ⊆ W` exactly when every
vertex of `S'` is joined to `γ` inside `S'` and every bond of the cut from `S'` to `W \ S'` has
mark above its level. The sprinkled cluster of `S` raises the level from `p₀` to `q` on the cut
from `S` to `W \ S` only.

A connection from `X` to `Y` inside `R` can be shortened to one whose interior avoids `X ∪ Y`, so
it does not depend on the bonds internal to `X` or to `Y`.
-/

noncomputable section

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External
open scoped unitInterval

variable {d : ℕ}

/-! ### Bond-dependent levels -/

/-- Threshold each bond mark at its own level. -/
def thresholdWith (β : Bond d → unitInterval) (ω : BondMarks d) : Configuration d :=
  fun e => markThreshold (β e) (ω e)

/-- Thresholding at bond-dependent levels uses only the marks at the corresponding bonds. -/
theorem measurable_thresholdWith_bondSigma (β : Bond d → unitInterval) (E : Set (Bond d)) :
    @Measurable _ _ (bondMarkSigma E) (bondSigma E) (thresholdWith β) := by
  apply measurable_iff_comap_le.mpr
  simp only [bondSigma, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  apply iSup₂_le
  intro e he
  have hcoord : @Measurable _ _ (bondMarkSigma E) _ (fun ω : BondMarks d => ω e) :=
    measurable_iff_comap_le.mpr (le_iSup_of_le e (le_iSup_of_le he le_rfl))
  exact ((measurable_markThreshold (β e)).comp hcoord).comap_le

/-- Thresholding at bond-dependent levels is measurable. -/
theorem measurable_thresholdWith (β : Bond d → unitInterval) :
    Measurable (thresholdWith (d := d) β) := by
  apply measurable_pi_lambda
  intro e
  exact (measurable_markThreshold (β e)).comp (measurable_pi_apply e)

/-- Raising the levels opens more bonds. -/
theorem thresholdWith_mono {β β' : Bond d → unitInterval} (h : ∀ e, β e ≤ β' e)
    (ω : BondMarks d) : thresholdWith β ω ≤ thresholdWith β' ω := by
  intro e
  change markThreshold (β e) (ω e) ≤ markThreshold (β' e) (ω e)
  unfold markThreshold
  by_cases h1 : ω e ≤ β e
  · simp [h1, h1.trans (h e)]
  · simp [h1]

/-- Levels below `q` open fewer bonds than the constant level `q`. -/
theorem thresholdWith_le_thresholdBondMarks {β : Bond d → unitInterval} {q : unitInterval}
    (h : ∀ e, β e ≤ q) (ω : BondMarks d) : thresholdWith β ω ≤ thresholdBondMarks q ω :=
  thresholdWith_mono (β' := constThreshold q) h ω

/-! ### Clusters at bond-dependent levels -/

/-- The vertices of `W` joined inside `W` to `γ` at the levels `β`. -/
def clusterWith (β : Bond d → unitInterval) (γ W : Finset (Vertex d)) (ω : BondMarks d) :
    Finset (Vertex d) := by
  classical
  exact W.filter fun z => ∃ g ∈ γ, (openIn (thresholdWith β ω) W).Reachable g z

/-- Every vertex of `S'` is joined to `γ` inside `S'` at the levels `β`. -/
def genWith (β : Bond d → unitInterval) (γ S' : Finset (Vertex d)) : Set (BondMarks d) :=
  {ω | ∀ z ∈ S', ∃ g ∈ γ, (openIn (thresholdWith β ω) S').Reachable g z}

/-- The cluster lies in the region. -/
theorem clusterWith_subset (β : Bond d → unitInterval) (γ W : Finset (Vertex d))
    (ω : BondMarks d) : clusterWith β γ W ω ⊆ W := by
  classical
  intro z hz
  exact (Finset.mem_filter.1 hz).1

/-- The cluster contains the generating set. -/
theorem subset_clusterWith (β : Bond d → unitInterval) {γ W : Finset (Vertex d)} (hγ : γ ⊆ W)
    (ω : BondMarks d) : γ ⊆ clusterWith β γ W ω := by
  classical
  intro g hg
  exact Finset.mem_filter.2 ⟨hγ hg, g, hg, SimpleGraph.Reachable.refl _⟩

/-- Every vertex of the cluster is joined to the generating set inside the cluster. -/
theorem reachable_of_mem_clusterWith (β : Bond d → unitInterval) {γ W : Finset (Vertex d)}
    (hγ : γ ⊆ W) {ω : BondMarks d} {z : Vertex d} (hz : z ∈ clusterWith β γ W ω) :
    ∃ g ∈ γ, (openIn (thresholdWith β ω) (clusterWith β γ W ω : Set (Vertex d))).Reachable g z := by
  classical
  obtain ⟨-, g, hg, ⟨w⟩⟩ := Finset.mem_filter.1 hz
  refine ⟨g, hg, reachable_cluster_of_walk (γ := (γ : Set (Vertex d))) ?_ w
    ⟨g, hg, SimpleGraph.Reachable.refl _⟩⟩
  rintro y ⟨g', hg', hg'y⟩
  have hyW : y ∈ (W : Set (Vertex d)) := mem_of_openIn_reachable hg'y.symm (hγ hg')
  exact Finset.mem_filter.2 ⟨hyW, g', hg', hg'y⟩

/-- **The cluster event at bond-dependent levels.** For `γ ⊆ S' ⊆ W`, the cluster of `γ` inside
`W` at the levels `β` is `S'` exactly when every vertex of `S'` is joined to `γ` inside `S'` and
every bond of the cut from `S'` to `W \ S'` has mark above its level. -/
theorem clusterWith_eq_iff (β : Bond d → unitInterval) {γ S' W : Finset (Vertex d)}
    (hγ : γ ⊆ S') (hS' : S' ⊆ W) (ω : BondMarks d) :
    clusterWith β γ W ω = S' ↔
      ω ∈ genWith β γ S' ∧ ω ∈ bondMarksAbove (vertexCutBondsIn S' W) β := by
  classical
  set η := thresholdWith β ω with hη
  constructor
  · intro h
    have hmem : ∀ z, (∃ g ∈ γ, (openIn η W).Reachable g z) → z ∈ S' := by
      intro z hz
      have hzW : z ∈ W := by
        obtain ⟨g, hg, hgz⟩ := hz
        rw [SimpleGraph.reachable_comm] at hgz
        exact mem_of_openIn_reachable hgz (hS' (hγ hg))
      rw [← h]
      exact Finset.mem_filter.2 ⟨hzW, hz⟩
    refine ⟨fun z hz => ?_, fun e he => ?_⟩
    · have hz' : z ∈ clusterWith β γ W ω := h ▸ hz
      obtain ⟨-, g, hg, ⟨w⟩⟩ := Finset.mem_filter.1 hz'
      exact ⟨g, hg, reachable_cluster_of_walk hmem w ⟨g, hg, SimpleGraph.Reachable.refl _⟩⟩
    · obtain ⟨x, hx, y, hy, hxy, rfl⟩ := exists_of_mem_vertexCutBondsIn he
      by_contra hle
      have hopen : η (bondOfAdjacent hxy) = true := by
        change markThreshold (β _) (ω (bondOfAdjacent hxy)) = true
        unfold markThreshold
        have : ω (bondOfAdjacent hxy) ≤ β (bondOfAdjacent hxy) := le_of_not_gt hle
        simp [this]
      have hxW : x ∈ (W : Set (Vertex d)) := hS' hx
      have hx' : x ∈ clusterWith β γ W ω := h ▸ hx
      obtain ⟨-, g, hg, hgx⟩ := Finset.mem_filter.1 hx'
      have hgy : (openIn η W).Reachable g y :=
        hgx.trans (SimpleGraph.Adj.reachable ⟨(openGraph_adj_iff η x y).2 ⟨hxy, hopen⟩, hxW, hy.1⟩)
      exact hy.2 (hmem y ⟨g, hg, hgy⟩)
  · rintro ⟨hgen, hcut⟩
    ext z
    constructor
    · intro hz
      obtain ⟨hzW, g, hg, ⟨w⟩⟩ := Finset.mem_filter.1 hz
      by_contra hzS
      obtain ⟨x, hx, y, hy, hxy⟩ := exists_exit_of_walk w (S := (S' : Set (Vertex d)))
        (Finset.mem_coe.2 (hγ hg)) (fun h => hzS (Finset.mem_coe.1 h))
      obtain ⟨hadj, hopen⟩ := (openGraph_adj_iff η x y).1 hxy.1
      have hcutmem : bondOfAdjacent hadj ∈ vertexCutBondsIn S' W :=
        bondOfAdjacent_mem_vertexCutBondsIn S' W (fun a ha => hS' ha) hx hy hadj
      have hgt := hcut _ hcutmem
      change markThreshold (β _) (ω (bondOfAdjacent hadj)) = true at hopen
      unfold markThreshold at hopen
      have : ¬ ω (bondOfAdjacent hadj) ≤ β (bondOfAdjacent hadj) := not_le.2 hgt
      simp [this] at hopen
    · intro hz
      obtain ⟨g, hg, hgz⟩ := hgen z hz
      exact Finset.mem_filter.2 ⟨hS' hz, g, hg,
        hgz.mono (by intro a b hab; exact ⟨hab.1, hS' hab.2.1, hS' hab.2.2⟩)⟩

/-- The generation event is determined by the bonds internal to `S'`. -/
theorem measurableSet_genWith (β : Bond d → unitInterval) (γ S' : Finset (Vertex d)) :
    MeasurableSet[bondMarkSigma (localBonds (S' : Set (Vertex d)))] (genWith β γ S') := by
  classical
  have heq : genWith β γ S' = ⋂ z ∈ S', ⋃ g ∈ γ,
      thresholdWith β ⁻¹' {η | (openIn η S').Reachable g z} := by
    ext ω
    simp only [genWith, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion, Set.mem_preimage,
      exists_prop]
  rw [heq]
  refine Finset.measurableSet_biInter _ fun z hz => Finset.measurableSet_biUnion _ fun g hg => ?_
  by_cases hgS : g ∈ S'
  · exact (measurable_thresholdWith_bondSigma β _)
      (measurableSet_reachable_openIn_bondSigma (S' : Set (Vertex d)) S'.finite_toSet hgS hz)
  · have : {η : Configuration d | (openIn η (S' : Set (Vertex d))).Reachable g z} =
        if g = z then Set.univ else ∅ := by
      ext η
      split_ifs with hgz
      · simp [hgz]
      · simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro h
        exact hgS (mem_of_openIn_reachable h hz)
    rw [this]
    split_ifs <;> simp

/-- The event that the cluster takes a given value is measurable. -/
theorem measurableSet_clusterWith_eq (β : Bond d → unitInterval) {γ W : Finset (Vertex d)}
    (hγ : γ ⊆ W) (S' : Finset (Vertex d)) :
    MeasurableSet {ω | clusterWith β γ W ω = S'} := by
  classical
  by_cases h : γ ⊆ S' ∧ S' ⊆ W
  · have heq : {ω | clusterWith β γ W ω = S'} =
        genWith β γ S' ∩ bondMarksAbove (vertexCutBondsIn S' W) β := by
      ext ω
      exact clusterWith_eq_iff β h.1 h.2 ω
    rw [heq]
    exact (bondMarkSigma_le _ _ (measurableSet_genWith β γ S')).inter
      (measurableSet_bondMarksAbove _ _)
  · have heq : {ω | clusterWith β γ W ω = S'} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hω
      exact h ⟨hω ▸ subset_clusterWith β hγ ω, hω ▸ clusterWith_subset β γ W ω⟩
    rw [heq]
    exact MeasurableSet.empty

/-! ### Connections avoiding the end sets -/

/-- Enlarging the region keeps reachability. -/
theorem openIn_reachable_mono_region {η : Configuration d} {B B' : Set (Vertex d)} (h : B ⊆ B')
    {x y : Vertex d} (hxy : (openIn η B).Reachable x y) : (openIn η B').Reachable x y :=
  hxy.mono (by intro a b hab; exact ⟨hab.1, h hab.2.1, h hab.2.2⟩)

/-- A walk inside `R` ending in `Y` and starting from a vertex joined to `x ∈ X` through vertices
outside `X ∪ Y` yields a connection from `X` to `Y` whose interior avoids `X ∪ Y`. -/
theorem exists_avoiding_of_walk {η : Configuration d} {R X Y : Set (Vertex d)} :
    ∀ {v b : Vertex d} (_w : (openIn η R).Walk v b), b ∈ Y → ∀ x ∈ X, x ∈ R →
      (openIn η (insert x (R \ (X ∪ Y)))).Reachable x v →
      ∃ x' ∈ X, x' ∈ R ∧ ∃ y ∈ Y, y ∈ R ∧
        (openIn η (insert x' (insert y (R \ (X ∪ Y))))).Reachable x' y
  | _, _, .nil, hb, x, hx, hxR, hxv => by
      rcases mem_of_openIn_reachable hxv.symm (Set.mem_insert x _) with h | h
      · subst h
        exact ⟨_, hx, hxR, _, hb, hxR, SimpleGraph.Reachable.refl _⟩
      · exact absurd (Or.inr hb) h.2
  | v, _, .cons (v := v') h w, hb, x, hx, hxR, hxv => by
      have hv : v ∈ insert x (R \ (X ∪ Y)) := mem_of_openIn_reachable hxv.symm (Set.mem_insert x _)
      by_cases hv'Y : v' ∈ Y
      · refine ⟨x, hx, hxR, v', hv'Y, h.2.2, ?_⟩
        have hsub : insert x (R \ (X ∪ Y)) ⊆ insert x (insert v' (R \ (X ∪ Y))) :=
          Set.insert_subset_insert (Set.subset_insert _ _)
        have hedge : (openIn η (insert x (insert v' (R \ (X ∪ Y))))).Adj v v' :=
          ⟨h.1, hsub hv, Set.mem_insert_of_mem _ (Set.mem_insert _ _)⟩
        exact (openIn_reachable_mono_region hsub hxv).trans hedge.reachable
      · by_cases hv'X : v' ∈ X
        · exact exists_avoiding_of_walk w hb v' hv'X h.2.2 (SimpleGraph.Reachable.refl _)
        · have hv'D : v' ∈ insert x (R \ (X ∪ Y)) :=
            Set.mem_insert_of_mem _ ⟨h.2.2, fun h' => h'.elim hv'X hv'Y⟩
          exact exists_avoiding_of_walk w hb x hx hxR (hxv.trans (SimpleGraph.Adj.reachable
            ⟨h.1, hv, hv'D⟩))

/-- A connection from `X` to `Y` inside `R` can be taken with interior outside `X ∪ Y`. -/
theorem connectsRegions_iff_exists_avoiding {η : Configuration d} {R X Y : Set (Vertex d)} :
    ConnectsRegions η R X Y ↔ ∃ x ∈ X, x ∈ R ∧ ∃ y ∈ Y, y ∈ R ∧
      (openIn η (insert x (insert y (R \ (X ∪ Y))))).Reachable x y := by
  constructor
  · rintro ⟨x, hxR, hxX, y, hyR, hyY, ⟨w⟩⟩
    exact exists_avoiding_of_walk w hyY x hxX hxR (SimpleGraph.Reachable.refl _)
  · rintro ⟨x, hxX, hxR, y, hyY, hyR, hreach⟩
    refine ⟨x, hxR, hxX, y, hyR, hyY, openIn_reachable_mono_region ?_ hreach⟩
    intro z hz
    rcases hz with rfl | rfl | hz
    · exact hxR
    · exact hyR
    · exact hz.1

/-- The bonds inside the avoiding region are bonds of `R` internal to neither `X` nor `Y`. -/
theorem localBonds_avoiding_subset {R X Y : Set (Vertex d)} (hXY : Disjoint X Y) {x y : Vertex d}
    (hx : x ∈ X) (hxR : x ∈ R) (hy : y ∈ Y) (hyR : y ∈ R) :
    localBonds (insert x (insert y (R \ (X ∪ Y)))) ⊆
      localBonds R \ (localBonds X ∪ localBonds Y) := by
  intro e he
  obtain ⟨u, v, huv, hdist⟩ := e.2
  have hu : u ∈ e.1 := huv ▸ Sym2.mem_mk_left u v
  have hv : v ∈ e.1 := huv ▸ Sym2.mem_mk_right u v
  have hne : u ≠ v := by
    rintro rfl
    simp at hdist
  have hmemD : ∀ z ∈ e.1, z ∈ R ∧ (z ∈ X → z = x) ∧ (z ∈ Y → z = y) := by
    intro z hz
    rcases he z hz with rfl | rfl | hz'
    · exact ⟨hxR, fun _ => rfl, fun h => absurd h (Set.disjoint_left.1 hXY hx)⟩
    · exact ⟨hyR, fun h => absurd hy (Set.disjoint_left.1 hXY h), fun _ => rfl⟩
    · exact ⟨hz'.1, fun h => absurd (Or.inl h) hz'.2, fun h => absurd (Or.inr h) hz'.2⟩
  refine ⟨fun z hz => (hmemD z hz).1, ?_⟩
  rintro (hX | hY)
  · exact hne (((hmemD u hu).2.1 (hX u hu)).trans ((hmemD v hv).2.1 (hX v hv)).symm)
  · exact hne (((hmemD u hu).2.2 (hY u hu)).trans ((hmemD v hv).2.2 (hY v hv)).symm)

/-- A connection between disjoint sets inside a finite region at level `q` is determined by the
bonds of the region internal to neither set. -/
theorem measurableSet_connectsRegions_avoiding (q : unitInterval) (R X Y : Finset (Vertex d))
    (hXY : Disjoint X Y) :
    MeasurableSet[bondMarkSigma (localBonds (R : Set (Vertex d)) \
        (localBonds (X : Set (Vertex d)) ∪ localBonds (Y : Set (Vertex d))))]
      {ω | ConnectsRegions (thresholdBondMarks q ω) R X Y} := by
  classical
  set E := localBonds (R : Set (Vertex d)) \
    (localBonds (X : Set (Vertex d)) ∪ localBonds (Y : Set (Vertex d))) with hE
  have hdisj : Disjoint (X : Set (Vertex d)) (Y : Set (Vertex d)) := Finset.disjoint_coe.2 hXY
  have heq : {ω | ConnectsRegions (thresholdBondMarks q ω) R X Y} =
      ⋃ x ∈ X.filter (· ∈ R), ⋃ y ∈ Y.filter (· ∈ R), thresholdBondMarks q ⁻¹'
        {η | (openIn η (insert x (insert y ((R : Set (Vertex d)) \
          ((X : Set (Vertex d)) ∪ Y))))).Reachable x y} := by
    ext ω
    simp only [Set.mem_setOf_eq, connectsRegions_iff_exists_avoiding, Set.mem_iUnion,
      Set.mem_preimage, Finset.mem_filter, Finset.mem_coe, exists_prop]
    constructor
    · rintro ⟨x, hx, hxR, y, hy, hyR, h⟩
      exact ⟨x, ⟨hx, hxR⟩, y, ⟨hy, hyR⟩, h⟩
    · rintro ⟨x, ⟨hx, hxR⟩, y, ⟨hy, hyR⟩, h⟩
      exact ⟨x, hx, hxR, y, hy, hyR, h⟩
  rw [heq]
  refine Finset.measurableSet_biUnion _ fun x hx => Finset.measurableSet_biUnion _ fun y hy => ?_
  obtain ⟨hxX, hxR⟩ := Finset.mem_filter.1 hx
  obtain ⟨hyY, hyR⟩ := Finset.mem_filter.1 hy
  have hfin : (insert x (insert y ((R : Set (Vertex d)) \
      ((X : Set (Vertex d)) ∪ Y)))).Finite :=
    ((R.finite_toSet.sdiff).insert y).insert x
  have hloc := localBonds_avoiding_subset hdisj (Finset.mem_coe.2 hxX) (Finset.mem_coe.2 hxR)
    (Finset.mem_coe.2 hyY) (Finset.mem_coe.2 hyR)
  exact (measurable_thresholdBondMarks_bondSigma q E)
    (bondSigma_mono hloc _ (measurableSet_reachable_openIn_bondSigma _ hfin
      (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))

end Rigidity.Percolation
