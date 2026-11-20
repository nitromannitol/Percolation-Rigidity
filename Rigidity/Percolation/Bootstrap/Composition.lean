import Rigidity.Percolation.Bootstrap.SprinkledExit

/-!
# Composition of connection estimates by sprinkling

Let `γ ⊆ W` be finite vertex sets. Suppose that at level `p₀` the set `γ` is joined inside `W` to
a target `T` with probability at least `1 - ε₁`, and that every set `S' ⊆ W` containing `γ`,
lattice-connected to `γ` inside itself, meeting `T` and missing `T'` is joined inside `W` to `T'`
with probability at least `1 - ε₂`. Then at level `p₀ + δ` the set `γ` is joined inside `W` to
`T'` with probability at least `1 - ε₁ - ε₂ / (1 - p₀)^K - (1 - δ)^K`, for every `K`.

The proof decomposes according to the value `S'` of the open cluster of `γ` inside `W` at level
`p₀`. The event that this cluster equals `S'` is the intersection of an event of the bonds
internal to `S'` with the event that the cut from `S'` to `W \ S'` is closed at level `p₀`; on
it, one candidate exit of `S'` towards `T'` opens at level `p₀ + δ` except with the probability
of the sprinkled-exit estimate. This is Lemma 2.3.4 of D. Contreras, *Percolation on graphs of
polynomial growth*, ETH Zürich dissertation (2022).
-/

noncomputable section

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External
open scoped unitInterval

variable {d : ℕ}

/-! ### Cut bonds -/

/-- A bond of the cut from `R` to `W \ R` joins a vertex of `R` to a vertex of `W \ R`. -/
theorem exists_of_mem_vertexCutBondsIn {R : Finset (Vertex d)} {W : Set (Vertex d)}
    {e : Bond d} (he : e ∈ vertexCutBondsIn R W) :
    ∃ x ∈ R, ∃ y ∈ W \ (R : Set (Vertex d)), ∃ hxy : (nearestNeighborGraph d).Adj x y,
      e = bondOfAdjacent hxy := by
  classical
  obtain ⟨hcut, hloc⟩ := Finset.mem_filter.1 he
  obtain ⟨x, hx, hxe⟩ := Finset.mem_biUnion.1 hcut
  unfold outgoingBonds at hxe
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hxe
  have hyR : y.1 ∉ (R : Set (Vertex d)) := by
    simp only [Finset.mem_filter] at hy
    exact hy.2
  have hyW : y.1 ∈ W := hloc y.1 (Sym2.mem_mk_right _ _)
  exact ⟨x, hx, y.1, ⟨hyW, hyR⟩, _, rfl⟩

/-! ### Open clusters inside a region -/

/-- The vertices of `W` joined inside `W` to `γ` at level `p`. -/
def levelCluster (p : unitInterval) (γ W : Finset (Vertex d)) (ω : BondMarks d) :
    Finset (Vertex d) := by
  classical
  exact W.filter fun z => ∃ g ∈ γ, (openIn (thresholdBondMarks p ω) W).Reachable g z

/-- Every vertex of `S'` is joined to `γ` inside `S'` at level `p`. -/
def clusterGen (p : unitInterval) (γ S' : Finset (Vertex d)) : Set (BondMarks d) :=
  {ω | ∀ z ∈ S', ∃ g ∈ γ, (openIn (thresholdBondMarks p ω) S').Reachable g z}

/-- An open walk inside `W` from a vertex of `S` to a vertex outside `S` uses an open bond from `S`
to `W \ S`. -/
theorem exists_exit_of_walk {η : Configuration d} {W S : Set (Vertex d)} :
    ∀ {a z : Vertex d} (_w : (openIn η W).Walk a z), a ∈ S → z ∉ S →
      ∃ x ∈ S, ∃ y ∈ W \ S, (openIn η W).Adj x y
  | _, _, .nil, ha, hz => absurd ha hz
  | a, _, .cons (v := b) h w, ha, hz => by
    by_cases hb : b ∈ S
    · exact exists_exit_of_walk w hb hz
    · exact ⟨a, ha, b, ⟨h.2.2, hb⟩, h⟩

/-- A walk inside `W` all of whose vertices are reachable from `γ` stays inside the cluster. -/
theorem reachable_cluster_of_walk {η : Configuration d} {W S : Set (Vertex d)}
    {γ : Set (Vertex d)} (hS : ∀ z, (∃ g ∈ γ, (openIn η W).Reachable g z) → z ∈ S) :
    ∀ {a z : Vertex d} (_w : (openIn η W).Walk a z), (∃ g ∈ γ, (openIn η W).Reachable g a) →
      (openIn η S).Reachable a z
  | _, _, .nil, _ => SimpleGraph.Reachable.refl _
  | a, _, .cons (v := b) h w, ⟨g, hg, hga⟩ => by
    have hgb : (openIn η W).Reachable g b := hga.trans h.reachable
    have hedge : (openIn η S).Adj a b := ⟨h.1, hS a ⟨g, hg, hga⟩, hS b ⟨g, hg, hgb⟩⟩
    exact hedge.reachable.trans (reachable_cluster_of_walk hS w ⟨g, hg, hgb⟩)

/-- **The cluster event.** For `γ ⊆ S' ⊆ W`, the level-`p` cluster of `γ` inside `W` is `S'`
exactly when every vertex of `S'` is joined to `γ` inside `S'` and the cut from `S'` to `W \ S'`
is closed at level `p`. -/
theorem levelCluster_eq_iff (p : unitInterval) {γ S' W : Finset (Vertex d)} (hγ : γ ⊆ S')
    (hS' : S' ⊆ W) (ω : BondMarks d) :
    levelCluster p γ W ω = S' ↔ ω ∈ clusterGen p γ S' ∧ ω ∈ cutClosed p S' W := by
  classical
  set η := thresholdBondMarks p ω with hη
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
    · have hz' : z ∈ levelCluster p γ W ω := h ▸ hz
      obtain ⟨-, g, hg, ⟨w⟩⟩ := Finset.mem_filter.1 hz'
      exact ⟨g, hg, reachable_cluster_of_walk hmem w ⟨g, hg, SimpleGraph.Reachable.refl _⟩⟩
    · obtain ⟨x, hx, y, hy, hxy, rfl⟩ := exists_of_mem_vertexCutBondsIn he
      by_contra hle
      have hopen : η (bondOfAdjacent hxy) = true := by
        change markThreshold p (ω (bondOfAdjacent hxy)) = true
        unfold markThreshold
        have : ω (bondOfAdjacent hxy) ≤ p := le_of_not_gt hle
        simp [this]
      have hxW : x ∈ (W : Set (Vertex d)) := hS' hx
      have hx' : x ∈ levelCluster p γ W ω := h ▸ hx
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
      change markThreshold p (ω (bondOfAdjacent hadj)) = true at hopen
      unfold markThreshold at hopen
      have : ¬ ω (bondOfAdjacent hadj) ≤ p := not_le.2 hgt
      simp [this] at hopen
    · intro hz
      obtain ⟨g, hg, hgz⟩ := hgen z hz
      exact Finset.mem_filter.2 ⟨hS' hz, g, hg,
        hgz.mono (by intro a b hab; exact ⟨hab.1, hS' hab.2.1, hS' hab.2.2⟩)⟩

/-! ### Measurability -/

/-- Candidate boundary bonds depend only on the bonds of any family containing the bonds
internal to the exterior. -/
theorem measurable_boundaryCandidateBonds_sigma (R D : Set (Vertex d)) (hD : D.Finite)
    (F : Finset (Bond d)) (T : Finset (Vertex d)) (E : Set (Bond d))
    (hlocal : localBonds (D \ R) ⊆ E) :
    @Measurable _ _ (bondSigma E) _ (boundaryCandidateBonds R D F (fun _ => T)) := by
  classical
  letI : MeasurableSpace (Configuration d) := bondSigma E
  apply measurable_finset_iff.mpr
  intro e
  have hreach (y z : Vertex d) (hy : y ∈ D \ R) (hz : z ∈ D \ R) :
      MeasurableSet {ω : Configuration d | (openIn ω (D \ R)).Reachable y z} :=
    bondSigma_mono hlocal _
      (measurableSet_reachable_openIn_bondSigma (D \ R) (hD.subset Set.sdiff_subset) hy hz)
  have heq : {ω : Configuration d | e ∈ boundaryCandidateBonds R D F (fun _ => T) ω} =
      ⋃ (_ : e ∈ F), ⋃ x ∈ R, ⋃ y ∈ D \ R,
      ⋃ hxy : (nearestNeighborGraph d).Adj x y, ⋃ (_ : e = bondOfAdjacent hxy),
      ⋃ z ∈ D \ R, ⋃ (_ : z ∈ T), {ω | (openIn ω (D \ R)).Reachable y z} := by
    ext ω
    simp only [Set.mem_setOf_eq, mem_boundaryCandidateBonds, Set.mem_iUnion]
    constructor
    · rintro ⟨he, x, hx, y, hy, hxy, heq, z, hzK, hz, h⟩
      exact ⟨he, x, hx, y, hy, hxy, heq, z, hz, hzK, h⟩
    · rintro ⟨he, x, hx, y, hy, hxy, heq, z, hz, hzK, h⟩
      exact ⟨he, x, hx, y, hy, hxy, heq, z, hzK, hz, h⟩
  apply measurableSet_setOf.mp
  rw [heq]
  exact MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun x =>
    MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun y =>
    MeasurableSet.iUnion fun hy => MeasurableSet.iUnion fun _ =>
    MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun z =>
    MeasurableSet.iUnion fun hz => MeasurableSet.iUnion fun _ => hreach y z hy hz

/-- A bond of the cut from `S` is not internal to `S`. -/
theorem not_mem_localBonds_of_mem_vertexCutBondsIn {S : Finset (Vertex d)} {W : Set (Vertex d)}
    {e : Bond d} (he : e ∈ vertexCutBondsIn S W) : e ∉ localBonds (S : Set (Vertex d)) := by
  obtain ⟨x, -, y, hy, hxy, rfl⟩ := exists_of_mem_vertexCutBondsIn he
  intro hloc
  exact hy.2 (hloc y (Sym2.mem_mk_right _ _))

/-- The generation event is determined by the bonds internal to `S'`. -/
theorem measurableSet_clusterGen (p : unitInterval) (γ S' : Finset (Vertex d)) :
    MeasurableSet[bondMarkSigma (localBonds (S' : Set (Vertex d)))] (clusterGen p γ S') := by
  classical
  have heq : clusterGen p γ S' = ⋂ z ∈ S', ⋃ g ∈ γ,
      thresholdBondMarks p ⁻¹' {η | (openIn η S').Reachable g z} := by
    ext ω
    simp only [clusterGen, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion, Set.mem_preimage,
      exists_prop]
  rw [heq]
  refine Finset.measurableSet_biInter _ fun z hz => Finset.measurableSet_biUnion _ fun g hg => ?_
  by_cases hgS : g ∈ S'
  · exact (measurable_thresholdBondMarks_bondSigma p _)
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

/-- The closed-cut event is determined by the bonds not internal to `S'`. -/
theorem measurableSet_cutClosed_compl (p : unitInterval) (S' W : Finset (Vertex d)) :
    MeasurableSet[bondMarkSigma (localBonds (S' : Set (Vertex d)))ᶜ] (cutClosed p S' W) := by
  apply bondMarkSigma_mono _ _ (measurableSet_bondMarksAbove_local _ _)
  intro e he
  exact not_mem_localBonds_of_mem_vertexCutBondsIn he

/-- The exit event is determined by the bonds not internal to `S'`. -/
theorem measurableSet_exitOpens_compl (p : unitInterval) (δ : ℝ) (hδ : 0 ≤ δ)
    (hδ1 : (p : ℝ) + δ ≤ 1) (S' W T : Finset (Vertex d)) :
    MeasurableSet[bondMarkSigma (localBonds (S' : Set (Vertex d)))ᶜ]
      (exitOpens p δ hδ hδ1 S' W T) := by
  classical
  set E := (localBonds (S' : Set (Vertex d)))ᶜ with hE
  have hlocal : localBonds ((W : Set (Vertex d)) \ (S' : Set (Vertex d))) ⊆ E := by
    intro e he hin
    obtain ⟨x, y, hxy, -⟩ := e.2
    have hx : x ∈ e.1 := hxy ▸ Sym2.mem_mk_left x y
    exact (he x hx).2 (hin x hx)
  have hU : @Measurable _ _ (bondMarkSigma E) _ (exitCandidates p S' W T) :=
    (measurable_boundaryCandidateBonds_sigma _ _ W.finite_toSet _ T E hlocal).comp
      (measurable_thresholdBondMarks_bondSigma p E)
  have heq : exitOpens p δ hδ hδ1 S' W T = ⋃ e ∈ vertexCutBondsIn S' W,
      {ω | e ∈ exitCandidates p S' W T ω} ∩
        (fun ω : BondMarks d => ω e) ⁻¹' Set.Iic (raisedLevel p δ hδ hδ1) := by
    ext ω
    simp only [exitOpens, selectedBondMarkSuccess, Set.mem_setOf_eq, Set.mem_iUnion,
      Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic, exists_prop]
    constructor
    · rintro ⟨e, he, hle⟩
      refine ⟨e, exitCandidates_subset p S' W T ω he, he, ?_⟩
      simpa only [raisedBondThreshold, he, ↓reduceIte, raisedLevel, constThreshold] using hle
    · rintro ⟨e, -, he, hle⟩
      refine ⟨e, he, ?_⟩
      simpa only [raisedBondThreshold, he, ↓reduceIte, raisedLevel, constThreshold] using hle
  rw [heq]
  refine Finset.measurableSet_biUnion _ fun e he => MeasurableSet.inter ?_ ?_
  · letI : MeasurableSpace (BondMarks d) := bondMarkSigma E
    exact measurableSet_setOf.mpr ((measurable_finset_iff.mp hU) e)
  · have hcoord : @Measurable _ _ (bondMarkSigma E) _ (fun ω : BondMarks d => ω e) :=
      measurable_iff_comap_le.mpr
        (le_iSup_of_le e (le_iSup_of_le (not_mem_localBonds_of_mem_vertexCutBondsIn he) le_rfl))
    exact measurableSet_Iic.preimage hcoord

/-- Events of the bonds internal to `S'` and of the other bonds are independent. -/
theorem bondMarkLaw_real_inter_localBonds (S : Set (Vertex d)) {A B : Set (BondMarks d)}
    (hA : MeasurableSet[bondMarkSigma (localBonds S)] A)
    (hB : MeasurableSet[bondMarkSigma (localBonds S)ᶜ] B) :
    (bondMarkLaw d).real (A ∩ B) = (bondMarkLaw d).real A * (bondMarkLaw d).real B := by
  have hind := (Indep_iff _ _ _).mp (indep_bondMarkSigma (disjoint_compl_right (a := localBonds S)))
    A B hA hB
  change ((bondMarkLaw d) (A ∩ B)).toReal = _
  rw [hind, ENNReal.toReal_mul]
  rfl

/-- Every threshold configuration is below the configuration with all bonds open. -/
theorem thresholdBondMarks_le_allOpen (p : unitInterval) (ω : BondMarks d) :
    thresholdBondMarks p ω ≤ allOpen d :=
  fun _ => Bool.le_true _

/-- **Composition by sprinkling.** If `γ` reaches `T` inside `W` at level `p₀` with probability
at least `1 - ε₁`, and every set containing `γ`, lattice-connected to `γ` inside itself, meeting
`T` and missing `T'` reaches `T'` inside `W` at level `p₀` with probability at least `1 - ε₂`,
then `γ` reaches `T'` inside `W` at level `p₀ + δ` with probability at least
`1 - ε₁ - ε₂ / (1 - p₀)^K - (1 - δ)^K`. -/
theorem composition_prob (p₀ : unitInterval) (hp₀ : (p₀ : ℝ) < 1) (δ : ℝ) (hδ : 0 < δ)
    (hδ1 : (p₀ : ℝ) + δ ≤ 1) (γ W T T' : Finset (Vertex d)) (hγW : γ ⊆ W) (ε₁ ε₂ : ℝ)
    (hε₂ : 0 ≤ ε₂) (K : ℕ)
    (h₁ : 1 - ε₁ ≤ (latticeBondLaw d p₀).real
      {ω | ConnectsRegions ω (W : Set (Vertex d)) γ T})
    (h₂ : ∀ S' : Finset (Vertex d), γ ⊆ S' → S' ⊆ W →
      (∀ z ∈ S', ∃ g ∈ γ, (openIn (allOpen d) (S' : Set (Vertex d))).Reachable g z) →
      (∃ t ∈ T, t ∈ S') → (∀ t ∈ T', t ∉ S') →
      1 - ε₂ ≤ (latticeBondLaw d p₀).real
        {ω | ConnectsRegions ω (W : Set (Vertex d)) S' T'}) :
    1 - (ε₁ + (ε₂ / (1 - (p₀ : ℝ)) ^ K + (1 - δ) ^ K)) ≤
      (latticeBondLaw d (raisedLevel p₀ δ hδ.le hδ1)).real
        {ω | ConnectsRegions ω (W : Set (Vertex d)) γ T'} := by
  classical
  set q := raisedLevel p₀ δ hδ.le hδ1 with hq
  set μ := bondMarkLaw d with hμdef
  set c : ℝ := ε₂ / (1 - (p₀ : ℝ)) ^ K + (1 - δ) ^ K with hc
  have hpK : 0 < (1 - (p₀ : ℝ)) ^ K := pow_pos (by linarith) _
  have hδ1' : δ ≤ 1 := by linarith [p₀.property.1]
  have hc0 : 0 ≤ c := add_nonneg (div_nonneg hε₂ hpK.le) (pow_nonneg (by linarith) _)
  have hpq : p₀ ≤ q := by
    change (p₀ : ℝ) ≤ (p₀ : ℝ) + δ
    linarith
  have hmono : ∀ ω : BondMarks d, ∀ B : Set (Vertex d),
      openIn (thresholdBondMarks p₀ ω) B ≤ openIn (thresholdBondMarks q ω) B :=
    fun ω B => openIn_mono_configuration (thresholdBondMarks_mono hpq ω) B
  have hWc : ((γ : Set (Vertex d))) ⊆ (W : Set (Vertex d)) := fun x hx => hγW hx
  set Good := {ω : Configuration d | ConnectsRegions ω (W : Set (Vertex d)) γ T'} with hGooddef
  have hGood : MeasurableSet Good := measurableSet_connectsRegions _ _ _
  have hthr : ∀ r : unitInterval, Measurable (thresholdBondMarks (d := d) r) := by
    intro r
    apply measurable_pi_lambda
    intro e
    exact (measurable_markThreshold r).comp (measurable_pi_apply e)
  rw [← bondMarkLaw_real_preimage_threshold q hGood]
  set A₀ : Set (BondMarks d) := thresholdBondMarks p₀ ⁻¹'
    {ω | ConnectsRegions ω (W : Set (Vertex d)) γ T}ᶜ with hA₀def
  have hA₀ : μ.real A₀ ≤ ε₁ := by
    rw [hA₀def, bondMarkLaw_real_preimage_threshold p₀
      (measurableSet_connectsRegions _ _ _).compl,
      measureReal_compl (measurableSet_connectsRegions _ _ _), probReal_univ]
    linarith
  set 𝒮 := W.powerset.filter fun S' => γ ⊆ S' ∧ (∃ t ∈ T, t ∈ S') ∧ ∀ t ∈ T', t ∉ S'
    with h𝒮
  set G : Finset (Vertex d) → Set (BondMarks d) := fun S' =>
    clusterGen p₀ γ S' ∩ cutClosed p₀ S' W with hGdef
  set B : Finset (Vertex d) → Set (BondMarks d) := fun S' =>
    clusterGen p₀ γ S' ∩ (cutClosed p₀ S' W ∩ (exitOpens p₀ δ hδ.le hδ1 S' W T')ᶜ)
    with hBdef
  have hcover : (thresholdBondMarks q ⁻¹' Good)ᶜ ⊆ A₀ ∪ ⋃ S' ∈ 𝒮, B S' := by
    intro ω hω
    have hω' : ¬ ConnectsRegions (thresholdBondMarks q ω) (W : Set (Vertex d)) γ T' := hω
    by_cases h0 : ConnectsRegions (thresholdBondMarks p₀ ω) (W : Set (Vertex d)) γ T
    · right
      set S' := levelCluster p₀ γ W ω with hS'def
      have hS'W : S' ⊆ W := Finset.filter_subset _ _
      have hγS' : γ ⊆ S' := fun g hg =>
        Finset.mem_filter.2 ⟨hγW hg, g, hg, SimpleGraph.Reachable.refl _⟩
      have hmeet : ∃ t ∈ T, t ∈ S' := by
        obtain ⟨x, -, hxγ, y, hyW, hyT, hxy⟩ := h0
        exact ⟨y, hyT, Finset.mem_filter.2 ⟨hyW, x, hxγ, hxy⟩⟩
      have hmiss : ∀ t ∈ T', t ∉ S' := by
        intro t ht htS
        obtain ⟨htW, g, hg, hgt⟩ := Finset.mem_filter.1 htS
        exact hω' ⟨g, hWc hg, hg, t, htW, ht, hgt.mono (hmono ω _)⟩
      have hmem : S' ∈ 𝒮 :=
        Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hS'W, hγS', hmeet, hmiss⟩
      have hchar := (levelCluster_eq_iff p₀ hγS' hS'W ω).1 rfl
      refine Set.mem_iUnion₂.2 ⟨S', hmem, hchar.1, hchar.2, fun hexit => ?_⟩
      obtain ⟨x, hx, z, hz, hzout, hxz⟩ := exitOpens_connects p₀ δ hδ.le hδ1 S' W T'
        (fun a ha => hS'W ha) hexit
      obtain ⟨-, g, hg, hgx⟩ := Finset.mem_filter.1 hx
      exact hω' ⟨g, hWc hg, hg, z, hzout.1, hz, (hgx.mono (hmono ω _)).trans hxz⟩
    · left
      exact h0
  have hBle : ∀ S' ∈ 𝒮, μ.real (B S') ≤ c * μ.real (G S') := by
    intro S' hS'
    obtain ⟨hS'pow, hγS', hmeet, hmiss⟩ := Finset.mem_filter.1 hS'
    have hS'W : S' ⊆ W := Finset.mem_powerset.1 hS'pow
    by_cases hconn : ∀ z ∈ S', ∃ g ∈ γ,
        (openIn (allOpen d) (S' : Set (Vertex d))).Reachable g z
    · have h2 := h₂ S' hγS' hS'W hconn hmeet hmiss
      have hexit := bondMarkLaw_real_cutClosed_inter_not_exitOpens_le p₀ hp₀ δ hδ hδ1 S' W T'
        (fun a ha => hS'W ha) K
      have hnot : (latticeBondLaw d p₀).real {ω | ¬ ∃ x ∈ S', ∃ z ∈ T',
          z ∈ (W : Set (Vertex d)) \ (S' : Set (Vertex d)) ∧
            (openIn ω (W : Set (Vertex d))).Reachable x z} ≤ ε₂ := by
        have hsub : {ω : Configuration d | ¬ ∃ x ∈ S', ∃ z ∈ T',
            z ∈ (W : Set (Vertex d)) \ (S' : Set (Vertex d)) ∧
              (openIn ω (W : Set (Vertex d))).Reachable x z} ⊆
            {ω | ConnectsRegions ω (W : Set (Vertex d)) S' T'}ᶜ := by
          intro ω hω hcon
          obtain ⟨x, -, hxS, y, hyW, hyT, hxy⟩ := hcon
          exact hω ⟨x, hxS, y, hyT, ⟨hyW, hmiss y hyT⟩, hxy⟩
        calc _ ≤ (latticeBondLaw d p₀).real
              {ω | ConnectsRegions ω (W : Set (Vertex d)) S' T'}ᶜ := measureReal_mono hsub
          _ = 1 - (latticeBondLaw d p₀).real
              {ω | ConnectsRegions ω (W : Set (Vertex d)) S' T'} := by
            rw [measureReal_compl (measurableSet_connectsRegions _ _ _), probReal_univ]
          _ ≤ ε₂ := by linarith
      have hfactor : (latticeBondLaw d p₀).real {ω | ¬ ∃ x ∈ S', ∃ z ∈ T',
          z ∈ (W : Set (Vertex d)) \ (S' : Set (Vertex d)) ∧
            (openIn ω (W : Set (Vertex d))).Reachable x z} / (1 - (p₀ : ℝ)) ^ K +
          (1 - δ) ^ K ≤ c := by
        rw [hc]
        gcongr
      calc μ.real (B S') = μ.real (clusterGen p₀ γ S') *
            μ.real (cutClosed p₀ S' W ∩ (exitOpens p₀ δ hδ.le hδ1 S' W T')ᶜ) :=
          bondMarkLaw_real_inter_localBonds _ (measurableSet_clusterGen p₀ γ S')
            ((measurableSet_cutClosed_compl p₀ S' W).inter
              (measurableSet_exitOpens_compl p₀ δ hδ.le hδ1 S' W T').compl)
        _ ≤ μ.real (clusterGen p₀ γ S') * (c * μ.real (cutClosed p₀ S' W)) :=
          mul_le_mul_of_nonneg_left
            (hexit.trans (mul_le_mul_of_nonneg_right hfactor measureReal_nonneg))
            measureReal_nonneg
        _ = c * (μ.real (clusterGen p₀ γ S') * μ.real (cutClosed p₀ S' W)) := by ring
        _ = c * μ.real (G S') := by
          rw [hGdef, bondMarkLaw_real_inter_localBonds _ (measurableSet_clusterGen p₀ γ S')
            (measurableSet_cutClosed_compl p₀ S' W)]
    · have hempty : B S' = ∅ := by
        ext ω
        simp only [hBdef, Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
        intro hgen
        exfalso
        apply hconn
        intro z hz
        obtain ⟨g, hg, hgz⟩ := hgen z hz
        exact ⟨g, hg, hgz.mono (openIn_mono_configuration (thresholdBondMarks_le_allOpen p₀ ω) _)⟩
      rw [hempty, measureReal_empty]
      exact mul_nonneg hc0 measureReal_nonneg
  have hGmeas : ∀ S' ∈ 𝒮, MeasurableSet (G S') := fun S' _ =>
    (bondMarkSigma_le _ _ (measurableSet_clusterGen p₀ γ S')).inter
      (bondMarkSigma_le _ _ (measurableSet_cutClosed_compl p₀ S' W))
  have hpair : Set.PairwiseDisjoint (↑𝒮 : Set (Finset (Vertex d))) G := by
    intro S₁ hS₁ S₂ hS₂ hne
    change Disjoint (G S₁) (G S₂)
    rw [Set.disjoint_left]
    intro ω h1 h2
    obtain ⟨-, hγ1, -, -⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hS₁)
    obtain ⟨-, hγ2, -, -⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hS₂)
    have hW1 : S₁ ⊆ W := Finset.mem_powerset.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hS₁)).1
    have hW2 : S₂ ⊆ W := Finset.mem_powerset.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hS₂)).1
    have e1 := (levelCluster_eq_iff p₀ hγ1 hW1 ω).2 h1
    have e2 := (levelCluster_eq_iff p₀ hγ2 hW2 ω).2 h2
    exact hne (e1.symm.trans e2)
  have hsum : ∑ S' ∈ 𝒮, μ.real (G S') ≤ 1 := by
    rw [← measureReal_biUnion_finset hpair hGmeas]
    exact measureReal_le_one
  have hfail : μ.real (thresholdBondMarks q ⁻¹' Good)ᶜ ≤ ε₁ + c := by
    calc μ.real (thresholdBondMarks q ⁻¹' Good)ᶜ ≤ μ.real (A₀ ∪ ⋃ S' ∈ 𝒮, B S') :=
          measureReal_mono hcover
      _ ≤ μ.real A₀ + μ.real (⋃ S' ∈ 𝒮, B S') := measureReal_union_le _ _
      _ ≤ μ.real A₀ + ∑ S' ∈ 𝒮, μ.real (B S') :=
          add_le_add le_rfl (measureReal_biUnion_finset_le _ _)
      _ ≤ ε₁ + ∑ S' ∈ 𝒮, c * μ.real (G S') :=
          add_le_add hA₀ (Finset.sum_le_sum hBle)
      _ = ε₁ + c * ∑ S' ∈ 𝒮, μ.real (G S') := by rw [Finset.mul_sum]
      _ ≤ ε₁ + c * 1 := add_le_add le_rfl (mul_le_mul_of_nonneg_left hsum hc0)
      _ = ε₁ + c := by ring
  rw [measureReal_compl ((hthr q) hGood), probReal_univ] at hfail
  linarith

end Rigidity.Percolation
