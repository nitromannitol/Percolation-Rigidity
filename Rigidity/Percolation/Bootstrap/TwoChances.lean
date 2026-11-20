import Rigidity.Percolation.Bootstrap.SprinkledCluster

/-!
# Two disjoint chances

This is the probabilistic step of the bootstrap. A left set `S` inside its zone `Z_S ⊆ W_S` and a
right set `T` inside its zone `Z_T ⊆ W_T` are conditioned to have their cuts inside their zones
closed at level `p₀`. Their sprinkled clusters are explored inside the disjoint regions `W_S` and
`W_T`: a bond of the cut from the set itself opens at level `q`, every other bond at level `p₀`.
Two disjoint subregions `R_k` meet the exploration regions exactly in their own zones. Given the
two clusters, their traces in the zones of the subregions are conditioned in the same way as the
original sets, while the remaining bonds of the subregions are unexplored. If each pair of traces
is joined inside its subregion with conditional probability at least `π`, and the traces are
admissible except with conditional probability `ε`, then `S` and `T` are joined with conditional
probability at least `(1 - ε)(1 - (1 - π)²)`.

This is the repaired form of Lemma 2.4.1 of D. Contreras, *Percolation on graphs of polynomial
growth*, ETH Zürich dissertation (2022): the zones make the conditioning of the traces exactly the
conditioning of the recursion, and each bond is sprinkled at most once.
-/

noncomputable section

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External
open scoped unitInterval

variable {d : ℕ}

/-! ### Sprinkled clusters -/

/-- The sprinkled levels: `q` on the cut from `S` to `W \ S`, and `p₀` on every other bond. -/
def sprinkleLevel (p₀ q : unitInterval) (S W : Finset (Vertex d)) : Bond d → unitInterval :=
  fun e => if e ∈ vertexCutBondsIn S W then q else p₀

/-- The sprinkled cluster of `S` inside `W`. -/
def sprinkledCluster (p₀ q : unitInterval) (S W : Finset (Vertex d)) (ω : BondMarks d) :
    Finset (Vertex d) :=
  clusterWith (sprinkleLevel p₀ q S W) S W ω

/-- The sprinkled levels are at most `q`. -/
theorem sprinkleLevel_le {p₀ q : unitInterval} (hpq : p₀ ≤ q) (S W : Finset (Vertex d))
    (e : Bond d) : sprinkleLevel p₀ q S W e ≤ q := by
  unfold sprinkleLevel
  split_ifs
  · exact le_rfl
  · exact hpq

/-! ### Bonds and their endpoints -/

/-- The endpoints of the bond of two adjacent vertices. -/
theorem mem_bondOfAdjacent {x y z : Vertex d} (hxy : (nearestNeighborGraph d).Adj x y) :
    z ∈ (bondOfAdjacent hxy).1 ↔ z = x ∨ z = y := Sym2.mem_iff

/-- The bond of two adjacent vertices is internal to a set exactly when both vertices are. -/
theorem bondOfAdjacent_mem_localBonds {x y : Vertex d} (hxy : (nearestNeighborGraph d).Adj x y)
    {U : Set (Vertex d)} : bondOfAdjacent hxy ∈ localBonds U ↔ x ∈ U ∧ y ∈ U := by
  constructor
  · intro h
    exact ⟨h x ((mem_bondOfAdjacent hxy).2 (Or.inl rfl)),
      h y ((mem_bondOfAdjacent hxy).2 (Or.inr rfl))⟩
  · rintro ⟨hx, hy⟩ z hz
    rcases (mem_bondOfAdjacent hxy).1 hz with rfl | rfl
    · exact hx
    · exact hy

/-- The cut from the trace of `c` in a zone `Z ⊆ W` is part of the cut from `c` inside `W`. -/
theorem vertexCutBondsIn_inter_subset {c Z : Finset (Vertex d)} {W : Set (Vertex d)}
    (hc : (c : Set (Vertex d)) ⊆ W) (hZ : (Z : Set (Vertex d)) ⊆ W) :
    vertexCutBondsIn (c ∩ Z) (Z : Set (Vertex d)) ⊆ vertexCutBondsIn c W := by
  intro e he
  obtain ⟨x, hx, y, hy, hxy, rfl⟩ := exists_of_mem_vertexCutBondsIn he
  have hx' := Finset.mem_inter.1 hx
  refine bondOfAdjacent_mem_vertexCutBondsIn c W hc hx'.1 ⟨hZ hy.1, fun hyc => hy.2 ?_⟩ hxy
  exact Finset.mem_coe.2 (Finset.mem_inter.2 ⟨hyc, hy.1⟩)

/-- A bond of a cut from `R` has an endpoint in `R`. -/
theorem exists_mem_of_mem_vertexCutBondsIn {R : Finset (Vertex d)} {W : Set (Vertex d)}
    {e : Bond d} (he : e ∈ vertexCutBondsIn R W) : ∃ x ∈ R, x ∈ e.1 := by
  obtain ⟨x, hx, y, -, hxy, rfl⟩ := exists_of_mem_vertexCutBondsIn he
  exact ⟨x, hx, (mem_bondOfAdjacent hxy).2 (Or.inl rfl)⟩

/-- A bond of a cut inside `W` is internal to `W`. -/
theorem mem_localBonds_of_mem_vertexCutBondsIn {R : Finset (Vertex d)} {W : Set (Vertex d)}
    {e : Bond d} (he : e ∈ vertexCutBondsIn R W) : e ∈ localBonds W := by
  classical
  exact (Finset.mem_filter.1 he).2

/-! ### Independence over disjoint bond sets -/

/-- Events of marks on disjoint bond sets are independent. -/
theorem bondMarkLaw_real_inter_of_disjoint {E F : Set (Bond d)} (hEF : Disjoint E F)
    {A B : Set (BondMarks d)} (hA : MeasurableSet[bondMarkSigma E] A)
    (hB : MeasurableSet[bondMarkSigma F] B) :
    (bondMarkLaw d).real (A ∩ B) = (bondMarkLaw d).real A * (bondMarkLaw d).real B := by
  have hind := (Indep_iff _ _ _).mp (indep_bondMarkSigma hEF) A B hA hB
  change ((bondMarkLaw d) (A ∩ B)).toReal = _
  rw [hind, ENNReal.toReal_mul]
  rfl

/-- Events of marks on three pairwise disjoint bond sets are independent. -/
theorem bondMarkLaw_real_inter_three {E F₁ F₂ : Set (Bond d)} (h₁ : Disjoint E F₁)
    (h₂ : Disjoint E F₂) (h₁₂ : Disjoint F₁ F₂) {A B₁ B₂ : Set (BondMarks d)}
    (hA : MeasurableSet[bondMarkSigma E] A) (hB₁ : MeasurableSet[bondMarkSigma F₁] B₁)
    (hB₂ : MeasurableSet[bondMarkSigma F₂] B₂) :
    (bondMarkLaw d).real (A ∩ (B₁ ∩ B₂)) =
      (bondMarkLaw d).real A * ((bondMarkLaw d).real B₁ * (bondMarkLaw d).real B₂) := by
  have hB : MeasurableSet[bondMarkSigma (F₁ ∪ F₂)] (B₁ ∩ B₂) :=
    (bondMarkSigma_mono Set.subset_union_left _ hB₁).inter
      (bondMarkSigma_mono Set.subset_union_right _ hB₂)
  rw [bondMarkLaw_real_inter_of_disjoint (Disjoint.union_right h₁ h₂) hA hB,
    bondMarkLaw_real_inter_of_disjoint h₁₂ hB₁ hB₂]

/-! ### Traces in the zones -/

/-- Bonds internal both to `c ⊆ W` and to `R` are internal to the trace of `c` in `R ∩ W`. -/
theorem mem_localBonds_inter_of_mem {c W R Z : Finset (Vertex d)} (hcW : c ⊆ W)
    (hZ : R ∩ W = Z) {e : Bond d} (hc : e ∈ localBonds (c : Set (Vertex d)))
    (hR : e ∈ localBonds (R : Set (Vertex d))) : e ∈ localBonds ((c ∩ Z : Finset (Vertex d)) :
      Set (Vertex d)) := by
  intro z hz
  have hzc : z ∈ c := hc z hz
  have hzR : z ∈ R := hR z hz
  rw [Finset.mem_coe, Finset.mem_inter, ← hZ, Finset.mem_inter]
  exact ⟨hzc, hzR, hcW hzc⟩

/-- A bond of the cut from `c` inside `W` internal to `R` belongs to the cut from the trace of `c`
in the zone `R ∩ W`. -/
theorem mem_vertexCutBondsIn_inter_of_mem {c W R Z : Finset (Vertex d)} (hZ : R ∩ W = Z)
    {e : Bond d} (he : e ∈ vertexCutBondsIn c (W : Set (Vertex d)))
    (hR : e ∈ localBonds (R : Set (Vertex d))) :
    e ∈ vertexCutBondsIn (c ∩ Z) (Z : Set (Vertex d)) := by
  obtain ⟨x, hx, y, hy, hxy, rfl⟩ := exists_of_mem_vertexCutBondsIn he
  obtain ⟨hxR, hyR⟩ := (bondOfAdjacent_mem_localBonds hxy).1 hR
  have hxZ : x ∈ Z := by
    rw [← hZ, Finset.mem_inter]
    exact ⟨hxR, (Finset.mem_coe.1 (show x ∈ (W : Set (Vertex d)) from by
      have := mem_localBonds_of_mem_vertexCutBondsIn he
      exact this x ((mem_bondOfAdjacent hxy).2 (Or.inl rfl))))⟩
  have hyZ : y ∈ Z := by
    rw [← hZ, Finset.mem_inter]
    exact ⟨hyR, Finset.mem_coe.1 hy.1⟩
  refine bondOfAdjacent_mem_vertexCutBondsIn (c ∩ Z) (Z : Set (Vertex d))
    (fun v hv => (Finset.mem_inter.1 (Finset.mem_coe.1 hv)).2) ?_ ⟨hyZ, ?_⟩ hxy
  · exact Finset.mem_inter.2 ⟨hx, hxZ⟩
  · intro hyc
    exact hy.2 (Finset.mem_inter.1 (Finset.mem_coe.1 hyc)).1

/-- The cut from `X ⊆ Z` inside `Z ⊆ R` consists of bonds internal to `R`, not internal to `X`,
and not internal to any set disjoint from `Z`. -/
theorem vertexCutBondsIn_subset_avoiding {X Z R B : Finset (Vertex d)} (hXZ : X ⊆ Z)
    (hZR : Z ⊆ R) (hZB : Disjoint Z B) {e : Bond d}
    (he : e ∈ vertexCutBondsIn X (Z : Set (Vertex d))) :
    e ∈ localBonds (R : Set (Vertex d)) ∧ e ∉ localBonds (X : Set (Vertex d)) ∧
      e ∉ localBonds (B : Set (Vertex d)) := by
  obtain ⟨x, hx, y, hy, hxy, rfl⟩ := exists_of_mem_vertexCutBondsIn he
  refine ⟨(bondOfAdjacent_mem_localBonds hxy).2 ⟨hZR (hXZ hx), hZR (Finset.mem_coe.1 hy.1)⟩,
    fun h => hy.2 ((bondOfAdjacent_mem_localBonds hxy).1 h).2, fun h => ?_⟩
  exact Finset.disjoint_left.1 hZB (hXZ hx) ((bondOfAdjacent_mem_localBonds hxy).1 h).1

/-- Splitting the cut from `c` into the cuts from its traces in two zones and the rest. -/
theorem bondMarksAbove_cut_split (β : Bond d → unitInterval) (p₀ : unitInterval)
    {c W : Finset (Vertex d)} (Z : Bool → Finset (Vertex d)) (hc : c ⊆ W)
    (hZ : ∀ k, Z k ⊆ W)
    (hβ : ∀ k, ∀ e ∈ vertexCutBondsIn (c ∩ Z k) (Z k : Set (Vertex d)), β e = p₀) :
    bondMarksAbove (vertexCutBondsIn c W) β =
      bondMarksAbove ((vertexCutBondsIn c W).filter
          fun e => ∀ k, e ∉ vertexCutBondsIn (c ∩ Z k) (Z k : Set (Vertex d))) β ∩
        (cutClosed p₀ (c ∩ Z true) (Z true) ∩ cutClosed p₀ (c ∩ Z false) (Z false)) := by
  classical
  have hsub : ∀ k, vertexCutBondsIn (c ∩ Z k) (Z k : Set (Vertex d)) ⊆
      vertexCutBondsIn c (W : Set (Vertex d)) := fun k =>
    vertexCutBondsIn_inter_subset (fun v hv => hc hv) (fun v hv => hZ k hv)
  ext ω
  simp only [bondMarksAbove, cutClosed, constThreshold, Set.mem_inter_iff, Set.mem_setOf_eq,
    Finset.mem_filter]
  constructor
  · intro h
    refine ⟨fun e he => h e he.1, fun e he => ?_, fun e he => ?_⟩
    · have := h e (hsub true he)
      rwa [hβ true e he] at this
    · have := h e (hsub false he)
      rwa [hβ false e he] at this
  · rintro ⟨h1, h2, h3⟩ e he
    by_cases hK : ∀ k, e ∉ vertexCutBondsIn (c ∩ Z k) (Z k : Set (Vertex d))
    · exact h1 e ⟨he, hK⟩
    · push Not at hK
      obtain ⟨k, hk⟩ := hK
      cases k
      · rw [hβ false e hk]
        exact h3 e hk
      · rw [hβ true e hk]
        exact h2 e hk

/-! ### One value of the two clusters -/

/-- **Two chances for fixed clusters.** On the event that the sprinkled clusters of `S` and `T`
take the values `c` and `c'`, the traces of `c` and `c'` are joined inside one of the two
subregions with conditional probability at least `1 - (1 - π)²`. -/
theorem two_chances_piece (p₀ q : unitInterval)
    (S T ZS ZT WS WT : Finset (Vertex d)) (R ZL ZR : Bool → Finset (Vertex d))
    (hWW : Disjoint WS WT)
    (hRR : Disjoint (R true) (R false)) (hZL : ∀ k, R k ∩ WS = ZL k)
    (hZR : ∀ k, R k ∩ WT = ZR k) (hSR : ∀ k, Disjoint S (R k)) (hTR : ∀ k, Disjoint T (R k))
    (Adm : Bool → Finset (Vertex d) → Finset (Vertex d) → Prop) {π : ℝ} (hπ1 : π ≤ 1)
    (hIH : ∀ k X Y, X ⊆ ZL k → Y ⊆ ZR k → Adm k X Y →
      π * (bondMarkLaw d).real (cutClosed p₀ X (ZL k) ∩ cutClosed p₀ Y (ZR k)) ≤
        (bondMarkLaw d).real ({ω | ConnectsRegions (thresholdBondMarks q ω) (R k) X Y} ∩
          (cutClosed p₀ X (ZL k) ∩ cutClosed p₀ Y (ZR k))))
    (c c' : Finset (Vertex d)) (hSc : S ⊆ c) (hcW : c ⊆ WS) (hTc : T ⊆ c') (hcW' : c' ⊆ WT)
    (hAdm : ∀ k, Adm k (c ∩ ZL k) (c' ∩ ZR k)) :
    (1 - (1 - π) ^ 2) * (bondMarkLaw d).real
        ({ω | sprinkledCluster p₀ q S WS ω = c} ∩ {ω | sprinkledCluster p₀ q T WT ω = c'} ∩
          (cutClosed p₀ S ZS ∩ cutClosed p₀ T ZT)) ≤
      (bondMarkLaw d).real
        ({ω | sprinkledCluster p₀ q S WS ω = c} ∩ {ω | sprinkledCluster p₀ q T WT ω = c'} ∩
          (cutClosed p₀ S ZS ∩ cutClosed p₀ T ZT) ∩
          ({ω | ConnectsRegions (thresholdBondMarks q ω) (R true)
              ((c ∩ ZL true : Finset (Vertex d)) : Set (Vertex d))
              ((c' ∩ ZR true : Finset (Vertex d)) : Set (Vertex d))} ∪
            {ω | ConnectsRegions (thresholdBondMarks q ω) (R false)
              ((c ∩ ZL false : Finset (Vertex d)) : Set (Vertex d))
              ((c' ∩ ZR false : Finset (Vertex d)) : Set (Vertex d))})) := by
  classical
  set μ := bondMarkLaw d with hμ
  set βS := sprinkleLevel p₀ q S WS with hβS
  set βT := sprinkleLevel p₀ q T WT with hβT
  set X : Bool → Finset (Vertex d) := fun k => c ∩ ZL k with hX
  set Y : Bool → Finset (Vertex d) := fun k => c' ∩ ZR k with hY
  have hZLR : ∀ k, ZL k ⊆ R k := fun k => hZL k ▸ Finset.inter_subset_left
  have hZLW : ∀ k, ZL k ⊆ WS := fun k => hZL k ▸ Finset.inter_subset_right
  have hZRR : ∀ k, ZR k ⊆ R k := fun k => hZR k ▸ Finset.inter_subset_left
  have hZRW : ∀ k, ZR k ⊆ WT := fun k => hZR k ▸ Finset.inter_subset_right
  have hXZ : ∀ k, X k ⊆ ZL k := fun k => Finset.inter_subset_right
  have hYZ : ∀ k, Y k ⊆ ZR k := fun k => Finset.inter_subset_right
  have hZLY : ∀ k, Disjoint (ZL k) (Y k) := fun k =>
    Finset.disjoint_of_subset_left (hZLW k)
      (Finset.disjoint_of_subset_right ((hYZ k).trans (hZRW k)) hWW)
  have hZRX : ∀ k, Disjoint (ZR k) (X k) := fun k =>
    Finset.disjoint_of_subset_left (hZRW k)
      (Finset.disjoint_of_subset_right ((hXZ k).trans (hZLW k)) hWW.symm)
  have hXY : ∀ k, Disjoint (X k) (Y k) := fun k =>
    Finset.disjoint_of_subset_left (hXZ k) (hZLY k)
  -- the levels vanish to `p₀` on the cuts of the traces
  have hβSp : ∀ k, ∀ e ∈ vertexCutBondsIn (c ∩ ZL k) (ZL k : Set (Vertex d)), βS e = p₀ := by
    intro k e he
    have hnot : e ∉ vertexCutBondsIn S (WS : Set (Vertex d)) := by
      intro hS
      obtain ⟨s, hs, hse⟩ := exists_mem_of_mem_vertexCutBondsIn hS
      have hloc := (vertexCutBondsIn_subset_avoiding (hXZ k) (hZLR k) (hZLY k) he).1
      exact Finset.disjoint_left.1 (hSR k) hs (hloc s hse)
    simp only [hβS, sprinkleLevel, hnot, ↓reduceIte]
  have hβTp : ∀ k, ∀ e ∈ vertexCutBondsIn (c' ∩ ZR k) (ZR k : Set (Vertex d)), βT e = p₀ := by
    intro k e he
    have hnot : e ∉ vertexCutBondsIn T (WT : Set (Vertex d)) := by
      intro hT
      obtain ⟨s, hs, hse⟩ := exists_mem_of_mem_vertexCutBondsIn hT
      have hloc := (vertexCutBondsIn_subset_avoiding (hYZ k) (hZRR k) (hZRX k) he).1
      exact Finset.disjoint_left.1 (hTR k) hs (hloc s hse)
    simp only [hβT, sprinkleLevel, hnot, ↓reduceIte]
  -- the factorization
  set FS := (vertexCutBondsIn c (WS : Set (Vertex d))).filter
    fun e => ∀ k, e ∉ vertexCutBondsIn (c ∩ ZL k) (ZL k : Set (Vertex d)) with hFS
  set FT := (vertexCutBondsIn c' (WT : Set (Vertex d))).filter
    fun e => ∀ k, e ∉ vertexCutBondsIn (c' ∩ ZR k) (ZR k : Set (Vertex d)) with hFT
  set G : Set (BondMarks d) := (genWith βS S c ∩ bondMarksAbove FS βS) ∩
    (genWith βT T c' ∩ bondMarksAbove FT βT) ∩ (cutClosed p₀ S ZS ∩ cutClosed p₀ T ZT) with hG
  set Hs : Bool → Set (BondMarks d) := fun k =>
    cutClosed p₀ (X k) (ZL k) ∩ cutClosed p₀ (Y k) (ZR k) with hHs
  set As : Bool → Set (BondMarks d) := fun k =>
    {ω | ConnectsRegions (thresholdBondMarks q ω) (R k) (X k) (Y k)} with hAs
  set E := {ω | sprinkledCluster p₀ q S WS ω = c} ∩ {ω | sprinkledCluster p₀ q T WT ω = c'} ∩
    (cutClosed p₀ S ZS ∩ cutClosed p₀ T ZT) with hEdef
  have hE : E = G ∩ (Hs true ∩ Hs false) := by
    have h1 : {ω | sprinkledCluster p₀ q S WS ω = c} =
        genWith βS S c ∩ bondMarksAbove (vertexCutBondsIn c (WS : Set (Vertex d))) βS := by
      ext ω
      exact clusterWith_eq_iff βS hSc hcW ω
    have h2 : {ω | sprinkledCluster p₀ q T WT ω = c'} =
        genWith βT T c' ∩ bondMarksAbove (vertexCutBondsIn c' (WT : Set (Vertex d))) βT := by
      ext ω
      exact clusterWith_eq_iff βT hTc hcW' ω
    rw [hEdef, h1, h2, bondMarksAbove_cut_split βS p₀ ZL hcW hZLW hβSp,
      bondMarksAbove_cut_split βT p₀ ZR hcW' hZRW hβTp]
    ext ω
    simp only [hG, hHs, hX, hY, Set.mem_inter_iff]
    tauto
  -- the bond sets
  set Z : Set (Bond d) := (localBonds (c : Set (Vertex d)) ∪ (FS : Set (Bond d)) ∪
      (vertexCutBondsIn S (ZS : Set (Vertex d)) : Set (Bond d))) ∪
    (localBonds (c' : Set (Vertex d)) ∪ (FT : Set (Bond d)) ∪
      (vertexCutBondsIn T (ZT : Set (Vertex d)) : Set (Bond d))) with hZdef
  set V : Bool → Set (Bond d) := fun k => localBonds (R k : Set (Vertex d)) \
    (localBonds (X k : Set (Vertex d)) ∪ localBonds (Y k : Set (Vertex d))) with hVdef
  have hGm : MeasurableSet[bondMarkSigma Z] G := by
    refine MeasurableSet.inter (MeasurableSet.inter (MeasurableSet.inter ?_ ?_)
      (MeasurableSet.inter ?_ ?_)) (MeasurableSet.inter ?_ ?_)
    · exact bondMarkSigma_mono (fun e he => Or.inl (Or.inl (Or.inl he))) _
        (measurableSet_genWith βS S c)
    · exact bondMarkSigma_mono (fun e he => Or.inl (Or.inl (Or.inr he))) _
        (measurableSet_bondMarksAbove_local FS βS)
    · exact bondMarkSigma_mono (fun e he => Or.inr (Or.inl (Or.inl he))) _
        (measurableSet_genWith βT T c')
    · exact bondMarkSigma_mono (fun e he => Or.inr (Or.inl (Or.inr he))) _
        (measurableSet_bondMarksAbove_local FT βT)
    · exact bondMarkSigma_mono (fun e he => Or.inl (Or.inr he)) _
        (measurableSet_bondMarksAbove_local _ _)
    · exact bondMarkSigma_mono (fun e he => Or.inr (Or.inr he)) _
        (measurableSet_bondMarksAbove_local _ _)
  have hHm : ∀ k, MeasurableSet[bondMarkSigma (V k)] (Hs k) := by
    intro k
    refine MeasurableSet.inter ?_ ?_
    · refine bondMarkSigma_mono (fun e he => ?_) _ (measurableSet_bondMarksAbove_local _ _)
      obtain ⟨h1, h2, h3⟩ := vertexCutBondsIn_subset_avoiding (hXZ k) (hZLR k) (hZLY k) he
      exact ⟨h1, fun h => h.elim h2 h3⟩
    · refine bondMarkSigma_mono (fun e he => ?_) _ (measurableSet_bondMarksAbove_local _ _)
      obtain ⟨h1, h2, h3⟩ := vertexCutBondsIn_subset_avoiding (hYZ k) (hZRR k) (hZRX k) he
      exact ⟨h1, fun h => h.elim h3 h2⟩
  have hAm : ∀ k, MeasurableSet[bondMarkSigma (V k)] (As k) := fun k =>
    measurableSet_connectsRegions_avoiding q (R k) (X k) (Y k) (hXY k)
  have hZV : ∀ k, Disjoint Z (V k) := by
    intro k
    rw [Set.disjoint_left]
    intro e hZe hVe
    obtain ⟨hRe, hnot⟩ := hVe
    rcases hZe with ((h | h) | h) | ((h | h) | h)
    · exact hnot (Or.inl (mem_localBonds_inter_of_mem hcW (hZL k) h hRe))
    · obtain ⟨he, hK⟩ := Finset.mem_filter.1 h
      exact hK k (mem_vertexCutBondsIn_inter_of_mem (hZL k) he hRe)
    · obtain ⟨s, hs, hse⟩ := exists_mem_of_mem_vertexCutBondsIn (Finset.mem_coe.1 h)
      exact Finset.disjoint_left.1 (hSR k) hs (hRe s hse)
    · exact hnot (Or.inr (mem_localBonds_inter_of_mem hcW' (hZR k) h hRe))
    · obtain ⟨he, hK⟩ := Finset.mem_filter.1 h
      exact hK k (mem_vertexCutBondsIn_inter_of_mem (hZR k) he hRe)
    · obtain ⟨s, hs, hse⟩ := exists_mem_of_mem_vertexCutBondsIn (Finset.mem_coe.1 h)
      exact Finset.disjoint_left.1 (hTR k) hs (hRe s hse)
  have hVV : Disjoint (V true) (V false) := by
    rw [Set.disjoint_left]
    intro e h1 h2
    obtain ⟨u, v, huv, -⟩ := e.2
    have hu : u ∈ e.1 := huv ▸ Sym2.mem_mk_left u v
    exact Finset.disjoint_left.1 hRR (h1.1 u hu) (h2.1 u hu)
  -- the computation
  have hAfull : ∀ k, MeasurableSet (As k) := fun k => bondMarkSigma_le _ _ (hAm k)
  have hμE : μ.real E = μ.real G * (μ.real (Hs true) * μ.real (Hs false)) := by
    rw [hE]
    exact bondMarkLaw_real_inter_three (hZV true) (hZV false) hVV hGm (hHm true) (hHm false)
  have hbadset : E ∩ (As true ∪ As false)ᶜ =
      G ∩ ((Hs true ∩ (As true)ᶜ) ∩ (Hs false ∩ (As false)ᶜ)) := by
    rw [hE]
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_union]
    tauto
  have hμbad : μ.real (E ∩ (As true ∪ As false)ᶜ) = μ.real G *
      (μ.real (Hs true ∩ (As true)ᶜ) * μ.real (Hs false ∩ (As false)ᶜ)) := by
    rw [hbadset]
    exact bondMarkLaw_real_inter_three (hZV true) (hZV false) hVV hGm
      ((hHm true).inter (hAm true).compl) ((hHm false).inter (hAm false).compl)
  have hsplit : μ.real (E ∩ (As true ∪ As false)) + μ.real (E ∩ (As true ∪ As false)ᶜ) =
      μ.real E := by
    rw [← Set.sdiff_eq]
    exact measureReal_inter_add_sdiff (s := E) ((hAfull true).union (hAfull false))
  have hbadk : ∀ k, μ.real (Hs k ∩ (As k)ᶜ) ≤ (1 - π) * μ.real (Hs k) := by
    intro k
    have h1 := measureReal_inter_add_sdiff (μ := μ) (s := Hs k) (hAfull k)
    have h2 := hIH k (X k) (Y k) (hXZ k) (hYZ k) (hAdm k)
    have h3 : μ.real (As k ∩ Hs k) = μ.real (Hs k ∩ As k) := by rw [Set.inter_comm]
    rw [← Set.sdiff_eq]
    change π * μ.real (Hs k) ≤ μ.real (As k ∩ Hs k) at h2
    linarith
  have hg : 0 ≤ μ.real G := measureReal_nonneg
  have hb1 := hbadk true
  have hb2 := hbadk false
  have hb1' : 0 ≤ μ.real (Hs true ∩ (As true)ᶜ) := measureReal_nonneg
  have hb2' : 0 ≤ μ.real (Hs false ∩ (As false)ᶜ) := measureReal_nonneg
  have hπ' : 0 ≤ 1 - π := by linarith
  have hprod : μ.real (Hs true ∩ (As true)ᶜ) * μ.real (Hs false ∩ (As false)ᶜ) ≤
      ((1 - π) * μ.real (Hs true)) * ((1 - π) * μ.real (Hs false)) :=
    mul_le_mul hb1 hb2 hb2' (mul_nonneg hπ' measureReal_nonneg)
  have hprod' := mul_le_mul_of_nonneg_left hprod hg
  have key : (1 - (1 - π) ^ 2) * μ.real E ≤ μ.real (E ∩ (As true ∪ As false)) := by
    rw [hμE]
    nlinarith
  exact key

/-- Thresholding all marks at a common level is measurable. -/
theorem measurable_thresholdBondMarks (q : unitInterval) :
    Measurable (thresholdBondMarks (d := d) q) :=
  measurable_thresholdWith (constThreshold q)

/-- Traces joined inside a subregion join the generating sets of the two clusters. -/
theorem connectsRegions_of_traces {p₀ q : unitInterval} (hpq : p₀ ≤ q) {Q : Set (Vertex d)}
    {S T WS WT : Finset (Vertex d)} (hSW : S ⊆ WS) (hTW : T ⊆ WT)
    (hWSQ : (WS : Set (Vertex d)) ⊆ Q) (hWTQ : (WT : Set (Vertex d)) ⊆ Q)
    {R X Y : Finset (Vertex d)} (hRQ : (R : Set (Vertex d)) ⊆ Q) {ω : BondMarks d}
    (hX : X ⊆ sprinkledCluster p₀ q S WS ω) (hY : Y ⊆ sprinkledCluster p₀ q T WT ω)
    (h : ConnectsRegions (thresholdBondMarks q ω) R X Y) :
    ConnectsRegions (thresholdBondMarks q ω) Q S T := by
  obtain ⟨x, hxR, hxX, y, hyR, hyY, hxy⟩ := h
  have hle : ∀ (U : Finset (Vertex d)) (W : Finset (Vertex d)),
      thresholdWith (sprinkleLevel p₀ q U W) ω ≤ thresholdBondMarks q ω := fun U W =>
    thresholdWith_le_thresholdBondMarks (sprinkleLevel_le hpq U W) ω
  obtain ⟨g, hg, hgx⟩ := reachable_of_mem_clusterWith _ hSW (hX hxX)
  obtain ⟨h, hh, hhy⟩ := reachable_of_mem_clusterWith _ hTW (hY hyY)
  have hgx' : (openIn (thresholdBondMarks q ω) Q).Reachable g x :=
    openIn_reachable_mono_region (fun v hv => hWSQ (clusterWith_subset _ _ _ ω hv))
      (hgx.mono (openIn_mono_configuration (hle S WS) _))
  have hhy' : (openIn (thresholdBondMarks q ω) Q).Reachable h y :=
    openIn_reachable_mono_region (fun v hv => hWTQ (clusterWith_subset _ _ _ ω hv))
      (hhy.mono (openIn_mono_configuration (hle T WT) _))
  have hxy' : (openIn (thresholdBondMarks q ω) Q).Reachable x y :=
    openIn_reachable_mono_region hRQ hxy
  exact ⟨g, hWSQ (hSW hg), hg, h, hWTQ (hTW hh), hh, hgx'.trans (hxy'.trans hhy'.symm)⟩

/-- **Two disjoint chances.** If the traces of the sprinkled clusters in the zones of the two
subregions are joined inside each subregion with conditional probability at least `π` whenever
they are admissible, and they are admissible in both subregions except with conditional
probability `ε`, then `S` and `T` are joined inside `Q` at level `q` with conditional probability
at least `(1 - ε)(1 - (1 - π)²)`. All conditional probabilities are given the closed cuts. -/
theorem two_chances (p₀ q : unitInterval) (hpq : p₀ ≤ q) (Q : Set (Vertex d))
    (S T ZS ZT WS WT : Finset (Vertex d)) (R ZL ZR : Bool → Finset (Vertex d))
    (hSZ : S ⊆ ZS) (hZWS : ZS ⊆ WS) (hTZ : T ⊆ ZT) (hZWT : ZT ⊆ WT) (hWW : Disjoint WS WT)
    (hWSQ : (WS : Set (Vertex d)) ⊆ Q) (hWTQ : (WT : Set (Vertex d)) ⊆ Q)
    (hRQ : ∀ k, (R k : Set (Vertex d)) ⊆ Q)
    (hRR : Disjoint (R true) (R false)) (hZL : ∀ k, R k ∩ WS = ZL k)
    (hZR : ∀ k, R k ∩ WT = ZR k) (hSR : ∀ k, Disjoint S (R k)) (hTR : ∀ k, Disjoint T (R k))
    (Adm : Bool → Finset (Vertex d) → Finset (Vertex d) → Prop) {π ε : ℝ} (hπ0 : 0 ≤ π)
    (hπ1 : π ≤ 1)
    (hIH : ∀ k X Y, X ⊆ ZL k → Y ⊆ ZR k → Adm k X Y →
      π * (bondMarkLaw d).real (cutClosed p₀ X (ZL k) ∩ cutClosed p₀ Y (ZR k)) ≤
        (bondMarkLaw d).real ({ω | ConnectsRegions (thresholdBondMarks q ω) (R k) X Y} ∩
          (cutClosed p₀ X (ZL k) ∩ cutClosed p₀ Y (ZR k))))
    (hF : (bondMarkLaw d).real ((cutClosed p₀ S ZS ∩ cutClosed p₀ T ZT) ∩
        {ω | ¬ ∀ k, Adm k (sprinkledCluster p₀ q S WS ω ∩ ZL k)
          (sprinkledCluster p₀ q T WT ω ∩ ZR k)}) ≤
        ε * (bondMarkLaw d).real (cutClosed p₀ S ZS ∩ cutClosed p₀ T ZT)) :
    (1 - ε) * (1 - (1 - π) ^ 2) *
        (bondMarkLaw d).real (cutClosed p₀ S ZS ∩ cutClosed p₀ T ZT) ≤
      (bondMarkLaw d).real ({ω | ConnectsRegions (thresholdBondMarks q ω) Q S T} ∩
        (cutClosed p₀ S ZS ∩ cutClosed p₀ T ZT)) := by
  classical
  set μ := bondMarkLaw d with hμ
  set H := cutClosed p₀ S ZS ∩ cutClosed p₀ T ZT with hH
  set CS := sprinkledCluster p₀ q S WS with hCS
  set CT := sprinkledCluster p₀ q T WT with hCT
  have hSW : S ⊆ WS := hSZ.trans hZWS
  have hTW : T ⊆ WT := hTZ.trans hZWT
  set Vals := (WS.powerset ×ˢ WT.powerset).filter fun cc : Finset (Vertex d) × Finset (Vertex d) =>
    S ⊆ cc.1 ∧ T ⊆ cc.2 ∧ ∀ k, Adm k (cc.1 ∩ ZL k) (cc.2 ∩ ZR k) with hVals
  set E : Finset (Vertex d) × Finset (Vertex d) → Set (BondMarks d) := fun cc =>
    {ω | CS ω = cc.1} ∩ {ω | CT ω = cc.2} ∩ H with hEdef
  set As : Bool → Finset (Vertex d) × Finset (Vertex d) → Set (BondMarks d) := fun k cc =>
    {ω | ConnectsRegions (thresholdBondMarks q ω) (R k)
      ((cc.1 ∩ ZL k : Finset (Vertex d)) : Set (Vertex d))
      ((cc.2 ∩ ZR k : Finset (Vertex d)) : Set (Vertex d))} with hAsdef
  set B : Finset (Vertex d) × Finset (Vertex d) → Set (BondMarks d) := fun cc =>
    E cc ∩ (As true cc ∪ As false cc) with hBdef
  have hHm : MeasurableSet H :=
    (measurableSet_bondMarksAbove _ _).inter (measurableSet_bondMarksAbove _ _)
  have hEm : ∀ cc, MeasurableSet (E cc) := fun cc =>
    ((measurableSet_clusterWith_eq _ hSW cc.1).inter
      (measurableSet_clusterWith_eq _ hTW cc.2)).inter hHm
  have hBm : ∀ cc, MeasurableSet (B cc) := fun cc =>
    (hEm cc).inter
      (((measurableSet_connectsRegions _ _ _).preimage (measurable_thresholdBondMarks q)).union
        ((measurableSet_connectsRegions _ _ _).preimage (measurable_thresholdBondMarks q)))
  have hEdisj : (Vals : Set (Finset (Vertex d) × Finset (Vertex d))).PairwiseDisjoint E := by
    intro cc _ cc' _ hne
    rw [Function.onFun, Set.disjoint_left]
    rintro ω ⟨⟨h1, h2⟩, -⟩ ⟨⟨h1', h2'⟩, -⟩
    exact hne (Prod.ext (h1.symm.trans h1') (h2.symm.trans h2'))
  have hBdisj : (Vals : Set (Finset (Vertex d) × Finset (Vertex d))).PairwiseDisjoint B := by
    intro cc hcc cc' hcc' hne
    exact (hEdisj hcc hcc' hne).mono Set.inter_subset_left Set.inter_subset_left
  -- the good event is covered by the values of the clusters
  set Good := {ω | ∀ k, Adm k (CS ω ∩ ZL k) (CT ω ∩ ZR k)} with hGood
  have hcover : H ∩ Good ⊆ ⋃ cc ∈ Vals, E cc := by
    rintro ω ⟨hωH, hωG⟩
    refine Set.mem_iUnion₂.2 ⟨(CS ω, CT ω), ?_, ⟨rfl, rfl⟩, hωH⟩
    refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨Finset.mem_powerset.2
      (clusterWith_subset _ _ _ ω), Finset.mem_powerset.2 (clusterWith_subset _ _ _ ω)⟩,
      subset_clusterWith _ hSW ω, subset_clusterWith _ hTW ω, hωG⟩
  have hgood : μ.real (H ∩ Good) ≤ ∑ cc ∈ Vals, μ.real (E cc) := by
    rw [← measureReal_biUnion_finset hEdisj (fun cc _ => hEm cc)]
    exact measureReal_mono hcover (measure_ne_top _ _)
  have hbad : μ.real H ≤ μ.real (H ∩ Good) + ε * μ.real H := by
    have hsplit : H ⊆ (H ∩ Good) ∪ (H ∩ {ω | ¬ ∀ k, Adm k (CS ω ∩ ZL k) (CT ω ∩ ZR k)}) := by
      intro ω hω
      by_cases hg : ω ∈ Good
      · exact Or.inl ⟨hω, hg⟩
      · exact Or.inr ⟨hω, hg⟩
    exact (measureReal_mono hsplit (measure_ne_top _ _)).trans ((measureReal_union_le _ _).trans
      (add_le_add le_rfl hF))
  -- each value contributes two chances
  have hpieces : ∀ cc ∈ Vals, (1 - (1 - π) ^ 2) * μ.real (E cc) ≤ μ.real (B cc) := by
    intro cc hcc
    obtain ⟨hpow, hSc, hTc, hAdm⟩ := Finset.mem_filter.1 hcc
    obtain ⟨h1, h2⟩ := Finset.mem_product.1 hpow
    exact two_chances_piece p₀ q S T ZS ZT WS WT R ZL ZR hWW hRR hZL hZR hSR hTR Adm hπ1 hIH
      cc.1 cc.2 hSc (Finset.mem_powerset.1 h1) hTc (Finset.mem_powerset.1 h2) hAdm
  have hBsub : ⋃ cc ∈ Vals, B cc ⊆ {ω | ConnectsRegions (thresholdBondMarks q ω) Q S T} ∩ H := by
    intro ω hω
    obtain ⟨cc, -, ⟨⟨h1, h2⟩, hωH⟩, hA⟩ := Set.mem_iUnion₂.1 hω
    refine ⟨?_, hωH⟩
    have h1' : CS ω = cc.1 := h1
    have h2' : CT ω = cc.2 := h2
    rcases hA with hA | hA
    · exact connectsRegions_of_traces hpq hSW hTW hWSQ hWTQ (hRQ true)
        (by rw [← hCS, h1']; exact Finset.inter_subset_left)
        (by rw [← hCT, h2']; exact Finset.inter_subset_left) hA
    · exact connectsRegions_of_traces hpq hSW hTW hWSQ hWTQ (hRQ false)
        (by rw [← hCS, h1']; exact Finset.inter_subset_left)
        (by rw [← hCT, h2']; exact Finset.inter_subset_left) hA
  have hsum : (1 - (1 - π) ^ 2) * ∑ cc ∈ Vals, μ.real (E cc) ≤
      μ.real ({ω | ConnectsRegions (thresholdBondMarks q ω) Q S T} ∩ H) := by
    rw [Finset.mul_sum]
    calc ∑ cc ∈ Vals, (1 - (1 - π) ^ 2) * μ.real (E cc) ≤ ∑ cc ∈ Vals, μ.real (B cc) :=
          Finset.sum_le_sum hpieces
      _ = μ.real (⋃ cc ∈ Vals, B cc) :=
          (measureReal_biUnion_finset hBdisj (fun cc _ => hBm cc)).symm
      _ ≤ _ := measureReal_mono hBsub (measure_ne_top _ _)
  have hc : 0 ≤ 1 - (1 - π) ^ 2 := by nlinarith
  have hHnn : 0 ≤ μ.real H := measureReal_nonneg
  calc (1 - ε) * (1 - (1 - π) ^ 2) * μ.real H
      = (1 - (1 - π) ^ 2) * (μ.real H - ε * μ.real H) := by ring
    _ ≤ (1 - (1 - π) ^ 2) * μ.real (H ∩ Good) :=
        mul_le_mul_of_nonneg_left (by linarith) hc
    _ ≤ (1 - (1 - π) ^ 2) * ∑ cc ∈ Vals, μ.real (E cc) := mul_le_mul_of_nonneg_left hgood hc
    _ ≤ _ := hsum

end Rigidity.Percolation
