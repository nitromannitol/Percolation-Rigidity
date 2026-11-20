import Rigidity.Percolation.BondSeedHistory
import Rigidity.Percolation.SlabAttachment

/-!
# Adaptive finite-batch revelation

An adaptive exploration may reveal a finite family of bonds at each step.
Its outcome is measurable in those bonds. The resulting history partition
supports seed tests which inspect several bonds at once.
-/

namespace Rigidity.Percolation

open Function LatticeProb.Percolation MeasureTheory

/-- A Boolean test determined by a finite set of bonds. -/
structure BondTest (d : ℕ) where
  bonds : Set (Bond d)
  finite_bonds : bonds.Finite
  outcome : Configuration d → Bool
  measurable_outcome : Measurable[bondSigma bonds, inferInstance] outcome

/-- The bonds read along a proposed history. -/
def historyBonds {d : ℕ} (next : List Bool → BondTest d) (h : List Bool) : Set (Bond d) :=
  ⋃ k ∈ Set.Iio h.length, (next (h.take k)).bonds

/-- Configurations whose successive bond values match a proposed history. -/
def bondHistoryEvent {d : ℕ} (next : List Bool → BondTest d) (h : List Bool) :
    Set (Configuration d) :=
  {ω | ∀ k < h.length, (next (h.take k)).outcome ω = h.getD k false}

/-- The history obtained by revealing bonds successively. -/
def observedBondHistory {d : ℕ} (next : List Bool → BondTest d) (ω : Configuration d) :
    ℕ → List Bool
  | 0 => []
  | n + 1 =>
    let h := observedBondHistory next ω n
    h ++ [(next h).outcome ω]

@[simp] theorem length_observedBondHistory {d : ℕ} (next : List Bool → BondTest d)
    (ω : Configuration d) (n : ℕ) : (observedBondHistory next ω n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [observedBondHistory, ih]

/-- The history event after one further observation. -/
theorem bondHistoryEvent_append {d : ℕ} (next : List Bool → BondTest d)
    (h : List Bool) (b : Bool) :
    bondHistoryEvent next (h ++ [b]) =
      bondHistoryEvent next h ∩ {ω | (next h).outcome ω = b} := by
  ext ω
  simp only [bondHistoryEvent, Set.mem_setOf_eq, Set.mem_inter_iff, List.length_append,
    List.length_singleton]
  constructor
  · intro hw
    constructor
    · intro k hk
      have hh := hw k (by omega)
      rw [List.take_append_of_le_length (Nat.le_of_lt hk), List.getD_append _ _ _ _ hk] at hh
      exact hh
    · have hh := hw h.length (by omega)
      simpa only [List.take_append_of_le_length (le_refl _), List.take_length,
        List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self, List.getD_cons_zero] using hh
  · rintro ⟨hw, hb⟩ k hk
    by_cases hlt : k < h.length
    · rw [List.take_append_of_le_length (Nat.le_of_lt hlt), List.getD_append _ _ _ _ hlt]
      exact hw k hlt
    · have hk' : k = h.length := by omega
      subst k
      simpa only [List.take_append_of_le_length (le_refl _), List.take_length,
        List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self, List.getD_cons_zero] using hb

/-- The bonds revealed along a history are finite. -/
theorem finite_historyBonds {d : ℕ} (next : List Bool → BondTest d) (h : List Bool) :
    (historyBonds next h).Finite := by
  exact (Set.finite_Iio h.length).biUnion (fun k _ => (next (h.take k)).finite_bonds)

/-- A history event only uses the bonds revealed along that history. -/
theorem measurableSet_bondHistoryEvent {d : ℕ} (next : List Bool → BondTest d)
    (h : List Bool) : MeasurableSet[bondSigma (historyBonds next h)]
      (bondHistoryEvent next h) := by
  have heq : bondHistoryEvent next h =
      ⋂ k : ℕ, ⋂ (_ : k < h.length), {ω : Configuration d |
        (next (h.take k)).outcome ω = h.getD k false} := by
    ext ω
    simp only [bondHistoryEvent, Set.mem_setOf_eq, Set.mem_iInter]
  rw [heq]
  apply MeasurableSet.iInter
  intro k
  apply MeasurableSet.iInter
  intro hk
  have hsub : (next (h.take k)).bonds ⊆ historyBonds next h := by
    intro e he
    exact Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨hk, he⟩⟩
  have hm : Measurable[bondSigma (historyBonds next h), inferInstance]
      (next (h.take k)).outcome :=
    (next (h.take k)).measurable_outcome.mono (bondSigma_mono hsub) le_rfl
  exact hm (measurableSet_singleton _)

/-- Every finite observation produces the corresponding history event. -/
theorem observedBondHistory_mem {d : ℕ} (next : List Bool → BondTest d)
    (ω : Configuration d) (n : ℕ) :
    ω ∈ bondHistoryEvent next (observedBondHistory next ω n) := by
  induction n with
  | zero => simp [bondHistoryEvent, observedBondHistory]
  | succ n ih =>
    rw [observedBondHistory, bondHistoryEvent_append]
    exact ⟨ih, rfl⟩

/-- A configuration determines its history uniquely. -/
theorem observedBondHistory_eq_of_mem {d : ℕ} (next : List Bool → BondTest d)
    (ω : Configuration d) (h : List Bool) (hw : ω ∈ bondHistoryEvent next h) :
    observedBondHistory next ω h.length = h := by
  induction h using List.reverseRecOn with
  | nil => rfl
  | append_singleton h b ih =>
    rw [bondHistoryEvent_append] at hw
    simp only [List.length_append, List.length_singleton, observedBondHistory]
    rw [ih hw.1]
    exact congrArg (fun v => h ++ [v]) hw.2

/-- Distinct histories of equal length define disjoint events. -/
theorem disjoint_bondHistoryEvent {d : ℕ} (next : List Bool → BondTest d)
    {h g : List Bool} (hlen : h.length = g.length) (hne : h ≠ g) :
    Disjoint (bondHistoryEvent next h) (bondHistoryEvent next g) := by
  apply Set.disjoint_left.mpr
  intro ω hh hg
  apply hne
  rw [← observedBondHistory_eq_of_mem next ω h hh,
    ← observedBondHistory_eq_of_mem next ω g hg, hlen]

/-- Histories with a fixed number of revealed bond values. -/
abbrev BondHistory (n : ℕ) := {h : List Bool // h.length = n}

noncomputable instance (n : ℕ) : Fintype (BondHistory n) :=
  (List.finite_length_eq Bool n).fintype

/-- Fixed-length adaptive histories cover configuration space. -/
theorem iUnion_bondHistoryEvent {d : ℕ} (next : List Bool → BondTest d) (n : ℕ) :
    (⋃ h : BondHistory n, bondHistoryEvent next h.1) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro ω
  exact Set.mem_iUnion.mpr ⟨⟨observedBondHistory next ω n,
    length_observedBondHistory next ω n⟩, observedBondHistory_mem next ω n⟩

/-- On a history event, any event determined by that history is either the
whole history event or the empty set. -/
theorem measurableSet_history_inter {d : ℕ} (next : List Bool → BondTest d)
    (n : ℕ) (S : Set (List Bool)) (h : BondHistory n) :
    MeasurableSet[bondSigma (historyBonds next h.1)]
      ({ω | observedBondHistory next ω n ∈ S} ∩ bondHistoryEvent next h.1) := by
  by_cases hs : h.1 ∈ S
  · have heq : {ω | observedBondHistory next ω n ∈ S} ∩ bondHistoryEvent next h.1 =
        bondHistoryEvent next h.1 := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · exact And.right
      · intro hw
        constructor
        · rw [← h.2, observedBondHistory_eq_of_mem next ω h.1 hw]
          exact hs
        · exact hw
    rw [heq]
    exact measurableSet_bondHistoryEvent next h.1
  · have heq : {ω | observedBondHistory next ω n ∈ S} ∩ bondHistoryEvent next h.1 =
        ∅ := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hw
      apply hs
      have hh := observedBondHistory_eq_of_mem next ω h.1 hw.2
      rw [h.2] at hh
      rw [← hh]
      exact hw.1
    rw [heq]
    exact @MeasurableSet.empty (Configuration d) (bondSigma (historyBonds next h.1))

/-- Seed survival decays geometrically for an adaptive bond exploration whose
survival is determined by the revealed history. The choice of the exploration
and the seed can depend on an independent base configuration. -/
theorem measureReal_prod_survival_le_of_bond_revelation {d : ℕ}
    (q r : unitInterval) (N : ℕ)
    (next : Configuration d → List Bool → BondTest d)
    (U : Configuration d → ∀ n, BondHistory n → Set (Vertex d))
    (hU : ∀ b n h, (U b n h).Finite)
    (hN : ∀ b n h, (finite_localBonds (hU b n h)).toFinset.card ≤ N)
    (hfresh : ∀ b n h, Disjoint (localBonds (U b n h)) (historyBonds (next b) h.1))
    (S : Configuration d → ℕ → Set (List Bool))
    (G : ℕ → Set (Configuration d × Configuration d))
    (hsection : ∀ b n ω, (b, ω) ∈ G n ↔ observedBondHistory (next b) ω n ∈ S b n)
    (hG : ∀ n, MeasurableSet (G n)) (hdecr : ∀ n, G (n + 1) ⊆ G n)
    (hfail : ∀ b n h, Disjoint ((Prod.mk b ⁻¹' G (n + 1)) ∩
      bondHistoryEvent (next b) h.1) (fullyOpenRegion (U b n h))) :
    ∀ n, ((latticeBondLaw d q).prod (latticeBondLaw d r)).real (G n) ≤
      (1 - (r : ℝ) ^ N) ^ n := by
  apply measureReal_prod_survival_le_of_fresh_seed_histories BondHistory q r N
    (fun b n h => historyBonds (next b) h.1) U hU hN hfresh
    (fun b n h => bondHistoryEvent (next b) h.1) G
  · intro b n h
    exact measurableSet_bondHistoryEvent (next b) h.1
  · intro b n h
    have heq : Prod.mk b ⁻¹' G n =
        {ω | observedBondHistory (next b) ω n ∈ S b n} := by
      ext ω
      exact hsection b n ω
    rw [heq]
    exact measurableSet_history_inter (next b) n (S b n) h
  · exact hG
  · intro b n
    rw [iUnion_bondHistoryEvent]
    exact Set.subset_univ _
  · intro b n h g hne
    apply disjoint_bondHistoryEvent (next b) (h.2.trans g.2.symm)
    intro heq
    exact hne (Subtype.ext heq)
  · exact hdecr
  · exact hfail

end Rigidity.Percolation
