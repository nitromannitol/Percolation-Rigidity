import Rigidity.Proofs.S4.OuterNonConstant.Defs

/-!
# Lemma 4.8, conditional form: resetting a finite set of bonds

The reset `resetConfig D π` of a finite set `D` of bonds to a pattern `π` satisfies the analogues
of the pattern-bond lemmas of `Rigidity.Proofs.S4.Conditioning`: the event `{ω_D = π}` has
positive probability, it is independent of `resetConfig D π ⁻¹' S`, and
`P[{ω_D = π}] P[resetConfig D π ⁻¹' S] ≤ P[S]`. Almost sure properties transfer to the reset
environment. The conditioning event `A_H = {𝒞_∞ ∩ Q_R = H}` is measurable, and an averaging
argument over the disjoint events `A_H ⊆ {ω_D = π}` gives some `H` with
`P[A_H ∩ G] / P[A_H] ≥ P[resetConfig D π ⁻¹' G]` (`exists_conditional_ge`).
-/

namespace Rigidity.Proofs.S4.OuterNonConstant

open MeasureTheory ProbabilityTheory LatticeProb.Percolation Rigidity.Section4 Rigidity.Steps.S4

variable {d : ℕ}

/-! ### Basic properties of the reset -/

theorem resetConfig_of_mem {D : Set (Bond d)} {π : Bond d → Bool} {ω : Configuration d}
    {e : Bond d} (he : e ∈ D) : resetConfig D π ω e = π e := by
  simp [resetConfig, he]

theorem resetConfig_of_not_mem {D : Set (Bond d)} {π : Bond d → Bool} {ω : Configuration d}
    {e : Bond d} (he : e ∉ D) : resetConfig D π ω e = ω e := by
  simp [resetConfig, he]

theorem resetConfig_of_mem_resetEvent {D : Set (Bond d)} {π : Bond d → Bool}
    {ω : Configuration d} (h : ω ∈ resetEvent D π) : resetConfig D π ω = ω := by
  funext e
  by_cases he : e ∈ D
  · rw [resetConfig_of_mem he]
    exact (h e he).symm
  · exact resetConfig_of_not_mem he

theorem resetEvent_eq_biInter {D : Set (Bond d)} (hD : D.Finite) (π : Bond d → Bool) :
    resetEvent D π = ⋂ e ∈ hD.toFinset, (fun ω : Configuration d => ω e) ⁻¹' {π e} := by
  ext ω
  simp [resetEvent]

theorem measurableSet_resetEvent {D : Set (Bond d)} (hD : D.Finite) (π : Bond d → Bool) :
    MeasurableSet (resetEvent D π) := by
  rw [resetEvent_eq_biInter hD]
  refine MeasurableSet.biInter (hD.toFinset.countable_toSet) fun e _ => ?_
  exact measurable_pi_apply e (measurableSet_singleton _)

/-! ### The reset event has positive probability -/

theorem ofReal_pow_le_measure_resetEvent (p : unitInterval) {D : Set (Bond d)} (hD : D.Finite)
    (π : Bond d → Bool) :
    ENNReal.ofReal (min (p : ℝ) (1 - p)) ^ D.ncard ≤ latticeBondLaw d p (resetEvent D π) := by
  rw [resetEvent_eq_biInter hD, (latticeBondLaw_iIndepFun p).measure_inter_preimage_eq_mul
    hD.toFinset (fun e _ => measurableSet_singleton _), Set.ncard_eq_toFinset_card _ hD]
  refine Finset.pow_card_le_prod _ _ _ fun e _ => ?_
  have hopen : MeasurableSet {ω : Configuration d | ω e = true} := by
    have h : MeasurableSet ((fun ω : Configuration d => ω e) ⁻¹' {true}) :=
      measurable_pi_apply e (measurableSet_singleton true)
    exact h
  cases π e
  · have hc : {ω : Configuration d | ω e = false} = {ω | ω e = true}ᶜ := by
      ext ω
      simp
    change ENNReal.ofReal _ ≤ latticeBondLaw d p {ω | ω e = false}
    rw [hc, prob_compl_eq_one_sub hopen, latticeBondLaw_open, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_sub _ (unitInterval.nonneg p)]
    exact ENNReal.ofReal_le_ofReal (min_le_right _ _)
  · change ENNReal.ofReal _ ≤ latticeBondLaw d p {ω | ω e = true}
    rw [latticeBondLaw_open]
    exact ENNReal.ofReal_le_ofReal (min_le_left _ _)

theorem measure_resetEvent_pos {p : unitInterval} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    {D : Set (Bond d)} (hD : D.Finite) (π : Bond d → Bool) :
    0 < latticeBondLaw d p (resetEvent D π) := by
  refine lt_of_lt_of_le ?_ (ofReal_pow_le_measure_resetEvent p hD π)
  exact ENNReal.pow_pos (ENNReal.ofReal_pos.mpr (lt_min hp0 (by linarith))) _

/-! ### Factorization -/

theorem measure_resetEvent_mul_le (p : unitInterval) {D : Set (Bond d)} (hD : D.Finite)
    (π : Bond d → Bool) (S : Set (Configuration d)) :
    latticeBondLaw d p (resetEvent D π) * latticeBondLaw d p (resetConfig D π ⁻¹' S) ≤
      latticeBondLaw d p S := by
  set μ := latticeBondLaw d p with hμ
  let mE : Bond d → MeasurableSpace (Configuration d) :=
    fun e => MeasurableSpace.comap (fun ω : Configuration d => ω e) inferInstance
  have hind : Indep (⨆ e ∈ D, mE e) (⨆ e ∈ Dᶜ, mE e) μ :=
    indep_iSup_of_disjoint (fun e => (measurable_pi_apply e).comap_le)
      (latticeBondLaw_iIndepFun p).iIndep disjoint_compl_right
  have hBmeas : MeasurableSet[⨆ e ∈ D, mE e] (resetEvent D π) := by
    rw [resetEvent_eq_biInter hD]
    refine MeasurableSet.biInter (hD.toFinset.countable_toSet) fun e he => ?_
    rw [Finset.mem_coe, Set.Finite.mem_toFinset] at he
    exact le_iSup₂ (f := fun e (_ : e ∈ D) => mE e) e he _
      (MeasurableSpace.measurableSet_comap.2 ⟨_, measurableSet_singleton _, rfl⟩)
  have hmap : Measurable[⨆ e ∈ Dᶜ, mE e] (resetConfig D π) := by
    refine (@measurable_pi_iff _ _ _ (⨆ e ∈ Dᶜ, mE e) _ _).2 fun e => ?_
    by_cases he : e ∈ D
    · have : (fun ω => resetConfig D π ω e) = fun _ => π e := by
        funext ω
        exact resetConfig_of_mem he
      rw [this]
      exact measurable_const
    · have : (fun ω => resetConfig D π ω e) = fun ω => ω e := by
        funext ω
        exact resetConfig_of_not_mem he
      rw [this]
      exact (comap_measurable (fun ω : Configuration d => ω e)).mono
        (le_iSup₂ (f := fun e (_ : e ∈ Dᶜ) => mE e) e he) le_rfl
  have hsub : ∀ T, resetEvent D π ∩ resetConfig D π ⁻¹' T ⊆ T := by
    rintro T ω ⟨hωB, hωT⟩
    rwa [Set.mem_preimage, resetConfig_of_mem_resetEvent hωB] at hωT
  have key : ∀ T, MeasurableSet T →
      μ (resetEvent D π) * μ (resetConfig D π ⁻¹' T) ≤ μ T := by
    intro T hT
    calc μ (resetEvent D π) * μ (resetConfig D π ⁻¹' T)
        = μ (resetEvent D π ∩ resetConfig D π ⁻¹' T) :=
          ((Indep_iff _ _ μ).1 hind _ _ hBmeas (hmap hT)).symm
      _ ≤ μ T := measure_mono (hsub T)
  calc μ (resetEvent D π) * μ (resetConfig D π ⁻¹' S)
      ≤ μ (resetEvent D π) * μ (resetConfig D π ⁻¹' toMeasurable μ S) := by
        gcongr
        exact Set.preimage_mono (subset_toMeasurable μ S)
    _ ≤ μ (toMeasurable μ S) := key _ (measurableSet_toMeasurable μ S)
    _ = μ S := measure_toMeasurable S

/-! ### Almost sure properties of the reset environment -/

theorem ae_resetConfig {p : unitInterval} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    {D : Set (Bond d)} (hD : D.Finite) (π : Bond d → Bool) {Q : Configuration d → Prop}
    (h : ∀ᵐ ω ∂latticeBondLaw d p, Q ω) :
    ∀ᵐ ω ∂latticeBondLaw d p, Q (resetConfig D π ω) := by
  rw [ae_iff] at h ⊢
  have hle := measure_resetEvent_mul_le p hD π {ω | ¬Q ω}
  rw [h, nonpos_iff_eq_zero, mul_eq_zero] at hle
  exact hle.resolve_left (measure_resetEvent_pos hp0 hp1 hD π).ne'

/-! ### Measurability of the conditioning event -/

theorem measurableSet_iff_const {α : Type*} [MeasurableSpace α] {X : Set α} (hX : MeasurableSet X)
    (c q : Prop) : MeasurableSet {ω : α | (ω ∈ X ∧ c) ↔ q} := by
  by_cases hc : c <;> by_cases hq : q
  · simpa [hc, hq] using hX
  · convert hX.compl using 1
    ext ω
    simp [hc, hq]
  · simp [hc, hq]
  · simp [hc, hq]

/-- The event that the bond `e` is open and both its endpoints lie in the unique infinite
component. -/
def clusterBondEvent (e : Bond d) : Set (Configuration d) :=
  {ω | ω e = true} ∩ ⋂ z : Vertex d, ⋂ (_ : z ∈ (e : Sym2 (Vertex d))), infiniteComponentEvent z

theorem measurableSet_clusterBondEvent (e : Bond d) : MeasurableSet (clusterBondEvent e) := by
  have hopen : MeasurableSet ((fun ω : Configuration d => ω e) ⁻¹' {true}) :=
    measurable_pi_apply e (measurableSet_singleton true)
  refine hopen.inter ?_
  exact MeasurableSet.iInter fun z => MeasurableSet.iInter fun _ =>
    measurableSet_infiniteComponentEvent z

theorem mem_componentBondsIn_uniqueInfiniteComponent_iff {ω : Configuration d}
    (h : HasUniqueInfiniteOpenComponent ω) (R : ℕ) (e : Bond d) :
    e ∈ componentBondsIn (uniqueInfiniteComponent h) (cube d R) ↔
      ω ∈ clusterBondEvent e ∧ ∀ z ∈ (e : Sym2 (Vertex d)), z ∈ cube d R := by
  simp only [componentBondsIn, clusterBondEvent, Set.mem_setOf_eq, Set.mem_inter_iff,
    Set.mem_iInter, mem_uniqueInfiniteComponent_iff h]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, fun z hz => (h2 z hz).2⟩, fun z hz => (h2 z hz).1⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, fun z hz => ⟨h3 z hz, h2 z hz⟩⟩

theorem conditioningEvent_eq (R : ℕ) (H : Set (Bond d)) :
    conditioningEvent d R H = uniqueInfiniteComponentEvent d ∩
      ⋂ e : Bond d, {ω : Configuration d |
        (ω ∈ clusterBondEvent e ∧ ∀ z ∈ (e : Sym2 (Vertex d)), z ∈ cube d R) ↔ e ∈ H} := by
  ext ω
  constructor
  · rintro ⟨h, hC⟩
    refine ⟨h, Set.mem_iInter.2 fun e => ?_⟩
    change (ω ∈ clusterBondEvent e ∧ ∀ z ∈ (e : Sym2 (Vertex d)), z ∈ cube d R) ↔ e ∈ H
    rw [← mem_componentBondsIn_uniqueInfiniteComponent_iff h R e, hC]
  · rintro ⟨h, hC⟩
    refine ⟨h, ?_⟩
    ext e
    rw [mem_componentBondsIn_uniqueInfiniteComponent_iff h R e]
    exact (Set.mem_iInter.1 hC e)

theorem measurableSet_conditioningEvent (R : ℕ) (H : Set (Bond d)) :
    MeasurableSet (conditioningEvent d R H) := by
  rw [conditioningEvent_eq]
  exact (measurableSet_uniqueInfiniteComponentEvent d).inter (MeasurableSet.iInter fun e =>
    measurableSet_iff_const (measurableSet_clusterBondEvent e) _ _)

/-! ### Averaging over the cluster configuration `H` -/

theorem componentBondsIn_subset_innerBonds {ω : Configuration d} (C : OpenComponent ω) (R : ℕ) :
    componentBondsIn C (cube d R) ⊆ Rigidity.Proofs.S4.Conditioning.innerBonds d R :=
  fun _ he z hz => (he.2 z hz).1

theorem finite_innerBonds (d R : ℕ) : (Rigidity.Proofs.S4.Conditioning.innerBonds d R).Finite := by
  refine (finite_bondsNear d R).subset fun e he => ?_
  obtain ⟨x, y, hxy, -⟩ := e.2
  have hx : x ∈ (e : Sym2 (Vertex d)) := by rw [hxy]; exact Sym2.mem_mk_left x y
  exact ⟨x, hx, he x hx⟩

theorem subset_innerBonds_of_nonempty {R : ℕ} {H : Set (Bond d)}
    (h : (conditioningEvent d R H).Nonempty) : H ⊆ Rigidity.Proofs.S4.Conditioning.innerBonds d R := by
  obtain ⟨ω, hh, hC⟩ := h
  rw [← hC]
  exact componentBondsIn_subset_innerBonds _ R

theorem conditioningEvent_disjoint (R : ℕ) {H H' : Set (Bond d)} (hne : H ≠ H') :
    Disjoint (conditioningEvent d R H) (conditioningEvent d R H') := by
  rw [Set.disjoint_left]
  rintro ω ⟨h, hC⟩ ⟨h', hC'⟩
  exact hne (hC.symm.trans hC')

/-- **Averaging over `H`.** If, after resetting the bonds of `D` to `π`, every environment of `G`
lies in some `A_H ⊆ {ω_D = π}` with `P H`, and the reset preimage of `G` has positive probability,
then some `H` with `P H` has `P[A_H ∩ G] / P[A_H] ≥ P[resetConfig D π ⁻¹' G]`. -/
theorem exists_conditional_ge {p : unitInterval} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (R : ℕ)
    {D : Set (Bond d)} (hD : D.Finite) (π : Bond d → Bool) (G : Set (Configuration d))
    (P : Set (Bond d) → Prop)
    (hcompat : ∀ ω, resetConfig D π ω ∈ G → ∃ H, P H ∧
      resetConfig D π ω ∈ conditioningEvent d R H ∧ conditioningEvent d R H ⊆ resetEvent D π)
    (hpos : 0 < latticeBondLaw d p (resetConfig D π ⁻¹' G)) :
    ∃ H, P H ∧ 0 < latticeBondLaw d p (conditioningEvent d R H) ∧
      latticeBondLaw d p (resetConfig D π ⁻¹' G) ≤
        latticeBondLaw d p (conditioningEvent d R H ∩ G) /
          latticeBondLaw d p (conditioningEvent d R H) := by
  classical
  set μ := latticeBondLaw d p with hμ
  set RE := resetEvent D π with hRE
  have hRE0 : μ RE ≠ 0 := (measure_resetEvent_pos hp0 hp1 hD π).ne'
  have hREtop : μ RE ≠ ⊤ := measure_ne_top μ _
  let 𝓗 : Set (Set (Bond d)) :=
    {H | P H ∧ conditioningEvent d R H ⊆ RE ∧ (conditioningEvent d R H).Nonempty}
  have h𝓗 : 𝓗.Finite :=
    (finite_innerBonds d R).finite_subsets.subset fun H hH => subset_innerBonds_of_nonempty hH.2.2
  set F := h𝓗.toFinset with hFdef
  have hF : ∀ H, H ∈ F ↔
      P H ∧ conditioningEvent d R H ⊆ RE ∧ (conditioningEvent d R H).Nonempty := fun H =>
    h𝓗.mem_toFinset
  have hcover : resetConfig D π ⁻¹' G ⊆
      ⋃ H ∈ F, resetConfig D π ⁻¹' (conditioningEvent d R H ∩ G) := by
    intro ω hω
    obtain ⟨H, hPH, hAH, hsub⟩ := hcompat ω hω
    simp only [Set.mem_iUnion]
    exact ⟨H, (hF H).2 ⟨hPH, hsub, _, hAH⟩, hAH, hω⟩
  have hsum1 : μ (resetConfig D π ⁻¹' G) ≤
      ∑ H ∈ F, μ (resetConfig D π ⁻¹' (conditioningEvent d R H ∩ G)) :=
    (measure_mono hcover).trans (measure_biUnion_finset_le F _)
  have hFne : F.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.sum_empty, nonpos_iff_eq_zero] at hsum1
    exact hpos.ne' hsum1
  obtain ⟨H₀, hH₀F, hmax⟩ := Finset.exists_max_image F
    (fun H => μ (conditioningEvent d R H ∩ G) / μ (conditioningEvent d R H)) hFne
  set r := μ (conditioningEvent d R H₀ ∩ G) / μ (conditioningEvent d R H₀) with hr
  have hterm : ∀ H ∈ F, μ (conditioningEvent d R H ∩ G) ≤ r * μ (conditioningEvent d R H) := by
    intro H hH
    by_cases h0 : μ (conditioningEvent d R H) = 0
    · have : μ (conditioningEvent d R H ∩ G) = 0 :=
        le_antisymm ((measure_mono Set.inter_subset_left).trans h0.le) bot_le
      rw [this]
      exact zero_le
    · calc μ (conditioningEvent d R H ∩ G)
          = μ (conditioningEvent d R H ∩ G) / μ (conditioningEvent d R H) *
              μ (conditioningEvent d R H) :=
            (ENNReal.div_mul_cancel h0 (measure_ne_top _ _)).symm
        _ ≤ r * μ (conditioningEvent d R H) := by gcongr; exact hmax H hH
  have hdisj : (↑F : Set (Set (Bond d))).PairwiseDisjoint (conditioningEvent d R) :=
    fun H _ H' _ hne => conditioningEvent_disjoint R hne
  have hsum2 : ∑ H ∈ F, μ (conditioningEvent d R H) ≤ μ RE := by
    rw [← measure_biUnion_finset hdisj (fun H _ => measurableSet_conditioningEvent R H)]
    exact measure_mono (Set.iUnion₂_subset fun H hH => ((hF H).1 hH).2.1)
  have hkey : μ RE * μ (resetConfig D π ⁻¹' G) ≤ μ RE * r := by
    calc μ RE * μ (resetConfig D π ⁻¹' G)
        ≤ μ RE * ∑ H ∈ F, μ (resetConfig D π ⁻¹' (conditioningEvent d R H ∩ G)) := by gcongr
      _ = ∑ H ∈ F, μ RE * μ (resetConfig D π ⁻¹' (conditioningEvent d R H ∩ G)) :=
          Finset.mul_sum _ _ _
      _ ≤ ∑ H ∈ F, μ (conditioningEvent d R H ∩ G) :=
          Finset.sum_le_sum fun H _ => measure_resetEvent_mul_le p hD π _
      _ ≤ ∑ H ∈ F, r * μ (conditioningEvent d R H) := Finset.sum_le_sum hterm
      _ = r * ∑ H ∈ F, μ (conditioningEvent d R H) := (Finset.mul_sum _ _ _).symm
      _ ≤ r * μ RE := by gcongr
      _ = μ RE * r := mul_comm _ _
  have hle : μ (resetConfig D π ⁻¹' G) ≤ r := (ENNReal.mul_le_mul_iff_right hRE0 hREtop).1 hkey
  have hAH₀ : μ (conditioningEvent d R H₀) ≠ 0 := by
    intro h0
    have h1 : μ (conditioningEvent d R H₀ ∩ G) = 0 :=
      le_antisymm ((measure_mono Set.inter_subset_left).trans h0.le) bot_le
    have : r = 0 := by rw [hr, h1, ENNReal.zero_div]
    rw [this, nonpos_iff_eq_zero] at hle
    exact hpos.ne' hle
  exact ⟨H₀, ((hF H₀).1 hH₀F).1, pos_iff_ne_zero.2 hAH₀, hle⟩

end Rigidity.Proofs.S4.OuterNonConstant
