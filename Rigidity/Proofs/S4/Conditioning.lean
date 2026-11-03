import Rigidity.Steps.S4.NonConstantOnGadgetJoint

/-!
# Lemma 4.8, conditional form: the conditioning event factorizes

Lemma 4.8 as printed (`Rigidity.Section4.NonConstantOnGadgetStmt`, the conditional form) is
proved without `OuterNonConstantStep` in `Rigidity/Proofs/S4/OuterNonConstant.lean`. This file
records the fixed-`H` route.

Lemma 4.8 (`paper/percolation-harmonic.tex` L1340-1347, printed conditional form
`Rigidity.Section4.NonConstantOnGadgetStmt`) bounds from below the conditional probability
`P[ℓ_q not constant on the gadget | 𝒞_∞ ∩ Q_R = H]` for a deterministic bond set `H` of `Q_R`.
The printed proof (L1417) only bounds the joint probability; `Rigidity.Steps.S4.ConditioningStep`
records the gap for the paper's `H`.

This file proves that the event `A_H = {𝒞_∞ ∩ Q_R = H}` factorizes, for every `H`, and reduces
the conditional form of Lemma 4.8 to a lower bound for an event of the bonds that `A_H` does not
fix (`OuterNonConstantStep`).

* The pattern bonds of `H` are the bonds of `Q_R` with an endpoint at a site of `H`. On `A_H`
  they are open exactly on `H` (`conditioningEvent_subset_patternEvent`): an open bond of `Q_R`
  at a site of the cluster is a bond of the cluster.
* `patternConfig R H ω` resets the pattern bonds to `H` and keeps the other bonds of `ω`. The
  pattern event `B_H` is independent of every event `patternConfig R H ⁻¹' S`, and
  `B_H ∩ patternConfig R H ⁻¹' S ⊆ S`, so `P[B_H] P[patternConfig R H ⁻¹' S] ≤ P[S]`
  (`measure_patternEvent_mul_le`).
* With `S = A_H ∩ G` and `P[A_H] ≤ P[B_H]`:
  `P[patternConfig R H ⁻¹' (A_H ∩ G)] ≤ P[A_H ∩ G] / P[A_H]` (`conditional_ge_pattern`).

The remaining step `OuterNonConstantStep` asks for `H ⊇` (gadget) whose outer event has
probability `≥ c R^{-2d+2}`; see its docstring for what is known about it.
-/

namespace Rigidity.Proofs.S4.Conditioning

open MeasureTheory ProbabilityTheory LatticeProb.Percolation LatticeProb.Network
  Rigidity.Section4 Rigidity.Steps.S4

variable {d : ℕ}

/-- The bonds of `Q_R`: both endpoints lie in `Q_R`. -/
def innerBonds (d R : ℕ) : Set (Bond d) :=
  {e | ∀ z ∈ (e : Sym2 (Vertex d)), z ∈ cube d R}

/-- The sites of a set of bonds. -/
def siteSet (H : Set (Bond d)) : Set (Vertex d) :=
  {z | ∃ e ∈ H, z ∈ (e : Sym2 (Vertex d))}

/-- The pattern bonds of `H`: the bonds of `Q_R` with an endpoint at a site of `H`. -/
def patternBonds (R : ℕ) (H : Set (Bond d)) : Set (Bond d) :=
  {e | e ∈ innerBonds d R ∧ ∃ z ∈ (e : Sym2 (Vertex d)), z ∈ siteSet H}

open scoped Classical in
/-- The pattern event of `H`: the pattern bonds of `H` are open exactly on `H`. -/
def patternEvent (R : ℕ) (H : Set (Bond d)) : Set (Configuration d) :=
  {ω | ∀ e ∈ patternBonds R H, ω e = decide (e ∈ H)}

open scoped Classical in
/-- The environment `ω` with the pattern bonds of `H` open exactly on `H`. -/
noncomputable def patternConfig (R : ℕ) (H : Set (Bond d)) (ω : Configuration d) :
    Configuration d :=
  fun e => if e ∈ patternBonds R H then decide (e ∈ H) else ω e

theorem patternBonds_subset_bondsNear (R : ℕ) (H : Set (Bond d)) :
    patternBonds R H ⊆ bondsNear d R := by
  rintro e ⟨he, z, hz, -⟩
  exact ⟨z, hz, he z hz⟩

theorem finite_patternBonds (R : ℕ) (H : Set (Bond d)) : (patternBonds R H).Finite :=
  (finite_bondsNear d R).subset (patternBonds_subset_bondsNear R H)

/-- An open bond at a site of an open component has its other endpoint in the component. -/
theorem mem_supp_of_open {ω : Configuration d} (C : OpenComponent ω) {e : Bond d}
    (he : ω e = true) {z w : Vertex d} (hzw : (e : Sym2 (Vertex d)) = s(z, w))
    (hz : z ∈ C.supp) : w ∈ C.supp := by
  obtain ⟨x, y, hxy, hsum⟩ := e.2
  have hadj : (nearestNeighborGraph d).Adj z w := by
    have h : s(z, w) = s(x, y) := hzw.symm.trans hxy
    rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact lattice_adj_iff_l1Dist.mpr hsum
    · exact (lattice_adj_iff_l1Dist.mpr hsum).symm
  have hbond : bondOfAdjacent hadj = e := Subtype.ext hzw.symm
  have hopen : (openGraph ω).Adj z w := ⟨hadj, by rw [hbond]; exact he⟩
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hz ⊢
  rw [← hz]
  exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hopen).symm

open scoped Classical in
/-- **The conditioning event fixes the pattern bonds.** On `𝒞_∞ ∩ Q_R = H`, the bonds of `Q_R`
at a site of `H` are open exactly on `H`: the sites of `H` lie in `𝒞_∞`, and an open bond of
`Q_R` at a site of `𝒞_∞` is a bond of `𝒞_∞ ∩ Q_R`. -/
theorem conditioningEvent_subset_patternEvent (R : ℕ) (H : Set (Bond d)) :
    conditioningEvent d R H ⊆ patternEvent R H := by
  rintro ω ⟨h, hC⟩ e ⟨he, z, hz, e', he'H, hze'⟩
  have hzC : z ∈ (uniqueInfiniteComponent h).supp := by
    rw [← hC] at he'H
    exact (he'H.2 z hze').2
  by_cases heH : e ∈ H
  · have hmem : e ∈ componentBondsIn (uniqueInfiniteComponent h) (cube d R) := by
      rw [hC]; exact heH
    simp only [heH, decide_true]
    exact hmem.1
  · simp only [heH, decide_false]
    by_contra hne
    have hopen : ω e = true := by simpa using hne
    apply heH
    rw [← hC]
    refine ⟨hopen, fun w hw => ⟨he w hw, ?_⟩⟩
    obtain ⟨w', hw'⟩ := Sym2.mem_iff_exists.mp hz
    rw [hw', Sym2.mem_iff] at hw
    rcases hw with rfl | rfl
    · exact hzC
    · exact mem_supp_of_open _ hopen hw' hzC

open scoped Classical in
/-- The pattern event has probability at least `min(p, 1-p)^{#pattern bonds}`. -/
theorem ofReal_pow_le_measure_patternEvent (p : unitInterval) (R : ℕ) (H : Set (Bond d)) :
    ENNReal.ofReal (min (p : ℝ) (1 - p)) ^ (patternBonds R H).ncard ≤
      latticeBondLaw d p (patternEvent R H) := by
  have hfin := finite_patternBonds R H
  have hB : patternEvent R H =
      ⋂ e ∈ hfin.toFinset, (fun ω : Configuration d => ω e) ⁻¹' {decide (e ∈ H)} := by
    ext ω
    simp [patternEvent]
  rw [hB, (latticeBondLaw_iIndepFun p).measure_inter_preimage_eq_mul hfin.toFinset
    (fun e _ => measurableSet_singleton _), Set.ncard_eq_toFinset_card _ hfin]
  refine Finset.pow_card_le_prod _ _ _ fun e _ => ?_
  have hopen : MeasurableSet {ω : Configuration d | ω e = true} := by
    have h : MeasurableSet ((fun ω : Configuration d => ω e) ⁻¹' {true}) :=
      measurable_pi_apply e (measurableSet_singleton true)
    exact h
  cases decide (e ∈ H)
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

/-- The pattern event has positive probability, for `0 < p < 1`. -/
theorem measure_patternEvent_pos {p : unitInterval} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (R : ℕ) (H : Set (Bond d)) : 0 < latticeBondLaw d p (patternEvent R H) := by
  refine lt_of_lt_of_le ?_ (ofReal_pow_le_measure_patternEvent p R H)
  exact ENNReal.pow_pos (ENNReal.ofReal_pos.mpr (lt_min hp0 (by linarith))) _

open scoped Classical in
/-- **Factorization.** The pattern event of `H` is determined by the pattern bonds and
`patternConfig R H ⁻¹' S` by the other bonds, so they are independent; on the pattern event
`patternConfig R H ω = ω`. Hence `P[B_H] P[patternConfig R H ⁻¹' S] ≤ P[S]` for every event `S`
(a nonmeasurable `S` is replaced by a measurable hull). -/
theorem measure_patternEvent_mul_le (p : unitInterval) (R : ℕ) (H : Set (Bond d))
    (S : Set (Configuration d)) :
    latticeBondLaw d p (patternEvent R H) * latticeBondLaw d p (patternConfig R H ⁻¹' S) ≤
      latticeBondLaw d p S := by
  set μ := latticeBondLaw d p with hμ
  have hfin := finite_patternBonds R H
  let mE : Bond d → MeasurableSpace (Configuration d) :=
    fun e => MeasurableSpace.comap (fun ω : Configuration d => ω e) inferInstance
  have hind : Indep (⨆ e ∈ patternBonds R H, mE e) (⨆ e ∈ (patternBonds R H)ᶜ, mE e) μ :=
    indep_iSup_of_disjoint (fun e => (measurable_pi_apply e).comap_le)
      (latticeBondLaw_iIndepFun p).iIndep disjoint_compl_right
  have hB : patternEvent R H =
      ⋂ e ∈ hfin.toFinset, (fun ω : Configuration d => ω e) ⁻¹' {decide (e ∈ H)} := by
    ext ω
    simp [patternEvent]
  have hBmeas : MeasurableSet[⨆ e ∈ patternBonds R H, mE e] (patternEvent R H) := by
    rw [hB]
    refine MeasurableSet.biInter (hfin.toFinset.countable_toSet) fun e he => ?_
    rw [Finset.mem_coe, Set.Finite.mem_toFinset] at he
    exact le_iSup₂ (f := fun e (_ : e ∈ patternBonds R H) => mE e) e he _
      (MeasurableSpace.measurableSet_comap.2 ⟨_, measurableSet_singleton _, rfl⟩)
  have hmap : Measurable[⨆ e ∈ (patternBonds R H)ᶜ, mE e] (patternConfig R H) := by
    refine (@measurable_pi_iff _ _ _ (⨆ e ∈ (patternBonds R H)ᶜ, mE e) _ _).2 fun e => ?_
    by_cases he : e ∈ patternBonds R H
    · have : (fun ω => patternConfig R H ω e) = fun _ => decide (e ∈ H) := by
        funext ω
        simp [patternConfig, he]
      rw [this]
      exact measurable_const
    · have : (fun ω => patternConfig R H ω e) = fun ω => ω e := by
        funext ω
        simp [patternConfig, he]
      rw [this]
      exact (comap_measurable (fun ω : Configuration d => ω e)).mono
        (le_iSup₂ (f := fun e (_ : e ∈ (patternBonds R H)ᶜ) => mE e) e he) le_rfl
  have hsub : ∀ T, patternEvent R H ∩ patternConfig R H ⁻¹' T ⊆ T := by
    rintro T ω ⟨hωB, hωT⟩
    have : patternConfig R H ω = ω := by
      funext e
      by_cases he : e ∈ patternBonds R H
      · simp [patternConfig, he, hωB e he]
      · simp [patternConfig, he]
    rwa [Set.mem_preimage, this] at hωT
  have key : ∀ T, MeasurableSet T →
      μ (patternEvent R H) * μ (patternConfig R H ⁻¹' T) ≤ μ T := by
    intro T hT
    calc μ (patternEvent R H) * μ (patternConfig R H ⁻¹' T)
        = μ (patternEvent R H ∩ patternConfig R H ⁻¹' T) :=
          ((Indep_iff _ _ μ).1 hind _ _ hBmeas (hmap hT)).symm
      _ ≤ μ T := measure_mono (hsub T)
  calc μ (patternEvent R H) * μ (patternConfig R H ⁻¹' S)
      ≤ μ (patternEvent R H) * μ (patternConfig R H ⁻¹' toMeasurable μ S) := by
        gcongr
        exact Set.preimage_mono (subset_toMeasurable μ S)
    _ ≤ μ (toMeasurable μ S) := key _ (measurableSet_toMeasurable μ S)
    _ = μ S := measure_toMeasurable S

/-- **The conditional probability given `𝒞_∞ ∩ Q_R = H` dominates the outer probability**, for
every `H` and every event `G`: `P[patternConfig R H ⁻¹' (A_H ∩ G)] ≤ P[A_H ∩ G] / P[A_H]`. -/
theorem conditional_ge_pattern {p : unitInterval} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (R : ℕ) (H : Set (Bond d)) (G : Set (Configuration d)) :
    latticeBondLaw d p (patternConfig R H ⁻¹' (conditioningEvent d R H ∩ G)) ≤
      latticeBondLaw d p (conditioningEvent d R H ∩ G) /
        latticeBondLaw d p (conditioningEvent d R H) := by
  set μ := latticeBondLaw d p
  set A := conditioningEvent d R H
  have hB0 : μ (patternEvent R H) ≠ 0 := (measure_patternEvent_pos hp0 hp1 R H).ne'
  have hBtop : μ (patternEvent R H) ≠ ⊤ := measure_ne_top μ _
  have hAB : μ A ≤ μ (patternEvent R H) :=
    measure_mono (conditioningEvent_subset_patternEvent R H)
  calc μ (patternConfig R H ⁻¹' (A ∩ G))
      = μ (patternEvent R H) * μ (patternConfig R H ⁻¹' (A ∩ G)) / μ (patternEvent R H) := by
        rw [mul_comm, ENNReal.mul_div_cancel_right hB0 hBtop]
    _ ≤ μ (A ∩ G) / μ (patternEvent R H) :=
        ENNReal.div_le_div_right (measure_patternEvent_mul_le p R H (A ∩ G)) _
    _ ≤ μ (A ∩ G) / μ A := ENNReal.div_le_div_left hAB _

/-- **Remaining step of the conditional Lemma 4.8** (not proved): for large `R` there is a bond set
`H` of `Q_R` containing a translate of the gadget of height `R` as an induced subgraph whose outer
event `patternConfig R H ⁻¹' (A_H ∩ G)`, an event of the bonds not fixed by `A_H`, has probability
at least `c R^{-2d+2}`.

Route and obstruction. Take `H` connected and
containing every site of `∂Q_R` up to an independent set (otherwise the bonds of `Q_R` between two
free boundary sites are not fixed by `A_H`, and whether they may be open depends on the outer
bonds). Write `H = S ∪ P₁ ∪ T ∪ P₂` with `S ⊇ ∂Q_R` and the gadget `T` joined to `S`
by interior paths at two sites `s₁, s₂`, which must have a neighbour inside `Q_{R-1}`. If the
corrected plane `ℓ^S` of the environment with `S` inside `Q_R` separates `s₁, s₂`, then `ℓ_q` is
not constant on the gadget (the Liouville argument of `AttachStep`). Comparing `ℓ^S` with the
corrected plane of `ω` on the event `E_R` of `EventStep` shows that `ℓ^S` is not constant on the
sites of `S`, and a union bound over pairs gives `c R^{-2d+2}`, PROVIDED the sites of `S` with no
neighbour in `Q_{R-1}` can be avoided. For `d = 2` these are the four corners; forcing their eight
bonds of `Q_R` closed costs the constant `(1-p)^8`. For `d ≥ 3` they form the `(d-2)`-skeleton of
`∂Q_R`, about `R^{d-2}` sites: the comparison with `ω` gives no information on the face sites
alone, and forcing the skeleton bonds costs `(1-p)^{c R^{d-2}}`. -/
def OuterNonConstantStep (d : ℕ) (hd : 2 ≤ d) (p : unitInterval) : Prop :=
  ∀ q : Fin d → ℝ, q ≠ 0 → ∃ c : ℝ, 0 < c ∧ ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
    ∃ (H : Set (Bond d)) (τ : Vertex d), IsGadgetPlacement hd R H τ ∧
      c * (R : ℝ) ^ (-(2 * (d : ℤ)) + 2) ≤
        (latticeBondLaw d p (patternConfig R H ⁻¹'
          (conditioningEvent d R H ∩ gadgetNonconstantEvent hd q R τ))).toReal

/-- **Lemma 4.8 (printed conditional form)** from the remaining step `OuterNonConstantStep`
(the fixed-`H` route), by the factorization `conditional_ge_pattern`. -/
theorem nonConstantOnGadget_of_outerStep [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (houter : OuterNonConstantStep d hd p) : NonConstantOnGadgetStmt d hd p := by
  have hp0 : 0 < (p : ℝ) := lt_of_le_of_lt (criticalProbability_nonneg d) hpc
  intro q hq
  obtain ⟨c, hc, R₀, hR₀⟩ := houter q hq
  refine ⟨c, hc, max R₀ 1, fun R hR => ?_⟩
  obtain ⟨H, τ, ⟨hHQ, hτQ, hind⟩, hbound⟩ := hR₀ R (le_of_max_le_left hR)
  have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast le_of_max_le_right hR
  have hpos : 0 < c * (R : ℝ) ^ (-(2 * (d : ℤ)) + 2) := by positivity
  set μ := latticeBondLaw d p
  set A := conditioningEvent d R H
  set G := gadgetNonconstantEvent hd q R τ
  have hratio : μ (A ∩ G) / μ A ≤ 1 :=
    ENNReal.div_le_of_le_mul (by rw [one_mul]; exact measure_mono Set.inter_subset_left)
  have hreal : (μ (patternConfig R H ⁻¹' (A ∩ G))).toReal ≤ (μ (A ∩ G) / μ A).toReal :=
    ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top hratio)
      (conditional_ge_pattern hp0 hp1 R H G)
  have hΦpos : μ (patternConfig R H ⁻¹' (A ∩ G)) ≠ 0 := by
    intro h0
    rw [h0, ENNReal.toReal_zero] at hbound
    linarith
  have hApos : 0 < μ A :=
    lt_of_lt_of_le (ENNReal.mul_pos (measure_patternEvent_pos hp0 hp1 R H).ne' hΦpos)
      ((measure_patternEvent_mul_le p R H (A ∩ G)).trans (measure_mono Set.inter_subset_left))
  exact ⟨H, τ, hHQ, hτQ, hind, hApos, hbound.trans hreal⟩

end Rigidity.Proofs.S4.Conditioning
