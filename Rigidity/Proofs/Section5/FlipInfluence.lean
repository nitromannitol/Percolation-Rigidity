import Rigidity.Steps.Section5.GradientTrichotomy

/-!
# Proposition 5.7, Step 1: the influence of one bond vanishes at infinity

`step:5.7-martingale` of Proposition 5.7 (corrected draft L1741-1790, eq. `event-not-dependent`),
in the form `FlipInfluenceStep p` of `Rigidity/Steps/Section5/GradientTrichotomy.lean`: for
`0 < p < 1` and a null-measurable event `E`, `P[E ∆ {ω^e ∈ E}] → 0` along the edges `e`.

Proof. The paper uses the martingale convergence theorem; we use the equivalent approximation by
cylinder events.
* Flipping one bond `b` distorts the law by a bounded factor:
  `min(p, 1 - p) P[ω^b ∈ T] ≤ P[T]` (`min_mul_measure_preimage_flipAt_le`). Writing
  `R_t = {ω : ω[b ↦ t] ∈ T}`, an event of the bonds other than `b`, one has
  `P[T] = p P[R_true] + (1 - p) P[R_false]` by independence, and `{ω^b ∈ T} ⊆ R_true ∪ R_false`.
* A measurable event `E'` with `E' = E` almost surely is approximated within `δ` by a cylinder
  event `C` depending on a finite set `s` of bonds (`exists_measure_symmDiff_lt_of_generateFrom_
  isSetRing`). For `e ∉ s`, `{ω^e ∈ C} = C`, so
  `P[E ∆ {ω^e ∈ E}] ≤ P[E ∆ C] + P[{ω^e ∈ C ∆ E}] ≤ (1 + min(p, 1 - p)⁻¹) δ`.
The bound `0 < p < 1` is used in the first point only.
-/

open MeasureTheory ProbabilityTheory LatticeProb.Percolation Filter Topology Set
open scoped ENNReal symmDiff
open Classical

namespace Rigidity.Proofs.Section5

open Rigidity.Section5 Rigidity.Steps.Section5

/-- The smallest σ-algebra for which the status of the bond `b` is measurable. -/
abbrev bondSigma (b : Bond 2) : MeasurableSpace (Configuration 2) :=
  MeasurableSpace.comap (fun ω : Configuration 2 => ω b) inferInstance

/-- Flipping a bond `b` sets its status to `!ω b`. -/
theorem flipAt_val_eq_update (b : Bond 2) (ω : Configuration 2) :
    flipAt b.val ω = Function.update ω b (!ω b) := by
  funext c
  by_cases hc : c = b
  · subst hc; simp [flipAt]
  · have hcv : c.val ≠ b.val := fun h => hc (Subtype.ext h)
    simp [flipAt, hcv, Function.update_of_ne hc]

/-- If `e` is not a bond, `ω^e = ω`. -/
theorem flipAt_eq_self_of_not_bond {e : Sym2 (Vertex 2)} (he : ∀ b : Bond 2, b.val ≠ e)
    (ω : Configuration 2) : flipAt e ω = ω := by
  funext c
  simp [flipAt, he c]

/-- Setting the status of `b` is measurable with respect to the bonds other than `b`. -/
theorem comap_update_bond_le (b : Bond 2) (t : Bool) :
    MeasurableSpace.comap (fun ω : Configuration 2 => Function.update ω b t) MeasurableSpace.pi ≤
      ⨆ i ∈ ({b}ᶜ : Set (Bond 2)), bondSigma i := by
  rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
  refine iSup_le fun j => ?_
  rw [MeasurableSpace.comap_comp]
  by_cases hj : j = b
  · subst hj
    have h : ((fun f : Configuration 2 => f j) ∘ fun ω : Configuration 2 =>
        Function.update ω j t) = fun _ => t := by
      funext ω; simp
    rw [h, MeasurableSpace.comap_const]
    exact bot_le
  · have h : ((fun f : Configuration 2 => f j) ∘ fun ω : Configuration 2 =>
        Function.update ω b t) = fun ω => ω j := by
      funext ω; simp [Function.update_of_ne hj]
    rw [h]
    exact le_iSup₂ (f := fun i (_ : i ∈ ({b}ᶜ : Set (Bond 2))) => bondSigma i) j hj

/-- The status of `b` is independent of the bonds other than `b`. -/
theorem indep_bond_compl (p : unitInterval) (b : Bond 2) :
    Indep (⨆ i ∈ ({b} : Set (Bond 2)), bondSigma i) (⨆ i ∈ ({b}ᶜ : Set (Bond 2)), bondSigma i)
      (latticeBondLaw 2 p) :=
  indep_iSup_of_disjoint (fun i => (measurable_pi_apply i).comap_le)
    ((iIndepFun_iff_iIndep _ _ _).mp (latticeBondLaw_iIndepFun p)) disjoint_compl_right

theorem measurableSet_bond_eq (b : Bond 2) (t : Bool) :
    MeasurableSet[⨆ i ∈ ({b} : Set (Bond 2)), bondSigma i] {ω : Configuration 2 | ω b = t} :=
  (le_iSup₂ (f := fun i (_ : i ∈ ({b} : Set (Bond 2))) => bondSigma i) b rfl) _
    ⟨{t}, measurableSet_singleton t, rfl⟩

theorem measurableSet_bond_eq' (b : Bond 2) (t : Bool) :
    MeasurableSet {ω : Configuration 2 | ω b = t} :=
  (measurable_pi_apply (X := fun _ : Bond 2 => Bool) b) (measurableSet_singleton t)

theorem latticeBondLaw_closed (p : unitInterval) (b : Bond 2) :
    latticeBondLaw 2 p {ω | ω b = false} = ENNReal.ofReal (1 - p) := by
  have h : {ω : Configuration 2 | ω b = false} = {ω | ω b = true}ᶜ := by
    ext ω; simp
  rw [h, prob_compl_eq_one_sub (measurableSet_bond_eq' b true),
    latticeBondLaw_open, ENNReal.ofReal_sub _ p.property.1, ENNReal.ofReal_one]

/-- Flipping one bond distorts the Bernoulli law by at most the factor `min(p, 1 - p)⁻¹`. -/
theorem min_mul_measure_preimage_flipAt_bond_le (p : unitInterval) (b : Bond 2)
    {T : Set (Configuration 2)} (hT : MeasurableSet T) :
    min (ENNReal.ofReal p) (ENNReal.ofReal (1 - p)) * latticeBondLaw 2 p (flipAt b.val ⁻¹' T) ≤
      latticeBondLaw 2 p T := by
  set μ := latticeBondLaw 2 p
  set R : Bool → Set (Configuration 2) := fun t => (fun ω => Function.update ω b t) ⁻¹' T
  set O : Bool → Set (Configuration 2) := fun t => {ω | ω b = t}
  have hR : ∀ t, MeasurableSet[⨆ i ∈ ({b}ᶜ : Set (Bond 2)), bondSigma i] (R t) :=
    fun t => comap_update_bond_le b t _ ⟨T, hT, rfl⟩
  have hprod : ∀ t, μ (O t ∩ R t) = μ (O t) * μ (R t) := fun t =>
    (Indep_iff _ _ μ).mp (indep_bond_compl p b) _ _ (measurableSet_bond_eq b t) (hR t)
  have hOm : MeasurableSet (O true) := measurableSet_bond_eq' b true
  have hsplit : μ T = μ (O true ∩ R true) + μ (O false ∩ R false) := by
    rw [← measure_inter_add_sdiff T hOm]
    congr 1
    · congr 1; ext ω
      simp only [mem_inter_iff, mem_preimage, O, R, mem_setOf_eq]
      constructor
      · rintro ⟨hω, hb⟩; exact ⟨hb, by rwa [← hb, Function.update_eq_self]⟩
      · rintro ⟨hb, hω⟩; exact ⟨by rwa [← hb, Function.update_eq_self] at hω, hb⟩
    · congr 1; ext ω
      simp only [Set.mem_sdiff, mem_inter_iff, mem_preimage, O, R, mem_setOf_eq,
        Bool.not_eq_true]
      constructor
      · rintro ⟨hω, hb⟩; exact ⟨hb, by rwa [← hb, Function.update_eq_self]⟩
      · rintro ⟨hb, hω⟩; exact ⟨by rwa [← hb, Function.update_eq_self] at hω, hb⟩
  have hsub : flipAt b.val ⁻¹' T ⊆ R false ∪ R true := by
    intro ω hω
    simp only [mem_preimage, flipAt_val_eq_update] at hω
    cases hb : ω b
    · right; simpa [R, hb] using hω
    · left; simpa [R, hb] using hω
  have hO1 : μ (O true) = ENNReal.ofReal p := latticeBondLaw_open p b
  have hO0 : μ (O false) = ENNReal.ofReal (1 - p) := latticeBondLaw_closed p b
  set m := min (ENNReal.ofReal p) (ENNReal.ofReal (1 - p))
  calc m * μ (flipAt b.val ⁻¹' T) ≤ m * (μ (R false) + μ (R true)) :=
        mul_le_mul_right ((measure_mono hsub).trans (measure_union_le _ _)) _
    _ = m * μ (R true) + m * μ (R false) := by rw [mul_add, add_comm]
    _ ≤ μ (O true) * μ (R true) + μ (O false) * μ (R false) := by
        rw [hO1, hO0]
        exact add_le_add (mul_le_mul_left (min_le_left _ _) _)
          (mul_le_mul_left (min_le_right _ _) _)
    _ = μ T := by rw [hsplit, hprod, hprod]

/-- The flip bound, for every unordered pair `e` and every (not necessarily measurable) set. -/
theorem min_mul_measure_preimage_flipAt_le (p : unitInterval) (e : Sym2 (Vertex 2))
    (T : Set (Configuration 2)) :
    min (ENNReal.ofReal p) (ENNReal.ofReal (1 - p)) * latticeBondLaw 2 p (flipAt e ⁻¹' T) ≤
      latticeBondLaw 2 p T := by
  by_cases he : ∃ b : Bond 2, b.val = e
  · obtain ⟨b, rfl⟩ := he
    calc min (ENNReal.ofReal p) (ENNReal.ofReal (1 - p)) *
          latticeBondLaw 2 p (flipAt b.val ⁻¹' T)
        ≤ min (ENNReal.ofReal p) (ENNReal.ofReal (1 - p)) *
          latticeBondLaw 2 p (flipAt b.val ⁻¹' toMeasurable (latticeBondLaw 2 p) T) :=
          mul_le_mul_right (measure_mono (preimage_mono (subset_toMeasurable _ _))) _
      _ ≤ latticeBondLaw 2 p (toMeasurable (latticeBondLaw 2 p) T) :=
          min_mul_measure_preimage_flipAt_bond_le p b (measurableSet_toMeasurable _ _)
      _ = latticeBondLaw 2 p T := measure_toMeasurable T
  · push Not at he
    have hid : flipAt e ⁻¹' T = T := by
      ext ω; simp [flipAt_eq_self_of_not_bond he]
    rw [hid]
    have hm : min (ENNReal.ofReal p) (ENNReal.ofReal (1 - p)) ≤ 1 :=
      (min_le_left _ _).trans (ENNReal.ofReal_le_one.mpr p.property.2)
    simpa using mul_le_mul_left hm (latticeBondLaw 2 p T)

/-- Flipping a bond outside the base of a cylinder event leaves it invariant. -/
theorem preimage_flipAt_cylinder {s : Finset (Bond 2)} {S : Set (s → Bool)}
    {e : Sym2 (Vertex 2)} (he : ∀ b ∈ s, b.val ≠ e) :
    flipAt e ⁻¹' cylinder s S = cylinder s S := by
  ext ω
  simp only [mem_preimage, mem_cylinder]
  have : s.restrict (flipAt e ω) = s.restrict ω := by
    funext c
    simp [Finset.restrict, flipAt, he c.val c.property]
  rw [this]

/-- The ordered pairs `(x, y)` with `{x, y}` a bond of a finite set form a finite set. -/
theorem finite_pairs_mem_bonds (s : Finset (Bond 2)) :
    {e : Vertex 2 × Vertex 2 | ∃ b ∈ s, b.val = s(e.1, e.2)}.Finite := by
  set U : Set (Vertex 2) := ⋃ b ∈ s, {v | v ∈ b.val}
  have hU : U.Finite := by
    refine s.finite_toSet.biUnion fun b _ => ?_
    obtain ⟨x, y, hxy, _⟩ := b.property
    rw [hxy]
    exact (({x, y} : Set (Vertex 2)).toFinite).subset fun v hv => by
      simpa [Sym2.mem_iff] using hv
  refine (hU.prod hU).subset fun e he => ?_
  obtain ⟨b, hb, hbe⟩ := he
  refine ⟨mem_biUnion hb ?_, mem_biUnion hb ?_⟩
  · show e.1 ∈ b.val; rw [hbe]; exact Sym2.mem_mk_left _ _
  · show e.2 ∈ b.val; rw [hbe]; exact Sym2.mem_mk_right _ _

/-- `step:5.7-martingale` (`FlipInfluenceStep`, eq. `event-not-dependent`). -/
theorem flipInfluenceStep (p : unitInterval) : FlipInfluenceStep p := by
  intro hp0 hp1 E hE
  set μ := latticeBondLaw 2 p
  set m := min (ENNReal.ofReal p) (ENNReal.ofReal (1 - p))
  have hm0 : m ≠ 0 :=
    (lt_min (ENNReal.ofReal_pos.mpr hp0) (ENNReal.ofReal_pos.mpr (sub_pos.mpr hp1))).ne'
  have hmtop : m ≠ ∞ := (min_le_left _ _).trans_lt ENNReal.ofReal_lt_top |>.ne
  have hflip : ∀ (e : Sym2 (Vertex 2)) (T : Set (Configuration 2)),
      μ (flipAt e ⁻¹' T) ≤ m⁻¹ * μ T := fun e T =>
    (ENNReal.mul_le_iff_le_inv hm0 hmtop).mp (min_mul_measure_preimage_flipAt_le p e T)
  obtain ⟨E', -, hE'm, hE'E⟩ := hE.exists_measurable_superset_ae_eq
  have hEE' : μ (E ∆ E') = 0 := measure_symmDiff_eq_zero_iff.mpr hE'E.symm
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  set K := 1 + m⁻¹
  have hKtop : K ≠ ∞ := ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, ENNReal.inv_ne_top.mpr hm0⟩
  have hδ : 0 < ε / K := ENNReal.div_pos_iff.mpr ⟨hε.ne', hKtop⟩
  obtain ⟨C, hC, hCE⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing (μ := μ)
    isSetRing_measurableCylinders
    ⟨{univ}, countable_singleton _, by simpa using univ_mem_measurableCylinders (fun _ : Bond 2 => Bool), by simp⟩
    generateFrom_measurableCylinders.symm hE'm hδ
  obtain ⟨s, S, -, rfl⟩ := (mem_measurableCylinders _).mp hC
  have hEC : μ (E ∆ cylinder s S) ≤ ε / K := by
    calc μ (E ∆ cylinder s S) ≤ μ (E ∆ E') + μ (E' ∆ cylinder s S) := measure_symmDiff_le _ _ _
      _ ≤ ε / K := by rw [hEE', zero_add, symmDiff_comm]; exact hCE.le
  rw [eventually_cofinite]
  refine (finite_pairs_mem_bonds s).subset fun e he => ?_
  by_contra hne
  refine he ?_
  have hinv : flipAt s(e.1, e.2) ⁻¹' cylinder s S = cylinder s S :=
    preimage_flipAt_cylinder fun b hb hbe => hne ⟨b, hb, hbe⟩
  calc μ (E ∆ (flipAt s(e.1, e.2) ⁻¹' E))
      ≤ μ (E ∆ cylinder s S) + μ (cylinder s S ∆ (flipAt s(e.1, e.2) ⁻¹' E)) :=
        measure_symmDiff_le _ _ _
    _ = μ (E ∆ cylinder s S) + μ (flipAt s(e.1, e.2) ⁻¹' (cylinder s S ∆ E)) := by
        rw [preimage_symmDiff, hinv]
    _ ≤ ε / K + m⁻¹ * (ε / K) := by
        gcongr
        refine (hflip _ _).trans ?_
        rw [symmDiff_comm]
        gcongr
    _ = K * (ε / K) := by rw [add_mul, one_mul]
    _ ≤ ε := ENNReal.mul_div_le

end Rigidity.Proofs.Section5
