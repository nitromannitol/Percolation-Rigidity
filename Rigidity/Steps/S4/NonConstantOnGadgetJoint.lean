import Rigidity.Steps.S4.NonConstantOnGadget

/-!
# Lemma 4.8, joint form

The proof of Lemma 4.8 (paper L1398-1418 of the corrected draft) bounds from below the probability
of an attachment event `W` of the bonds away from `Q_R`; what it gives is the joint lower bound
`P[𝒞_∞ ∩ Q_R = H, ℓ_q not constant on the gadget] ≥ c R^{-2d+2} min(p, 1-p)^{#bonds meeting Q_R}`,
which is the form used in the proof of Lemma 4.7. The draft statement
`Rigidity.Section4.NonConstantOnGadgetStmt` is Lemma 4.8 as printed (the conditional form), proved
by averaging over `H` in `Rigidity.Proofs.S4.OuterNonConstant`; from the steps below it would need
in addition the comparison `ConditioningStep`, which the paper does not prove (see
`Rigidity/Steps/S4/NonConstantOnGadget.lean`). This file states the joint form with the gadget
isolated in `H` (inside `Q_{R-1}`, attached at its terminals only, `IsIsolatedGadget`),
`NonConstantOnGadgetJointStmt` (exponent `#bondsNear`, and `P[𝒞_∞ ∩ Q_R = H] > 0`), a proved
support result, and proves it from the steps of Lemma 4.8 and the finite energy step below, which
replaces `ConditioningStep`.

* `FiniteEnergyStep` (`finiteEnergyStep`, proved): fixing the bonds meeting `Q_R` to a prescribed
  configuration costs at most a factor `min(p, 1-p)^{#bonds meeting Q_R}`: on the cylinder event
  where the bonds meeting `Q_R` are open exactly on `F`, the environment equals `attachConfig R F ω`,
  and the cylinder event is independent of the bonds away from `Q_R`.

The exponent counts the bonds with an endpoint in `Q_R` (`bondsNear`), not only the bonds with both
endpoints in `Q_R`: the attachment also fixes the bonds from `∂Q_R` to the outside (all closed but
`x x̃` and `y ỹ`).
-/

namespace Rigidity.Steps.S4

open MeasureTheory ProbabilityTheory LatticeProb.Percolation LatticeProb.Network Rigidity.Section4

variable {d : ℕ}

/-- **Lemma 4.8, joint form** (auxiliary result, what the proof of Lemma 4.8 gives and the proof
of Lemma 4.7 uses): for a deterministic slope `q ≠ 0` there are `c > 0` and `R₀` such that for
`R ≥ R₀` some bond set `H` of `Q_R` contains a translate by `τ` of the gadget of height `R` as an
induced subgraph, with
`P[𝒞_∞ ∩ Q_R = H, ℓ_q not constant on the gadget] ≥ c R^{-2d+2} min(p, 1-p)^{#bonds meeting Q_R}`,
and `P[𝒞_∞ ∩ Q_R = H] > 0`. The gadget is isolated in `H` (`IsIsolatedGadget`: inside `Q_{R-1}`,
every bond of `H` at a non-terminal gadget site joins two gadget sites). The events are those of
`Rigidity.Section4.NonConstantOnGadgetStmt`; the exponent `#bondsNear` counts the bonds with an
endpoint in `Q_R`. -/
def NonConstantOnGadgetJointStmt (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval) : Prop :=
  ∀ q : Fin d → ℝ, q ≠ 0 → ∃ c : ℝ, 0 < c ∧ ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
    ∃ (H : Set (Bond d)) (τ : Vertex d),
      (∀ e ∈ H, ∀ z ∈ (e : Sym2 (Vertex d)), z ∈ cube d R) ∧
      (∀ x ∈ OpenLadder.Embedding.ambientSites hd (R : ℤ), τ + x ∈ cube d (R - 1)) ∧
      (∀ x (hx : x ∈ OpenLadder.Embedding.ambientSites hd (R : ℤ))
          y (hy : y ∈ OpenLadder.Embedding.ambientSites hd (R : ℤ))
          (hxy : (nearestNeighborGraph d).Adj (τ + x) (τ + y)),
        bondOfAdjacent hxy ∈ H ↔
          (OpenLadder.Embedding.ambientGraph hd (R : ℤ)).Adj ⟨x, hx⟩ ⟨y, hy⟩) ∧
      (∀ e ∈ H, ∀ x ∈ OpenLadder.Embedding.ambientSites hd (R : ℤ),
        x ≠ OpenLadder.Embedding.zeroPad d (1, 1) → x ≠ OpenLadder.Embedding.zeroPad d (4, 1) →
        τ + x ∈ (e : Sym2 (Vertex d)) → ∀ z ∈ (e : Sym2 (Vertex d)),
          ∃ y ∈ OpenLadder.Embedding.ambientSites hd (R : ℤ), z = τ + y) ∧
      0 < latticeBondLaw d p {ω | ∃ h : HasUniqueInfiniteOpenComponent ω,
        componentBondsIn (uniqueInfiniteComponent h) (cube d R) = H} ∧
      c * (R : ℝ) ^ (-(2 * (d : ℤ)) + 2) * min (p : ℝ) (1 - p) ^ (bondsNear d R).ncard ≤
        (latticeBondLaw d p ({ω | ∃ h : HasUniqueInfiniteOpenComponent ω,
            componentBondsIn (uniqueInfiniteComponent h) (cube d R) = H} ∩
          {ω | ∃ h : HasUniqueInfiniteOpenComponent ω,
            ∃ u, IsCorrectedPlane (uniqueInfiniteComponent h) q u ∧
              ∃ x ∈ OpenLadder.Embedding.ambientSites hd (R : ℤ),
              ∃ y ∈ OpenLadder.Embedding.ambientSites hd (R : ℤ),
              ∃ hx : τ + x ∈ (uniqueInfiniteComponent h).supp,
              ∃ hy : τ + y ∈ (uniqueInfiniteComponent h).supp,
                u ⟨τ + x, hx⟩ ≠ u ⟨τ + y, hy⟩})).toReal

/-- Finite energy step: for every event `S`, fixing the bonds meeting `Q_R` to be open exactly on
`F` changes the probability by a factor at least `min(p, 1-p)^{#bonds meeting Q_R}`. -/
def FiniteEnergyStep (d : ℕ) (p : unitInterval) : Prop :=
  ∀ (R : ℕ) (F : Set (Bond d)) (S : Set (Configuration d)),
    min (p : ℝ) (1 - p) ^ (bondsNear d R).ncard *
        (latticeBondLaw d p (attachConfig R F ⁻¹' S)).toReal ≤
      (latticeBondLaw d p S).toReal

/-- **Lemma 4.8, joint form**, from the steps of Lemma 4.8 and the finite energy step, for a
construction `H, τ` of the attached gadget: the union bound gives a pair of boundary placements
whose attachment event `W` has `P[W] ≥ (2 C² R^{2d-2})⁻¹`, and finite energy gives
`P[𝒞_∞ ∩ Q_R = H, ℓ_q not constant on the gadget] ≥ min(p, 1-p)^{#bonds meeting Q_R} P[W]`. -/
theorem nonConstantOnGadgetJoint_of_steps [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (H : ℕ → Vertex d → Vertex d → Set (Bond d)) (τ : ℕ → Vertex d)
    (hevent : EventStep d p) (hclosed : ∀ q : Fin d → ℝ, q ≠ 0 → ClosedBoundaryStep d p q)
    (hgeom : AttachGeometryStep hd H τ)
    (hattach : ∀ q : Fin d → ℝ, q ≠ 0 → AttachStep hd p q H τ)
    (hcount : PlacementCountStep d) (henergy : FiniteEnergyStep d p) :
    NonConstantOnGadgetJointStmt d hd p := by
  intro q hq
  obtain ⟨R₁, hR₁⟩ := hevent
  obtain ⟨R₂, hR₂⟩ := hgeom
  obtain ⟨R₃, hR₃⟩ := hattach q hq
  obtain ⟨C, hC, hCR⟩ := hcount
  refine ⟨1 / (2 * C ^ 2), by positivity, max (max R₁ R₂) (max R₃ 1), fun R hR => ?_⟩
  simp only [max_le_iff] at hR
  obtain ⟨⟨h1, h2⟩, h3, h5⟩ := hR
  obtain ⟨hfin, hcard⟩ := hCR R h5
  set μ := latticeBondLaw d p with hμ
  -- the finite set of placements, and the union bound
  obtain ⟨s, hs⟩ : ∃ s : Finset ((Vertex d × Vertex d) × (Vertex d × Vertex d)),
      s = ((hfin.prod hfin).toFinset).filter (fun i => i.1.1 ≠ i.2.1) := ⟨_, rfl⟩
  let W : (Vertex d × Vertex d) × (Vertex d × Vertex d) → Set (Configuration d) :=
    fun i => attachEvent hd q H τ R i.1.1 i.1.2 i.2.1 i.2.2
  have hsub : ∀ᵐ ω ∂μ, ω ∈ goodCubeEvent d R → ω ∈ ⋃ i ∈ s, W i := by
    filter_upwards [hclosed q hq R, hR₃ R h3] with ω hω hω' hE
    obtain ⟨x, x', y, y', hx, hy, hxy, hwit⟩ := hω hE
    refine Set.mem_iUnion₂.mpr ⟨((x, x'), (y, y')), ?_, hω' x x' y y' hx hy hxy hwit⟩
    rw [hs, Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨Set.mk_mem_prod hx hy, hxy⟩
  have hhalf : (1 / 2 : ℝ) ≤ ∑ i ∈ s, (μ (W i)).toReal :=
    calc (1 / 2 : ℝ) ≤ (μ (goodCubeEvent d R)).toReal := hR₁ R h1
      _ ≤ (μ (⋃ i ∈ s, W i)).toReal :=
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae (hsub.mono fun _ h => h))
      _ ≤ ∑ i ∈ s, (μ (W i)).toReal := measureReal_biUnion_finset_le s W
  have hsne : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro hempty
    rw [hempty, Finset.sum_empty] at hhalf
    norm_num at hhalf
  obtain ⟨⟨⟨x, x'⟩, ⟨y, y'⟩⟩, his, himax⟩ :=
    Finset.exists_max_image s (fun i => (μ (W i)).toReal) hsne
  have hW : (1 / 2 : ℝ) ≤ s.card * (μ (W ((x, x'), (y, y')))).toReal := by
    have := Finset.sum_le_card_nsmul s (fun i => (μ (W i)).toReal) _ himax
    rw [nsmul_eq_mul] at this
    exact hhalf.trans this
  have hcard_s : (s.card : ℝ) ≤ C ^ 2 * (R : ℝ) ^ (2 * d - 2) := by
    have hle : s.card ≤ hfin.toFinset.card * hfin.toFinset.card := by
      calc s.card ≤ (hfin.prod hfin).toFinset.card := hs ▸ Finset.card_filter_le _ _
        _ = hfin.toFinset.card * hfin.toFinset.card := by
          rw [← Set.Finite.toFinset_prod, Finset.card_product]
    have hC' : (hfin.toFinset.card : ℝ) ≤ C * (R : ℝ) ^ (d - 1) := by
      rwa [← Set.ncard_eq_toFinset_card _ hfin]
    have hpow : (R : ℝ) ^ (2 * d - 2) = ((R : ℝ) ^ (d - 1)) ^ 2 := by
      rw [← pow_mul]
      congr 1
      omega
    calc (s.card : ℝ) ≤ (hfin.toFinset.card : ℝ) * hfin.toFinset.card := by exact_mod_cast hle
      _ ≤ (C * (R : ℝ) ^ (d - 1)) * (C * (R : ℝ) ^ (d - 1)) :=
        mul_le_mul hC' hC' (by positivity) (by positivity)
      _ = C ^ 2 * (R : ℝ) ^ (2 * d - 2) := by rw [hpow]; ring
  rw [hs, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_prod] at his
  obtain ⟨⟨hx, hy⟩, hxy⟩ := his
  obtain ⟨⟨hHQ, -, hind⟩, hτQ, hiso⟩ := hR₂ R h2 x x' y y' hx hy hxy
  have hR0 : (0 : ℝ) < (R : ℝ) ^ (2 * d - 2) := by
    have : (1 : ℝ) ≤ R := by exact_mod_cast h5
    positivity
  have hWnn : 0 ≤ (μ (W ((x, x'), (y, y')))).toReal := ENNReal.toReal_nonneg
  have hkey : 1 ≤ 2 * C ^ 2 * (R : ℝ) ^ (2 * d - 2) * (μ (W ((x, x'), (y, y')))).toReal := by
    nlinarith
  -- finite energy: the attachment event is the preimage of the joint event under `attachConfig`
  set m := min (p : ℝ) (1 - p) ^ (bondsNear d R).ncard with hm_def
  have hm : 0 < m :=
    pow_pos (lt_min ((criticalProbability_nonneg d).trans_lt hpc) (sub_pos.2 hp1)) _
  have hjoint : m * (μ (W ((x, x'), (y, y')))).toReal ≤
      (μ (conditioningEvent d R (H R x y) ∩ gadgetNonconstantEvent hd q R (τ R))).toReal :=
    henergy R (attachBonds (H R x y) x x' y y') _
  have hWpos : 0 < (μ (W ((x, x'), (y, y')))).toReal := by
    by_contra hneg
    have h0 : (μ (W ((x, x'), (y, y')))).toReal = 0 :=
      le_antisymm (not_lt.mp hneg) ENNReal.toReal_nonneg
    rw [h0, mul_zero] at hkey
    norm_num at hkey
  have hApos : 0 < μ (conditioningEvent d R (H R x y)) :=
    (ENNReal.toReal_pos_iff.1 ((mul_pos hm hWpos).trans_le hjoint)).1.trans_le
      (measure_mono Set.inter_subset_left)
  refine ⟨H R x y, τ R, hHQ, hτQ, hind, hiso, hApos, ?_⟩
  calc 1 / (2 * C ^ 2) * (R : ℝ) ^ (-(2 * (d : ℤ)) + 2) * m
      = m / (2 * C ^ 2 * (R : ℝ) ^ (2 * d - 2)) := by
        rw [zpow_neg_two_mul_add_two hd]
        field_simp
    _ ≤ m * (μ (W ((x, x'), (y, y')))).toReal := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_left hkey hm.le]
    _ ≤ _ := hjoint

/-- The bonds meeting `Q_R` are finitely many: their endpoints lie in `Q_{R+1}`. -/
theorem finite_bondsNear (d R : ℕ) : (bondsNear d R).Finite := by
  have hcube : (cube d (R + 1)).Finite := by
    refine (Set.finite_Icc (fun _ => -((R + 1 : ℕ) : ℤ)) (fun _ => ((R + 1 : ℕ) : ℤ))).subset
      fun y hy => ?_
    exact ⟨fun i => (abs_le.mp (hy i)).1, fun i => (abs_le.mp (hy i)).2⟩
  refine (hcube.toFinset.sym2.finite_toSet.preimage Subtype.val_injective.injOn).subset
    fun e he => ?_
  simp only [Set.mem_preimage, Finset.mem_coe, Finset.mem_sym2_iff, Set.Finite.mem_toFinset]
  obtain ⟨z, hz, hzR⟩ := he
  obtain ⟨x, y, hexy, hsum⟩ := e.2
  rw [hexy, Sym2.mem_iff] at hz
  intro w hw
  rw [hexy, Sym2.mem_iff] at hw
  simp only [cube, Set.mem_setOf_eq] at hzR ⊢
  intro i
  have hi : |x i - y i| ≤ 1 :=
    hsum ▸ Finset.single_le_sum (f := fun j => |x j - y j|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ i)
  have hzi := hzR i
  rw [abs_le] at hi hzi ⊢
  push_cast
  rcases hz with rfl | rfl <;> rcases hw with rfl | rfl <;> constructor <;> linarith

open scoped Classical in
/-- **Finite energy step** (proved): on the cylinder event `B` where the bonds meeting `Q_R` are
open exactly on `F`, `attachConfig R F ω = ω`, so `B ∩ attachConfig R F ⁻¹' S ⊆ S`; the event `B`
is determined by the bonds meeting `Q_R` and `attachConfig R F ⁻¹' S` by the other bonds, so they
are independent, and `P[B] ≥ min(p, 1-p)^{#bonds meeting Q_R}`. A nonmeasurable `S` is replaced by
a measurable hull. -/
theorem finiteEnergyStep (p : unitInterval) : FiniteEnergyStep d p := by
  intro R F S
  set μ := latticeBondLaw d p with hμ
  set m := min (p : ℝ) (1 - p) with hm_def
  have hm0 : 0 ≤ m := le_min (unitInterval.nonneg p) (sub_nonneg.2 (unitInterval.le_one p))
  have hfin := finite_bondsNear d R
  -- the σ-algebras of the bonds meeting `Q_R` and of the other bonds are independent
  let mE : Bond d → MeasurableSpace (Configuration d) :=
    fun e => MeasurableSpace.comap (fun ω : Configuration d => ω e) inferInstance
  have hind : Indep (⨆ e ∈ bondsNear d R, mE e) (⨆ e ∈ (bondsNear d R)ᶜ, mE e) μ :=
    indep_iSup_of_disjoint (fun e => (measurable_pi_apply e).comap_le)
      (latticeBondLaw_iIndepFun p).iIndep disjoint_compl_right
  -- the cylinder event of the bonds meeting `Q_R`
  let B : Set (Configuration d) := {ω | ∀ e ∈ bondsNear d R, ω e = decide (e ∈ F)}
  have hB : B = ⋂ e ∈ hfin.toFinset, (fun ω : Configuration d => ω e) ⁻¹' {decide (e ∈ F)} := by
    ext ω
    simp [B]
  have hBmeas : MeasurableSet[⨆ e ∈ bondsNear d R, mE e] B := by
    rw [hB]
    refine MeasurableSet.biInter (hfin.toFinset.countable_toSet) fun e he => ?_
    rw [Finset.mem_coe, Set.Finite.mem_toFinset] at he
    exact le_iSup₂ (f := fun e (_ : e ∈ bondsNear d R) => mE e) e he _
      (MeasurableSpace.measurableSet_comap.2 ⟨_, measurableSet_singleton _, rfl⟩)
  have hBlow : ENNReal.ofReal m ^ (bondsNear d R).ncard ≤ μ B := by
    rw [hB, (latticeBondLaw_iIndepFun p).measure_inter_preimage_eq_mul hfin.toFinset
      (fun e _ => measurableSet_singleton _), Set.ncard_eq_toFinset_card _ hfin]
    refine Finset.pow_card_le_prod _ _ _ fun e _ => ?_
    have hopen : MeasurableSet {ω : Configuration d | ω e = true} := by
      have h : MeasurableSet ((fun ω : Configuration d => ω e) ⁻¹' {true}) :=
        measurable_pi_apply e (measurableSet_singleton true)
      exact h
    cases decide (e ∈ F)
    · have hc : {ω : Configuration d | ω e = false} = {ω | ω e = true}ᶜ := by
        ext ω
        simp
      change ENNReal.ofReal m ≤ μ {ω | ω e = false}
      rw [hc, prob_compl_eq_one_sub hopen, hμ, latticeBondLaw_open, ← ENNReal.ofReal_one,
        ← ENNReal.ofReal_sub _ (unitInterval.nonneg p)]
      exact ENNReal.ofReal_le_ofReal (min_le_right _ _)
    · change ENNReal.ofReal m ≤ μ {ω | ω e = true}
      rw [hμ, latticeBondLaw_open]
      exact ENNReal.ofReal_le_ofReal (min_le_left _ _)
  -- `attachConfig R F` only reads the bonds away from `Q_R`
  have hattach : Measurable[⨆ e ∈ (bondsNear d R)ᶜ, mE e] (attachConfig R F) := by
    refine (@measurable_pi_iff _ _ _ (⨆ e ∈ (bondsNear d R)ᶜ, mE e) _ _).2 fun e => ?_
    by_cases he : e ∈ bondsNear d R
    · have : (fun ω => attachConfig R F ω e) = fun _ => decide (e ∈ F) := by
        funext ω
        simp [attachConfig, he]
      rw [this]
      exact measurable_const
    · have : (fun ω => attachConfig R F ω e) = fun ω => ω e := by
        funext ω
        simp [attachConfig, he]
      rw [this]
      exact (comap_measurable (fun ω : Configuration d => ω e)).mono
        (le_iSup₂ (f := fun e (_ : e ∈ (bondsNear d R)ᶜ) => mE e) e he) le_rfl
  have hsub : ∀ T, B ∩ attachConfig R F ⁻¹' T ⊆ T := by
    rintro T ω ⟨hωB, hωT⟩
    have : attachConfig R F ω = ω := by
      funext e
      by_cases he : e ∈ bondsNear d R
      · simp [attachConfig, he, hωB e he]
      · simp [attachConfig, he]
    rwa [Set.mem_preimage, this] at hωT
  have key : ∀ T, MeasurableSet T →
      ENNReal.ofReal (m ^ (bondsNear d R).ncard) * μ (attachConfig R F ⁻¹' T) ≤ μ T := by
    intro T hT
    calc ENNReal.ofReal (m ^ (bondsNear d R).ncard) * μ (attachConfig R F ⁻¹' T)
        ≤ μ B * μ (attachConfig R F ⁻¹' T) := by
          rw [ENNReal.ofReal_pow hm0]
          gcongr
      _ = μ (B ∩ attachConfig R F ⁻¹' T) :=
          ((Indep_iff _ _ μ).1 hind B _ hBmeas (hattach hT)).symm
      _ ≤ μ T := measure_mono (hsub T)
  have hS : ENNReal.ofReal (m ^ (bondsNear d R).ncard) * μ (attachConfig R F ⁻¹' S) ≤ μ S := by
    refine le_trans ?_ ((measure_toMeasurable S).symm ▸
      key (toMeasurable μ S) (measurableSet_toMeasurable μ S))
    gcongr
    exact Set.preimage_mono (subset_toMeasurable μ S)
  have := ENNReal.toReal_mono (measure_ne_top μ S) hS
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hm0 _)] at this

/-- **Lemma 4.8, joint form**, from the steps of Lemma 4.8 other than finite energy. -/
theorem nonConstantOnGadgetJoint_of_attachSteps [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (H : ℕ → Vertex d → Vertex d → Set (Bond d)) (τ : ℕ → Vertex d)
    (hevent : EventStep d p) (hclosed : ∀ q : Fin d → ℝ, q ≠ 0 → ClosedBoundaryStep d p q)
    (hgeom : AttachGeometryStep hd H τ)
    (hattach : ∀ q : Fin d → ℝ, q ≠ 0 → AttachStep hd p q H τ)
    (hcount : PlacementCountStep d) :
    NonConstantOnGadgetJointStmt d hd p :=
  nonConstantOnGadgetJoint_of_steps hd p hpc hp1 H τ hevent hclosed hgeom hattach hcount
    (finiteEnergyStep p)

end Rigidity.Steps.S4
