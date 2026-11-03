import Rigidity.Proofs.S4.OuterNonConstant.Steps
import Rigidity.Proofs.S4.GadgetEvent
import Rigidity.Proofs.S3.SublinearLiouville

/-!
# Lemma 4.8, conditional form, in every dimension `d ≥ 2`

`nonConstantOnGadget` proves the printed statement of Lemma 4.8, the draft statement
`Rigidity.Section4.NonConstantOnGadgetStmt` (Lemma 4.8 as printed):
for a deterministic slope `q ≠ 0` and every large
`R` there is a deterministic bond set `H` of `Q_R`, containing the gadget of height `R` as an
induced subgraph, with `P[𝒞_∞ ∩ Q_R = H] > 0` and
`P[ℓ_q not constant on the gadget | 𝒞_∞ ∩ Q_R = H] ≥ c R^{-2d+2}`.

The printed proof (L1417) only bounds the joint probability, for an `H` depending on the
random placement. The route here (definitions in `OuterNonConstant/Defs.lean`):

1. **Averaging over `H`** (`exists_conditional_ge`, `OuterNonConstant/Reset.lean`). Reset a finite
   set `D` of bonds of `Q_R`, fixed by every event `A_H` that occurs after the reset. Then
   `P[G | A_H] ≥ P[reset⁻¹ G]` for some `H`: the events `A_H` are disjoint and contained in
   `{ω_D = π}`, and the conditional probabilities average to at most their maximum. `H` is not
   chosen in advance, so the skeleton bonds of `Q_R` can stay random. This removes the obstruction
   of the fixed-`H` route (`Rigidity.Proofs.S4.Conditioning.OuterNonConstantStep`, which is not
   needed).
2. **The comparison step** (`compare_faces`, `OuterNonConstant/Steps.lean`). In `ρ₀`
   (`compareEnv`) the bonds between face sites and the connector bonds are open, and the other bonds
   of `Q_R` with no skeleton endpoint are closed. Its corrected plane is not constant on the face
   sites when the connector bonds of `ω` are open and `ℓ_q(ω)` takes two values on `Q_{R-1}`: else
   the function equal to `ℓ₀` off `Q_R` and constant on the face sites and `Q_{R-1}` is a corrected
   plane of `ω` (`exists_const_of_compare`, `OuterNonConstant/Compare.lean`). The bonds where `ω`
   and `ρ₀` differ all have a face endpoint or lie in `Q_{R-1}`. The connector event has
   probability at least `min(p, 1-p)^{8d²}`. Since it is measurable it splits every set additively,
   so the comparison holds with probability at least `min(p, 1-p)^{8d²}/2` for large `R`
   (`measure_inter_add_diff`; no measurability of the corrector events is needed).
3. **Union bound** over the face sites `w ≠ z₀` separated from `z₀ = (1, -R, 0, …)`: at most
   `|Q_R| ≤ (3R)^d` of them.
4. **Attachment** (`attach_gadget_nonconstant`, `OuterNonConstant/Envs.lean`): the gadget joined to
   `w` and `z₀` by the paths of `OuterNonConstant/Geometry.lean` is not constant (Liouville
   argument), and the reset is compatible with `A_H` (`attach_compat`).

Hypotheses: `p_c(d) < p < 1`, `ArmstrongDarioOrderZero` (Theorem 2.4 at order zero: uniqueness of
the infinite cluster, Liouville) and `SupercriticalBondCorrectorInput` (corrected planes).
-/

namespace Rigidity.Proofs.S4.OuterNonConstant

open MeasureTheory ProbabilityTheory Filter Topology LatticeProb LatticeProb.Percolation
  LatticeProb.Network LatticeProb.Network.OpenLadder.Embedding Rigidity.Section4
  Rigidity.Steps.S4

variable {d : ℕ}

/-- The bonds of `Q_R` with no skeleton endpoint are finitely many. -/
theorem finite_coreBonds (R : ℕ) : (coreBonds d R).Finite :=
  (finite_innerBonds d R).subset fun _ he => mem_cube_of_mem_coreBonds he

/-- The cube `Q_R` has at most `(2R + 1)^d` sites. -/
theorem ncard_cube_le (R : ℕ) : (cube d R).ncard ≤ (2 * R + 1) ^ d := by
  classical
  let T := Fintype.piFinset fun _ : Fin d => Finset.Icc (-(R : ℤ)) R
  have hsub : cube d R ⊆ ↑T := fun x hx => by
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    exact abs_le.mp (hx i)
  calc (cube d R).ncard ≤ (↑T : Set (Vertex d)).ncard := Set.ncard_le_ncard hsub T.finite_toSet
    _ = T.card := Set.ncard_coe_finset T
    _ = (2 * R + 1) ^ d := by
      rw [Fintype.card_piFinset]
      simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      congr 1
      omega

/-- `P[E_R]`, second property, tends to `1` (the argument of `eventStep`). -/
theorem tendsto_twoValued [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hAD : LatticeProb.External.ArmstrongDarioOrderZero)
    (hcorr : LatticeProb.External.SupercriticalBondCorrectorInput) :
    Tendsto (fun R => (latticeBondLaw d p (twoValuedEvent d R)).toReal) atTop (𝓝 1) := by
  set μ := latticeBondLaw d p
  have hae : ∀ᵐ ω ∂μ, ω ∈ ⋃ R, twoValuedEvent d R := by
    obtain ⟨_, _, _, _, _, _, X, _, _, _, _, hAD'⟩ := hAD d hd p hpc hp1
    filter_upwards [hAD', hcorr d hd p hpc hp1] with ω hω hcω
    obtain ⟨h, -⟩ := hω
    obtain ⟨hplanes, hslope⟩ := hcω h
    obtain ⟨o, ho⟩ := (uniqueInfiniteComponent_infinite h).nonempty
    haveI := finiteDimensional_harmonicGrowthSpace_one _ ⟨o, ho⟩ (fun q => hplanes q _)
      (fun u hu => (hslope u hu).exists)
    obtain ⟨R₀, hR₀⟩ := exists_radius_twoValued (uniqueInfiniteComponent h)
    exact Set.mem_iUnion.mpr ⟨R₀, h, hR₀⟩
  have hU1 : μ (⋃ R, twoValuedEvent d R) = 1 := by
    rw [measure_congr (ae_eq_univ.mpr (ae_iff.mp hae)), measure_univ]
  have h := tendsto_measure_iUnion_atTop (μ := μ) twoValuedEvent_mono
  rw [hU1] at h
  have h' := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp h
  rw [ENNReal.toReal_one] at h'
  exact h'

/-- **The bound at a fixed radius.** If the comparison event (connector bonds open, `ℓ_q`
two-valued on `Q_{R-1}`) has probability at least `c₀ > 0`, some placement `H` has
`P[G | A_H] ≥ c₀ / #(face sites)`. -/
theorem outer_bound [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hAD : LatticeProb.External.ArmstrongDarioOrderZero)
    (hcorr : LatticeProb.External.SupercriticalBondCorrectorInput) {q : Fin d → ℝ} (hq : q ≠ 0)
    {R : ℕ} (hR : 10 ≤ R) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hX : c₀ ≤ (latticeBondLaw d p (twoValuedEvent d (R - 1) ∩
      resetEvent (connectorBonds d R) fun _ => true)).toReal) :
    ∃ H, IsGadgetPlacement hd R H (gadgetShift d R) ∧
      0 < latticeBondLaw d p (conditioningEvent d R H) ∧
      c₀ / ((faceSites d R).ncard : ℝ) ≤
        (latticeBondLaw d p (conditioningEvent d R H ∩
            gadgetNonconstantEvent hd q R (gadgetShift d R)) /
          latticeBondLaw d p (conditioningEvent d R H)).toReal := by
  classical
  have hp0 : 0 < (p : ℝ) := (criticalProbability_nonneg d).trans_lt hpc
  set μ := latticeBondLaw d p with hμ
  set G := gadgetNonconstantEvent hd q R (gadgetShift d R) with hG
  set X := twoValuedEvent d (R - 1) ∩ resetEvent (connectorBonds d R) fun _ => true with hXdef
  have hD₀ : (coreBonds d R ∪ connectorBonds d R).Finite :=
    (finite_coreBonds R).union finite_connectorBonds
  -- almost sure properties of `ω`, `ρ₀`
  have hU : ∀ᵐ ω ∂μ, HasUniqueInfiniteOpenComponent ω := by
    obtain ⟨_, _, _, _, _, _, X, _, _, _, _, hae⟩ := hAD d hd p hpc hp1
    filter_upwards [hae] with ω hω
    exact hω.1
  have hCo := hcorr d hd p hpc hp1
  have hL := Rigidity.Proofs.S3.sublinearLiouvilleStep hd p hpc hp1 hAD
  let π₀ : Bond d → Bool := fun e => decide (e ∈ faceBonds d R ∨ e ∈ connectorBonds d R)
  have hU₀ := ae_resetConfig hp0 hp1 hD₀ π₀ hU
  have hC₀ := ae_resetConfig hp0 hp1 hD₀ π₀ hCo
  have hL₀ := ae_resetConfig hp0 hp1 hD₀ π₀ hL
  -- the events `U_w`
  let U : Vertex d → Set (Configuration d) := fun w =>
    {ω | ∃ h₀ : HasUniqueInfiniteOpenComponent (compareEnv d R ω),
      ∃ hface : faceSites d R ⊆ (uniqueInfiniteComponent h₀).supp,
        ∃ ℓ₀, IsCorrectedPlane (uniqueInfiniteComponent h₀) q ℓ₀ ∧
          ∃ hw : w ∈ faceSites d R,
            ℓ₀ ⟨w, hface hw⟩ ≠ ℓ₀ ⟨refSite d R, hface (refSite_mem hd hR)⟩}
  have hFfin : (faceSites d R \ {refSite d R}).Finite := finite_faceSites.subset Set.sdiff_subset
  set Fs := hFfin.toFinset with hFs
  have hXU : ∀ᵐ ω ∂μ, ω ∈ X → ω ∈ ⋃ w ∈ Fs, U w := by
    filter_upwards [hCo, hL, hU₀, hC₀] with ω hcω hLω hU₀ω hC₀ω
    rintro ⟨⟨h, hA1⟩, hK⟩
    obtain ⟨hplanes, hslope⟩ := hcω h
    obtain ⟨o, ho⟩ := (uniqueInfiniteComponent_infinite h).nonempty
    obtain ⟨ℓ, ⟨hℓ, -⟩, -⟩ := hplanes q ⟨o, ho⟩
    have hnc : ∃ x y, ℓ x ≠ ℓ y := by
      by_contra hcon
      push Not at hcon
      have hconst : ℓ = fun _ => ℓ ⟨o, ho⟩ := funext fun x => hcon x _
      obtain ⟨q₀, -, hq₀⟩ := hslope ℓ hℓ.1
      have e2 : IsCorrectedPlane (uniqueInfiniteComponent h) 0 ℓ := by
        rw [hconst]
        exact isCorrectedPlane_const _ _
      exact hq ((hq₀ q hℓ).trans (hq₀ 0 e2).symm)
    have htwo := hA1 ℓ hℓ.1 hnc
    have h₀ : HasUniqueInfiniteOpenComponent (compareEnv d R ω) := hU₀ω
    obtain ⟨hplanes₀, -⟩ := hC₀ω h₀
    obtain ⟨o₀, ho₀⟩ := (uniqueInfiniteComponent_infinite h₀).nonempty
    obtain ⟨ℓ₀, ⟨hℓ₀, -⟩, -⟩ := hplanes₀ q ⟨o₀, ho₀⟩
    obtain ⟨hface, w, hw, hw0, hne⟩ := compare_faces hd hR (fun e he => hK e he)
      (uniqueInfiniteComponent h) (uniqueInfiniteComponent_infinite h) (hLω h) ℓ hℓ htwo
      (uniqueInfiniteComponent h₀) (uniqueInfiniteComponent_infinite h₀)
      (fun D hD => (eq_uniqueInfiniteComponent_iff h₀ D).mpr hD) ℓ₀ hℓ₀
    refine Set.mem_biUnion (x := w) ?_ ⟨h₀, hface, ℓ₀, hℓ₀, hw, hne⟩
    simp only [hFs, Finset.mem_coe, Set.Finite.mem_toFinset]
    exact ⟨hw, hw0⟩
  have hμX : μ X ≤ ∑ w ∈ Fs, μ (U w) :=
    (measure_mono_ae hXU).trans (measure_biUnion_finset_le Fs U)
  have hXr : c₀ ≤ ∑ w ∈ Fs, (μ (U w)).toReal := by
    rw [← ENNReal.toReal_sum fun w _ => measure_ne_top _ _]
    exact hX.trans (ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr fun w _ => measure_ne_top _ _)
      hμX)
  have hFne : Fs.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.sum_empty] at hXr
    linarith
  obtain ⟨w, hwF, hwb⟩ : ∃ w ∈ Fs, c₀ / (Fs.card : ℝ) ≤ (μ (U w)).toReal := by
    by_contra hcon
    push Not at hcon
    have hlt := Finset.sum_lt_sum_of_nonempty hFne hcon
    rw [Finset.sum_const, nsmul_eq_mul, mul_div_cancel₀ _ (by exact_mod_cast hFne.card_pos.ne')]
      at hlt
    linarith
  rw [hFs, Set.Finite.mem_toFinset] at hwF
  obtain ⟨hw, hw0⟩ := hwF
  have hw0' : w ≠ refSite d R := hw0
  -- the attachment at `w`
  have hD : (attachResetBonds hd R w).Finite := hD₀.subset (attachResetBonds_subset hd)
  have hU' := ae_resetConfig hp0 hp1 hD (attachPattern hd R w) hU
  have hC' := ae_resetConfig hp0 hp1 hD (attachPattern hd R w) hCo
  have hUG : ∀ᵐ ω ∂μ, ω ∈ U w → attachEnv hd R w ω ∈ G := by
    filter_upwards [hL₀, hU', hC'] with ω hL₀ω hU'ω hC'ω
    rintro ⟨h₀, hface, ℓ₀, hℓ₀, hw', hne⟩
    have h' : HasUniqueInfiniteOpenComponent (attachEnv hd R w ω) := hU'ω
    obtain ⟨hplanes', -⟩ := hC'ω h'
    obtain ⟨o', ho'⟩ := (uniqueInfiniteComponent_infinite h').nonempty
    obtain ⟨u, ⟨hu, -⟩, -⟩ := hplanes' q ⟨o', ho'⟩
    exact ⟨h', u, hu, attach_gadget_nonconstant hd hR hw hw0' (uniqueInfiniteComponent h₀)
      (uniqueInfiniteComponent_infinite h₀) hface ℓ₀ hℓ₀ hne (hL₀ω h₀)
      (uniqueInfiniteComponent h')
      (supp_subset_of_adj_le (fun _ _ hh => openGraph_compareEnv_le hd hh) h₀ h') u hu⟩
  have hμG : μ (U w) ≤ μ (attachEnv hd R w ⁻¹' G) := measure_mono_ae hUG
  have hcard : 0 < (Fs.card : ℝ) := by exact_mod_cast hFne.card_pos
  have hpos : 0 < μ (resetConfig (attachResetBonds hd R w) (attachPattern hd R w) ⁻¹' G) := by
    refine lt_of_lt_of_le ?_ hμG
    refine ENNReal.toReal_pos_iff.mp (lt_of_lt_of_le (by positivity) hwb) |>.1
  obtain ⟨H, hHpl, hHpos, hHle⟩ := exists_conditional_ge hp0 hp1 R hD (attachPattern hd R w) G
    (fun H => IsGadgetPlacement hd R H (gadgetShift d R))
    (fun ω hω => attach_compat hd hR hw hw0' ω hω) hpos
  refine ⟨H, hHpl, hHpos, ?_⟩
  have hratio : μ (conditioningEvent d R H ∩ G) / μ (conditioningEvent d R H) ≤ 1 :=
    ENNReal.div_le_of_le_mul (by rw [one_mul]; exact measure_mono Set.inter_subset_left)
  have hreal : (μ (attachEnv hd R w ⁻¹' G)).toReal ≤
      (μ (conditioningEvent d R H ∩ G) / μ (conditioningEvent d R H)).toReal :=
    ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top hratio) hHle
  have hFcard : (Fs.card : ℝ) ≤ (faceSites d R).ncard := by
    rw [hFs, ← Set.ncard_eq_toFinset_card _ hFfin]
    exact_mod_cast Set.ncard_le_ncard Set.sdiff_subset finite_faceSites
  calc c₀ / ((faceSites d R).ncard : ℝ) ≤ c₀ / (Fs.card : ℝ) :=
        div_le_div_of_nonneg_left hc₀.le hcard hFcard
    _ ≤ (μ (U w)).toReal := hwb
    _ ≤ (μ (attachEnv hd R w ⁻¹' G)).toReal := ENNReal.toReal_mono (measure_ne_top _ _) hμG
    _ ≤ _ := hreal

/-- **Lemma 4.8** (`Rigidity.Section4.NonConstantOnGadgetStmt`, the printed conditional form), for
every `d ≥ 2` and `p_c(d) < p < 1`. -/
theorem nonConstantOnGadget [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hAD : LatticeProb.External.ArmstrongDarioOrderZero)
    (hcorr : LatticeProb.External.SupercriticalBondCorrectorInput) :
    NonConstantOnGadgetStmt d hd p := by
  intro q hq
  have hp0 : 0 < (p : ℝ) := (criticalProbability_nonneg d).trans_lt hpc
  set μ := latticeBondLaw d p with hμ
  set m : ℝ := min (p : ℝ) (1 - p) with hm
  have hm0 : 0 < m := lt_min hp0 (by linarith)
  have hm1 : m ≤ 1 := (min_le_left _ _).trans p.2.2
  set c₁ : ℝ := m ^ (8 * d ^ 2) with hc₁
  have hc₁0 : 0 < c₁ := pow_pos hm0 _
  have hK : ∀ R : ℕ, c₁ ≤ (μ (resetEvent (connectorBonds d R) fun _ => true)).toReal := by
    intro R
    have h1 := ofReal_pow_le_measure_resetEvent p (finite_connectorBonds (d := d) (R := R))
      (fun _ => true)
    have h2 : ENNReal.ofReal m ^ (8 * d ^ 2) ≤ ENNReal.ofReal m ^ (connectorBonds d R).ncard :=
      pow_le_pow_right_of_le_one' (ENNReal.ofReal_le_one.mpr hm1) ncard_connectorBonds_le
    have h3 := ENNReal.toReal_mono (measure_ne_top _ _) (h2.trans h1)
    rwa [ENNReal.toReal_pow, ENNReal.toReal_ofReal hm0.le] at h3
  have hlim := tendsto_twoValued hd p hpc hp1 hAD hcorr
  rw [← hμ] at hlim
  obtain ⟨R₁, hR₁⟩ := eventually_atTop.mp
    (hlim.eventually (lt_mem_nhds (show 1 - c₁ / 2 < 1 by linarith)))
  refine ⟨c₁ / 2 / 3 ^ d, by positivity, max 10 (R₁ + 1), fun R hR => ?_⟩
  have hR10 : 10 ≤ R := le_of_max_le_left hR
  have hRR₁ : R₁ ≤ R - 1 := by have := le_of_max_le_right hR; omega
  -- the comparison event has probability at least `c₁ / 2`
  have hX : c₁ / 2 ≤ (μ (twoValuedEvent d (R - 1) ∩
      resetEvent (connectorBonds d R) fun _ => true)).toReal := by
    have hT := hR₁ (R - 1) hRR₁
    have hKR := hK R
    set T := twoValuedEvent d (R - 1)
    set Kv := resetEvent (connectorBonds d R) fun _ => true
    have hKm : MeasurableSet Kv := measurableSet_resetEvent finite_connectorBonds _
    have h1 := measure_inter_add_sdiff (μ := μ) T hKm
    have h2 : μ (T \ Kv) ≤ μ Kvᶜ := measure_mono fun x hx => hx.2
    have h3 : μ Kvᶜ = 1 - μ Kv := prob_compl_eq_one_sub hKm
    have h1r : (μ (T ∩ Kv)).toReal + (μ (T \ Kv)).toReal = (μ T).toReal := by
      rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), h1]
    have h2r : (μ (T \ Kv)).toReal ≤ 1 - (μ Kv).toReal := by
      have := ENNReal.toReal_mono (measure_ne_top _ _) h2
      rwa [h3, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]
        at this
    linarith
  obtain ⟨H, hH, hpos, hbound⟩ :=
    outer_bound hd p hpc hp1 hAD hcorr hq hR10 (by positivity : (0 : ℝ) < c₁ / 2) hX
  refine ⟨H, gadgetShift d R, hH.1, hH.2.1, hH.2.2, hpos, ?_⟩
  refine le_trans ?_ hbound
  -- `#(face sites) ≤ (3R)^d ≤ 3^d R^{2d-2}`
  have hRpos : (0 : ℝ) < R := by exact_mod_cast (show 0 < R by omega)
  have hF0 : 0 < ((faceSites d R).ncard : ℝ) := by
    exact_mod_cast (Set.ncard_pos finite_faceSites).mpr ⟨_, refSite_mem hd hR10⟩
  have hFle : ((faceSites d R).ncard : ℝ) ≤ 3 ^ d * (R : ℝ) ^ (2 * d - 2) := by
    have h1 : (faceSites d R).ncard ≤ (cube d R).ncard :=
      Set.ncard_le_ncard (fun _ hx => mem_cube_of_mem_faceSites hx) (cube_finite d R)
    have h2 := ncard_cube_le (d := d) R
    have hR1' : (1 : ℝ) ≤ R := by exact_mod_cast (show 1 ≤ R by omega)
    have h3 : ((2 * R + 1 : ℕ) : ℝ) ≤ 3 * R := by push_cast; linarith
    have h4 : (R : ℝ) ^ d ≤ (R : ℝ) ^ (2 * d - 2) :=
      pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ R by omega)) (by omega)
    calc ((faceSites d R).ncard : ℝ) ≤ ((2 * R + 1 : ℕ) : ℝ) ^ d := by
          exact_mod_cast h1.trans h2
      _ ≤ (3 * R) ^ d := pow_le_pow_left₀ (by positivity) h3 d
      _ = 3 ^ d * (R : ℝ) ^ d := mul_pow _ _ _
      _ ≤ 3 ^ d * (R : ℝ) ^ (2 * d - 2) := by gcongr
  rw [zpow_neg_two_mul_add_two hd, ← div_eq_mul_inv, div_div]
  exact div_le_div_of_nonneg_left (by positivity) hF0 hFle

end Rigidity.Proofs.S4.OuterNonConstant
