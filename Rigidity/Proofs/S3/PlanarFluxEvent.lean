import Rigidity.Proofs.S3.PlanarCoefficient

/-!
# Planar corrected-plane flux

The corrected-plane flux estimate follows from planar corrector estimates.
-/

open MeasureTheory Filter Topology LatticeProb LatticeProb.Percolation LatticeProb.External
  Rigidity.Section3 Rigidity.Steps.S3
open scoped BigOperators Classical ENNReal

namespace Rigidity.Proofs.S3

open FluxEvent

/-- The planar flux estimate follows from the planar corrector inputs. -/
theorem fluxEventStep_two (hU : SupercriticalBondUniqueness)
    (hCorr : Rigidity.External.SupercriticalBondCorrectorInputTwo)
    (hQ : Rigidity.External.CorrectorQuantitativeInputTwo)
    (hHom : HomogenizedCoefficientProposedTwo) (p : unitInterval) : FluxEventStep 2 p := by
  let d : ℕ := 2
  change FluxEventStep d p
  intro hd hpc hp1
  set μ := latticeBondLaw d p
  obtain ⟨G, hG, hG1, Φ, hΦm, hex, hΦ⟩ := exists_edgeField_two hU hCorr p hpc hp1
  have hGae : ∀ᵐ ω ∂μ, ω ∈ G := mem_ae_iff.2 ((prob_compl_eq_zero_iff hG).2 hG1)
  have hall : ∀ᵐ ω ∂μ, ∀ z, configurationTranslation z ω ∈ G :=
    ae_all_iff.2 fun z =>
      (measurePreserving_configurationTranslation p z).quasiMeasurePreserving.ae hGae
  obtain ⟨abar, habar, hX⟩ := hHom p hpc hp1
  obtain ⟨hXi, hXm⟩ := hX (Φ (unit 0) 0) (by
    filter_upwards [hGae] with ω hω h u hu
    exact (hΦ ω hω _ (uniqueInfiniteComponent_infinite h) u hu _ _).symm)
  have hYi : ∀ j, j ≠ 0 → Integrable (Φ 0 (unit j)) μ := fun j hj =>
    integrable_sideField_two hQ p hpc hp1 hGae hΦm hex hΦ hj
  have hYm : ∀ j, j ≠ 0 → ∫ ω, Φ 0 (unit j) ω ∂μ = 0 := fun j hj =>
    integral_sideField_eq_zero p hGae hex hΦ hj (hYi j hj)
  refine ⟨abar / 2, half_pos habar, fun ε hε => ?_⟩
  set η : ℝ := ε / (2 * d * 3 ^ d) with hηdef
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hη : 0 < η := by positivity
  let k1 : Fin d := ⟨1, hd⟩
  have hk1 : k1 ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp [k1] at this
  set BL : ℕ → Set (Configuration d) := fun N => {ω | abar / 2 ≤
    |faceAverage (Φ (unit 0) 0) (leftFace d N) (unit 0) ω - ∫ ω', Φ (unit 0) 0 ω' ∂μ|}
  set BU : Fin d → ℕ → Set (Configuration d) := fun j N => {ω | η ≤
    |faceAverage (Φ 0 (unit j)) (upperSide j N) 0 ω - ∫ ω', Φ 0 (unit j) ω' ∂μ|}
  set BD : Fin d → ℕ → Set (Configuration d) := fun j N => {ω | η ≤
    |faceAverage (Φ 0 (unit j)) (lowerSide j N) (unit j) ω - ∫ ω', Φ 0 (unit j) ω' ∂μ|}
  have hL : Tendsto (fun N => μ (BL N)) atTop (𝓝 0) :=
    tendsto_measure_faceAverage p (hΦm _ _) hXi k1 (fun N => leftFace d N) (fun _ => unit 0)
      (fun N => -(N : ℤ)) (fun N => (N : ℤ)) (fun N => show -(N : ℤ) ≤ N by omega)
      (tendsto_atTop_mono (fun N => show N ≤ ((N : ℤ) - -(N : ℤ) + 1).toNat by omega)
        tendsto_id)
      (fun N x => mem_leftFace_iff N hk1 x)
      (fun N => ⟨fun _ => -(N : ℤ),
        Finset.mem_filter.2 ⟨mem_latticeCube.2 fun _ => ⟨le_rfl, by omega⟩, rfl⟩⟩) (half_pos habar)
  have hUp : ∀ j ∈ Finset.univ.erase (0 : Fin d), Tendsto (fun N => μ (BU j N)) atTop (𝓝 0) := by
    intro j hj
    have hj0 := Finset.ne_of_mem_erase hj
    exact tendsto_measure_faceAverage p (hΦm _ _) (hYi j hj0) 0 (fun N => upperSide j N)
      (fun _ => 0) (fun N => -(N : ℤ)) (fun _ => 0) (fun N => show -(N : ℤ) ≤ 0 by omega)
      (tendsto_atTop_mono (fun N => show N ≤ ((0 : ℤ) - -(N : ℤ) + 1).toNat by omega)
        tendsto_id)
      (fun N x => mem_side_iff N hj0 (N : ℤ) x)
      (fun N => ⟨fun i => if i = j then (N : ℤ) else -(N : ℤ),
        Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨mem_latticeCube.2 fun i => by
          split_ifs <;> omega, by simp only [if_neg (Ne.symm hj0)]; omega⟩, if_pos rfl⟩⟩) hη
  have hLow : ∀ j ∈ Finset.univ.erase (0 : Fin d), Tendsto (fun N => μ (BD j N)) atTop (𝓝 0) := by
    intro j hj
    have hj0 := Finset.ne_of_mem_erase hj
    exact tendsto_measure_faceAverage p (hΦm _ _) (hYi j hj0) 0 (fun N => lowerSide j N)
      (fun _ => unit j) (fun N => -(N : ℤ)) (fun _ => 0) (fun N => show -(N : ℤ) ≤ 0 by omega)
      (tendsto_atTop_mono (fun N => show N ≤ ((0 : ℤ) - -(N : ℤ) + 1).toNat by omega)
        tendsto_id)
      (fun N x => mem_side_iff N hj0 (-(N : ℤ)) x)
      (fun N => ⟨fun _ => -(N : ℤ), Finset.mem_filter.2 ⟨Finset.mem_filter.2
        ⟨mem_latticeCube.2 fun _ => ⟨le_rfl, by omega⟩, show -(N : ℤ) ≤ 0 by omega⟩, rfl⟩⟩) hη
  have hnull : μ {ω | ¬ ∀ z, configurationTranslation z ω ∈ G} = 0 := ae_iff.1 hall
  have hsub : ∀ N : ℕ, 1 ≤ N → {ω | ¬ ∃ h : HasUniqueInfiniteOpenComponent ω,
      ∃ u, IsCorrectedPlane (uniqueInfiniteComponent h) (slopeE1 d) u ∧
        abar / 2 * (N : ℝ) ^ ((d : ℝ) - 1) ≤ leftFlux (uniqueInfiniteComponent h) u N ∧
        |sideFlux (uniqueInfiniteComponent h) u N| ≤ ε * (N : ℝ) ^ ((d : ℝ) - 1)} ⊆
      {ω | ¬ ∀ z, configurationTranslation z ω ∈ G} ∪
        (BL N ∪ ⋃ j ∈ Finset.univ.erase (0 : Fin d), (BU j N ∪ BD j N)) := by
    intro N hN ω hbad
    by_contra hgood
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq, not_or, not_exists,
      not_le, not_not, BL, BU, BD] at hgood
    obtain ⟨hω, hLω, hSω⟩ := hgood
    apply hbad
    have hω0 : ω ∈ G := by simpa only [configurationTranslation_zero] using hω 0
    obtain ⟨h, hexu⟩ := hex ω hω0
    have hinf := uniqueInfiniteComponent_infinite h
    obtain ⟨u, hu⟩ := hexu _ hinf
    have key : ∀ x y w, edgeDifference (uniqueInfiniteComponent h) u x y =
        Φ (x - w) (y - w) (configurationTranslation (-w) ω) := by
      intro x y w
      have := edgeDifference_add_eq hΦ hω _ hinf u hu (x - w) (y - w) w
      rwa [sub_add_cancel, sub_add_cancel] at this
    have hpow : (N : ℝ) ^ ((d : ℝ) - 1) = (N : ℝ) ^ (d - 1) := by
      rw [← Real.rpow_natCast, Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hcube : ((2 * N + 1 : ℕ) : ℝ) ^ (d - 1) ≤ 3 ^ (d - 1) * (N : ℝ) ^ (d - 1) := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by push_cast; linarith) _
    refine ⟨h, u, hu, ?_, ?_⟩
    ·
      have hne : (leftFace d N).Nonempty := ⟨fun _ => -(N : ℤ),
        Finset.mem_filter.2 ⟨mem_latticeCube.2 fun _ => ⟨le_rfl, by omega⟩, rfl⟩⟩
      have hsum : leftFlux (uniqueInfiniteComponent h) u N =
          faceAverage (Φ (unit 0) 0) (leftFace d N) (unit 0) ω * (leftFace d N).card := by
        rw [← sum_eq_faceAverage_mul _ hne]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [key x (x - unit 0) (x - unit 0), sub_sub_cancel, sub_self, neg_sub]
      have hcard : ((leftFace d N).card : ℝ) = ((2 * N + 1 : ℕ) : ℝ) ^ (d - 1) := by
        rw [show leftFace d N = (latticeCube d N).filter (fun x => x 0 = -(N : ℤ)) from rfl,
          card_latticeCube_filter_eq N 0 (-(N : ℤ)) le_rfl (by omega)]
        push_cast
        ring
      have hcardN : (N : ℝ) ^ (d - 1) ≤ ((leftFace d N).card : ℝ) := by
        rw [hcard]
        exact pow_le_pow_left₀ (by positivity) (by push_cast; linarith) _
      rw [hXm] at hLω
      have hA : abar / 2 < faceAverage (Φ (unit 0) 0) (leftFace d N) (unit 0) ω := by
        have := (abs_lt.1 hLω).1
        linarith
      rw [hsum, hpow]
      exact mul_le_mul hA.le hcardN (by positivity) ((half_pos habar).le.trans hA.le)
    ·
      have hside : ∀ j ∈ Finset.univ.erase (0 : Fin d),
          |∑ x ∈ upperSide j N, edgeDifference (uniqueInfiniteComponent h) u x (x + unit j) +
            ∑ x ∈ lowerSide j N, edgeDifference (uniqueInfiniteComponent h) u x (x - unit j)| ≤
          2 * η * (3 ^ (d - 1) * (N : ℝ) ^ (d - 1)) := by
        intro j hj
        have hj0 := Finset.ne_of_mem_erase hj
        obtain ⟨hUj, hDj⟩ := hSω j hj
        rw [hYm j hj0, sub_zero] at hUj hDj
        have hneU : (upperSide j N).Nonempty :=
          ⟨fun i => if i = j then (N : ℤ) else -(N : ℤ),
            Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨mem_latticeCube.2 fun i => by
              split_ifs <;> omega, by simp only [if_neg (Ne.symm hj0)]; omega⟩, if_pos rfl⟩⟩
        have hneD : (lowerSide j N).Nonempty := ⟨fun _ => -(N : ℤ), Finset.mem_filter.2
          ⟨Finset.mem_filter.2 ⟨mem_latticeCube.2 fun _ => ⟨le_rfl, by omega⟩,
            show -(N : ℤ) ≤ 0 by omega⟩, rfl⟩⟩
        have hU : ∑ x ∈ upperSide j N, edgeDifference (uniqueInfiniteComponent h) u x (x + unit j) =
            faceAverage (Φ 0 (unit j)) (upperSide j N) 0 ω * (upperSide j N).card := by
          rw [← sum_eq_faceAverage_mul _ hneU]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [key x (x + unit j) x, sub_self, add_sub_cancel_left, zero_sub]
        have hD : ∑ x ∈ lowerSide j N, edgeDifference (uniqueInfiniteComponent h) u x (x - unit j) =
            -(faceAverage (Φ 0 (unit j)) (lowerSide j N) (unit j) ω * (lowerSide j N).card) := by
          rw [← sum_eq_faceAverage_mul _ hneD, ← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [edgeDifference_comm, key (x - unit j) x (x - unit j), sub_self, sub_sub_cancel,
            neg_sub]
        have hcU : ((upperSide j N).card : ℝ) ≤ ((2 * N + 1 : ℕ) : ℝ) ^ (d - 1) := by
          have := card_side_le N j (N : ℤ) (by omega) le_rfl
          exact_mod_cast this
        have hcD : ((lowerSide j N).card : ℝ) ≤ ((2 * N + 1 : ℕ) : ℝ) ^ (d - 1) := by
          have := card_side_le N j (-(N : ℤ)) le_rfl (by omega)
          exact_mod_cast this
        rw [hU, hD]
        calc _ ≤ |faceAverage (Φ 0 (unit j)) (upperSide j N) 0 ω * (upperSide j N).card| +
              |-(faceAverage (Φ 0 (unit j)) (lowerSide j N) (unit j) ω *
                (lowerSide j N).card)| := abs_add_le _ _
          _ ≤ η * ((2 * N + 1 : ℕ) : ℝ) ^ (d - 1) + η * ((2 * N + 1 : ℕ) : ℝ) ^ (d - 1) := by
              rw [abs_neg, abs_mul, abs_mul, Nat.abs_cast, Nat.abs_cast]
              gcongr
          _ ≤ _ := by nlinarith
      unfold sideFlux sidesSum
      calc _ ≤ ∑ j ∈ Finset.univ.erase (0 : Fin d),
            |∑ x ∈ upperSide j N, edgeDifference (uniqueInfiniteComponent h) u x (x + unit j) +
              ∑ x ∈ lowerSide j N, edgeDifference (uniqueInfiniteComponent h) u x (x - unit j)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _j ∈ Finset.univ.erase (0 : Fin d), 2 * η * (3 ^ (d - 1) * (N : ℝ) ^ (d - 1)) :=
            Finset.sum_le_sum hside
        _ ≤ ε * (N : ℝ) ^ ((d : ℝ) - 1) := by
            rw [Finset.sum_const, nsmul_eq_mul, hpow, hηdef]
            have hcard : ((Finset.univ.erase (0 : Fin d)).card : ℝ) ≤ d := by
              rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
                Fintype.card_fin]
              exact_mod_cast Nat.sub_le d 1
            have h3 : (3 : ℝ) ^ d = 3 * 3 ^ (d - 1) := by
              rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ d)]
            have hNd : 0 ≤ (N : ℝ) ^ (d - 1) := by positivity
            have h3p : 0 < (3 : ℝ) ^ (d - 1) := by positivity
            rw [h3]
            field_simp
            nlinarith [mul_nonneg (mul_nonneg hNd h3p.le) hε.le]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (h := fun N => μ {ω | ¬ ∀ z, configurationTranslation z ω ∈ G} +
      (μ (BL N) + ∑ j ∈ Finset.univ.erase (0 : Fin d), (μ (BU j N) + μ (BD j N))))
    ?_ (Eventually.of_forall fun _ => zero_le) ?_
  · rw [hnull]
    have := (tendsto_const_nhds (x := (0 : ENNReal))).add (hL.add
      (tendsto_finsetSum _ fun j hj => (hUp j hj).add (hLow j hj)))
    simpa using this
  · filter_upwards [eventually_ge_atTop 1] with N hN
    refine (measure_mono (hsub N hN)).trans ((measure_union_le _ _).trans
      (add_le_add le_rfl ((measure_union_le _ _).trans (add_le_add le_rfl
        ((measure_biUnion_finset_le _ _).trans
          (Finset.sum_le_sum fun j _ => measure_union_le _ _))))))

end Rigidity.Proofs.S3
