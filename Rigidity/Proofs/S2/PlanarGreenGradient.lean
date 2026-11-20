import Rigidity.External.PlanarInputs
import Rigidity.Proofs.S2.GreenGradientCore

/-!
# Planar Green-gradient homogenization

The Green-gradient composition needs quantitative Green and corrector estimates only in
dimension two.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory LatticeProb.Percolation Rigidity.Section2 Rigidity.Steps.S2

/-- The Green-function comparison scales from the planar quantitative estimate. -/
theorem greenClose_scales_two (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGQ : Rigidity.External.SupercriticalBondGreenQuantitativeTwo) :
    ∃ κ : ℝ, ∃ hκ : 0 < κ, ∀ η : ℝ, 0 < η → ∃ C s : ℝ, 0 < C ∧ 0 < s ∧ ∀ y : Vertex 2,
      ∃ M K : Configuration 2 → ℝ, Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧
        HasStretchedExpTail 2 p M s C ∧
        ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω,
          ∀ hy : y ∈ (uniqueInfiniteComponent h).supp, ∀ g : uniqueInfiniteComponent h → ℝ,
            IsGreenColumn 2 le_rfl (uniqueInfiniteComponent h) ⟨y, hy⟩ g →
            GreenCloseAt le_rfl ⟨κ, hκ⟩ (uniqueInfiniteComponent h) ⟨y, hy⟩ g (K ω) C η (M ω) := by
  obtain ⟨κ, hκ, K, _, hK⟩ := hGQ p hpc hp1
  refine ⟨κ, hκ, fun η hη => ?_⟩
  obtain ⟨C, s, hC, hs, hy⟩ := hK η hη
  refine ⟨C, s, hC, hs, fun y => ?_⟩
  obtain ⟨_, M, hMm, hM0, hMt, hMae⟩ := hy y
  refine ⟨M, K y, hMm, hM0, hMt, ?_⟩
  filter_upwards [hMae] with ω hω h hy g hg z v hv hMv
  simpa using (hω h hy g hg).2 z v hv hMv

/-- Planar Green-gradient homogenization from planar quantitative estimates and scale steps. -/
theorem greenGradientHomogenization_of_planar_inputs (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGQ : Rigidity.External.SupercriticalBondGreenQuantitativeTwo)
    (hCQ : Rigidity.External.CorrectorQuantitativeInputTwo)
    (hReg : RegularityScaleStep 2 p) (hDense : DensityScaleStep 2 p)
    (hTail : TailOfOsStep 2 p) (hScale : MinimalScaleStep 2 p)
    (hCore : GreenGradientCoreStep 2 le_rfl) :
    GreenGradientHomogenizationStmt 2 le_rfl p := by
  obtain ⟨κ, hκ, hH⟩ := greenClose_scales_two p hpc hp1 hGQ
  refine ⟨⟨κ, hκ⟩, fun δ hδ => ?_⟩
  have hδ' : 0 < min δ 1 := lt_min hδ one_pos
  have hη : 0 < min δ 1 / 4 := by positivity
  obtain ⟨Ch, sh, hCh, hsh, hHy⟩ := hH _ hη
  obtain ⟨sc, Cc, hsc, hCc, hCx⟩ := hCQ p hpc hp1 _ hη
  obtain ⟨sr, Cr, hsr, hCr, hRx⟩ := hReg hpc hp1
  obtain ⟨sd, Cd, cD, hsd, hCd, hcD, hDx⟩ := hDense hpc hp1
  obtain ⟨A, N, hA, hcore⟩ :=
    hCore ⟨κ, hκ⟩ (min δ 1) Ch Cc Cr cD hδ' (min_le_right _ _) hCh hCc hCr hcD
  obtain ⟨Tc, hTc, hTcX⟩ := hTail sc Cc hsc hCc
  obtain ⟨Tr, hTr, hTrX⟩ := hTail sr Cr hsr hCr
  obtain ⟨Td, hTd, hTdX⟩ := hTail sd Cd hsd hCd
  choose Mc hMcm hMc0 hMcO hMcae using hCx
  choose Mr hMrm hMr0 hMrO hMrae using hRx
  choose Md hMdm hMd0 hMdO hMdae using hDx
  obtain ⟨s', C', hs', hAC', hS⟩ := hScale 4 ![sh, sc, sr, sd] ![Ch, Tc, Tr, Td] A N
    (by intro i; fin_cases i <;> simp [hsh, hsc, hsr, hsd])
    (by intro i; fin_cases i <;> simp [hCh, hTc, hTr, hTd]) (by linarith)
  refine ⟨s', C', hs', by linarith, fun y => ?_⟩
  obtain ⟨Mh, K, hMhm, hMh0, hMht, hMhae⟩ := hHy y
  obtain ⟨M, hMm, hM0, hMO, hMae⟩ := hS y (fun i x => ![Mh, Mc x, Mr x, Md x] i)
    (by intro i x; fin_cases i; exacts [hMhm, hMcm x, hMrm x, hMdm x])
    (by
      intro i x; fin_cases i
      exacts [hMht, hTcX _ (hMcm x) (hMcO x), hTrX _ (hMrm x) (hMrO x),
        hTdX _ (hMdm x) (hMdO x)])
  refine ⟨M, hMm, hM0, hMO, ?_⟩
  filter_upwards [hMhae, ae_all_iff.2 hMcae, ae_all_iff.2 hMrae, ae_all_iff.2 hMdae, hMae]
    with ω h1 h2 h3 h4 h5
  intro h hy g hg ℓ hℓ x hx
  have e := h5 x.val hx
  obtain ⟨X, hX2, hhX, hcX, hrX, hdX, hAX⟩ :=
    exists_scale_max (a := Mh ω) (b := Mc x.val ω) (c := Mr x.val ω) (e := Md x.val ω)
      (e 0) (e 1) (e 2) (e 3)
  have hD1 : 1 ≤ Rigidity.Steps.S2.latticeL1Dist x.val y := by
    have : 1 ≤ A * X ^ N := one_le_mul_of_one_le_of_one_le hA (one_le_pow₀ (by linarith))
    linarith
  have hbound := hcore (uniqueInfiniteComponent h) ⟨y, hy⟩ g (K ω) ℓ x X hX2
    (fun z hz => by have := hg.1 z; rw [if_neg hz] at this; linarith)
    hℓ ((h1 h hy g hg).mono hhX) ((h3 x.val h ℓ hℓ).mono hrX)
    (fun q ℓ' hq r hr => h2 x.val h q ℓ' hq r (hcX.trans hr)) ((h4 x.val h).mono hdX) hAX.le
  unfold Rigidity.Steps.S2.latticeL1Dist at hbound hD1
  refine hbound.trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (by linarith) _))
  exact mul_le_mul hAC' (Real.rpow_le_rpow_of_exponent_le hD1 (by linarith [min_le_left δ 1]))
    (Real.rpow_nonneg (by linarith) _) (by linarith)


/-- Planar Green-gradient homogenization from the regularity and density scales. -/
theorem greenGradientHomogenization_two (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGQ : Rigidity.External.SupercriticalBondGreenQuantitativeTwo)
    (hCQ : Rigidity.External.CorrectorQuantitativeInputTwo)
    (hReg : RegularityScaleStep 2 p) (hDense : DensityScaleStep 2 p) :
    GreenGradientHomogenizationStmt 2 le_rfl p :=
  greenGradientHomogenization_of_planar_inputs p hpc hp1 hGQ hCQ hReg hDense
    (tailOfOsStep 2 p) (minimalScaleStep 2 p) (greenGradientCoreStep le_rfl)

end Rigidity.Proofs.S2
