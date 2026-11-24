import Rigidity.Proofs.Green.DarioGuTwoScaleStepFour

/-!
# The estimate of the source term of Proposition 4.3 of Dario–Gu from Step 3

The source term of the equation of `w` on the cluster splits as
`θ^{-1} (f - Σ_i (F_i(· - e_i) - F_i) - ξ)` with `f = 1_𝒞 stepFourF` (`clusterF`),
`F_i = 1_𝒞 stepOneF` (`clusterFlux`) and `ξ = 1_𝒞 Σ_{k,i} g̃_{k,i} D_i D_k p̄` (`clusterXi`)
(`clusterSource_eq_split`; on the cluster `1_𝒞 F_i(x - e_i) = F_i(x - e_i)` because an open edge
does not leave the cluster). Step 4 bounds `f` and `F` (`tsum_sq_clusterF_le`,
`tsum_sq_clusterFlux_le`), with the growth of the corrector given by Proposition 2.12 (R5).

`DarioGuTwoScaleFluxTermTwo` is the estimate of Step 3 of the source (lines 2333-2405), (4.32)
after Young's inequality: `-θ^{-1} Σ_x ψ_R² v ξ ≤ E(ψ_R v)/4 + (8r)^{-1} Σ_x (ψ_R v)² + Q r^{α - 3}`.
`darioGuTwoScaleSourceBoundTwo_of_fluxTerm` proves `DarioGuTwoScaleSourceBoundTwo` (Steps 3-4)
from it and R5, through `tsum_source_le_of_split`, and
`darioGuTwoScaleErrorTwo_of_fluxTerm` proves Proposition 4.3 (`DarioGuTwoScaleErrorTwo`).
-/

open scoped Classical
open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External

namespace Rigidity.Green

/-- The flux term `ξ = 1_𝒞 Σ_{k,i} g̃_{k,i} D_i D_k p̄(r, · - y)` of the source. -/
noncomputable def clusterXi {ω : Configuration 2} (K : OpenComponent ω) (σ : ℝ)
    (χ : Fin 2 → Vertex 2 → ℝ) (r : ℝ) (y x : Vertex 2) : ℝ :=
  if x ∈ K.supp then ∑ k : Fin 2, ∑ i : Fin 2, centeredFlux ω σ χ k i x *
    fwdDiff i (fwdDiff k fun z => latticeGaussian σ r z y) x else 0

/-- **Step 3 of the proof of Proposition 4.3 of Dario–Gu** ((4.32) with Young's inequality), in
dimension two, for the weights `ψ_R` with `C ≥ C₀`. -/
def DarioGuTwoScaleFluxTermTwo (p : unitInterval) (σ : ℝ) : Prop :=
  ∀ α : ℝ, 0 < α → ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ C : ℝ, C₀ ≤ C → ∃ Q s : ℝ, 0 < Q ∧ 0 < s ∧
    ∀ y : Vertex 2, ∃ M : Configuration 2 → ℝ, Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧
      IsOsBond 2 p M s Q ∧
      ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω,
        y ∈ (uniqueInfiniteComponent h).supp → ∀ χ : Fin 2 → Vertex 2 → ℝ,
          IsDGCorrector (uniqueInfiniteComponent h) y χ → ∀ r : ℝ, M ω ≤ r →
          ∀ R : ℝ, 0 ≤ R → ∀ v : Vertex 2 → ℝ, Summable (fun x => v x ^ 2) →
            (∀ x, x ∉ (uniqueInfiniteComponent h).supp → v x = 0) →
            Summable (fun x => dgWeightTrunc C r R y x ^ 2 * v x *
              clusterXi (uniqueInfiniteComponent h) σ χ r y x) ∧
            -((theta 2 p)⁻¹ * ∑' x, dgWeightTrunc C r R y x ^ 2 * v x *
                clusterXi (uniqueInfiniteComponent h) σ χ r y x) ≤
              openEnergy ω (fun x => dgWeightTrunc C r R y x * v x) / 4 +
                1 / (8 * r) * ∑' x, (dgWeightTrunc C r R y x * v x) ^ 2 + Q * r ^ (α - 3)

/-- On the cluster, `1_𝒞 F_i(x - e_i) = F_i(x - e_i)`. -/
theorem clusterFlux_sub_unit_eq {ω : Configuration 2} (K : OpenComponent ω) (σ : ℝ)
    (χ : Fin 2 → Vertex 2 → ℝ) (r : ℝ) (y : Vertex 2) (i : Fin 2) {x : Vertex 2}
    (hx : x ∈ K.supp) :
    clusterFlux K.supp ω σ χ r y i (x - unit i) =
      stepOneF ω χ (fun z => latticeGaussian σ r z y) i (x - unit i) := by
  unfold clusterFlux
  split_ifs with h
  · rfl
  · unfold stepOneF openCond
    rw [sub_add_cancel]
    split_ifs with hadj
    · exact absurd (K.mem_supp_of_adj_mem_supp hx hadj.symm) h
    · rw [zero_mul]

/-- The splitting of the source term. -/
theorem clusterSource_eq_split {ω : Configuration 2} (K : OpenComponent ω) (σ θ : ℝ)
    (χ : Fin 2 → Vertex 2 → ℝ) (r : ℝ) (y : Vertex 2) {v : Vertex 2 → ℝ}
    (hv : ∀ x, x ∉ K.supp → v x = 0) (ψ : Vertex 2 → ℝ) (x : Vertex 2) :
    ψ x ^ 2 * v x * clusterSource K σ θ χ y r x =
      θ⁻¹ * (ψ x ^ 2 * v x * (clusterF K.supp σ χ r y x -
        ∑ i : Fin 2, (clusterFlux K.supp ω σ χ r y i (x - unit i) -
          clusterFlux K.supp ω σ χ r y i x) - clusterXi K σ χ r y x)) := by
  by_cases hx : x ∈ K.supp
  · have h1 : ∀ i : Fin 2, clusterFlux K.supp ω σ χ r y i x =
        stepOneF ω χ (fun z => latticeGaussian σ r z y) i x := fun i => by
      unfold clusterFlux
      rw [if_pos hx]
    simp only [clusterFlux_sub_unit_eq K σ χ r y _ hx, h1]
    unfold clusterSource clusterF clusterXi twoScaleSource stepFourF
    rw [if_pos hx, if_pos hx, if_pos hx]
    ring
  · rw [hv x hx]
    ring

theorem abs_dgWeightTrunc_le {C r R : ℝ} (hC : 0 < C) (hr : 0 < r) (hR : 0 ≤ R) (y x : Vertex 2) :
    |dgWeightTrunc C r R y x| ≤ Real.exp (R ^ 2 / r / C) := by
  rw [abs_of_pos (dgWeightTrunc_pos C r R y x)]
  exact dgWeightTrunc_le hC hr hR y x

theorem clusterFlux_eq_openCond_mul {ω : Configuration 2} (S : Set (Vertex 2)) (σ : ℝ)
    (χ : Fin 2 → Vertex 2 → ℝ) (r : ℝ) (y : Vertex 2) (i : Fin 2) (x : Vertex 2) :
    clusterFlux S ω σ χ r y i x = openCond ω i x * clusterFlux S ω σ χ r y i x := by
  unfold clusterFlux
  split_ifs
  · unfold stepOneF
    rw [← mul_assoc, ← sq, openCond_sq]
  · rw [mul_zero]

/-- **Steps 3-4 of Proposition 4.3 of Dario–Gu** from Step 3 and Proposition 2.12. -/
theorem darioGuTwoScaleSourceBoundTwo_of_fluxTerm (hR5 : CorrectorQuantitativeInputTwo)
    {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) {σ : ℝ}
    (hσ : 0 < σ) (hξ : DarioGuTwoScaleFluxTermTwo p σ) : DarioGuTwoScaleSourceBoundTwo p σ := by
  intro α hα
  set θ := theta 2 p with hθdef
  have hθ : 0 < θ := Rigidity.Percolation.theta_pos_of_criticalProbability_lt 2 p hpc
  set β := min α 1 / 2 with hβdef
  have hβ0 : 0 < β := by positivity
  have hβ1 : β ≤ 1 := by
    have := min_le_right α 1
    linarith
  have hβα : β ≤ α := by
    have := min_le_left α 1
    linarith
  obtain ⟨C₀ξ, hC₀ξ, hξ'⟩ := hξ α hα
  obtain ⟨Qf, hQf, hf⟩ := tsum_sq_clusterF_le hσ
  obtain ⟨QF, hQF, hF⟩ := tsum_sq_clusterFlux_le hσ
  obtain ⟨s₅, C₅, hs₅, hC₅, h5⟩ := hR5 p hpc hp1 β hβ0
  refine ⟨max C₀ξ (128 * σ), lt_max_of_lt_left hC₀ξ, fun C hC => ?_⟩
  have hC128 : 128 * σ ≤ C := (le_max_right _ _).trans hC
  have hC0 : 0 < C := by nlinarith
  obtain ⟨Qξ, sξ, hQξ, hsξ, hξC⟩ := hξ' C ((le_max_left _ _).trans hC)
  choose Mξ hMξm hMξ0 hMξos hMξae using hξC
  choose M₅ hM5m hM50 hM5os hM5ae using h5
  set Q₁ := Qf * Real.exp (4 / C) * (1 + C₅) ^ 2 with hQ₁
  set Q₂ := QF * (Real.exp (4 / C) + 18 / C ^ 2 * Real.exp (15 / C)) * (1 + C₅) ^ 2 with hQ₂
  set s := min sξ (s₅ / 2) with hs
  have hs0 : 0 < s := lt_min hsξ (by positivity)
  set θ1 := Qξ * (6 : ℝ) ^ (1 / s) with hθ1
  set θ2 := C₅ ^ 2 * (6 : ℝ) ^ (1 / s) with hθ2
  set θ3 := (1 : ℝ) * (3 : ℝ) ^ (1 / s) with hθ3
  set θM := max (max θ1 θ2 * (4 : ℝ) ^ (1 / s)) θ3 * (4 : ℝ) ^ (1 / s) with hθM
  set Qt := 2 * θ⁻¹ ^ 2 * Q₁ + 5 * θ⁻¹ ^ 2 * Q₂ + Qξ with hQt
  have hθM0 : 0 < θM := by positivity
  have hQt0 : 0 < Qt := by positivity
  refine ⟨max Qt θM, s, lt_max_of_lt_right hθM0, hs0, fun y => ?_⟩
  set M : Configuration 2 → ℝ := fun ω => max (max (Mξ y ω) (M₅ y ω ^ 2)) 1 with hM
  have hMm : Measurable M := ((hMξm y).max ((hM5m y).pow_const 2)).max measurable_const
  have hos1 : IsOsBond 2 p (Mξ y) s θ1 :=
    Rigidity.Proofs.S2.IsOsBond.mono_exponent hs0 (min_le_left _ _) (hMξm y) (hMξos y)
  have hos2 : IsOsBond 2 p (fun ω => M₅ y ω ^ 2) s θ2 :=
    Rigidity.Proofs.S2.IsOsBond.mono_exponent hs0 (min_le_right _ _) ((hM5m y).pow_const 2)
      (IsOsBond.sq_of_nonneg hC₅ (hM50 y) (hM5os y))
  have hos12 := Rigidity.Proofs.S2.IsOsBond.max hs0 (by positivity) (by positivity)
    (hMξm y) ((hM5m y).pow_const 2) hos1 hos2
  have hosM : IsOsBond 2 p M s θM :=
    Rigidity.Proofs.S2.IsOsBond.max hs0 (by positivity) (by positivity)
      ((hMξm y).max ((hM5m y).pow_const 2)) measurable_const hos12
      (Rigidity.Proofs.S2.isOsBond_const one_pos hs0)
  refine ⟨M, hMm, fun ω => le_max_of_le_right zero_le_one,
    Rigidity.Proofs.S2.IsOsBond.mono_scale hs0 hθM0
      (le_max_right _ _) hMm hosM, ?_⟩
  filter_upwards [hMξae y, hM5ae y] with ω hωξ hω5
  intro h hy χ hχ r hr R hR v hv hvK
  set K := uniqueInfiniteComponent h with hK
  have hr1 : 1 ≤ r := (le_max_right _ _).trans hr
  have hr0 : 0 < r := by linarith
  have hMξr : Mξ y ω ≤ r := (le_max_left _ _).trans ((le_max_left _ _).trans hr)
  have hM5r : M₅ y ω ≤ Real.sqrt r := by
    rw [← Real.sqrt_sq (hM50 y ω)]
    exact Real.sqrt_le_sqrt ((le_max_right _ _).trans ((le_max_left _ _).trans hr))
  -- the growth of the corrector on the cluster (Proposition 2.12 at the centre `y`)
  have hχb : ∀ x ∈ K.supp, ∀ k : Fin 2,
      |χ k x| ≤ C₅ * (Real.sqrt r + latticeDist x y + 2) ^ β := by
    intro x hx k
    obtain ⟨b', hadj, hb'd⟩ := exists_adj_near (uniqueInfiniteComponent_infinite h) ⟨x, hx⟩
    have hd0 := latticeDist_nonneg x y
    have hsq0 := Real.sqrt_nonneg r
    have hrr : M₅ y ω ≤ Real.sqrt r + latticeDist x y + 2 := by linarith
    have hb'y : latticeDist b'.val y ≤ latticeDist x y + 1 := by
      have := latticeDist_triangle b'.val x y
      rw [latticeDist_comm x b'.val] at this
      linarith
    have := hω5 h (Pi.single k 1) (fun a => (a.val k : ℝ) + χ k a.val) (hχ k).1 _ hrr
      ⟨x, hx⟩ ⟨y, hy⟩ ⟨x, hx⟩ b' (by change latticeDist x y < _; linarith)
      (by change latticeDist y y < _
          rw [show latticeDist y y = 0 by simp [latticeDist]]; linarith)
      (by change latticeDist x y < _; linarith) (by change latticeDist b'.val y < _; linarith) hadj
    simp only [Rigidity.Corrector.sum_single_mul, Rigidity.Corrector.sum_abs_single,
      mul_one] at this
    have e1 : (x k : ℝ) + χ k x - x k - ((y k : ℝ) + χ k y - y k) = χ k x := by
      rw [(hχ k).2]; ring
    rw [e1] at this
    exact le_of_add_le_of_nonneg_left this (abs_nonneg _)
  -- Step 4
  obtain ⟨hfs, hfb⟩ := hf C β r R C₅ K.supp χ y hC128 hβ0.le hβ1 hr1 hR hC₅.le hχb
  obtain ⟨hFs, ⟨hF1s, hF1b⟩, ⟨hF2s, hF2b⟩⟩ :=
    hF C β r R C₅ K.supp ω χ y hC128 hβ0.le hβ1 hr1 hR hC₅.le hχb
  have hpow3 : r ^ (β - 3) ≤ r ^ (α - 3) := Real.rpow_le_rpow_of_exponent_le hr1 (by linarith)
  have hpow4 : r ^ (β - 4) ≤ r ^ (α - 4) := Real.rpow_le_rpow_of_exponent_le hr1 (by linarith)
  have hp3 : 0 ≤ r ^ (β - 3) := Real.rpow_nonneg hr0.le _
  have hp4 : 0 ≤ r ^ (β - 4) := Real.rpow_nonneg hr0.le _
  have hfb' : ∑' x, (dgWeightTrunc C r R y x * clusterF K.supp σ χ r y x) ^ 2 ≤
      Q₁ * r ^ (α - 4) := by
    refine hfb.trans ?_
    rw [hQ₁]
    exact mul_le_mul_of_nonneg_left hpow4 (by positivity)
  have hE1 : Real.exp (4 / C) ≤ Real.exp (4 / C) + 18 / C ^ 2 * Real.exp (15 / C) := by
    have : 0 ≤ 18 / C ^ 2 * Real.exp (15 / C) := by positivity
    linarith
  have hE2 : 18 / C ^ 2 * Real.exp (15 / C) ≤
      Real.exp (4 / C) + 18 / C ^ 2 * Real.exp (15 / C) := by
    have : 0 ≤ Real.exp (4 / C) := by positivity
    linarith
  have hF1b' : ∑' x, ∑ i : Fin 2, (clusterFlux K.supp ω σ χ r y i x *
      dgWeightTrunc C r R y (x + unit i)) ^ 2 ≤ Q₂ * r ^ (α - 3) := by
    refine hF1b.trans ?_
    rw [hQ₂]
    calc QF * Real.exp (4 / C) * (1 + C₅) ^ 2 * r ^ (β - 3)
        ≤ QF * (Real.exp (4 / C) + 18 / C ^ 2 * Real.exp (15 / C)) * (1 + C₅) ^ 2 *
            r ^ (β - 3) := by gcongr
      _ ≤ QF * (Real.exp (4 / C) + 18 / C ^ 2 * Real.exp (15 / C)) * (1 + C₅) ^ 2 *
            r ^ (α - 3) := mul_le_mul_of_nonneg_left hpow3 (by positivity)
  have hF2b' : ∑' x, ∑ i : Fin 2, (clusterFlux K.supp ω σ χ r y i x *
      (dgWeightTrunc C r R y (x + unit i) - dgWeightTrunc C r R y x)) ^ 2 ≤
      Q₂ * r ^ (α - 4) := by
    refine hF2b.trans ?_
    rw [hQ₂]
    calc QF * (18 / C ^ 2 * Real.exp (15 / C)) * (1 + C₅) ^ 2 * r ^ (β - 4)
        ≤ QF * (Real.exp (4 / C) + 18 / C ^ 2 * Real.exp (15 / C)) * (1 + C₅) ^ 2 *
            r ^ (β - 4) := by gcongr
      _ ≤ QF * (Real.exp (4 / C) + 18 / C ^ 2 * Real.exp (15 / C)) * (1 + C₅) ^ 2 *
            r ^ (α - 4) := mul_le_mul_of_nonneg_left hpow4 (by positivity)
  -- Step 3
  obtain ⟨hξs, hξb⟩ := hωξ h hy χ hχ r hMξr R hR v hv hvK
  -- the splitting
  have hsplit := tsum_source_le_of_split ω hθ hr0 (abs_dgWeightTrunc_le hC0 hr0 hR y) hv hfs hfb'
    hFs (clusterFlux_eq_openCond_mul K.supp σ χ r y) hF1b' hF2b' hξs hξb
  have heq : ∑' x, dgWeightTrunc C r R y x ^ 2 * v x * clusterSource K σ θ χ y r x =
      θ⁻¹ * ∑' x, dgWeightTrunc C r R y x ^ 2 * v x * (clusterF K.supp σ χ r y x -
        ∑ i : Fin 2, (clusterFlux K.supp ω σ χ r y i (x - unit i) -
          clusterFlux K.supp ω σ χ r y i x) - clusterXi K σ χ r y x) := by
    rw [← tsum_mul_left]
    exact tsum_congr fun x => clusterSource_eq_split K σ θ χ r y hvK _ x
  rw [heq]
  refine hsplit.trans ?_
  have hQ : 2 * θ⁻¹ ^ 2 * Q₁ + 5 * θ⁻¹ ^ 2 * Q₂ + Qξ ≤ max Qt θM := le_max_left _ _
  have hr3 : 0 ≤ r ^ (α - 3) := Real.rpow_nonneg hr0.le _
  have := mul_le_mul_of_nonneg_right hQ hr3
  linarith

/-- **Proposition 4.3 of Dario–Gu** (`DarioGuTwoScaleErrorTwo`) from Step 3 of its proof and
Proposition 2.12. -/
theorem darioGuTwoScaleErrorTwo_of_fluxTerm (hR5 : CorrectorQuantitativeInputTwo)
    {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) {σ : ℝ}
    (hσ : 0 < σ) (hξ : DarioGuTwoScaleFluxTermTwo p σ) : DarioGuTwoScaleErrorTwo p σ :=
  darioGuTwoScaleErrorTwo_of_sourceBound hR5 hpc hp1 hσ
    (darioGuTwoScaleSourceBoundTwo_of_fluxTerm hR5 hpc hp1 hσ hξ)

end Rigidity.Green
