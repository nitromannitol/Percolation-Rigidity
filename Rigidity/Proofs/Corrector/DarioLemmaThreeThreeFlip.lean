import Rigidity.Proofs.Corrector.DarioBondResampling
import Rigidity.Proofs.Regularity.PlanarHarmonicApproximationHolds

/-!
# Lemma 3.3 of Dario from the flip form of (3.13)

Dario reduces Lemma 3.3, `𝕍[X] ≤ O_s(C r^{-d})` for `X = Φ_{r²} * ∇[χ_p]_𝒫(0)`, to the estimate
(3.13) `Σ_e |Φ_{r²} * (∇[χ_p]_𝒫 - ∇[χ_p^e]_{𝒫^e})(0)|² ≤ O_s'(C r^{-d})` on the doubled
probability space, by Jensen's inequality and the argument of Armstrong, Kuusi and Mourrat,
Lemma 2.3. For the Bernoulli bond law, `𝕍[X] ≤ Σ_e (D_e X)²` almost surely with the flip
difference `D_e X(ω) = X(ω^{e,1}) - X(ω^{e,0})` (`ae_resampleVar_le_tsum_bondFlipDiff`), so
(3.13) takes the flip form `DarioFlipSumBound`: `Σ_e (D_e X)² ≤ O_s(C/r²)` in dimension two, for
every direction, component, radius `r ≥ 1` and point. Here

* `heatFlipSum`: the flip sum `Σ_e (D_e X)²` of `X = Φ_{r²} * ∇_j[χ_{e_i}]_𝒫(x)`;
* `isOsBond_of_ae_le`: `O_s` bounds pass to almost surely smaller variables;
* `darioLemmaThreeThree_of_flipSum`: Lemma 3.3 (`DarioLemmaThreeThree`) from `DarioFlipSumBound`,
  the integrability of `X` coming from R3 (`armstrongDarioOrderZeroTwo_holds`) through
  `heatGradient_coarseField_isOsBond`.
-/

namespace Rigidity.Corrector

open MeasureTheory Filter LatticeProb.Percolation Rigidity.External
open scoped ENNReal

section Flip

variable {G : Set (Configuration 2)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2)

/-- The variable `X = Φ_{r²} * ∇_j[χ_{e_i}]_𝒫(x)` of Dario's Lemma 3.3. -/
noncomputable def heatCoarseComp (i j : Fin 2) (r : ℝ) (x : Vertex 2) (ω : Configuration 2) : ℝ :=
  heatComp (fun z => coarseField hG hGv i 0 z ω) r x j

/-- The flip sum `Σ_e (X(ω^{e,1}) - X(ω^{e,0}))²` of `X = Φ_{r²} * ∇_j[χ_{e_i}]_𝒫(x)`. -/
noncomputable def heatFlipSum (i j : Fin 2) (r : ℝ) (x : Vertex 2) (ω : Configuration 2) : ℝ≥0∞ :=
  ∑' e, ENNReal.ofReal (bondFlipDiff (heatCoarseComp hG hGv i j r x) e ω ^ 2)

theorem measurable_heatCoarseComp (i j : Fin 2) (r : ℝ) (x : Vertex 2) :
    Measurable (heatCoarseComp hG hGv i j r x) :=
  measurable_heatComp (fun z => measurable_coarseField hG hGv i 0 z) r x j

end Flip

/-- **Dario, (3.13) in flip form, in dimension two**: for the conull sets `G` of the
measurable corrector there are `s, C > 0` such that for all `i, j`, `r ≥ 1` and `x`, the flip sum
`Σ_e (D_e X)²` of `X = Φ_{r²} * ∇_j[χ_{e_i}]_𝒫(x)` is almost surely finite and `≤ O_s(C/r²)`.
It holds: `darioFlipSumBound_of_stepTwo darioStepTwoSumBound_holds`. -/
def DarioFlipSumBound : Prop :=
  ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
    ∀ (G : Set (Configuration 2)) (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2),
      (∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G) → ∃ s C : ℝ, 0 < s ∧ 0 < C ∧
        ∀ (i j : Fin 2) (r : ℝ), 1 ≤ r → ∀ x : Vertex 2,
          (∀ᵐ ω ∂latticeBondLaw 2 p, heatFlipSum hG hGv i j r x ω < ∞) ∧
          IsOsBond 2 p (fun ω => (heatFlipSum hG hGv i j r x ω).toReal) s (C / r ^ 2)

/-- `O_s` bounds pass to almost surely smaller measurable variables. -/
theorem isOsBond_of_ae_le {p : unitInterval} {X Y : Configuration 2 → ℝ} {s θ : ℝ}
    (hs : 0 < s) (hθ : 0 < θ) (hX : Measurable X)
    (hXY : ∀ᵐ ω ∂latticeBondLaw 2 p, X ω ≤ Y ω) (hY : IsOsBond 2 p Y s θ) :
    IsOsBond 2 p X s θ := by
  have hpoint : ∀ᵐ ω ∂latticeBondLaw 2 p, Real.exp (Real.rpow (max (X ω / θ) 0) s) ≤
      Real.exp (Real.rpow (max (Y ω / θ) 0) s) := by
    filter_upwards [hXY] with ω hω
    apply Real.exp_le_exp.mpr
    exact Real.rpow_le_rpow (le_max_right _ _)
      (max_le_max (div_le_div_of_nonneg_right hω hθ.le) le_rfl) hs.le
  have hXi : Integrable (fun ω => Real.exp (Real.rpow (max (X ω / θ) 0) s))
      (latticeBondLaw 2 p) := by
    refine Integrable.mono' hY.1
      (Rigidity.Proofs.S2.measurable_exp_rpow_max_div s hX).aestronglyMeasurable ?_
    filter_upwards [hpoint] with ω hω
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact hω
  exact ⟨hXi, (integral_mono_ae hXi hY.1 hpoint).trans hY.2⟩

theorem measurable_resampleVar (p : unitInterval) {X : Configuration 2 → ℝ} (hX : Measurable X) :
    Measurable (resampleVar p X) := by
  unfold resampleVar
  refine Measurable.tsum fun e => ENNReal.measurable_ofReal.comp ?_
  exact (hX.sub (stronglyMeasurable_condExp.measurable.mono (bondsExcept_le e) le_rfl)).pow_const 2

/-- **Dario, Lemma 3.3 in dimension two, from the flip form of (3.13)**: the resampling variance
is almost surely at most the flip sum, which is `O_s(C/r²)`. -/
theorem darioLemmaThreeThree_of_flipSum (h : DarioFlipSumBound) : DarioLemmaThreeThree := by
  intro p hpc hp1 G hG hGv hGae
  obtain ⟨s, C, hs, hC, hflip⟩ := h p hpc hp1 G hG hGv hGae
  obtain ⟨s₀, C₀, hs₀, hC₀, h0⟩ := heatGradient_coarseField_isOsBond hG hGv
    Rigidity.Proofs.Regularity.armstrongDarioOrderZeroTwo_holds hpc hp1 hGae
  refine ⟨s, C, hs, hC, fun i j r hr x => ?_⟩
  have hF : ∀ z, Measurable (coarseField hG hGv i 0 z) := fun z =>
    measurable_coarseField hG hGv i 0 z
  have hHm := measurable_heatGradient_const hF r x
  have hXm : Measurable (heatCoarseComp hG hGv i j r x) := measurable_heatCoarseComp hG hGv i j r x
  have hHi : Integrable (fun ω => heatGradient (fun z => coarseField hG hGv i 0 z ω) r x)
      (latticeBondLaw 2 p) := by
    have := (IsOsBond.integral_rpow_le hs₀ hC₀ one_pos hHm (fun ω => heatGradient_nonneg _ _ _)
      (h0 i r x)).1
    simpa only [Real.rpow_one] using this
  have hXi : Integrable (heatCoarseComp hG hGv i j r x) (latticeBondLaw 2 p) :=
    hHi.mono' hXm.aestronglyMeasurable (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]
      exact abs_heatComp_le_heatGradient _ _ _ _)
  obtain ⟨hfin, hOs⟩ := hflip i j r hr x
  have hle := ae_resampleVar_le_tsum_bondFlipDiff p hXm hXi
  have hfinV : ∀ᵐ ω ∂latticeBondLaw 2 p,
      resampleVar p (fun ω => heatComp (fun z => coarseField hG hGv i 0 z ω) r x j) ω < ∞ := by
    filter_upwards [hle, hfin] with ω h1 h2
    exact lt_of_le_of_lt h1 h2
  refine ⟨hfinV, ?_⟩
  have hr0 : 0 < r := by linarith
  refine isOsBond_of_ae_le hs (by positivity) (measurable_resampleVar p hXm).ennreal_toReal ?_ hOs
  filter_upwards [hle, hfin] with ω h1 h2
  exact ENNReal.toReal_mono h2.ne h1

end Rigidity.Corrector
