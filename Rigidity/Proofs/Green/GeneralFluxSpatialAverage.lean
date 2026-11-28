import Rigidity.Proofs.Green.GeneralFluxObservable

/-!
# The spatial average of the flux on the infinite cluster of `ℤ^d`

**Gu, Proposition 1.1** (*An efficient algorithm for solving elliptic problems on percolation
clusters*, arXiv:1907.13571, (1.7)), on `ℤ^d` with the heat kernel `Φ_{r²}` of `ℤ^d` as the kernel
`K_R`, `R = r`: the spatial average of the centered flux `g_{e_k} = a(Dχ_{e_k} + e_k) - ā e_k`
satisfies `|Φ_{r²} ⋆ [g_{e_k}]_i(x)| ≤ O_s(C r^{-d/2})` (`exists_fluxSpatialAverageD`). Here `ā`
is the mean of the flux (`exists_fluxMeanD`), the flux vanishes off the infinite cluster, and the
kernel is the discrete heat kernel on the lattice points instead of a continuous kernel against the
piecewise constant extension.

The proof is Gu's (Step 1): the exponential Efron–Stein inequality (Proposition 2.17 of Dario,
`Rigidity.Corrector.GeneralDim.concentration_holds`) with the mean `E[X] = ā δ_{ik}`
(`integral_fluxObsD`) and the variance bound (3.4) of Gu's proof, `𝕍[X] ≤ O_s(C r^{-d})`. The
variance bound is the statement `FluxVarianceBoundD`; Gu proves it (Steps 2–4) from the
bound of the vertical derivatives `Σ_e (D_e X)²` by the Green function of the cluster, the
argument of Dario's Lemma 3.3 (Step 2). It is proved in dimension two (`fluxVarianceBoundD_two`,
`GeneralFluxVarianceTwo.lean`) and in every dimension `d ≥ 3`
(`fluxVarianceBoundThree_of_stepTwoWeight` with
`Rigidity.Corrector.GeneralDim.darioStepTwoWeightThree_holds`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter LatticeProb LatticeProb.Percolation Rigidity.External Rigidity.Corrector
open scoped Classical ENNReal

namespace Rigidity.Green.GeneralFlux

/-- **The variance bound (3.4) of Gu's proof of Proposition 1.1** on `ℤ^d`: for every
measurable conull set `G` of valid configurations, the resampling variance of the heat average
`X = Σ_z Φ_{r²}(x, z) flux_{e_k}(z, i)` of the flux is `O_s(C r^{-d})` for `r ≥ 1`, uniformly in
`k, i, x`. In the source it follows from `𝕍[X] ≤ Σ_e (D_e X)²` and the bound of the vertical
derivatives through the Green function of the cluster (Gu, Steps 2–4, the argument of Dario's
Lemma 3.3). It is proved for `d = 2` (`fluxVarianceBoundD_two`) and for every `d ≥ 3`
(`fluxVarianceBoundThree_of_stepTwoWeight`). -/
def FluxVarianceBoundD (d : ℕ) (p : unitInterval) : Prop :=
  ∀ (G : Set (Configuration d)) (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent d),
    (∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) →
    ∃ s C : ℝ, 0 < s ∧ 0 < C ∧ ∀ (k i : Fin d) (r : ℝ), 1 ≤ r → ∀ x : Vertex d,
      (∀ᵐ ω ∂latticeBondLaw d p, GeneralDim.resampleVar p (fluxObsD hG hGv k i r x) ω < ∞) ∧
      IsOsBond d p (fun ω => (GeneralDim.resampleVar p (fluxObsD hG hGv k i r x) ω).toReal) s
        (C / r ^ (d : ℝ))

variable {d : ℕ}

section Average

variable {G : Set (Configuration d)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent d)

/-- **Gu, Proposition 1.1, on `ℤ^d`**, from the variance bound (3.4): the heat averages of the
centered flux are `O_s(C r^{-d/2})`. -/
theorem exists_fluxSpatialAverageD [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) (hV : FluxVarianceBoundD d p) :
    ∃ abar s C : ℝ, 0 < abar ∧ 0 < s ∧ 0 < C ∧ ∀ (k i : Fin d) (r : ℝ), 1 ≤ r → ∀ x : Vertex d,
      IsOsBond d p (fun ω => |fluxObsD hG hGv k i r x ω - if i = k then abar else 0|) s
        (C / r ^ ((d : ℝ) / 2)) := by
  obtain ⟨abar, habar0, habar⟩ := exists_fluxMeanD hd hpc hp1
  obtain ⟨s₁, C₁, hs₁, hC₁, hV⟩ := hV G hG hGv hGae
  obtain ⟨A, hA, hmomX⟩ := GeneralDim.lintegral_abs_sub_integral_rpow_le (p := p)
    (GeneralDim.concentration_holds (d := d)) hs₁
  set κ : ℝ := (1 + s₁) / (2 * s₁) with hκ
  have hκ0 : 0 < κ := by positivity
  set B : ℝ := A * Real.sqrt C₁ with hB
  have hB0 : 0 < B := by positivity
  have hs' : 0 < 1 / (2 * κ) := by positivity
  have hsk : 1 / (2 * κ) * κ < 1 := by
    rw [one_div_mul_eq_div, div_lt_one (by positivity)]
    linarith
  obtain ⟨C, hC, hmom⟩ := isOsBond_of_moment_le (d := d) (p := p) hB0 hs' hsk
  refine ⟨abar, 1 / (2 * κ), C, habar0, hs', hC, fun k i r hr x => ?_⟩
  have hr0 : 0 < r := by linarith
  set X := fluxObsD hG hGv k i r x
  have hXm : Measurable X := measurable_fluxObsD hG hGv k i r x
  obtain ⟨hXi, hXmean⟩ := integral_fluxObsD hG hGv hGae habar k i r x
  obtain ⟨hresfin, hresOs⟩ := hV k i r hr x
  have hθ : 0 < C₁ / r ^ (d : ℝ) := by positivity
  have hm := hmomX X (C₁ / r ^ (d : ℝ)) hθ hXi hresfin hresOs
  rw [hXmean] at hm
  set R : ℝ := r ^ ((d : ℝ) / 2) with hR
  have hR0 : 0 < R := by positivity
  have hRsq : Real.sqrt (r ^ (d : ℝ)) = R := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hr0.le, hR]
    ring_nf
  refine GeneralDim.isOsBond_div_of_mul (GeneralDim.isOsBond_of_ae_ofReal_le hB0.le hmom
    (measurable_const.mul ((hXm.sub measurable_const).abs))
    (fun ω => mul_nonneg hR0.le (abs_nonneg _)) (T := fun ω => ENNReal.ofReal
      (R * |X ω - if i = k then abar else 0|)) (Eventually.of_forall fun ω => le_rfl)
    fun q hq => ?_)
  have hq0 : 0 < q := by linarith
  calc ∫⁻ ω, ENNReal.ofReal (R * |X ω - if i = k then abar else 0|) ^ q ∂latticeBondLaw d p
      = ∫⁻ ω, ENNReal.ofReal (R ^ q) * ENNReal.ofReal (|X ω - if i = k then abar else 0| ^ q)
          ∂latticeBondLaw d p := by
        refine lintegral_congr fun ω => ?_
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hq0.le,
          Real.mul_rpow hR0.le (abs_nonneg _), ENNReal.ofReal_mul (by positivity)]
    _ = ENNReal.ofReal (R ^ q) * ∫⁻ ω, ENNReal.ofReal (|X ω - if i = k then abar else 0| ^ q)
          ∂latticeBondLaw d p :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (R ^ q) * ENNReal.ofReal
          ((A * Real.sqrt (C₁ / r ^ (d : ℝ)) * q ^ κ) ^ q) := mul_le_mul_right (hm q hq) _
    _ = ENNReal.ofReal ((B * q ^ κ) ^ q) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← Real.mul_rpow hR0.le (by positivity),
          Real.sqrt_div' _ (by positivity), hRsq, hB]
        congr 2
        field_simp

end Average

end Rigidity.Green.GeneralFlux
