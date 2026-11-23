import Rigidity.Proofs.Corrector.DarioPropThreeOne
import Rigidity.Proofs.Probability.BernoulliMoments
import Rigidity.Proofs.Probability.StretchedExponential

/-!
# Dario's Proposition 2.17: the concentration inequality for stretched exponential moments

`concentrationTwo_holds : ConcentrationTwo` proves the input `ConcentrationTwo`
(`DarioPropThreeOne.lean`): Dario, Proposition 2.17, which cites Armstrong and Lin, *Optimal
quantitative estimates in stochastic homogenization for elliptic equations in nondivergence form*
(ARMA 225, 2017), Proposition 2.2. For `p ∈ (0, 1)`, `β ∈ (0, 2)` and an integrable `X` of the
bond configuration with `𝕍[X] < ∞` almost surely,

  `E[exp(|X - E X|^β)] ≤ C E[exp((C 𝕍[X])^{β/(2-β)})]^{(2-β)/β}`,

with `C` depending on `p` and `β`. The proof follows Armstrong and Lin (Appendix A):

* the moment inequality `E[|X - E X|^q] ≤ 2 (3q/c)^{q/2} E[𝕍[X]^{q/2}]`, `q ≥ 2`,
  `c = min(p, 1 - p)` (`lintegral_abs_sub_rpow_le_vertSum`). Armstrong and Lin cite it from
  Boucheron, Lugosi and Massart with `𝕍` defined through conditional expectations; Boucheron,
  Bousquet, Lugosi and Massart (Ann. Probab. 33 (2005), Theorem 2) prove it with the resampled
  quantity `V⁺`. For Bernoulli bonds the two are comparable up to the factor `c`, and their proof
  (tensorization of `φ`-entropies, two-point bound, induction on the moments) is carried out in
  `Rigidity.Proofs.Probability` on the finite cube and extended to the infinitely many bonds by
  conditioning on finitely many of them;
* the expansion of `exp(|X - E X|^β)` in powers (`lintegral_exp_rpow_le_of_moments`).

For `p ∈ {0, 1}` the law of the configuration is a point mass and the inequality holds with
`C = 1`.
-/

namespace Rigidity.Corrector

open MeasureTheory LatticeProb.Percolation Rigidity.Probability

theorem resampleVar_eq_vertSum (p : unitInterval) (X : Configuration 2 → ℝ) :
    resampleVar p X = vertSum p X := rfl

/-- `𝕍[X]` does not change, almost surely, when `X` is modified on a null set. -/
theorem resampleVar_congr_ae {p : unitInterval} {X Y : Configuration 2 → ℝ}
    (h : X =ᵐ[latticeBondLaw 2 p] Y) : resampleVar p X =ᵐ[latticeBondLaw 2 p] resampleVar p Y := by
  have hc : ∀ e : Bond 2, condExp (bondsExcept e) (latticeBondLaw 2 p) X =ᵐ[latticeBondLaw 2 p]
      condExp (bondsExcept e) (latticeBondLaw 2 p) Y := fun e => condExp_congr_ae h
  filter_upwards [ae_all_iff.2 hc, h] with ω hω hXY
  simp only [resampleVar, hω, hXY]

/-- At `p ∈ {0, 1}` the bond law is a point mass. -/
theorem exists_latticeBondLaw_eq_dirac {p : unitInterval} (hp : ¬(0 < (p : ℝ) ∧ (p : ℝ) < 1)) :
    ∃ ω₀ : Configuration 2, latticeBondLaw 2 p = Measure.dirac ω₀ := by
  rcases p.2.1.eq_or_lt with h0 | h0
  · have hp0 : p = 0 := Subtype.ext h0.symm
    subst hp0
    refine ⟨fun _ => false, ?_⟩
    simp only [latticeBondLaw, ProbabilityTheory.bernoulliMeasure_zero, Measure.infinitePi_dirac]
  · have h1 : (p : ℝ) = 1 := by
      by_contra hne
      exact hp ⟨h0, lt_of_le_of_ne p.2.2 hne⟩
    have hp1 : p = 1 := Subtype.ext h1
    subst hp1
    exact ⟨allOpen 2, latticeBondLaw_one 2⟩

/-- **Dario, Proposition 2.17 in dimension two** (Armstrong and Lin, Proposition 2.2):
the input `ConcentrationTwo` holds. -/
theorem concentrationTwo_holds : ConcentrationTwo := by
  intro p β hβ0 hβ2
  haveI : Nonempty (Bond 2) :=
    ⟨bondOfAdjacent (x := (0 : Vertex 2)) (y := 0 + LatticeProb.unit 0) ⟨0, Or.inl rfl⟩⟩
  by_cases hp : 0 < (p : ℝ) ∧ (p : ℝ) < 1
  · obtain ⟨hp0, hp1⟩ := hp
    have hc : 0 < min (p : ℝ) (1 - p) := lt_min hp0 (by linarith)
    obtain ⟨C, hC, hbound⟩ := lintegral_exp_rpow_le_of_moments (Ω := Configuration 2)
      (K := 3 / min (p : ℝ) (1 - p)) (by positivity) hβ0 hβ2
    refine ⟨C, hC, fun X hX hfin => ?_⟩
    set X' := hX.aestronglyMeasurable.mk X with hX'_def
    have hXX' : X =ᵐ[latticeBondLaw 2 p] X' := hX.aestronglyMeasurable.ae_eq_mk
    have hX'm : Measurable X' := hX.aestronglyMeasurable.stronglyMeasurable_mk.measurable
    have hX'i : Integrable X' (latticeBondLaw 2 p) := hX.congr hXX'
    have hres := resampleVar_congr_ae hXX'
    have hfin' : ∀ᵐ ω ∂(bernProd (Bond 2) p), vertSum p X' ω < ⊤ := by
      filter_upwards [hfin, hres] with ω h1 h2
      rw [← resampleVar_eq_vertSum, ← h2]
      exact h1
    have hint : ∫ ω, X ω ∂(latticeBondLaw 2 p) = ∫ ω, X' ω ∂(latticeBondLaw 2 p) :=
      integral_congr_ae hXX'
    have hL : ∫⁻ ω, ENNReal.ofReal (Real.exp (|X ω - ∫ ω', X ω' ∂latticeBondLaw 2 p| ^ β))
        ∂latticeBondLaw 2 p =
        ∫⁻ ω, ENNReal.ofReal (Real.exp (|X' ω - ∫ ω', X' ω' ∂latticeBondLaw 2 p| ^ β))
          ∂latticeBondLaw 2 p := by
      refine lintegral_congr_ae ?_
      filter_upwards [hXX'] with ω h
      rw [h, hint]
    have hR : ∫⁻ ω, ENNReal.ofReal (Real.exp ((C * (resampleVar p X ω).toReal) ^ (β / (2 - β))))
        ∂latticeBondLaw 2 p =
        ∫⁻ ω, ENNReal.ofReal (Real.exp ((C * (vertSum p X' ω).toReal) ^ (β / (2 - β))))
          ∂latticeBondLaw 2 p := by
      refine lintegral_congr_ae ?_
      filter_upwards [hres] with ω h
      rw [h, resampleVar_eq_vertSum]
    rw [hL, hR]
    exact hbound (latticeBondLaw 2 p) (fun ω => X' ω - ∫ ω', X' ω' ∂latticeBondLaw 2 p)
      (fun ω => (vertSum p X' ω).toReal) (hX'm.sub measurable_const).aemeasurable
      (measurable_vertSum p hX'm).ennreal_toReal.aemeasurable
      (fun ω => ENNReal.toReal_nonneg)
      (fun q hq => lintegral_abs_sub_rpow_le_vertSum p hp0 hp1 hX'm hX'i hfin' hq)
  · obtain ⟨ω₀, hω₀⟩ := exists_latticeBondLaw_eq_dirac hp
    refine ⟨1, one_pos, fun X _ _ => ?_⟩
    rw [hω₀, integral_dirac, lintegral_dirac, lintegral_dirac, sub_self, abs_zero,
      Real.zero_rpow hβ0.ne', Real.exp_zero, ENNReal.ofReal_one, one_mul]
    have h1 : 1 ≤ ENNReal.ofReal (Real.exp ((1 * (resampleVar p X ω₀).toReal) ^ (β / (2 - β)))) :=
      ENNReal.one_le_ofReal.2 (Real.one_le_exp (Real.rpow_nonneg (by
        rw [one_mul]; exact ENNReal.toReal_nonneg) _))
    calc (1 : ENNReal) = 1 ^ ((2 - β) / β) := (ENNReal.one_rpow _).symm
      _ ≤ _ := ENNReal.rpow_le_rpow h1 (div_nonneg (by linarith) hβ0.le)

end Rigidity.Corrector
