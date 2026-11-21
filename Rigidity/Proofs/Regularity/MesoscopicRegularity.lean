import Rigidity.Proofs.Regularity.InfiniteClusterBalls
import Rigidity.Proofs.Regularity.LatticeHarmonicExcessTwo

/-!
# The form of Armstrong–Dario, Lemma 7.3

Armstrong and Dario (arXiv:1609.09431v2), Lemma 7.3, state the outcome of Lemma 7.2 as
`D_k(r) ≤ C (r / R)^{k+1} D_k(R) + C r^{-δ} (r / R) ‖u‖_{L̲²(B_R)}`. For `r ≥ 1` the error term
`C r^{1-α} (D_0(R) / R + E / r)` of Lemma 7.2 is at most `2 C r^{-α} (r / R) U` whenever
`D_0(R) ≤ U` and `R E ≤ U` (`mul_rpow_one_sub_mul_le`). On the balls of a cluster,
`U = ‖u‖_{L̲²(B_R)}` bounds `D_0(R)` (the constant `0`), and `R E ≤ U` holds for the choice
`E = R^{-1} inf_a ‖u - a‖` made in the proof of Lemma 7.3. This gives the form of Lemma 7.3, with
`δ = α`, for `k = 0, 1` on the balls of the infinite cluster
(`armstrongDario_lemma_7_3_zero_infiniteCluster`, `armstrongDario_lemma_7_3_one_infiniteCluster`)
and for lattice harmonic functions on the balls of the lattice
(`armstrongDario_lemma_7_3_zero_latticeHarmonic`, `armstrongDario_lemma_7_3_one_latticeHarmonic`).
-/

namespace Rigidity.Proofs.Regularity

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External Rigidity.Proofs.S2

variable {d : ℕ}

/-- The error term of Lemma 7.2 in the form of Lemma 7.3. -/
theorem mul_rpow_one_sub_mul_le {C α r R D₀ E U : ℝ} (hC : 0 ≤ C) (hr : 1 ≤ r) (hR : 0 < R)
    (hE : 0 ≤ E) (hD₀ : D₀ ≤ U) (hRE : R * E ≤ U) :
    C * r ^ (1 - α) * (D₀ / R + E / r) ≤ 2 * C * r ^ (-α) * (r / R) * U := by
  have hr0 : 0 < r := by linarith
  have hU : 0 ≤ U := le_trans (mul_nonneg hR.le hE) hRE
  have e : r ^ (1 - α) = r * r ^ (-α) := by
    rw [sub_eq_add_neg, Real.rpow_add hr0, Real.rpow_one]
  rw [e]
  have hra : 0 ≤ r ^ (-α) := Real.rpow_nonneg hr0.le _
  have hEr : r * (E / r) = E := by rw [← mul_div_assoc, mul_div_cancel_left₀ E hr0.ne']
  have h1 : r * (D₀ / R + E / r) ≤ 2 * (r / R) * U := by
    rw [mul_add, hEr]
    have h2 : r * (D₀ / R) ≤ r * U / R := by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hD₀ hr0.le) hR.le
    have h3 : E ≤ r * U / R := by
      rw [le_div_iff₀ hR]
      have : U ≤ r * U := le_mul_of_one_le_left hU hr
      linarith [mul_comm E R]
    have : 2 * (r / R) * U = r * U / R + r * U / R := by ring
    linarith
  calc C * (r * r ^ (-α)) * (D₀ / R + E / r) = C * r ^ (-α) * (r * (D₀ / R + E / r)) := by ring
    _ ≤ C * r ^ (-α) * (2 * (r / R) * U) := mul_le_mul_of_nonneg_left h1 (mul_nonneg hC hra)
    _ = 2 * C * r ^ (-α) * (r / R) * U := by ring

theorem ballExcess_le_componentBallL2 {ω : Configuration d} (C : OpenComponent ω) (z : Vertex d)
    (P : AddSubgroup (C → ℝ)) (R : ℝ) (u : C → ℝ) :
    ballExcess (componentBallSeminorm C z) P R u ≤ componentBallL2 C z R u := by
  have := ballExcess_le (componentBallSeminorm C z) P (s := R) (u := u) (zero_mem P)
  rwa [sub_zero, componentBallSeminorm_apply] at this

/-- **Armstrong–Dario, Lemma 7.3 (`k = 0`), on the balls of the infinite cluster**, in the form
`D_0(r) ≤ C (r / R) D_0(R) + 2 C r^{-α} (r / R) ‖u‖_{L̲²(B_R)}`, above a minimal scale
`M(z) ≤ O_s(C₀)`, under the excess decay of order one of the class `Abar` and the harmonic
approximation hypothesis of Lemma 7.2 with `R E ≤ ‖u‖_{L̲²(B_R)}`. -/
theorem armstrongDario_lemma_7_3_zero_infiniteCluster [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) {A α CH : ℝ} (hA : 2 ≤ A)
    (hα : 0 < α) (hCH : 0 ≤ CH) :
    ∃ s C₀ C : ℝ, 0 < s ∧ 0 < C₀ ∧ 0 < C ∧ ∀ z : Vertex d,
      ∃ M : Configuration d → ℝ, Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧ IsOsBond d p M s C₀ ∧
      ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω,
        ∀ (Abar : ℝ → Set (uniqueInfiniteComponent h → ℝ)) (R X E : ℝ)
          (u : uniqueInfiniteComponent h → ℝ),
        1 ≤ X → M ω ≤ X → X ≤ R / A → 0 ≤ E →
        R * E ≤ componentBallL2 (uniqueInfiniteComponent h) z R u →
        HarmonicRegularity (componentBallSeminorm (uniqueInfiniteComponent h) z) Abar
          (clusterAffine (uniqueInfiniteComponent h)) 1 X R CH →
        (∀ r : ℝ, X ≤ r → r ≤ R / A → (Abar r).Nonempty) →
        HarmonicApproximation (componentBallSeminorm (uniqueInfiniteComponent h) z) Abar
          (clusterConstants (uniqueInfiniteComponent h)) A α X R E u →
        ∀ r : ℝ, max X C ≤ r → r ≤ R / 2 →
          ballExcess (componentBallSeminorm (uniqueInfiniteComponent h) z)
              (clusterConstants (uniqueInfiniteComponent h)) r u ≤
            C * (r / R) * ballExcess (componentBallSeminorm (uniqueInfiniteComponent h) z)
              (clusterConstants (uniqueInfiniteComponent h)) R u +
            2 * C * r ^ (-α) * (r / R) * componentBallL2 (uniqueInfiniteComponent h) z R u := by
  obtain ⟨s, C₀, C, hs, hC₀, hC, hlem⟩ :=
    armstrongDario_lemma_7_2_zero_infiniteCluster hd p hpc hp1 hA hα hCH
  refine ⟨s, C₀, C, hs, hC₀, hC, fun z => ?_⟩
  obtain ⟨M, hMm, hM0, hMos, hae⟩ := hlem z
  refine ⟨M, hMm, hM0, hMos, ?_⟩
  filter_upwards [hae] with ω hω h Abar R X E u hX hMX hXR hE hRE hreg hne happ r hr hrR
  have h1 := hω h Abar R X E u hX hMX hXR hE hreg hne happ r hr hrR
  have hr1 : 1 ≤ r := hX.trans ((le_max_left _ _).trans hr)
  have hR : 0 < R := by linarith
  have h2 := mul_rpow_one_sub_mul_le (α := α) hC.le hr1 hR hE
    (ballExcess_le_componentBallL2 _ z (clusterConstants _) R u) hRE
  linarith

/-- **Armstrong–Dario, Lemma 7.3 (`k = 1`), on the balls of the infinite cluster**, in the form
`D_1(r) ≤ C (r / R)² D_1(R) + 2 C r^{-α} (r / R) ‖u‖_{L̲²(B_R)}`, above a minimal scale
`M(z) ≤ O_s(C₀)`, under the excess decay of orders one and two of the class `Abar` and the
harmonic approximation hypothesis of Lemma 7.2 with `R E ≤ ‖u‖_{L̲²(B_R)}`. -/
theorem armstrongDario_lemma_7_3_one_infiniteCluster [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) {A α CH : ℝ} (hA : 2 ≤ A)
    (hα : 0 < α) (hCH : 0 ≤ CH) :
    ∃ s C₀ C : ℝ, 0 < s ∧ 0 < C₀ ∧ 0 < C ∧ ∀ z : Vertex d,
      ∃ M : Configuration d → ℝ, Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧ IsOsBond d p M s C₀ ∧
      ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω,
        ∀ (P₂ : AddSubgroup (uniqueInfiniteComponent h → ℝ))
          (Abar : ℝ → Set (uniqueInfiniteComponent h → ℝ)) (R X E : ℝ)
          (u : uniqueInfiniteComponent h → ℝ),
        clusterAffine (uniqueInfiniteComponent h) ≤ P₂ →
        P₂ ≤ clusterQuadratic (uniqueInfiniteComponent h) →
        1 ≤ X → M ω ≤ X → X ≤ R / A → 0 ≤ E →
        R * E ≤ componentBallL2 (uniqueInfiniteComponent h) z R u →
        HarmonicRegularity (componentBallSeminorm (uniqueInfiniteComponent h) z) Abar
          (clusterAffine (uniqueInfiniteComponent h)) 1 X R CH →
        HarmonicRegularity (componentBallSeminorm (uniqueInfiniteComponent h) z) Abar P₂ 2 X R CH →
        (∀ r : ℝ, X ≤ r → r ≤ R / A → (Abar r).Nonempty) →
        HarmonicApproximation (componentBallSeminorm (uniqueInfiniteComponent h) z) Abar
          (clusterConstants (uniqueInfiniteComponent h)) A α X R E u →
        ∀ r : ℝ, max X C ≤ r → r ≤ R / 2 →
          ballExcess (componentBallSeminorm (uniqueInfiniteComponent h) z)
              (clusterAffine (uniqueInfiniteComponent h)) r u ≤
            C * (r / R) ^ 2 * ballExcess (componentBallSeminorm (uniqueInfiniteComponent h) z)
              (clusterAffine (uniqueInfiniteComponent h)) R u +
            2 * C * r ^ (-α) * (r / R) * componentBallL2 (uniqueInfiniteComponent h) z R u := by
  obtain ⟨s, C₀, C, hs, hC₀, hC, hlem⟩ :=
    armstrongDario_lemma_7_2_one_infiniteCluster hd p hpc hp1 hA hα hCH
  refine ⟨s, C₀, C, hs, hC₀, hC, fun z => ?_⟩
  obtain ⟨M, hMm, hM0, hMos, hae⟩ := hlem z
  refine ⟨M, hMm, hM0, hMos, ?_⟩
  filter_upwards [hae] with ω hω h P₂ Abar R X E u hAP hPQ hX hMX hXR hE hRE hreg₁ hreg₂ hne happ
    r hr hrR
  have h1 := hω h P₂ Abar R X E u hAP hPQ hX hMX hXR hE hreg₁ hreg₂ hne happ r hr hrR
  have hr1 : 1 ≤ r := hX.trans ((le_max_left _ _).trans hr)
  have hR : 0 < R := by linarith
  have h2 := mul_rpow_one_sub_mul_le (α := α) hC.le hr1 hR hE
    (ballExcess_le_componentBallL2 _ z (clusterConstants _) R u) hRE
  linarith

/-- **Armstrong–Dario, Lemma 7.3 (`k = 1`), for lattice harmonic functions on the balls of the
lattice**, in the form `D_1(r) ≤ C (r / R)² D_1(R) + 2 C r^{-α} (r / R) ‖u‖_{L̲²(B_R)}`, with the
excess decay of orders one and two proved: only the harmonic approximation hypothesis of
Lemma 7.2, with `R E ≤ ‖u‖_{L̲²(B_R)}`, remains. -/
theorem armstrongDario_lemma_7_3_one_latticeHarmonic (d : ℕ) [NeZero d] {A α : ℝ} (hA : 2 ≤ A)
    (hα : 0 < α) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : Vertex d) (R X E : ℝ) (u : latticeComponent d → ℝ),
      1 ≤ X →
      max (latticeHRScale d) (max (latticeHRScaleTwo d) (quadLocality d (capFraction d 1))) ≤ X →
      X ≤ R / A → 0 ≤ E → R * E ≤ componentBallL2 (latticeComponent d) z R u →
      HarmonicApproximation (componentBallSeminorm (latticeComponent d) z)
        (latticeHarmonicClass z) (clusterConstants (latticeComponent d)) A α X R E u →
      ∀ r : ℝ, max X C ≤ r → r ≤ R / 2 →
        ballExcess (componentBallSeminorm (latticeComponent d) z)
            (clusterAffine (latticeComponent d)) r u ≤
          C * (r / R) ^ 2 * ballExcess (componentBallSeminorm (latticeComponent d) z)
            (clusterAffine (latticeComponent d)) R u +
          2 * C * r ^ (-α) * (r / R) * componentBallL2 (latticeComponent d) z R u := by
  obtain ⟨C, hC, hlem⟩ := armstrongDario_lemma_7_2_one_latticeHarmonic d hA hα
  refine ⟨C, hC, fun z R X E u hX hXs hXR hE hRE happ r hr hrR => ?_⟩
  have h1 := hlem z R X E u hX hXs hXR hE happ r hr hrR
  have hr1 : 1 ≤ r := hX.trans ((le_max_left _ _).trans hr)
  have hR : 0 < R := by linarith
  have h2 := mul_rpow_one_sub_mul_le (α := α) hC.le hr1 hR hE
    (ballExcess_le_componentBallL2 _ z (clusterConstants _) R u) hRE
  linarith

/-- **Armstrong–Dario, Lemma 7.3 (`k = 0`), for lattice harmonic functions on the balls of the
lattice**, in the form `D_0(r) ≤ C (r / R) D_0(R) + 2 C r^{-α} (r / R) ‖u‖_{L̲²(B_R)}`, with the
excess decay of order one proved: only the harmonic approximation hypothesis of Lemma 7.2, with
`R E ≤ ‖u‖_{L̲²(B_R)}`, remains. -/
theorem armstrongDario_lemma_7_3_zero_latticeHarmonic (d : ℕ) [NeZero d] {A α : ℝ} (hA : 2 ≤ A)
    (hα : 0 < α) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : Vertex d) (R X E : ℝ) (u : latticeComponent d → ℝ),
      1 ≤ X → max (latticeHRScale d) (24 * Real.sqrt d) ≤ X → X ≤ R / A → 0 ≤ E →
      R * E ≤ componentBallL2 (latticeComponent d) z R u →
      HarmonicApproximation (componentBallSeminorm (latticeComponent d) z)
        (latticeHarmonicClass z) (clusterConstants (latticeComponent d)) A α X R E u →
      ∀ r : ℝ, max X C ≤ r → r ≤ R / 2 →
        ballExcess (componentBallSeminorm (latticeComponent d) z)
            (clusterConstants (latticeComponent d)) r u ≤
          C * (r / R) * ballExcess (componentBallSeminorm (latticeComponent d) z)
            (clusterConstants (latticeComponent d)) R u +
          2 * C * r ^ (-α) * (r / R) * componentBallL2 (latticeComponent d) z R u := by
  obtain ⟨C, hC, hlem⟩ := armstrongDario_lemma_7_2_zero_latticeHarmonic d hA hα
  refine ⟨C, hC, fun z R X E u hX hXs hXR hE hRE happ r hr hrR => ?_⟩
  have h1 := hlem z R X E u hX hXs hXR hE happ r hr hrR
  have hr1 : 1 ≤ r := hX.trans ((le_max_left _ _).trans hr)
  have hR : 0 < R := by linarith
  have h2 := mul_rpow_one_sub_mul_le (α := α) hC.le hr1 hR hE
    (ballExcess_le_componentBallL2 _ z (clusterConstants _) R u) hRE
  linarith

end Rigidity.Proofs.Regularity
