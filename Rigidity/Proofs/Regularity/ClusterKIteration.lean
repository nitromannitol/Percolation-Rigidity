import Rigidity.Proofs.Regularity.ClusterBallGeometry
import Rigidity.Proofs.Regularity.OrderZeroOrigin

/-!
# Lemma 7.2 of Armstrong–Dario on cluster balls, order zero

The abstract Lemma 7.2 of Armstrong and Dario (arXiv:1609.09431v2) for `k = 0`
(`armstrongDario_lemma_7_2_zero`) and its consequence at the origin
(`armstrongDario_orderZero_origin`), specialized to the normalized `L²` norms `componentBallL2`
on the balls of an open cluster centred at a vertex `z`, with the constants and the affine
functions restricted to the cluster as `Ā_0 ≤ Ā_1`. The norms on balls and the affine functions
have the properties required by the iteration as soon as the cluster balls satisfy the volume
comparison `ClusterBallVolumeComparison` and the cap density `ClusterBallCapDensity` between the
radii `X` and `R`; the class `Abar` of harmonic functions and its excess decay remain hypotheses.
The constants depend only on `d`, `A`, `α`, the volume constant `K`, the cap fraction `δ` and the
constant `CH` of the excess decay of `Abar`. The versions `..._of_clusterCubeDensity` take instead a
lower bound `κ > 0` on the density of the cluster in the triadic cubes of size `3^m ≥ ℓ` inside
`B_{24 √d 3^m}(z)` (`ClusterCubeDensity` with `Λ = 24 √d`), for `X ≥ 24 √d max ℓ 1`.
-/

namespace Rigidity.Proofs.Regularity

open LatticeProb LatticeProb.Percolation

/-- **Armstrong–Dario, Lemma 7.2 (`k = 0`), on cluster balls.** -/
theorem armstrongDario_lemma_7_2_zero_cluster (d : ℕ) {A α K δ CH : ℝ} (hA : 2 ≤ A)
    (hα : 0 < α) (hK : 0 ≤ K) (hδ : 0 < δ) (hCH : 0 ≤ CH) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ω : Configuration d) (Cl : OpenComponent ω) (z : Vertex d)
      (Abar : ℝ → Set (Cl → ℝ)) (R X E : ℝ) (u : Cl → ℝ),
      1 ≤ X → X ≤ R / A → 0 ≤ E →
      ClusterBallVolumeComparison Cl z X R K → ClusterBallCapDensity Cl z X R δ →
      HarmonicRegularity (componentBallSeminorm Cl z) Abar (clusterAffine Cl) 1 X R CH →
      (∀ r : ℝ, X ≤ r → r ≤ R / A → (Abar r).Nonempty) →
      HarmonicApproximation (componentBallSeminorm Cl z) Abar (clusterConstants Cl) A α X R E u →
      ∀ r : ℝ, max X C ≤ r → r ≤ R / 2 →
        ballExcess (componentBallSeminorm Cl z) (clusterConstants Cl) r u ≤
          C * (r / R) * ballExcess (componentBallSeminorm Cl z) (clusterConstants Cl) R u +
            C * r ^ (1 - α) *
              (ballExcess (componentBallSeminorm Cl z) (clusterConstants Cl) R u / R + E / r) := by
  obtain ⟨C, hC, h⟩ := armstrongDario_lemma_7_2_zero.{0} (γ := (d : ℝ) / 2)
    (CV := Real.sqrt K) (CP := 2 / Real.sqrt δ) hA hα (by positivity) (Real.sqrt_nonneg K)
    (by positivity) hCH
  refine ⟨C, hC, fun ω Cl z Abar R X E u hX hXR hE hvol hcap hreg hne happ => ?_⟩
  exact h (componentBallSeminorm Cl z) (clusterConstants Cl) (clusterAffine Cl) Abar R X E u
    (clusterConstants_le_clusterAffine Cl) hX hXR hE
    (radiusMonotone_componentBallSeminorm Cl z (by linarith) hK hvol)
    (polynomialComparison_componentBallSeminorm Cl z (by linarith) hδ hcap) hreg hne happ

/-- **Order-zero regularity at the origin on cluster balls**: one constant `φ` with
`componentBallL2 C z r (u - φ) ≤ C (r / R) B` for `r ∈ [X ∨ C, R / 2]`, for any bound `B > 0` of
`D_0(R) + R E`. -/
theorem armstrongDario_orderZero_origin_cluster (d : ℕ) {A α K δ CH : ℝ} (hA : 2 ≤ A)
    (hα : 0 < α) (hK : 0 ≤ K) (hδ : 0 < δ) (hCH : 0 ≤ CH) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ω : Configuration d) (Cl : OpenComponent ω) (z : Vertex d)
      (Abar : ℝ → Set (Cl → ℝ)) (R X E : ℝ) (u : Cl → ℝ),
      1 ≤ X → X ≤ R / A → 0 ≤ E →
      ClusterBallVolumeComparison Cl z X R K → ClusterBallCapDensity Cl z X R δ →
      HarmonicRegularity (componentBallSeminorm Cl z) Abar (clusterAffine Cl) 1 X R CH →
      (∀ r : ℝ, X ≤ r → r ≤ R / A → (Abar r).Nonempty) →
      HarmonicApproximation (componentBallSeminorm Cl z) Abar (clusterConstants Cl) A α X R E u →
      ∀ B : ℝ, 0 < B →
        ballExcess (componentBallSeminorm Cl z) (clusterConstants Cl) R u + R * E ≤ B →
        ∃ φ ∈ clusterConstants Cl, ∀ r : ℝ, max X C ≤ r → r ≤ R / 2 →
          componentBallL2 Cl z r (u - φ) ≤ C * (r / R) * B := by
  obtain ⟨C, hC, h⟩ := armstrongDario_orderZero_origin.{0} (γ := (d : ℝ) / 2)
    (CV := Real.sqrt K) (CP := 2 / Real.sqrt δ) (CG := 1) hA hα (by positivity)
    (Real.sqrt_nonneg K) (by positivity) hCH zero_le_one
  refine ⟨C, hC, fun ω Cl z Abar R X E u hX hXR hE hvol hcap hreg hne happ => ?_⟩
  have hgrowth : PolynomialGrowth (componentBallSeminorm Cl z) (clusterConstants Cl) 0 X R 1 :=
    polynomialGrowth_clusterConstants Cl z fun ρ hρ hρR =>
      Finset.card_pos.1 (hcap ρ hρ hρR).1
  exact h (componentBallSeminorm Cl z) (clusterConstants Cl) (clusterAffine Cl) Abar R X E u
    (clusterConstants_le_clusterAffine Cl) hX hXR hE
    (radiusMonotone_componentBallSeminorm Cl z (by linarith) hK hvol)
    (polynomialComparison_componentBallSeminorm Cl z (by linarith) hδ hcap) hreg hne happ hgrowth

theorem ClusterBallVolumeComparison.of_le {d : ℕ} {ω : Configuration d} {C : OpenComponent ω}
    {z : Vertex d} {X X' R K : ℝ} (h : ClusterBallVolumeComparison C z X R K) (hX : X ≤ X') :
    ClusterBallVolumeComparison C z X' R K :=
  fun s r hs hsr hr => h s r (hX.trans hs) hsr hr

theorem ClusterBallCapDensity.of_le {d : ℕ} {ω : Configuration d} {C : OpenComponent ω}
    {z : Vertex d} {X X' R δ : ℝ} (h : ClusterBallCapDensity C z X R δ) (hX : X ≤ X') :
    ClusterBallCapDensity C z X' R δ :=
  fun ρ hρ hρR => h ρ (hX.trans hρ) hρR

/-- **Armstrong–Dario, Lemma 7.2 (`k = 0`), on cluster balls, from the density in cubes.** -/
theorem armstrongDario_lemma_7_2_zero_of_clusterCubeDensity (d : ℕ) (hd : 0 < d)
    {A α κ CH : ℝ} (hA : 2 ≤ A) (hα : 0 < α) (hκ : 0 < κ) (hCH : 0 ≤ CH) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ω : Configuration d) (Cl : OpenComponent ω) (z : Vertex d)
      (Abar : ℝ → Set (Cl → ℝ)) (R X E ℓ : ℝ) (u : Cl → ℝ),
      1 ≤ X → X ≤ R / A → 0 ≤ E → 24 * Real.sqrt d * max ℓ 1 ≤ X →
      ClusterCubeDensity Cl z (24 * Real.sqrt d) ℓ κ →
      HarmonicRegularity (componentBallSeminorm Cl z) Abar (clusterAffine Cl) 1 X R CH →
      (∀ r : ℝ, X ≤ r → r ≤ R / A → (Abar r).Nonempty) →
      HarmonicApproximation (componentBallSeminorm Cl z) Abar (clusterConstants Cl) A α X R E u →
      ∀ r : ℝ, max X C ≤ r → r ≤ R / 2 →
        ballExcess (componentBallSeminorm Cl z) (clusterConstants Cl) r u ≤
          C * (r / R) * ballExcess (componentBallSeminorm Cl z) (clusterConstants Cl) R u +
            C * r ^ (1 - α) *
              (ballExcess (componentBallSeminorm Cl z) (clusterConstants Cl) R u / R + E / r) := by
  obtain ⟨C, hC, h⟩ := armstrongDario_lemma_7_2_zero_cluster d
    (K := (5 * (6 * Real.sqrt d)) ^ d / κ)
    (δ := κ / (5 * (24 * Real.sqrt d)) ^ d) hA hα (by positivity) (by positivity) hCH
  refine ⟨C, hC, fun ω Cl z Abar R X E ℓ u hX hXR hE hXℓ hcube hreg hne happ => ?_⟩
  have h6 : 6 * Real.sqrt d * max ℓ 1 ≤ X := by
    have : 0 ≤ Real.sqrt d * max ℓ 1 :=
      mul_nonneg (Real.sqrt_nonneg _) ((zero_le_one).trans (le_max_right _ _))
    linarith
  exact h ω Cl z Abar R X E u hX hXR hE
    ((clusterBallVolumeComparison_of_clusterCubeDensity Cl z R hd hκ hcube).of_le h6)
    ((clusterBallCapDensity_of_clusterCubeDensity Cl z R hd hκ hcube).of_le hXℓ) hreg hne happ

/-- **Order-zero regularity at the origin on cluster balls, from the density in cubes.** -/
theorem armstrongDario_orderZero_origin_of_clusterCubeDensity (d : ℕ) (hd : 0 < d)
    {A α κ CH : ℝ} (hA : 2 ≤ A) (hα : 0 < α) (hκ : 0 < κ) (hCH : 0 ≤ CH) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ω : Configuration d) (Cl : OpenComponent ω) (z : Vertex d)
      (Abar : ℝ → Set (Cl → ℝ)) (R X E ℓ : ℝ) (u : Cl → ℝ),
      1 ≤ X → X ≤ R / A → 0 ≤ E → 24 * Real.sqrt d * max ℓ 1 ≤ X →
      ClusterCubeDensity Cl z (24 * Real.sqrt d) ℓ κ →
      HarmonicRegularity (componentBallSeminorm Cl z) Abar (clusterAffine Cl) 1 X R CH →
      (∀ r : ℝ, X ≤ r → r ≤ R / A → (Abar r).Nonempty) →
      HarmonicApproximation (componentBallSeminorm Cl z) Abar (clusterConstants Cl) A α X R E u →
      ∀ B : ℝ, 0 < B →
        ballExcess (componentBallSeminorm Cl z) (clusterConstants Cl) R u + R * E ≤ B →
        ∃ φ ∈ clusterConstants Cl, ∀ r : ℝ, max X C ≤ r → r ≤ R / 2 →
          componentBallL2 Cl z r (u - φ) ≤ C * (r / R) * B := by
  obtain ⟨C, hC, h⟩ := armstrongDario_orderZero_origin_cluster d
    (K := (5 * (6 * Real.sqrt d)) ^ d / κ) (δ := κ / (5 * (24 * Real.sqrt d)) ^ d) hA hα
    (by positivity) (by positivity) hCH
  refine ⟨C, hC, fun ω Cl z Abar R X E ℓ u hX hXR hE hXℓ hcube hreg hne happ => ?_⟩
  have h6 : 6 * Real.sqrt d * max ℓ 1 ≤ X := by
    have : 0 ≤ Real.sqrt d * max ℓ 1 :=
      mul_nonneg (Real.sqrt_nonneg _) ((zero_le_one).trans (le_max_right _ _))
    linarith
  exact h ω Cl z Abar R X E u hX hXR hE
    ((clusterBallVolumeComparison_of_clusterCubeDensity Cl z R hd hκ hcube).of_le h6)
    ((clusterBallCapDensity_of_clusterCubeDensity Cl z R hd hκ hcube).of_le hXℓ) hreg hne happ

end Rigidity.Proofs.Regularity
