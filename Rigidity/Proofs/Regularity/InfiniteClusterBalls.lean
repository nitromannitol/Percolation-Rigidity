import Rigidity.Proofs.S2.ClusterDensityConcentration
import Rigidity.Proofs.Regularity.ClusterCubeDensityOfConcentration
import Rigidity.Proofs.Regularity.ClusterKIteration

/-!
# Balls of the infinite cluster above a minimal scale

For supercritical bond percolation, `d ≥ 2`, `p_c(d) < p < 1`, and every centre `z`, there is a
minimal scale `M(z) ≤ O_s(C)` such that almost surely the balls of the infinite cluster centred at
`z` with radii at least `M(z)` satisfy the volume comparison `ClusterBallVolumeComparison` and the
cap density `ClusterBallCapDensity` with deterministic constants `K, δ > 0`
(`infiniteCluster_ballVolume_capDensity`). This combines the concentration of the density of the
infinite cluster in triadic cubes (Dario–Gu, Proposition A.1, proved as
`Rigidity.Proofs.S2.cluster_density_concentration`) with
`Rigidity.Proofs.Regularity.exists_clusterCubeDensity_of_concentration` and the deterministic
geometry of `Rigidity.Proofs.Regularity.ClusterBallGeometry`. These are the properties that the
iteration of Armstrong–Dario, Lemma 7.2 (arXiv:1609.09431v2), asks of the normalized norms on the
balls of the infinite cluster and of the affine functions on it
(`armstrongDario_lemma_7_2_zero_cluster`).
-/

namespace Rigidity.Proofs.Regularity

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External Rigidity.Proofs.S2

variable {d : ℕ}

/-- **Volume comparison and cap density of the balls of the infinite cluster above a minimal
scale.** -/
theorem infiniteCluster_ballVolume_capDensity [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∃ s C K δ : ℝ, 0 < s ∧ 0 < C ∧ 0 < K ∧ 0 < δ ∧ ∀ z : Vertex d,
      ∃ M : Configuration d → ℝ, Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧ IsOsBond d p M s C ∧
      ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω, ∀ R : ℝ,
        ClusterBallVolumeComparison (uniqueInfiniteComponent h) z (M ω) R K ∧
          ClusterBallCapDensity (uniqueInfiniteComponent h) z (M ω) R δ := by
  have hd0 : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  obtain ⟨s, C, hs, hC, hcube⟩ := exists_clusterCubeDensity_of_concentration hd p
    (cluster_density_concentration d hd p hpc hp1) (24 * Real.sqrt d)
  rcases (theta_nonneg d p).eq_or_lt with hθ0 | hθ
  · refine ⟨s, C, 1, 1, hs, hC, one_pos, one_pos, fun z => ?_⟩
    obtain ⟨M, hMm, hM0, hMos, -⟩ := hcube z
    refine ⟨M, hMm, hM0, hMos, ?_⟩
    filter_upwards [ae_not_hasUniqueInfiniteOpenComponent_of_theta_eq_zero p hθ0.symm] with ω hω h
    exact absurd h hω
  set κ := theta d p / 2 with hκ
  have hκ0 : 0 < κ := by positivity
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 (Nat.cast_pos.2 hd0)
  set a := 24 * Real.sqrt d with ha
  have ha0 : 0 < a := by positivity
  refine ⟨s, a * (max C (1 * 3 ^ (1 / s)) * 4 ^ (1 / s)), (5 * (6 * Real.sqrt d)) ^ d / κ,
    κ / (5 * (24 * Real.sqrt d)) ^ d, hs, by positivity, by positivity, by positivity,
    fun z => ?_⟩
  obtain ⟨M, hMm, hM0, hMos, hae⟩ := hcube z
  have hmax : IsOsBond d p (fun ω => max (M ω) 1) s (max C (1 * 3 ^ (1 / s)) * 4 ^ (1 / s)) :=
    IsOsBond.max hs hC (by positivity) hMm measurable_const hMos
      (isOsBond_const (p := p) one_pos hs)
  refine ⟨fun ω => a * max (M ω) 1, (hMm.max measurable_const).const_mul a,
    fun ω => by positivity, IsOsBond.const_mul ha0 hmax, ?_⟩
  filter_upwards [hae] with ω hω h R
  have hc := hω h
  constructor
  · refine (clusterBallVolumeComparison_of_clusterCubeDensity _ z R hd0 hκ0 hc).of_le ?_
    have : 0 ≤ Real.sqrt d * max (M ω) 1 :=
      mul_nonneg hsd.le ((zero_le_one).trans (le_max_right _ _))
    simp only [ha]
    linarith
  · exact clusterBallCapDensity_of_clusterCubeDensity _ z R hd0 hκ0 hc

/-- **Armstrong–Dario, Lemma 7.2 (`k = 0`), on the balls of the infinite cluster** above the
minimal scale of `infiniteCluster_ballVolume_capDensity`: the constants depend only on `d`, `p`,
`A`, `α` and the constant `CH` of the excess decay of the class `Abar` of harmonic functions, which
remains a hypothesis together with the harmonic approximation hypothesis. -/
theorem armstrongDario_lemma_7_2_zero_infiniteCluster [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) {A α CH : ℝ} (hA : 2 ≤ A)
    (hα : 0 < α) (hCH : 0 ≤ CH) :
    ∃ s C₀ C : ℝ, 0 < s ∧ 0 < C₀ ∧ 0 < C ∧ ∀ z : Vertex d,
      ∃ M : Configuration d → ℝ, Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧ IsOsBond d p M s C₀ ∧
      ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω,
        ∀ (Abar : ℝ → Set (uniqueInfiniteComponent h → ℝ)) (R X E : ℝ)
          (u : uniqueInfiniteComponent h → ℝ),
        1 ≤ X → M ω ≤ X → X ≤ R / A → 0 ≤ E →
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
            C * r ^ (1 - α) * (ballExcess (componentBallSeminorm (uniqueInfiniteComponent h) z)
              (clusterConstants (uniqueInfiniteComponent h)) R u / R + E / r) := by
  obtain ⟨s, C₀, K, δ, hs, hC₀, hK, hδ, hgeo⟩ := infiniteCluster_ballVolume_capDensity hd p hpc hp1
  obtain ⟨C, hC, hlemma⟩ := armstrongDario_lemma_7_2_zero_cluster d hA hα hK.le hδ hCH
  refine ⟨s, C₀, C, hs, hC₀, hC, fun z => ?_⟩
  obtain ⟨M, hMm, hM0, hMos, hae⟩ := hgeo z
  refine ⟨M, hMm, hM0, hMos, ?_⟩
  filter_upwards [hae] with ω hω h Abar R X E u hX hMX hXR hE hreg hne happ r hr hrR
  obtain ⟨hvol, hcap⟩ := hω h R
  exact hlemma ω (uniqueInfiniteComponent h) z Abar R X E u hX hXR hE (hvol.of_le hMX)
    (hcap.of_le hMX) hreg hne happ r hr hrR

end Rigidity.Proofs.Regularity
