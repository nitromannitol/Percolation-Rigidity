import Rigidity.Proofs.Regularity.ClusterQuadraticComparison
import Rigidity.Proofs.Regularity.ClusterKIteration

/-!
# Lemma 7.2 of Armstrong–Dario on cluster balls, order one

The case `k = 1` of the abstract Lemma 7.2 of Armstrong and Dario (arXiv:1609.09431v2),
`armstrongDario_lemma_7_2_one`, specialized to the normalized `L²` norms `componentBallL2` on the
balls of an open cluster centred at `z`, with the constants, the affine functions and a subgroup
`P₂` of the quadratic functions containing the affine functions (for instance the restrictions of
the `ā`-harmonic quadratic polynomials) as `Ā_0 ≤ Ā_1 ≤ Ā_2`. The polynomial comparison of the
quadratic functions over the affine functions (`polynomialComparison_clusterQuadratic`) and the
other properties of the cluster balls follow from a lower bound on the density of the cluster in
the triadic cubes of size `3^m ≥ ℓ` inside `B_{Λ 3^m}(z)` with `Λ = quadLocality d δ`; the class
`Abar` of harmonic functions and its excess decay of orders one and two remain hypotheses.
-/

namespace Rigidity.Proofs.Regularity

open LatticeProb LatticeProb.Percolation Rigidity.External

variable {F : Type*} [AddCommGroup F]

theorem PolynomialComparison.mono_const (N : ℝ → AddGroupSeminorm F) {Plow Phigh : AddSubgroup F}
    {j : ℕ} {X R CP CP' : ℝ} (hX : 0 ≤ X) (h : PolynomialComparison N Plow Phigh j X R CP)
    (hCP : CP ≤ CP') : PolynomialComparison N Plow Phigh j X R CP' := by
  intro w hw ρ ρ' hXρ hρρ' hρ'R
  have hρ0 : 0 ≤ ρ / ρ' := div_nonneg (hX.trans hXρ) ((hX.trans hXρ).trans hρρ')
  exact (h w hw ρ ρ' hXρ hρρ' hρ'R).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hCP (pow_nonneg hρ0 _)) (ballExcess_nonneg _ _ _ _))

theorem PolynomialComparison.of_le_high (N : ℝ → AddGroupSeminorm F)
    {Plow Phigh Phigh' : AddSubgroup F} {j : ℕ} {X R CP : ℝ}
    (h : PolynomialComparison N Plow Phigh j X R CP) (hP : Phigh' ≤ Phigh) :
    PolynomialComparison N Plow Phigh' j X R CP :=
  fun w hw => h w (hP hw)

variable {d : ℕ} {ω : Configuration d}

theorem quadLowerConst_pos (hd : 0 < d) {κ δ : ℝ} (hκ : 0 < κ) (hδ : 0 < δ) :
    0 < quadLowerConst d κ δ := by
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 (Nat.cast_pos.2 hd)
  have hL : 0 < quadSlopeConst d δ := by
    rw [quadSlopeConst]; have : (0 : ℝ) < d := Nat.cast_pos.2 hd; positivity
  have hΛ : 0 < quadLocality d δ := by rw [quadLocality]; positivity
  have hf : 0 < quadFraction d κ δ := by rw [quadFraction]; positivity
  rw [quadLowerConst]
  exact lt_min (Nat.cast_pos.2 hd) (by positivity)

theorem capFraction_pos (hd : 0 < d) {κ : ℝ} (hκ : 0 < κ) : 0 < capFraction d κ := by
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 (Nat.cast_pos.2 hd)
  rw [capFraction]; positivity

theorem le_quadLocality (hd : 0 < d) {δ : ℝ} (hδ : 0 < δ) :
    24 * Real.sqrt d ≤ quadLocality d δ := by
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 (Nat.cast_pos.2 hd)
  have hd1 : (1 : ℝ) ≤ d := Nat.one_le_cast.2 hd
  have hL : 1 ≤ quadSlopeConst d δ := by
    rw [quadSlopeConst]
    have : 0 ≤ 4 * (d : ℝ) / Real.sqrt δ := by positivity
    linarith
  rw [quadLocality]
  nlinarith

/-- **Polynomial comparison for quadratic functions over affine functions on cluster balls**, with
degree `2`, from the density of the cluster in cubes. -/
theorem polynomialComparison_clusterQuadratic (C : OpenComponent ω) (z : Vertex d) {ℓ κ : ℝ}
    (R : ℝ) (hd : 0 < d) (hκ : 0 < κ)
    (hcube : ClusterCubeDensity C z (quadLocality d (capFraction d κ)) ℓ κ) :
    PolynomialComparison (componentBallSeminorm C z) (clusterAffine C) (clusterQuadratic C) 2
      (quadLocality d (capFraction d κ) * max ℓ 1) R
      (d / quadLowerConst d κ (capFraction d κ)) := by
  rintro w ⟨a, p, M, hw⟩ ρ ρ' hXρ hρρ' _
  have hne : (Finset.univ : Finset (Fin d × Fin d)).Nonempty :=
    ⟨(⟨0, hd⟩, ⟨0, hd⟩), Finset.mem_univ _⟩
  obtain ⟨⟨i₀, j₀⟩, -, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun ij : Fin d × Fin d => |symEntry M ij.1 ij.2|) hne
  set m := |symEntry M i₀ j₀| with hmdef
  have hm : ∀ i j, |symEntry M i j| ≤ m := fun i j => hmax (i, j) (Finset.mem_univ _)
  have hm0 : 0 ≤ m := abs_nonneg _
  have hc₂ := quadLowerConst_pos hd hκ (capFraction_pos hd hκ)
  have hΛ := le_quadLocality hd (capFraction_pos hd hκ)
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 (Nat.cast_pos.2 hd)
  have hX0 : 0 < quadLocality d (capFraction d κ) * max ℓ 1 :=
    mul_pos (by linarith) (lt_of_lt_of_le one_pos (le_max_right _ _))
  have hρ0 : 0 < ρ := hX0.trans_le hXρ
  have hρ'0 : 0 < ρ' := hρ0.trans_le hρρ'
  have hup := ballExcess_clusterQuadratic_le C z (ρ := ρ) hw hm0 hm
  have hlow := le_ballExcess_clusterQuadratic C z hd hκ hcube (hXρ.trans hρρ') hw hm hmdef.symm
  set c₂ := quadLowerConst d κ (capFraction d κ)
  calc ballExcess (componentBallSeminorm C z) (clusterAffine C) ρ w ≤ d * m * ρ ^ 2 := hup
    _ = d / c₂ * (ρ / ρ') ^ 2 * (c₂ * m * ρ' ^ 2) := by field_simp
    _ ≤ d / c₂ * (ρ / ρ') ^ 2 *
        ballExcess (componentBallSeminorm C z) (clusterAffine C) ρ' w :=
        mul_le_mul_of_nonneg_left hlow (by positivity)

/-- **Armstrong–Dario, Lemma 7.2 (`k = 1`), on cluster balls, from the density in cubes**, with
`Ā_2 = P₂` any subgroup of the quadratic functions on the cluster containing the affine
functions. -/
theorem armstrongDario_lemma_7_2_one_of_clusterCubeDensity (d : ℕ) (hd : 0 < d)
    {A α κ CH : ℝ} (hA : 2 ≤ A) (hα : 0 < α) (hκ : 0 < κ) (hCH : 0 ≤ CH) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ω : Configuration d) (Cl : OpenComponent ω) (z : Vertex d)
      (P₂ : AddSubgroup (Cl → ℝ)) (Abar : ℝ → Set (Cl → ℝ)) (R X E ℓ : ℝ) (u : Cl → ℝ),
      clusterAffine Cl ≤ P₂ → P₂ ≤ clusterQuadratic Cl →
      1 ≤ X → X ≤ R / A → 0 ≤ E → quadLocality d (capFraction d κ) * max ℓ 1 ≤ X →
      ClusterCubeDensity Cl z (quadLocality d (capFraction d κ)) ℓ κ →
      HarmonicRegularity (componentBallSeminorm Cl z) Abar (clusterAffine Cl) 1 X R CH →
      HarmonicRegularity (componentBallSeminorm Cl z) Abar P₂ 2 X R CH →
      (∀ r : ℝ, X ≤ r → r ≤ R / A → (Abar r).Nonempty) →
      HarmonicApproximation (componentBallSeminorm Cl z) Abar (clusterConstants Cl) A α X R E u →
      ∀ r : ℝ, max X C ≤ r → r ≤ R / 2 →
        ballExcess (componentBallSeminorm Cl z) (clusterAffine Cl) r u ≤
          C * (r / R) ^ 2 * ballExcess (componentBallSeminorm Cl z) (clusterAffine Cl) R u +
            C * r ^ (1 - α) *
              (ballExcess (componentBallSeminorm Cl z) (clusterConstants Cl) R u / R + E / r) := by
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 (Nat.cast_pos.2 hd)
  have hδ := capFraction_pos hd hκ
  have hc₂ := quadLowerConst_pos hd hκ hδ
  have hΛ := le_quadLocality hd hδ
  set δ := capFraction d κ with hδdef
  set K := (5 * (6 * Real.sqrt d)) ^ d / κ with hK
  set CP := max (2 / Real.sqrt δ) (d / quadLowerConst d κ δ) with hCP
  obtain ⟨C, hC, h⟩ := armstrongDario_lemma_7_2_one.{0} (γ := (d : ℝ) / 2) (CV := Real.sqrt K)
    (CP := CP) hA hα (by positivity) (Real.sqrt_nonneg K)
    ((by positivity : (0 : ℝ) ≤ 2 / Real.sqrt δ).trans (le_max_left _ _)) hCH
  refine ⟨C, hC, fun ω Cl z P₂ Abar R X E ℓ u hAP hPQ hX hXR hE hXℓ hcube hreg₁ hreg₂ hne happ =>
    ?_⟩
  have hX0 : 0 < X := by linarith
  have hmax0 : 0 ≤ max ℓ 1 := zero_le_one.trans (le_max_right _ _)
  have hcube24 := hcube.of_le Cl z hΛ
  have h24 : 24 * Real.sqrt d * max ℓ 1 ≤ X :=
    (mul_le_mul_of_nonneg_right hΛ hmax0).trans hXℓ
  have h6 : 6 * Real.sqrt d * max ℓ 1 ≤ X := by
    have : 0 ≤ Real.sqrt d * max ℓ 1 := mul_nonneg hsd.le hmax0
    linarith
  have hvol := (clusterBallVolumeComparison_of_clusterCubeDensity Cl z R hd hκ hcube24).of_le h6
  have hcap : ClusterBallCapDensity Cl z X R δ :=
    (clusterBallCapDensity_of_clusterCubeDensity Cl z R hd hκ hcube24).of_le h24
  have hmono := radiusMonotone_componentBallSeminorm Cl z hX0 (by positivity) hvol
  have hpc₁ : PolynomialComparison (componentBallSeminorm Cl z) (clusterConstants Cl)
      (clusterAffine Cl) 1 X R CP :=
    (polynomialComparison_componentBallSeminorm Cl z hX0 hδ hcap).mono_const _ hX0.le
      (le_max_left _ _)
  have hpc₂ : PolynomialComparison (componentBallSeminorm Cl z) (clusterAffine Cl) P₂ 2 X R CP :=
    ((((polynomialComparison_clusterQuadratic Cl z R hd hκ hcube).of_le_high _
      hPQ).of_le _ hXℓ).mono_const _ hX0.le (le_max_right _ _))
  exact h (componentBallSeminorm Cl z) (clusterConstants Cl) (clusterAffine Cl) P₂ Abar R X E u
    (clusterConstants_le_clusterAffine Cl) hAP hX hXR hE hmono hpc₁ hpc₂ hreg₁ hreg₂ hne happ

end Rigidity.Proofs.Regularity
