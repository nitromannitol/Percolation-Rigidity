import Rigidity.External.ArmstrongDarioRegularity
import Rigidity.Proofs.Regularity.ClusterOrderOne
import Rigidity.Proofs.Regularity.InfiniteClusterBalls
import LatticeProb.External.SupercriticalBondCorrectorInput

/-!
# Regularity of order one at the origin from the mesoscopic estimate at degree two

Armstrong and Dario (arXiv:1609.09431v2), Lemma 7.3, prove the mesoscopic estimate (7.18): there
are `s, δ > 0`, a random scale `𝒳 ≤ O_s(C)` and, for each `k`, a constant `C(k)` such that for
`R ≥ 2 𝒳`, `u ∈ 𝒜(𝒞_∞ ∩ B_R)` and `r ∈ [𝒳, R / 2]`,
`inf_{w ∈ Ā_k} |B_r|^{-1/2} ‖u - w‖_{L²(𝒞_∞ ∩ B_r)} ≤
  C (r / R)^{k+1} inf_{w ∈ Ā_k} |B_R|^{-1/2} ‖u - w‖_{L²(𝒞_∞ ∩ B_R)} +
  C r^{-δ} (r / R) |B_R|^{-1/2} ‖u‖_{L²(𝒞_∞ ∩ B_R)}`.
`ArmstrongDarioMesoscopicDegreeTwo` is this statement at `k = 2` for bond percolation, at the
origin, with `Ā_2` the harmonic quadratic polynomials (`clusterHarmonicQuadratic`; the homogenized
matrix is `σ² I / 2`, p. 3 of the source) and `|B_r| = r^d` (`clusterBallVolumeL2`); the Lebesgue
measure `ω_d r^d` gives the same statement, the factor `ω_d^{-1/2}` appearing on both sides.

`armstrongDarioOrderOneOrigin_of_mesoscopicDegreeTwo` proves Theorem 2 (iii) at `k = 1`,
`Rigidity.External.ArmstrongDarioOrderOneOrigin`, from this estimate, the quantitative bound on the
first-order correctors `Rigidity.External.CorrectorQuantitativeInput` (with exponent `1/2`) and the
existence of the corrected planes in `LatticeProb.External.SupercriticalBondCorrectorInput`, by the
endpoint iteration `exists_forall_le_of_orderOneEndpoint`: the corrected planes of slope `eᵢ`,
normalized at a vertex of `𝒞_∞ ∩ B_𝒳`, lift the affine functions with relative error at most
`C t^{-1/2}` on `B_t`, and the density of the infinite cluster in cubes
(`Rigidity.Proofs.S2.cluster_density_concentration`) gives the comparison of the sizes of polynomials
with the normalized norms. The source deduces Theorem 2 from Lemma 7.3 by the argument of
Armstrong, Kuusi and Mourrat, Proposition 3.1, which lifts the polynomials of degree two; the
endpoint iteration lifts only the affine functions.
-/

namespace Rigidity.Proofs.Regularity

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External Rigidity.Proofs.S2

variable {d : ℕ} {ω : Configuration d}

/-- The normalization `r^{-d/2} ‖f‖_{L²(C ∩ B_r)}` of Armstrong–Dario, Lemma 7.3. -/
noncomputable def clusterBallVolumeL2 (C : OpenComponent ω) (r : ℝ) (f : C → ℝ) : ℝ :=
  Real.sqrt ((∑ x ∈ componentEuclideanBall C 0 r, f x ^ 2) / r ^ d)

/-- **Armstrong–Dario, Lemma 7.3, (7.18) at `k = 2`** (arXiv:1609.09431v2), for bond percolation
at the origin, with `Ā_2` the harmonic quadratic polynomials and the normalization
`r^{-d/2} ‖·‖_{L²(𝒞_∞ ∩ B_r)}`. The infima are over the nonempty subgroup `Ā_2` of nonnegative
quantities. -/
def ArmstrongDarioMesoscopicDegreeTwo : Prop :=
  ∀ (d : ℕ) [NeZero d], 2 ≤ d → ∀ p : unitInterval,
    criticalProbability d < (p : ℝ) → (p : ℝ) < 1 →
    ∃ s C₀ δ : ℝ, 0 < s ∧ 0 < C₀ ∧ 0 < δ ∧
      ∃ X : Configuration d → ℝ, Measurable X ∧ (∀ ω, 0 ≤ X ω) ∧ IsOsBond d p X s C₀ ∧
      ∃ C : ℝ, ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω,
        ∀ R : ℝ, 2 * X ω ≤ R → ∀ u : uniqueInfiniteComponent h → ℝ,
          (∀ z ∈ componentEuclideanBall (uniqueInfiniteComponent h) 0 R,
            (∀ w, (componentGraph (uniqueInfiniteComponent h)).Adj z w →
              w ∈ componentEuclideanBall (uniqueInfiniteComponent h) 0 R) →
            componentLaplacian (uniqueInfiniteComponent h) u z = 0) →
          ∀ r : ℝ, X ω ≤ r → r ≤ R / 2 →
            (⨅ w : clusterHarmonicQuadratic (uniqueInfiniteComponent h),
                clusterBallVolumeL2 (uniqueInfiniteComponent h) r (u - w)) ≤
              C * (r / R) ^ 3 * (⨅ w : clusterHarmonicQuadratic (uniqueInfiniteComponent h),
                  clusterBallVolumeL2 (uniqueInfiniteComponent h) R (u - w)) +
                C * r ^ (-δ) * (r / R) * clusterBallVolumeL2 (uniqueInfiniteComponent h) R u

theorem clusterBallVolumeL2_eq (C : OpenComponent ω) {r : ℝ} (hr : 0 ≤ r) (f : C → ℝ) :
    clusterBallVolumeL2 C r f =
      Real.sqrt (((componentEuclideanBall C 0 r).card : ℝ) / r ^ d) * componentBallL2 C 0 r f := by
  unfold clusterBallVolumeL2 componentBallL2
  rw [← Real.sqrt_mul (div_nonneg (Nat.cast_nonneg _) (pow_nonneg hr _))]
  congr 1
  rcases Nat.eq_zero_or_pos (componentEuclideanBall C 0 r).card with h0 | h0
  · rw [Finset.card_eq_zero.1 h0]
    simp
  · have : ((componentEuclideanBall C 0 r).card : ℝ) ≠ 0 := by exact_mod_cast h0.ne'
    field_simp

/-- **Passage from the normalization of Lemma 7.3 to the normalized norms**: under the volume
comparison of the cluster balls, (7.18) for `clusterBallVolumeL2` gives it for `componentBallL2`
with the constant multiplied by `√K`. -/
theorem ballExcess_le_of_clusterBallVolumeL2 (C : OpenComponent ω) {X R K A₀ δ v r : ℝ}
    {w : C → ℝ} (hK : 0 ≤ K) (hvol : ClusterBallVolumeComparison C 0 X R K) (hXv : X ≤ v)
    (hvr : v ≤ r) (hrR : r ≤ R) (hv0 : 0 < v) (hcard : 0 < (componentEuclideanBall C 0 v).card)
    (h : (⨅ q : clusterHarmonicQuadratic C, clusterBallVolumeL2 C v (w - q)) ≤
      A₀ * (v / r) ^ 3 * (⨅ q : clusterHarmonicQuadratic C, clusterBallVolumeL2 C r (w - q)) +
        A₀ * v ^ (-δ) * (v / r) * clusterBallVolumeL2 C r w) :
    ballExcess (componentBallSeminorm C 0) (clusterHarmonicQuadratic C) v w ≤
      Real.sqrt K * max A₀ 1 * (v / r) ^ 3 *
          ballExcess (componentBallSeminorm C 0) (clusterHarmonicQuadratic C) r w +
        Real.sqrt K * max A₀ 1 * v ^ (-δ) * (v / r) * componentBallSeminorm C 0 r w := by
  have hr0 : 0 < r := hv0.trans_le hvr
  set N := componentBallSeminorm C 0 with hN
  set P := clusterHarmonicQuadratic C with hP
  set c : ℝ → ℝ := fun t => Real.sqrt (((componentEuclideanBall C 0 t).card : ℝ) / t ^ d) with hc
  have hinf : ∀ t, 0 ≤ t → (⨅ q : P, clusterBallVolumeL2 C t (w - q)) = c t * ballExcess N P t w := by
    intro t ht
    rw [ballExcess, Real.mul_iInf_of_nonneg (Real.sqrt_nonneg _)]
    exact iInf_congr fun q => by rw [clusterBallVolumeL2_eq C ht, hN, componentBallSeminorm_apply]
  rw [hinf v hv0.le, hinf r hr0.le, clusterBallVolumeL2_eq C hr0.le] at h
  set Dv := ballExcess N P v w
  set Dr := ballExcess N P r w
  set Nr := componentBallL2 C 0 r w
  have hDr : 0 ≤ Dr := ballExcess_nonneg _ _ _ _
  have hNr : 0 ≤ Nr := componentBallL2_nonneg _ _ _ _
  have hcv : 0 < c v := by
    apply Real.sqrt_pos.2
    exact div_pos (by exact_mod_cast hcard) (by positivity)
  have hcr : c r ≤ Real.sqrt K * c v := by
    have hcount := hvol v r hXv hvr hrR
    have h1 : ((componentEuclideanBall C 0 r).card : ℝ) / r ^ d ≤
        K * (((componentEuclideanBall C 0 v).card : ℝ) / v ^ d) := by
      rw [div_le_iff₀ (by positivity)]
      calc ((componentEuclideanBall C 0 r).card : ℝ) ≤
            K * (r / v) ^ d * ((componentEuclideanBall C 0 v).card : ℝ) := hcount
        _ = K * (((componentEuclideanBall C 0 v).card : ℝ) / v ^ d) * r ^ d := by
            rw [div_pow]; field_simp
    calc c r ≤ Real.sqrt (K * (((componentEuclideanBall C 0 v).card : ℝ) / v ^ d)) :=
          Real.sqrt_le_sqrt h1
      _ = Real.sqrt K * c v := Real.sqrt_mul hK _
  have hA : A₀ ≤ max A₀ 1 := le_max_left _ _
  have hA1 : 0 ≤ max A₀ 1 := zero_le_one.trans (le_max_right _ _)
  have hvr0 : 0 ≤ v / r := div_nonneg hv0.le hr0.le
  have hδv : 0 ≤ v ^ (-δ) := Real.rpow_nonneg hv0.le _
  have hcr0 : 0 ≤ c r := Real.sqrt_nonneg _
  have h1 : A₀ * (v / r) ^ 3 * (c r * Dr) ≤ max A₀ 1 * (v / r) ^ 3 * (Real.sqrt K * c v * Dr) :=
    mul_le_mul (mul_le_mul_of_nonneg_right hA (by positivity))
      (mul_le_mul_of_nonneg_right hcr hDr) (mul_nonneg hcr0 hDr) (by positivity)
  have h2 : A₀ * v ^ (-δ) * (v / r) * (c r * Nr) ≤
      max A₀ 1 * v ^ (-δ) * (v / r) * (Real.sqrt K * c v * Nr) :=
    mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA hδv) hvr0)
      (mul_le_mul_of_nonneg_right hcr hNr) (mul_nonneg hcr0 hNr) (by positivity)
  have h3 : c v * Dv ≤ c v * (Real.sqrt K * max A₀ 1 * (v / r) ^ 3 * Dr +
      Real.sqrt K * max A₀ 1 * v ^ (-δ) * (v / r) * Nr) := by
    have e : c v * (Real.sqrt K * max A₀ 1 * (v / r) ^ 3 * Dr +
        Real.sqrt K * max A₀ 1 * v ^ (-δ) * (v / r) * Nr) =
        max A₀ 1 * (v / r) ^ 3 * (Real.sqrt K * c v * Dr) +
          max A₀ 1 * v ^ (-δ) * (v / r) * (Real.sqrt K * c v * Nr) := by ring
    rw [e]
    linarith only [h, h1, h2]
  rw [hN, componentBallSeminorm_apply]
  exact le_of_mul_le_mul_left h3 hcv

/-- Every vertex of an infinite open cluster has a neighbour in it. -/
theorem exists_adj_of_supp_infinite_cluster {C : OpenComponent ω} (hC : C.supp.Infinite) (y : C) :
    ∃ y' : C, (componentGraph C).Adj y y' := by
  obtain ⟨w, hw, hwy⟩ := hC.nontrivial.exists_ne y.val
  have hreach : (openGraph ω).Reachable y.val w :=
    SimpleGraph.ConnectedComponent.exact
      (((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 y.2).trans
        ((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 hw).symm)
  obtain ⟨q⟩ := hreach
  cases q with
  | nil => exact absurd rfl hwy
  | @cons _ v _ hadj _ =>
    have hv : v ∈ C.supp := C.mem_supp_of_adj_mem_supp y.2 hadj
    exact ⟨⟨v, hv⟩, (C.toSimpleGraph_adj y.2 hv).2 hadj⟩

theorem sum_single_mul (i : Fin d) (f : Fin d → ℝ) :
    ∑ j, (Pi.single i (1 : ℝ) : Fin d → ℝ) j * f j = f i := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [hj]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem sum_abs_single (i : Fin d) : ∑ j, |(Pi.single i (1 : ℝ) : Fin d → ℝ) j| = 1 := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [hj]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- **Armstrong–Dario, Theorem 2 (iii) at `k = 1`, at the origin**, from (7.18) at `k = 2`, the
quantitative bound on the correctors and the existence of the corrected planes. -/
theorem armstrongDarioOrderOneOrigin_of_mesoscopicDegreeTwo
    (hmeso : ArmstrongDarioMesoscopicDegreeTwo) (hcorr : CorrectorQuantitativeInput)
    (hqual : LatticeProb.External.SupercriticalBondCorrectorInput) :
    ArmstrongDarioOrderOneOrigin := by
  intro d _ hd p hpc hp1
  have hd0 : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  rcases (theta_nonneg d p).eq_or_lt with hθ0 | hθp
  · refine ⟨1, 1 * 3 ^ ((1 : ℝ) / 1), one_pos, by positivity, fun _ => 1, measurable_const,
      fun _ => zero_le_one, isOsBond_const one_pos one_pos, 0, ?_⟩
    filter_upwards [ae_not_hasUniqueInfiniteOpenComponent_of_theta_eq_zero p hθ0.symm] with ω hω h
    exact absurd h hω
  obtain ⟨s₁, C₁, δ, hs₁, hC₁, hδ, X₁, hX₁m, hX₁0, hX₁os, A₀, hae₁⟩ := hmeso d hd p hpc hp1
  set κ := theta d p / 2 with hκdef
  have hκ : 0 < κ := by positivity
  set Λ := quadLocality d (capFraction d κ) with hΛdef
  have hΛ24 := le_quadLocality hd0 (capFraction_pos hd0 hκ)
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 (Nat.cast_pos.2 hd0)
  have hΛ0 : 0 < Λ := by linarith
  obtain ⟨s₂, C₂, hs₂, hC₂, hcube⟩ := exists_clusterCubeDensity_of_concentration hd p
    (cluster_density_concentration d hd p hpc hp1) Λ
  obtain ⟨M₂, hM₂m, hM₂0, hM₂os, hae₂⟩ := hcube 0
  obtain ⟨s₃, C₃, hs₃, hC₃, hM⟩ := hcorr d hd p hpc hp1 (1 / 2) (by norm_num)
  obtain ⟨M₃, hM₃m, hM₃0, hM₃os, hae₃⟩ := hM 0
  have hae₄ := hqual d hd p hpc hp1
  -- deterministic constants
  set K := clusterVolumeConst d κ with hKdef
  have hK0 : 0 ≤ K := by rw [hKdef, clusterVolumeConst]; positivity
  set CV := Real.sqrt K with hCV
  set γ : ℝ := (d : ℝ) / 2 with hγ
  set CL := clusterPolyConst d κ with hCLdef
  have hCL : 0 ≤ CL := by
    have h1 := capFraction_pos hd0 hκ
    have h2 := quadLowerConst_pos hd0 hκ h1
    rw [hCLdef, clusterPolyConst]
    positivity
  set A := Real.sqrt K * max A₀ 1 with hAdef
  have hA : 0 ≤ A := mul_nonneg (Real.sqrt_nonneg _) (zero_le_one.trans (le_max_right _ _))
  set θ := 1 / (4 * A + 2) with hθdef
  have hθ : 0 < θ := by rw [hθdef]; positivity
  have hθ2 : θ ≤ 1 / 2 := by
    rw [hθdef, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hAθ : A * θ ≤ 1 / 4 := by
    rw [hθdef, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  set B := endpointSlopeConst A CV γ CL θ with hBdef
  have hB : 0 ≤ B := by
    rw [hBdef, endpointSlopeConst]
    have : 0 ≤ (1 / θ) ^ γ := Real.rpow_nonneg (by positivity) _
    have : 0 ≤ CV := Real.sqrt_nonneg _
    positivity
  set ε := 1 / (4 * B + 2 * CL + 1) with hεdef
  have hε : 0 < ε := by rw [hεdef]; positivity
  have hε1 : ε ≤ 1 := by
    rw [hεdef, div_le_one (by positivity)]; linarith
  have hεB : ε * B ≤ 1 / 4 := by
    rw [hεdef, one_div_mul_eq_div, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hCLε : CL * ε ≤ 1 / 2 := by
    rw [hεdef, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  set T := (C₃ * Real.sqrt d / ε) ^ 2 with hT
  have hT0 : 0 ≤ T := sq_nonneg _
  set c₀ := 2 * Λ + T + 2 with hc₀
  have hc₀0 : 0 < c₀ := by rw [hc₀]; positivity
  -- the random scale
  set s := min s₁ (min s₂ s₃) with hsdef
  have hs : 0 < s := lt_min hs₁ (lt_min hs₂ hs₃)
  have hs1 : s ≤ s₁ := min_le_left _ _
  have hs2 : s ≤ s₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hs3 : s ≤ s₃ := (min_le_right _ _).trans (min_le_right _ _)
  have h1os := IsOsBond.mono_exponent hs hs1 hX₁m hX₁os
  have h2os := IsOsBond.mono_exponent hs hs2 hM₂m hM₂os
  have h3os := IsOsBond.mono_exponent hs hs3 hM₃m hM₃os
  have h4os := isOsBond_const (d := d) (p := p) one_pos hs
  have h34 := IsOsBond.max hs (by positivity) (by positivity) hM₃m measurable_const h3os h4os
  have h234 := IsOsBond.max hs (by positivity) (by positivity) hM₂m
    (hM₃m.max measurable_const) h2os h34
  have h1234 := IsOsBond.max hs (by positivity) (by positivity) hX₁m
    (hM₂m.max (hM₃m.max measurable_const)) h1os h234
  have hXos := IsOsBond.const_mul hc₀0 h1234
  set Xs : Configuration d → ℝ := fun ω => c₀ * max (X₁ ω) (max (M₂ ω) (max (M₃ ω) 1)) with hXs
  refine ⟨s, _, hs, by positivity, Xs,
    (hX₁m.max (hM₂m.max (hM₃m.max measurable_const))).const_mul c₀, fun ω => ?_, hXos,
    singlePolynomialConst CV (2 * CL * (1 + ε)) γ 1 * endpointFitConst A δ CV γ d CL θ, ?_⟩
  · have : 0 ≤ max (X₁ ω) (max (M₂ ω) (max (M₃ ω) 1)) :=
      (hX₁0 ω).trans (le_max_left _ _)
    exact mul_nonneg hc₀0.le this
  filter_upwards [hae₁, hae₂, hae₃, hae₄] with ω h₁ h₂ h₃ h₄
  intro h R hR u hu
  set Cl := uniqueInfiniteComponent h with hCl
  have hc := h₂ h
  set m := max (X₁ ω) (max (M₂ ω) (max (M₃ ω) 1)) with hm
  have hm1 : 1 ≤ m := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hmX₁ : X₁ ω ≤ m := le_max_left _ _
  have hmM₂ : max (M₂ ω) 1 ≤ m :=
    max_le ((le_max_left _ _).trans (le_max_right _ _))
      (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _))
  have hmM₃ : M₃ ω ≤ m := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hXω : Xs ω = c₀ * m := rfl
  have hc₀1 : 1 ≤ c₀ := by rw [hc₀]; linarith
  have hmc : m ≤ c₀ * m := le_mul_of_one_le_left (by linarith) hc₀1
  have hcm : c₀ ≤ Xs ω := by rw [hXω]; exact le_mul_of_one_le_right hc₀0.le hm1
  have hXX₁ : X₁ ω ≤ Xs ω := by rw [hXω]; linarith only [hmX₁, hmc]
  have hXM₃ : M₃ ω ≤ Xs ω := by rw [hXω]; linarith only [hmM₃, hmc]
  have hXT : T ≤ Xs ω := by linarith only [hcm, hc₀, hΛ0]
  have hX2 : 2 ≤ Xs ω := by linarith only [hcm, hc₀, hΛ0, hT0]
  have hXΛ : 2 * Λ * max (M₂ ω) 1 ≤ Xs ω := by
    rw [hXω]
    have h1 : 2 * Λ * max (M₂ ω) 1 ≤ 2 * Λ * m := mul_le_mul_of_nonneg_left hmM₂ (by positivity)
    have h2 : 2 * Λ * m ≤ c₀ * m := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    linarith
  have hmax0 : 1 ≤ max (M₂ ω) 1 := le_max_right _ _
  have hsd1 : 1 ≤ Real.sqrt d := Real.one_le_sqrt.2 (Nat.one_le_cast.2 hd0)
  have hΛ1 : 1 ≤ Λ * max (M₂ ω) 1 := by
    have : Λ ≤ Λ * max (M₂ ω) 1 := le_mul_of_one_le_right hΛ0.le hmax0
    linarith only [this, hΛ24, hsd1]
  have hXΛ1 : Λ * max (M₂ ω) 1 ≤ Xs ω := by linarith only [hXΛ, hΛ1]
  have hXR : 2 * Xs ω ≤ R := hR
  have hX1 : 1 ≤ Xs ω := by linarith
  -- geometry of the balls of the cluster
  have hcube24 := hc.of_le Cl 0 hΛ24
  have h24 : 24 * Real.sqrt d * max (M₂ ω) 1 ≤ Λ * max (M₂ ω) 1 :=
    mul_le_mul_of_nonneg_right hΛ24 (by linarith)
  have h6 : 6 * Real.sqrt d * max (M₂ ω) 1 ≤ 24 * Real.sqrt d * max (M₂ ω) 1 := by
    have : 0 ≤ Real.sqrt d * max (M₂ ω) 1 := mul_nonneg hsd.le (by linarith)
    linarith
  have hvol := clusterBallVolumeComparison_of_clusterCubeDensity Cl 0 R hd0 hκ hcube24
  have hcapR := clusterBallCapDensity_of_clusterCubeDensity Cl 0 R hd0 hκ hcube24
  -- a vertex of the cluster in `B_{X - 1}` and a neighbour
  set ρ₀ := Xs ω - 1 with hρ₀
  have hρ₀24 : 24 * Real.sqrt d * max (M₂ ω) 1 ≤ ρ₀ := by
    rw [hρ₀]; linarith only [h24, hXΛ, hΛ1]
  have hcard₀ := ((clusterBallCapDensity_of_clusterCubeDensity Cl 0 ρ₀ hd0 hκ hcube24) ρ₀ hρ₀24
    le_rfl).1
  obtain ⟨a₀, ha₀⟩ := Finset.card_pos.1 hcard₀
  obtain ⟨a₁, ha₁⟩ := exists_adj_of_supp_infinite_cluster (uniqueInfiniteComponent_infinite h) a₀
  have ha₀n : ‖latticeEuclideanEmbedding a₀.val‖ < ρ₀ := norm_lt_of_mem_componentEuclideanBall ha₀
  have ha₁n : ‖latticeEuclideanEmbedding a₁.val‖ < Xs ω := by
    have hadj : (openGraph ω).Adj a₀.val a₁.val := (Cl.toSimpleGraph_adj a₀.2 a₁.2).1 ha₁
    have hd1 := dist_embedding_adj hadj
    have : ‖latticeEuclideanEmbedding a₁.val‖ ≤ ‖latticeEuclideanEmbedding a₀.val‖ +
        dist (latticeEuclideanEmbedding a₀.val) (latticeEuclideanEmbedding a₁.val) := by
      rw [dist_comm, dist_eq_norm]
      calc ‖latticeEuclideanEmbedding a₁.val‖ =
            ‖(latticeEuclideanEmbedding a₁.val - latticeEuclideanEmbedding a₀.val) +
              latticeEuclideanEmbedding a₀.val‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
        _ = _ := add_comm _ _
    linarith only [this, hd1, ha₀n, hρ₀]
  -- the corrected planes of slope `eᵢ` vanishing at `a₀`
  choose ℓc hℓc using fun i : Fin d => ((h₄ h).1 (Pi.single i 1) a₀).exists
  set g : Fin d → Cl → ℝ := fun i => ℓc i + fun _ => ((a₀.val i : ℤ) : ℝ) with hg
  have hgharm : ∀ i, g i ∈ harmonicGrowthSpace Cl 1 := fun i =>
    add_mem (hℓc i).1.1 (const_mem_harmonicGrowthSpace Cl 1 _)
  have hglift : ∀ t, Xs ω ≤ t → t ≤ R → ∀ i, ∀ x ∈ componentEuclideanBall Cl 0 t,
      |g i x - latticeEuclideanEmbedding x.val i| ≤ ε / Real.sqrt d * t := by
    intro t ht _ i x hx
    have ht0 : 0 < t := by linarith
    have hxn := norm_lt_of_mem_componentEuclideanBall hx
    have hb := h₃ h (Pi.single i 1) (ℓc i) (hℓc i).1 t (hXM₃.trans ht) x a₀ a₀ a₁
      (by rw [latticeEuclideanEmbedding_zero, sub_zero]; exact hxn)
      (by rw [latticeEuclideanEmbedding_zero, sub_zero]; linarith only [ha₀n, hρ₀, ht])
      (by rw [latticeEuclideanEmbedding_zero, sub_zero]; linarith only [ha₀n, hρ₀, ht])
      (by rw [latticeEuclideanEmbedding_zero, sub_zero]; linarith only [ha₁n, ht]) ha₁
    simp only [sum_single_mul, sum_abs_single, (hℓc i).2, mul_one] at hb
    have he : g i x - latticeEuclideanEmbedding x.val i =
        (ℓc i x - (x.val i : ℝ)) - (0 - (a₀.val i : ℝ)) := by
      show ℓc i x + ((a₀.val i : ℤ) : ℝ) - ((x.val i : ℤ) : ℝ) = _
      ring
    rw [he]
    have h1 := le_trans (le_add_of_nonneg_right (abs_nonneg _)) hb
    have hsq : t ^ (1 / 2 : ℝ) = Real.sqrt t := (Real.sqrt_eq_rpow t).symm
    rw [hsq] at h1
    have hst : C₃ * Real.sqrt d / ε ≤ Real.sqrt t := by
      rw [← Real.sqrt_sq (by positivity : 0 ≤ C₃ * Real.sqrt d / ε)]
      exact Real.sqrt_le_sqrt (hXT.trans ht)
    have h2 : C₃ * Real.sqrt t ≤ ε / Real.sqrt d * t := by
      have hs0 : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
      have hst2 : C₃ ≤ ε / Real.sqrt d * Real.sqrt t := by
        rw [div_le_iff₀ hε] at hst
        rw [div_mul_eq_mul_div, le_div_iff₀ hsd]
        linarith only [hst]
      calc C₃ * Real.sqrt t ≤ ε / Real.sqrt d * Real.sqrt t * Real.sqrt t :=
            mul_le_mul_of_nonneg_right hst2 hs0
        _ = ε / Real.sqrt d * t := by rw [mul_assoc, Real.mul_self_sqrt ht0.le]
    exact h1.trans h2
  -- the mesoscopic estimate in the normalized norms
  have hmeso' : ∀ r w, 2 * Xs ω ≤ r → r ≤ R → ClusterBallHarmonic Cl r w →
      ∀ v, Xs ω ≤ v → v ≤ r / 2 →
        ballExcess (componentBallSeminorm Cl 0) (clusterHarmonicQuadratic Cl) v w ≤
          A * (v / r) ^ 3 * ballExcess (componentBallSeminorm Cl 0) (clusterHarmonicQuadratic Cl)
            r w + A * v ^ (-δ) * (v / r) * componentBallSeminorm Cl 0 r w := by
    intro r w hr hrR hw v hv hvr
    have hv0 : 0 < v := by linarith
    have h7 := h₁ h r (by linarith) w hw v (hXX₁.trans hv) hvr
    have hcardv := (hcapR v (by linarith) (by linarith)).1
    have hvolv : ClusterBallVolumeComparison Cl 0 (6 * Real.sqrt d * max (M₂ ω) 1) R
        ((5 * (6 * Real.sqrt d)) ^ d / κ) := hvol
    have := ballExcess_le_of_clusterBallVolumeL2 Cl hK0 hvolv (by linarith) (by linarith) hrR hv0
      hcardv h7
    rw [hAdef]
    exact this
  have hD := orderOneEndpointData_cluster Cl hd0 (δ := δ) (A := A) hκ hε.le hc hXΛ1 hgharm hglift
    hmeso'
  have hγ0 : 0 ≤ γ := by rw [hγ]; positivity
  obtain ⟨ℓ, hℓ⟩ := exists_forall_le_of_orderOneEndpoint hD hX1 hA (Real.sqrt_nonneg _) hγ0
    (Nat.cast_pos.2 hd0) hCL hδ hθ hθ2 hAθ hε.le hε1 hεB hCLε hXR hu
  refine ⟨clusterLiftMap Cl g ℓ, clusterLiftMap_mem_harmonicGrowthSpace Cl hgharm ℓ, ?_⟩
  intro r hr hrR
  have := hℓ r hr hrR
  simpa only [componentBallSeminorm_apply] using this

end Rigidity.Proofs.Regularity
