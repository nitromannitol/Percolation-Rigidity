import Rigidity.Proofs.Regularity.OrderOneOrigin
import Rigidity.External.PlanarInputs

/-!
# Regularity of order one at the origin in the plane from (7.18) at degree two

`MesoscopicDegreeTwoAt d p` is the estimate (7.18) of Armstrong and Dario (arXiv:1609.09431v2),
Lemma 7.3, at `k = 2`, for bond percolation of parameter `p` in dimension `d`, at the origin, in the
normalization of `ArmstrongDarioMesoscopicDegreeTwo` (which is this statement for every `d ≥ 2` and
every supercritical `p`, `armstrongDarioMesoscopicDegreeTwo_iff`);
`ArmstrongDarioMesoscopicDegreeTwoPlanar` is its planar case. The reduction
`armstrongDarioOrderOneOrigin_of_mesoscopicDegreeTwo` runs in one dimension and for one law at a
time (`orderOneOrigin_of_mesoscopicDegreeTwoAt`), so that Theorem 2 (iii) at `k = 1` in the plane,
`Rigidity.External.ArmstrongDarioOrderOneOriginTwo`, follows from the planar (7.18) at `k = 2` and
the planar corrector inputs `Rigidity.External.CorrectorQuantitativeInputTwo` and
`Rigidity.External.SupercriticalBondCorrectorInputTwo`
(`armstrongDarioOrderOneOriginTwo_of_mesoscopicDegreeTwoPlanar`).
-/

namespace Rigidity.Proofs.Regularity

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External Rigidity.Proofs.S2

/-- **Armstrong–Dario, Lemma 7.3, (7.18) at `k = 2`**, in dimension `d` for the law of parameter
`p`, at the origin, with `Ā_2` the harmonic quadratic polynomials and the normalization
`r^{-d/2} ‖·‖_{L²(𝒞_∞ ∩ B_r)}`. -/
def MesoscopicDegreeTwoAt (d : ℕ) [NeZero d] (p : unitInterval) : Prop :=
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

theorem armstrongDarioMesoscopicDegreeTwo_iff :
    ArmstrongDarioMesoscopicDegreeTwo ↔ ∀ (d : ℕ) [NeZero d], 2 ≤ d → ∀ p : unitInterval,
      criticalProbability d < (p : ℝ) → (p : ℝ) < 1 → MesoscopicDegreeTwoAt d p :=
  Iff.rfl

/-- **Armstrong–Dario, Lemma 7.3, (7.18) at `k = 2`, in the plane.** -/
def ArmstrongDarioMesoscopicDegreeTwoPlanar : Prop :=
  ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 → MesoscopicDegreeTwoAt 2 p

/-- The all-dimensional estimate implies its planar case. -/
theorem armstrongDarioMesoscopicDegreeTwoPlanar_of_mesoscopicDegreeTwo
    (h : ArmstrongDarioMesoscopicDegreeTwo) : ArmstrongDarioMesoscopicDegreeTwoPlanar :=
  h 2 le_rfl

/-- **Armstrong–Dario, Theorem 2 (iii) at `k = 1`, at the origin, in one dimension and for one
law**, from (7.18) at `k = 2`, the quantitative bound on the correctors and the existence of the
corrected planes for that dimension and law. -/
theorem orderOneOrigin_of_mesoscopicDegreeTwoAt {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    {p : unitInterval} (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hmeso : MesoscopicDegreeTwoAt d p)
    (hcorr : ∀ α : ℝ, 0 < α → ∃ s C : ℝ, 0 < s ∧ 0 < C ∧ ∀ x : Vertex d,
      ∃ M : Configuration d → ℝ, Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧ IsOsBond d p M s C ∧
      ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω,
        ∀ (q : Fin d → ℝ) (ℓ : uniqueInfiniteComponent h → ℝ),
          IsCorrectedPlane (uniqueInfiniteComponent h) q ℓ →
        ∀ r : ℝ, M ω ≤ r →
        ∀ a b a' b' : uniqueInfiniteComponent h,
          ‖latticeEuclideanEmbedding a.val - latticeEuclideanEmbedding x‖ < r →
          ‖latticeEuclideanEmbedding b.val - latticeEuclideanEmbedding x‖ < r →
          ‖latticeEuclideanEmbedding a'.val - latticeEuclideanEmbedding x‖ < r →
          ‖latticeEuclideanEmbedding b'.val - latticeEuclideanEmbedding x‖ < r →
          (componentGraph (uniqueInfiniteComponent h)).Adj a' b' →
          |(ℓ a - ∑ i, q i * a.val i) - (ℓ b - ∑ i, q i * b.val i)| +
              |(ℓ a' - ∑ i, q i * a'.val i) - (ℓ b' - ∑ i, q i * b'.val i)|
            ≤ C * (∑ i, |q i|) * r ^ α)
    (hqual : ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω,
      (∀ q : Fin d → ℝ, ∀ o : uniqueInfiniteComponent h,
        ∃! u : uniqueInfiniteComponent h → ℝ,
          IsCorrectedPlane (uniqueInfiniteComponent h) q u ∧ u o = 0) ∧
      (∀ u : uniqueInfiniteComponent h → ℝ,
        u ∈ harmonicGrowthSpace (uniqueInfiniteComponent h) 1 →
        ∃! q : Fin d → ℝ, IsCorrectedPlane (uniqueInfiniteComponent h) q u)) :
    ∃ s C₀ : ℝ, 0 < s ∧ 0 < C₀ ∧
      ∃ X : Configuration d → ℝ, Measurable X ∧ (∀ ω, 0 ≤ X ω) ∧ IsOsBond d p X s C₀ ∧
      ∃ C : ℝ, ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω,
        ∀ R : ℝ, 2 * X ω ≤ R → ∀ u : uniqueInfiniteComponent h → ℝ,
          (∀ z ∈ componentEuclideanBall (uniqueInfiniteComponent h) 0 R,
            (∀ w, (componentGraph (uniqueInfiniteComponent h)).Adj z w →
              w ∈ componentEuclideanBall (uniqueInfiniteComponent h) 0 R) →
            componentLaplacian (uniqueInfiniteComponent h) u z = 0) →
          ∃ φ ∈ harmonicGrowthSpace (uniqueInfiniteComponent h) 1,
            ∀ r : ℝ, X ω ≤ r → r ≤ R / 2 →
              componentBallL2 (uniqueInfiniteComponent h) 0 r (u - φ) ≤
                C * (r / R) ^ 2 * componentBallL2 (uniqueInfiniteComponent h) 0 R u := by
  have hd0 : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  rcases (theta_nonneg d p).eq_or_lt with hθ0 | hθp
  · refine ⟨1, 1 * 3 ^ ((1 : ℝ) / 1), one_pos, by positivity, fun _ => 1, measurable_const,
      fun _ => zero_le_one, isOsBond_const one_pos one_pos, 0, ?_⟩
    filter_upwards [ae_not_hasUniqueInfiniteOpenComponent_of_theta_eq_zero p hθ0.symm] with ω hω h
    exact absurd h hω
  obtain ⟨s₁, C₁, δ, hs₁, hC₁, hδ, X₁, hX₁m, hX₁0, hX₁os, A₀, hae₁⟩ := hmeso
  set κ := theta d p / 2 with hκdef
  have hκ : 0 < κ := by positivity
  set Λ := quadLocality d (capFraction d κ) with hΛdef
  have hΛ24 := le_quadLocality hd0 (capFraction_pos hd0 hκ)
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 (Nat.cast_pos.2 hd0)
  have hΛ0 : 0 < Λ := by linarith
  obtain ⟨s₂, C₂, hs₂, hC₂, hcube⟩ := exists_clusterCubeDensity_of_concentration hd p
    (cluster_density_concentration d hd p hpc hp1) Λ
  obtain ⟨M₂, hM₂m, hM₂0, hM₂os, hae₂⟩ := hcube 0
  obtain ⟨s₃, C₃, hs₃, hC₃, hM⟩ := hcorr (1 / 2) (by norm_num)
  obtain ⟨M₃, hM₃m, hM₃0, hM₃os, hae₃⟩ := hM 0
  have hae₄ := hqual
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

/-- **Armstrong–Dario, Theorem 2 (iii) at `k = 1`, at the origin, in the plane**, from the planar
(7.18) at `k = 2`, the planar quantitative bound on the correctors and the planar existence of the
corrected planes. -/
theorem armstrongDarioOrderOneOriginTwo_of_mesoscopicDegreeTwoPlanar
    (hmeso : ArmstrongDarioMesoscopicDegreeTwoPlanar) (hcorr : CorrectorQuantitativeInputTwo)
    (hqual : SupercriticalBondCorrectorInputTwo) : ArmstrongDarioOrderOneOriginTwo :=
  fun p hpc hp1 => orderOneOrigin_of_mesoscopicDegreeTwoAt le_rfl hpc hp1 (hmeso p hpc hp1)
    (hcorr p hpc hp1) (hqual p hpc hp1)

end Rigidity.Proofs.Regularity
