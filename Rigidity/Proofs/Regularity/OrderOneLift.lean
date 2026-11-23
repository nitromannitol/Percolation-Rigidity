import Rigidity.Proofs.Regularity.OrderOneOrigin

/-!
# Every element of `𝒜_1` is a lifted affine function

Step 4 of the proof of Proposition 3.1 of Armstrong, Kuusi and Mourrat (arXiv:1602.00512v1), at
`k = 1`: a harmonic function on the cluster with growth `o(R²)` is a combination of the constants
and of the corrected planes of slopes `e₁, …, e_d`. Here it is deduced, for one configuration, from
(7.18) at `k = 2` of Armstrong and Dario (arXiv:1609.09431v2) and the density of the cluster in
cubes, through the endpoint iteration `exists_forall_le_of_orderOneEndpoint`: at every radius
`R ≥ 2 X` one lifted affine function `L ℓ_R` approximates `u` on `B_t` with the error
`C (t / R)² ‖u‖_{B_R}`, which tends to zero as `R → ∞` for `u ∈ 𝒜_1`; the sizes of the `ℓ_R` are
bounded, and a limit point `ℓ` of them satisfies `u = L ℓ` (`eq_clusterLiftMap_of_orderOne`).

Only the qualitative sublinearity `IsCorrectedPlane` of the corrected planes is used: the lift
error `ε t / √d` of the endpoint iteration holds above the radius `R₀` of `componentSlopeAsymptotics`
for that `ε`, and the scale above which the argument runs is finite but not controlled.
-/

namespace Rigidity.Proofs.Regularity

open Filter Topology MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External
  Rigidity.Proofs.S2

variable {d : ℕ} {ω : Configuration d}

/-- A function with zero normalized norm on a ball containing `x` vanishes at `x`. -/
theorem eq_zero_of_componentBallL2_eq_zero (C : OpenComponent ω) {r : ℝ} {f : C → ℝ}
    (h : componentBallL2 C 0 r f = 0) {x : C} (hx : x ∈ componentEuclideanBall C 0 r) :
    f x = 0 := by
  have hcard : (0 : ℝ) < (componentEuclideanBall C 0 r).card := by
    exact_mod_cast Finset.card_pos.2 ⟨x, hx⟩
  unfold componentBallL2 at h
  rw [Real.sqrt_eq_zero (div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) hcard.le),
    div_eq_zero_iff] at h
  rcases h with h | h
  · have := (Finset.sum_eq_zero_iff_of_nonneg fun y _ => sq_nonneg (f y)).1 h x hx
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
  · exact absurd h hcard.ne'

theorem continuous_affineSize (t : ℝ) :
    Continuous (affineSize (d := d) t) := by
  unfold affineSize
  fun_prop

theorem affineSize_zero (t : ℝ) : affineSize (d := d) t 0 = 0 := by
  simp [affineSize]

/-- **Step 4 of Proposition 3.1 at `k = 1` for one configuration.** -/
theorem eq_clusterLiftMap_of_orderOne [NeZero d] (C : OpenComponent ω) {κ M X₁ A₀ δ : ℝ}
    (hκ : 0 < κ) (hδ : 0 < δ)
    (hc : ClusterCubeDensity C 0 (quadLocality d (capFraction d κ)) M κ)
    (hmeso : ∀ R : ℝ, 2 * X₁ ≤ R → ∀ u : C → ℝ, ClusterBallHarmonic C R u →
      ∀ r : ℝ, X₁ ≤ r → r ≤ R / 2 →
        (⨅ w : clusterHarmonicQuadratic C, clusterBallVolumeL2 C r (u - w)) ≤
          A₀ * (r / R) ^ 3 * (⨅ w : clusterHarmonicQuadratic C, clusterBallVolumeL2 C R (u - w)) +
            A₀ * r ^ (-δ) * (r / R) * clusterBallVolumeL2 C R u)
    {g : Fin d → C → ℝ} (hg : ∀ i, IsCorrectedPlane C (Pi.single i 1) (g i))
    {u : C → ℝ} (hu : u ∈ harmonicGrowthSpace C 1) :
    ∃ ℓ, u = clusterLiftMap C g ℓ := by
  have hd0 : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  set Λ := quadLocality d (capFraction d κ) with hΛdef
  have hΛ24 := le_quadLocality hd0 (capFraction_pos hd0 hκ)
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 (Nat.cast_pos.2 hd0)
  have hΛ0 : 0 < Λ := by linarith
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
  -- the radii of the slope asymptotics
  choose R₀ hR₀ hR₀b using fun i => (hg i).2 (ε / Real.sqrt d) (by positivity)
  set S := ∑ i, R₀ i with hS
  have hRS : ∀ i, R₀ i ≤ S := fun i =>
    Finset.single_le_sum (fun j _ => (hR₀ j).le) (Finset.mem_univ i)
  -- the scale
  set c₀ := 2 * Λ + 2 with hc₀
  have hc₀0 : 0 < c₀ := by rw [hc₀]; positivity
  set m := max X₁ (max M (max S 1)) with hm
  have hm1 : 1 ≤ m := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hmX₁ : X₁ ≤ m := le_max_left _ _
  have hmM : max M 1 ≤ m :=
    max_le ((le_max_left _ _).trans (le_max_right _ _))
      (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _))
  have hmS : S ≤ m := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  set Xs := c₀ * m with hXs
  have hc₀1 : 1 ≤ c₀ := by rw [hc₀]; linarith
  have hmc : m ≤ c₀ * m := le_mul_of_one_le_left (by linarith) hc₀1
  have hcm : c₀ ≤ Xs := by rw [hXs]; exact le_mul_of_one_le_right hc₀0.le hm1
  have hXX₁ : X₁ ≤ Xs := by rw [hXs]; linarith only [hmX₁, hmc]
  have hXS : S ≤ Xs := by rw [hXs]; linarith only [hmS, hmc]
  have hX2 : 2 ≤ Xs := by linarith only [hcm, hc₀, hΛ0]
  have hXΛ : 2 * Λ * max M 1 ≤ Xs := by
    rw [hXs]
    have h1 : 2 * Λ * max M 1 ≤ 2 * Λ * m := mul_le_mul_of_nonneg_left hmM (by positivity)
    have h2 : 2 * Λ * m ≤ c₀ * m := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    linarith
  have hmax0 : 1 ≤ max M 1 := le_max_right _ _
  have hsd1 : 1 ≤ Real.sqrt d := Real.one_le_sqrt.2 (Nat.one_le_cast.2 hd0)
  have hΛ1 : 1 ≤ Λ * max M 1 := by
    have : Λ ≤ Λ * max M 1 := le_mul_of_one_le_right hΛ0.le hmax0
    linarith only [this, hΛ24, hsd1]
  have hXΛ1 : Λ * max M 1 ≤ Xs := by linarith only [hXΛ, hΛ1]
  have hX1 : 1 ≤ Xs := by linarith
  have hX0 : 0 < Xs := by linarith
  have hcube24 := hc.of_le C 0 hΛ24
  have h24 : 24 * Real.sqrt d * max M 1 ≤ Λ * max M 1 :=
    mul_le_mul_of_nonneg_right hΛ24 (by linarith)
  have h6 : 6 * Real.sqrt d * max M 1 ≤ 24 * Real.sqrt d * max M 1 := by
    have : 0 ≤ Real.sqrt d * max M 1 := mul_nonneg hsd.le (by linarith)
    linarith
  -- the lift of the affine functions
  have hgharm : ∀ i, g i ∈ harmonicGrowthSpace C 1 := fun i => (hg i).1
  have hglift : ∀ R t, Xs ≤ t → t ≤ R → ∀ i, ∀ x ∈ componentEuclideanBall C 0 t,
      |g i x - latticeEuclideanEmbedding x.val i| ≤ ε / Real.sqrt d * t := by
    intro R t ht _ i x hx
    have h := hR₀b i t ((hRS i).trans (hXS.trans ht)) x hx
    have e : componentSlope C (Pi.single i 1) x = latticeEuclideanEmbedding x.val i := by
      unfold componentSlope
      rw [sum_single_mul]
      rfl
    rwa [e] at h
  -- the mesoscopic estimate in the normalized norms
  have hmeso' : ∀ R, ∀ r w, 2 * Xs ≤ r → r ≤ R → ClusterBallHarmonic C r w →
      ∀ v, Xs ≤ v → v ≤ r / 2 →
        ballExcess (componentBallSeminorm C 0) (clusterHarmonicQuadratic C) v w ≤
          A * (v / r) ^ 3 * ballExcess (componentBallSeminorm C 0) (clusterHarmonicQuadratic C)
            r w + A * v ^ (-δ) * (v / r) * componentBallSeminorm C 0 r w := by
    intro R r w hr hrR hw v hv hvr
    have hv0 : 0 < v := by linarith
    have h7 := hmeso r (by linarith) w hw v (hXX₁.trans hv) hvr
    have hcapR := clusterBallCapDensity_of_clusterCubeDensity C 0 R hd0 hκ hcube24
    have hcardv := (hcapR v (by linarith) (by linarith)).1
    have hvolv : ClusterBallVolumeComparison C 0 (6 * Real.sqrt d * max M 1) R
        ((5 * (6 * Real.sqrt d)) ^ d / κ) :=
      clusterBallVolumeComparison_of_clusterCubeDensity C 0 R hd0 hκ hcube24
    have := ballExcess_le_of_clusterBallVolumeL2 C hK0 hvolv (by linarith) (by linarith) hrR hv0
      hcardv h7
    rw [hAdef]
    exact this
  have hD : ∀ R, OrderOneEndpointData (componentBallSeminorm C 0) (clusterHarmonicQuadratic C)
      (clusterAffineMap C) (clusterLiftMap C g) (clusterQuadMap C) affineSize quadSize
      (ClusterBallHarmonic C) Xs R A δ CV γ d CL ε := fun R =>
    orderOneEndpointData_cluster C hd0 (δ := δ) (A := A) hκ hε.le hc hXΛ1 hgharm (hglift R)
      (hmeso' R)
  have hγ0 : 0 ≤ γ := by rw [hγ]; positivity
  set Cf := singlePolynomialConst CV (2 * CL * (1 + ε)) γ 1 *
    endpointFitConst A δ CV γ d CL θ with hCf
  have hfit : ∀ R, 2 * Xs ≤ R → ∃ ℓ, ∀ t, Xs ≤ t → t ≤ R / 2 →
      componentBallL2 C 0 t (u - clusterLiftMap C g ℓ) ≤ Cf * (t / R) ^ 2 *
        componentBallL2 C 0 R u := by
    intro R hR
    have hu' : ClusterBallHarmonic C R u := fun z _ _ => hu.1 z
    obtain ⟨ℓ, hℓ⟩ := exists_forall_le_of_orderOneEndpoint (hD R) hX1 hA (Real.sqrt_nonneg _) hγ0
      (Nat.cast_pos.2 hd0) hCL hδ hθ hθ2 hAθ hε.le hε1 hεB hCLε hR hu'
    exact ⟨ℓ, fun t ht htR => by simpa only [componentBallSeminorm_apply] using hℓ t ht htR⟩
  -- the two comparisons of the sizes with the norms of the lifts
  have hlow : ∀ t, Xs ≤ t → ∀ ℓ,
      affineSize t ℓ ≤ 2 * CL * componentBallL2 C 0 t (clusterLiftMap C g ℓ) := by
    intro t ht ℓ
    have h1 := (hD t).le_poly t ht le_rfl ℓ 0
    have h2 := (hD t).lift_le t ht le_rfl ℓ
    rw [(hD t).nq_zero, mul_zero, add_zero, map_zero, add_zero] at h1
    have h3 : componentBallSeminorm C 0 t (clusterAffineMap C ℓ) ≤
        componentBallSeminorm C 0 t (clusterLiftMap C g ℓ) +
          componentBallSeminorm C 0 t (clusterLiftMap C g ℓ - clusterAffineMap C ℓ) := by
      have := map_sub_le_add (componentBallSeminorm C 0 t) (clusterLiftMap C g ℓ)
        (clusterLiftMap C g ℓ - clusterAffineMap C ℓ)
      rwa [sub_sub_cancel] at this
    have hsz := (hD t).sz_nonneg t ℓ ht
    simp only [componentBallSeminorm_apply] at h1 h2 h3 ⊢
    have k1 := mul_le_mul_of_nonneg_left (h3.trans (add_le_add le_rfl h2)) hCL
    have k2 := mul_le_mul_of_nonneg_right hCLε hsz
    linarith
  have hup : ∀ t, Xs ≤ t → ∀ ℓ,
      componentBallL2 C 0 t (clusterLiftMap C g ℓ) ≤ (1 + ε) * affineSize t ℓ := by
    intro t ht ℓ
    have h1 := (hD t).affine_le t ht le_rfl ℓ
    have h2 := (hD t).lift_le t ht le_rfl ℓ
    have h3 := map_add_le_add (componentBallSeminorm C 0 t) (clusterAffineMap C ℓ)
      (clusterLiftMap C g ℓ - clusterAffineMap C ℓ)
    rw [add_sub_cancel] at h3
    simp only [componentBallSeminorm_apply] at h1 h2 h3 ⊢
    linarith
  -- the radii
  have hgrow := hu.2
  obtain ⟨R₁, hR₁⟩ := (eventually_atTop.1 ((hgrow.eventually (ge_mem_nhds zero_lt_one))))
  set R₂ := max (2 * Xs) R₁ with hR₂
  set Rn : ℕ → ℝ := fun n => R₂ + n with hRn
  have hRn2 : ∀ n, 2 * Xs ≤ Rn n := fun n =>
    (le_max_left _ _).trans (le_add_of_nonneg_right (Nat.cast_nonneg n))
  have hRn1 : ∀ n, R₁ ≤ Rn n := fun n =>
    (le_max_right _ _).trans (le_add_of_nonneg_right (Nat.cast_nonneg n))
  have hRnpos : ∀ n, 0 < Rn n := fun n => by linarith [hRn2 n]
  have hRntop : Tendsto Rn atTop atTop :=
    tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
  choose ℓn hℓn using fun n => hfit (Rn n) (hRn2 n)
  -- the error at a fixed radius in terms of the growth
  have herr : ∀ n t, Xs ≤ t → t ≤ Rn n / 2 →
      componentBallL2 C 0 t (u - clusterLiftMap C g (ℓn n)) ≤
        Cf * t ^ 2 * (((Rn n) ^ (1 + 1))⁻¹ * componentBallL2 C 0 (Rn n) u) := by
    intro n t ht htR
    refine (hℓn n t ht htR).trans (le_of_eq ?_)
    rw [show ((Rn n) ^ (1 + 1))⁻¹ = ((Rn n) ^ 2)⁻¹ from rfl, div_pow, div_eq_mul_inv]
    ring
  -- the sizes of the slopes are bounded
  set Bd := 2 * CL * (componentBallL2 C 0 Xs u + |Cf| * Xs ^ 2) with hBd
  have hbound : ∀ n, affineSize Xs (ℓn n) ≤ Bd := by
    intro n
    have h1 := hlow Xs le_rfl (ℓn n)
    have h2 := herr n Xs le_rfl (by linarith [hRn2 n])
    have h3 : componentBallL2 C 0 Xs (clusterLiftMap C g (ℓn n)) ≤
        componentBallL2 C 0 Xs u + componentBallL2 C 0 Xs (u - clusterLiftMap C g (ℓn n)) := by
      have := map_sub_le_add (componentBallSeminorm C 0 Xs) u (u - clusterLiftMap C g (ℓn n))
      rw [sub_sub_cancel] at this
      simpa only [componentBallSeminorm_apply] using this
    set y := ((Rn n) ^ (1 + 1))⁻¹ * componentBallL2 C 0 (Rn n) u with hy
    have hy0 : 0 ≤ y := mul_nonneg (inv_nonneg.2 (pow_nonneg (hRnpos n).le _))
      (componentBallL2_nonneg C 0 _ u)
    have hy1 : y ≤ 1 := hR₁ _ (hRn1 n)
    have h4 : Cf * Xs ^ 2 * y ≤ |Cf| * Xs ^ 2 :=
      calc Cf * Xs ^ 2 * y ≤ |Cf| * Xs ^ 2 * y :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)) hy0
        _ ≤ |Cf| * Xs ^ 2 * 1 := mul_le_mul_of_nonneg_left hy1 (by positivity)
        _ = |Cf| * Xs ^ 2 := mul_one _
    have h5 : componentBallL2 C 0 Xs (clusterLiftMap C g (ℓn n)) ≤
        componentBallL2 C 0 Xs u + |Cf| * Xs ^ 2 := by linarith
    exact h1.trans (mul_le_mul_of_nonneg_left h5 (by positivity))
  set ρ := max Bd (Bd / Xs) with hρ
  have hmem : ∀ n, ℓn n ∈ Metric.closedBall (0 : ℝ × EuclideanSpace ℝ (Fin d)) ρ := by
    intro n
    rw [Metric.mem_closedBall, dist_zero_right, norm_prod_le_iff]
    have h := hbound n
    unfold affineSize at h
    have h1 := abs_nonneg (ℓn n).1
    have h2 := norm_nonneg (ℓn n).2
    have hXn : 0 ≤ Xs * ‖(ℓn n).2‖ := mul_nonneg hX0.le h2
    constructor
    · rw [Real.norm_eq_abs]
      exact le_max_of_le_left (by linarith)
    · refine le_max_of_le_right ?_
      rw [le_div_iff₀ hX0]
      linarith
  obtain ⟨ℓs, -, φ, hφ, hlim⟩ :=
    (isCompact_closedBall (0 : ℝ × EuclideanSpace ℝ (Fin d)) ρ).tendsto_subseq hmem
  have hRφ : Tendsto (fun k => Rn (φ k)) atTop atTop := hRntop.comp hφ.tendsto_atTop
  -- the limit point
  have hzero : ∀ t, Xs ≤ t → componentBallL2 C 0 t (u - clusterLiftMap C g ℓs) = 0 := by
    intro t ht
    have h1 : Tendsto (fun k => Cf * t ^ 2 *
        (((Rn (φ k)) ^ (1 + 1))⁻¹ * componentBallL2 C 0 (Rn (φ k)) u)) atTop
        (𝓝 (Cf * t ^ 2 * 0)) := (hgrow.comp hRφ).const_mul _
    have h2 : Tendsto (fun k => (1 + ε) * affineSize t (ℓn (φ k) - ℓs)) atTop
        (𝓝 ((1 + ε) * affineSize t (ℓs - ℓs))) :=
      (((continuous_affineSize t).tendsto _).comp (hlim.sub_const ℓs)).const_mul _
    rw [mul_zero] at h1
    rw [sub_self, affineSize_zero, mul_zero] at h2
    have hf := h1.add h2
    rw [add_zero] at hf
    have hev : ∀ᶠ k in atTop, componentBallL2 C 0 t (u - clusterLiftMap C g ℓs) ≤
        Cf * t ^ 2 * (((Rn (φ k)) ^ (1 + 1))⁻¹ * componentBallL2 C 0 (Rn (φ k)) u) +
          (1 + ε) * affineSize t (ℓn (φ k) - ℓs) := by
      filter_upwards [hRφ.eventually (eventually_ge_atTop (2 * t))] with k hk
      have e1 := herr (φ k) t ht (by linarith)
      have e2 := hup t ht (ℓn (φ k) - ℓs)
      have e3 : componentBallL2 C 0 t (u - clusterLiftMap C g ℓs) ≤
          componentBallL2 C 0 t (u - clusterLiftMap C g (ℓn (φ k))) +
            componentBallL2 C 0 t (clusterLiftMap C g (ℓn (φ k) - ℓs)) := by
        have := map_add_le_add (componentBallSeminorm C 0 t)
          (u - clusterLiftMap C g (ℓn (φ k))) (clusterLiftMap C g (ℓn (φ k) - ℓs))
        rw [map_sub (clusterLiftMap C g) (ℓn (φ k)) ℓs, sub_add_sub_cancel] at this
        rw [map_sub (clusterLiftMap C g) (ℓn (φ k)) ℓs]
        simpa only [componentBallSeminorm_apply] using this
      linarith
    exact le_antisymm (ge_of_tendsto hf hev) (componentBallL2_nonneg C 0 t _)
  refine ⟨ℓs, funext fun x => ?_⟩
  set t := max Xs (‖latticeEuclideanEmbedding x.val‖ + 1) with ht
  have hx : x ∈ componentEuclideanBall C 0 t := by
    rw [mem_componentEuclideanBall, latticeEuclideanEmbedding_zero, dist_zero_right]
    exact lt_of_lt_of_le (lt_add_one _) (le_max_right _ _)
  have := eq_zero_of_componentBallL2_eq_zero C (hzero t (le_max_left _ _)) hx
  rw [Pi.sub_apply, sub_eq_zero] at this
  exact this

end Rigidity.Proofs.Regularity
