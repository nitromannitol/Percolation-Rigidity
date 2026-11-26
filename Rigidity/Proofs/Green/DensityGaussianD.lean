import Rigidity.Proofs.Green.DensityGaussianBoundD
import Rigidity.Proofs.Green.DarioGuDensityGaussian
import Rigidity.Proofs.Green.NamedInputsD
import PercolationClusterHomogenization.Proofs.Density.ClusterDensityConcentration

/-!
# Proposition A.7 of Dario–Gu on `ℤ^d`

The `d`-dimensional form of `DarioGuDensityGaussian.lean`: for `d ≥ 2` and every `α > 0` there are
`C, s > 0` and, for every `y ∈ ℤ^d`, a minimal time `T_dense,α(y) ≤ O_s(C)` with

`|Σ_{x ∈ 𝒞_∞} p̄(t, x - y) - θ(p)| ≤ C t^{-(1/2 - α)}` for every `t > T_dense,α(y)`

(`darioGuDensityGaussianD_holds`, the statement `DarioGuDensityGaussianD`), from Proposition A.1
on `ℤ^d` (`cluster_density_concentration`), the multiscale bound `abs_sum_gaussianHeatD_mul_le`, the
mass `abs_tsum_gaussianHeatD_sub_one_le` and the far mass `sum_gaussianHeatD_far_le` of the
Gaussian kernel on `ℤ^d`. A scale `k` is bad if one of the `(37 · 3^{nk})^d` cubes of scale `k`
around `y` has density at distance at least `(3^k)^{α - 1}` from `θ`.
-/

open MeasureTheory Finset LatticeProb.Percolation Rigidity.External Rigidity.Proofs.S2

namespace Rigidity.Green

local notation "ldist" => Rigidity.WeakPoincare.latticeDist

variable {d : ℕ}

/-! ### The deviation of the cluster from its density -/

/-- `1_{x ∈ 𝒞_∞} - θ`, where `x ∈ 𝒞_∞` is the event that the open cluster of `x` is infinite. -/
noncomputable def clusterDeviationD (ω : Configuration d) (θ : ℝ) (x : Vertex d) : ℝ :=
  (infiniteComponentEvent x).indicator (fun _ => (1 : ℝ)) ω - θ

theorem abs_clusterDeviation_leD {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (ω : Configuration d)
    (x : Vertex d) : |clusterDeviationD ω θ x| ≤ 1 := by
  unfold clusterDeviationD
  by_cases hx : ω ∈ infiniteComponentEvent x
  · rw [Set.indicator_of_mem hx, abs_le]
    constructor <;> linarith
  · rw [Set.indicator_of_notMem hx, abs_le]
    constructor <;> linarith

/-- The average of `1_{𝒞_∞} - θ` on a triadic cube is `|𝒞_∞ ∩ □|/|□| - θ`. -/
theorem cubeMean_clusterDeviationD (ω : Configuration d) (θ : ℝ) (k : ℕ) (j : Vertex d) :
    cubeMeanD (clusterDeviationD ω θ) k j =
      (infiniteClusterCount (triadicCube d k j) ω : ℝ) / ((triadicCube d k j).ncard : ℝ) - θ := by
  classical
  have hsum : ∑ x ∈ triadicCubeFinset d k j, (infiniteComponentEvent x).indicator
      (fun _ => (1 : ℝ)) ω =
      (((triadicCubeFinset d k j).filter fun y => ω ∈ infiniteComponentEvent y).card : ℝ) := by
    rw [Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases hy : ω ∈ infiniteComponentEvent y <;> simp [hy]
  have h9 : ((triadicCube d k j).ncard : ℝ) = ((3 : ℝ) ^ d) ^ k := by
    rw [ncard_triadicCube, pow_mul]
    norm_num
  rw [cubeMeanD, h9, infiniteClusterCount_triadicCube]
  simp only [clusterDeviationD, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  rw [hsum, card_triadicCubeFinsetD]
  field_simp

theorem measurable_cubeMean_clusterDeviationD (θ : ℝ) (k : ℕ) (j : Vertex d) :
    Measurable fun ω => cubeMeanD (clusterDeviationD ω θ) k j := by
  simp only [cubeMean_clusterDeviationD]
  exact ((measurable_infiniteClusterCount_triadicCube k j).div_const _).sub_const _

/-! ### Bad scales -/

/-- The scale `k` is bad: some cube of scale `k` whose index is within `18 · 3^{nk}` of that of
`y` has density at distance at least `(3^k)^{α - 1}` from `θ`. -/
def densityBadScaleD (y : Vertex d) (n : ℕ) (α θ : ℝ) (k : ℕ) : Set (Configuration d) :=
  ⋃ j ∈ indexBoxD (cubeIndexD k y) ((18 * 3 ^ (n * k) : ℕ) : ℤ),
    {ω | ((3 : ℝ) ^ k) ^ (α - 1) ≤ |cubeMeanD (clusterDeviationD ω θ) k j|}

theorem measurableSet_densityBadScaleD (y : Vertex d) (n : ℕ) (α θ : ℝ) (k : ℕ) :
    MeasurableSet (densityBadScaleD y n α θ k) :=
  Finset.measurableSet_biUnion _ fun j _ =>
    measurableSet_le measurable_const (measurable_cubeMean_clusterDeviationD θ k j).abs

/-- `3^{αk} / C ≤ (3^k)^{α - 1} / (C 3^{-dk/2})` for `d ≥ 2`. -/
theorem div_le_rpow_sub_one_divD {C α : ℝ} (hC : 0 < C) (hd : 2 ≤ d) (k : ℕ) :
    ((3 : ℝ) ^ α) ^ k / C ≤
      ((3 : ℝ) ^ k) ^ (α - 1) / (C * (3 : ℝ) ^ (-((d : ℝ) * (k : ℝ)) / 2)) := by
  have h3 : (0 : ℝ) < 3 ^ k := by positivity
  have e : (3 : ℝ) ^ (-((d : ℝ) * (k : ℝ)) / 2) = ((3 : ℝ) ^ ((d : ℝ) * (k : ℝ) / 2))⁻¹ := by
    rw [show -((d : ℝ) * (k : ℝ)) / 2 = -((d : ℝ) * (k : ℝ) / 2) by ring,
      Real.rpow_neg (by norm_num)]
  have hk : (3 : ℝ) ^ k ≤ (3 : ℝ) ^ ((d : ℝ) * (k : ℝ) / 2) := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  rw [e, ← pow_mul_rpow_sub_one α k]
  have h0 : 0 ≤ ((3 : ℝ) ^ k) ^ (α - 1) := by positivity
  calc 3 ^ k * ((3 : ℝ) ^ k) ^ (α - 1) / C = ((3 : ℝ) ^ k) ^ (α - 1) * 3 ^ k / C := by ring
    _ ≤ ((3 : ℝ) ^ k) ^ (α - 1) * (3 : ℝ) ^ ((d : ℝ) * (k : ℝ) / 2) / C := by gcongr
    _ = _ := by field_simp

/-- **Proposition A.1 and a union bound**:
`P[scale k bad] ≤ 2 · 37^d · 3^{dnk} exp(-(3^{αk}/C₁)^{s₀})`. -/
theorem measure_densityBadScale_leD (hd : 2 ≤ d) {p : unitInterval} {C₁ s₀ : ℝ} (hC₁ : 0 < C₁)
    (hs₀ : 0 < s₀)
    (hA1 : ∀ (m : ℕ) (k : Vertex d), IsOsBond d p
      (fun ω => |(infiniteClusterCount (triadicCube d m k) ω : ℝ) /
        ((triadicCube d m k).ncard : ℝ) - theta d p|) s₀
      (C₁ * (3 : ℝ) ^ (-((d : ℝ) * (m : ℝ)) / 2)))
    (y : Vertex d) (n : ℕ) (α : ℝ) (k : ℕ) :
    latticeBondLaw d p (densityBadScaleD y n α (theta d p) k) ≤
      ENNReal.ofReal ((2 * 37 ^ d) * ((3 : ℝ) ^ d) ^ (n * k) *
        Real.exp (-((((3 : ℝ) ^ α) ^ k / C₁) ^ s₀))) := by
  set c := 2 * Real.exp (-((((3 : ℝ) ^ α) ^ k / C₁) ^ s₀)) with hc
  have hc0 : 0 ≤ c := by positivity
  have hj : ∀ j, latticeBondLaw d p
      {ω | ((3 : ℝ) ^ k) ^ (α - 1) ≤ |cubeMeanD (clusterDeviationD ω (theta d p)) k j|} ≤
        ENNReal.ofReal c := by
    intro j
    have h := measure_le_le_of_isOsBond (by positivity) hs₀ (by positivity) (hA1 k j)
      (t := ((3 : ℝ) ^ k) ^ (α - 1))
    simp only [cubeMean_clusterDeviationD]
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hc]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.exp_le_exp.2
    apply neg_le_neg
    exact Real.rpow_le_rpow (by positivity) (div_le_rpow_sub_one_divD hC₁ hd k) hs₀.le
  set I := indexBoxD (cubeIndexD k y) ((18 * 3 ^ (n * k) : ℕ) : ℤ)
  have hI : (I.card : ℝ) ≤ 37 ^ d * ((3 : ℝ) ^ d) ^ (n * k) := by
    rw [card_indexBoxD]
    push_cast
    have h1 : (1 : ℝ) ≤ 3 ^ (n * k) := one_le_pow₀ (by norm_num)
    calc (2 * (18 * (3 : ℝ) ^ (n * k)) + 1) ^ d ≤ (37 * (3 : ℝ) ^ (n * k)) ^ d :=
          pow_le_pow_left₀ (by positivity) (by linarith) d
      _ = 37 ^ d * ((3 : ℝ) ^ d) ^ (n * k) := by
          rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm (n * k) d]
  calc latticeBondLaw d p (densityBadScaleD y n α (theta d p) k)
      ≤ ∑ j ∈ I, latticeBondLaw d p
          {ω | ((3 : ℝ) ^ k) ^ (α - 1) ≤ |cubeMeanD (clusterDeviationD ω (theta d p)) k j|} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ I, ENNReal.ofReal c := Finset.sum_le_sum fun j _ => hj j
    _ = ENNReal.ofReal ((I.card : ℝ) * c) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((2 * 37 ^ d) * ((3 : ℝ) ^ d) ^ (n * k) *
          Real.exp (-((((3 : ℝ) ^ α) ^ k / C₁) ^ s₀))) := by
        apply ENNReal.ofReal_le_ofReal
        rw [hc]
        have := Real.exp_pos (-((((3 : ℝ) ^ α) ^ k / C₁) ^ s₀))
        nlinarith

/-- The bounds on the probabilities of the bad scales are summable against `exp((3^{k+1})^s)`,
`s = α s₀ / 2`. -/
theorem summable_densityBadD {α s₀ C₁ : ℝ} (hα : 0 < α) (hs₀ : 0 < s₀) (hC₁ : 0 < C₁) (n : ℕ) :
    Summable fun k : ℕ => (2 * 37 ^ d) * ((3 : ℝ) ^ d) ^ (n * k) *
      Real.exp (-((((3 : ℝ) ^ α) ^ k / C₁) ^ s₀)) *
      Real.exp ((1 * 3 ^ (k + 1)) ^ (α * s₀ / 2)) := by
  set s := α * s₀ / 2 with hs
  have hs0 : 0 < s := by positivity
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  set τ := s * Real.log 3 with hτ
  have hτ0 : 0 < τ := mul_pos hs0 hl3
  have hv1 : ∀ k : ℕ, (((3 : ℝ) ^ α) ^ k / C₁) ^ s₀ = (C₁ ^ s₀)⁻¹ * Real.exp (τ * k) ^ 2 := by
    intro k
    rw [Real.div_rpow (by positivity) hC₁.le, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3),
      ← Real.exp_nat_mul, ← Real.exp_mul, sq, ← Real.exp_add, div_eq_inv_mul]
    congr 2
    rw [hτ, hs]
    ring
  have hv2 : ∀ k : ℕ, ((1 : ℝ) * 3 ^ (k + 1)) ^ s = 3 ^ s * Real.exp (τ * k) := by
    intro k
    rw [scale_exponent_eq (by norm_num) k, mul_one, hτ]
  have hv3 : ∀ k : ℕ, ((3 : ℝ) ^ d) ^ (n * k) ≤ Real.exp (d * n / s * Real.exp (τ * k)) := by
    intro k
    have e : ((3 : ℝ) ^ d) ^ (n * k) = Real.exp ((n * k : ℕ) * (d * Real.log 3)) := by
      rw [Real.exp_nat_mul, show (d : ℝ) * Real.log 3 = Real.log (3 ^ d) by rw [Real.log_pow],
        Real.exp_log (by positivity)]
    rw [e]
    apply Real.exp_le_exp.2
    have h1 : τ * k ≤ Real.exp (τ * k) := by
      have := Real.add_one_le_exp (τ * k)
      linarith
    have h2 : d * n / s * (τ * k) = (n * k : ℕ) * (d * Real.log 3) := by
      rw [hτ]
      push_cast
      field_simp
    rw [← h2]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    ((summable_exp_mul_sub_sq (d * n / s + 3 ^ s) (C₁ ^ s₀)⁻¹ τ (by positivity) hτ0).mul_left
      (2 * 37 ^ d))
  rw [hv1, hv2]
  calc (2 * 37 ^ d) * ((3 : ℝ) ^ d) ^ (n * k) * Real.exp (-((C₁ ^ s₀)⁻¹ * Real.exp (τ * k) ^ 2)) *
        Real.exp (3 ^ s * Real.exp (τ * k))
      ≤ (2 * 37 ^ d) * Real.exp (d * n / s * Real.exp (τ * k)) *
          Real.exp (-((C₁ ^ s₀)⁻¹ * Real.exp (τ * k) ^ 2)) *
          Real.exp (3 ^ s * Real.exp (τ * k)) := by
        gcongr
        exact hv3 k
    _ = (2 * 37 ^ d) * Real.exp ((d * n / s + 3 ^ s) * Real.exp (τ * k) -
          (C₁ ^ s₀)⁻¹ * Real.exp (τ * k) ^ 2) := by
        rw [mul_assoc (2 * 37 ^ d : ℝ), mul_assoc (2 * 37 ^ d : ℝ), ← Real.exp_add, ← Real.exp_add]
        congr 2
        ring

/-! ### Proposition A.7 -/

/-- **Dario–Gu, Proposition A.7**, (A.13), for `0 < α ≤ 1/4`, with `T_dense ≥ 81`. -/
theorem darioGuDensityGaussianD_of_le_quarter [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hp : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) {σ : ℝ} (hσ : 0 < σ) {α : ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) :
    ∃ C s : ℝ, 0 < C ∧ 0 < s ∧ ∀ y : Vertex d,
      ∃ T : Configuration d → ℝ, Measurable T ∧ (∀ ω, 81 ≤ T ω) ∧ IsOsBond d p T s C ∧
        ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω, ∀ t : ℝ, T ω < t →
          |∑' x : (uniqueInfiniteComponent h).supp, gaussianHeatD d σ t (edzD x.val y) -
            theta d p| ≤
            C * t ^ (-(1 / 2 - α)) := by
  obtain ⟨C₁, hC₁, hA1⟩ := cluster_density_concentration d hd p hp hp1
  set s₀ : ℝ := 2 * ((d : ℝ) - 1) / (3 * (d : ℝ) ^ 2 + 2 * (d : ℝ) - 1) with hs₀def
  have hs₀ : 0 < s₀ := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    rw [hs₀def]
    apply div_pos <;> nlinarith
  obtain ⟨CD, hCD, hdet⟩ := abs_sum_gaussianHeatD_mul_le (d := d) hσ hα hα4
  obtain ⟨Cm, hCm, hmass⟩ := abs_tsum_gaussianHeatD_sub_one_le (d := d) hσ
  obtain ⟨Cf, hCf, hfar⟩ := sum_gaussianHeatD_far_le (d := d) hσ
  set θ := theta d p with hθ
  have hθ0 : 0 ≤ θ := theta_nonneg d p
  have hθ1 : θ ≤ 1 := theta_le_one d p
  set n : ℕ := ⌈1 / α⌉₊ with hn
  set s := α * s₀ / 2 with hs
  have hs0 : 0 < s := by positivity
  set b : ℕ → ℝ := fun k => (2 * 37 ^ d) * ((3 : ℝ) ^ d) ^ (n * k) *
    Real.exp (-((((3 : ℝ) ^ α) ^ k / C₁) ^ s₀))
    with hb
  have hb0 : ∀ k, 0 ≤ b k := fun k => by positivity
  have hsum : Summable fun k => b k * Real.exp ((1 * 3 ^ (k + 1)) ^ s) :=
    summable_densityBadD hα hs₀ hC₁ n
  set B₁ := Real.exp ((1 : ℝ) ^ s) + ∑' k, b k * Real.exp ((1 * 3 ^ (k + 1)) ^ s) with hB₁
  have hB₁0 : 0 ≤ B₁ :=
    add_nonneg (Real.exp_pos _).le (tsum_nonneg fun k => mul_nonneg (hb0 k) (Real.exp_pos _).le)
  set A := Real.exp ((81 : ℝ) ^ (α * s)) + B₁ with hA
  have hA1' : 1 ≤ A := by
    have := Real.one_le_exp (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 81) (α * s))
    linarith
  set CT := 1 * A ^ (1 / (α * s)) with hCT
  have hCT0 : 0 < CT := by positivity
  refine ⟨max CT (CD + Cm + Cf), α * s, by positivity, by positivity, fun y => ?_⟩
  obtain ⟨M, hMm, hM0, hMint, hMle, hMae⟩ := exists_minimalScale_of_summable (latticeBondLaw d p)
    (densityBadScaleD y n α θ) (measurableSet_densityBadScaleD y n α θ) one_pos b hb0
    (measure_densityBadScale_leD hd hC₁ hs₀ hA1 y n α) hsum
  set T : Configuration d → ℝ := fun ω => max 81 (M ω ^ (1 / α)) with hT
  have hTm : Measurable T := measurable_const.max (hMm.pow_const _)
  have hT81 : ∀ ω, 81 ≤ T ω := fun ω => le_max_left _ _
  refine ⟨T, hTm, hT81, ?_, ?_⟩
  · -- `T ≤ O_{αs}(C)`
    have hpt : ∀ ω, Real.exp ((max (T ω / 1) 0).rpow (α * s)) ≤
        Real.exp ((81 : ℝ) ^ (α * s)) + Real.exp (M ω ^ s) := by
      intro ω
      have hTω : T ω = max 81 (M ω ^ (1 / α)) := rfl
      have hT0 : 0 ≤ T ω := by linarith [hT81 ω]
      rw [div_one, max_eq_left hT0]
      change Real.exp (T ω ^ (α * s)) ≤ _
      rcases le_total 81 (M ω ^ (1 / α)) with h | h
      · have e : T ω ^ (α * s) = M ω ^ s := by
          rw [hTω, max_eq_right h, ← Real.rpow_mul (hM0 ω)]
          congr 1
          field_simp
        rw [e]
        linarith [Real.exp_pos ((81 : ℝ) ^ (α * s))]
      · rw [hTω, max_eq_left h]
        linarith [Real.exp_pos (M ω ^ s)]
    have hmeas : Measurable fun ω => Real.exp ((max (T ω / 1) 0).rpow (α * s)) := by
      simpa only [Real.rpow_eq_pow] using
        ((((hTm.div_const 1).max measurable_const).pow_const (α * s)).exp)
    have hmaj : Integrable (fun ω => Real.exp ((81 : ℝ) ^ (α * s)) + Real.exp (M ω ^ s))
        (latticeBondLaw d p) := (integrable_const _).add hMint
    have hint : Integrable (fun ω => Real.exp ((max (T ω / 1) 0).rpow (α * s)))
        (latticeBondLaw d p) := by
      refine hmaj.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact hpt ω
    have hle : ∫ ω, Real.exp ((max (T ω / 1) 0).rpow (α * s)) ∂latticeBondLaw d p ≤ A := by
      calc ∫ ω, Real.exp ((max (T ω / 1) 0).rpow (α * s)) ∂latticeBondLaw d p
          ≤ ∫ ω, (Real.exp ((81 : ℝ) ^ (α * s)) + Real.exp (M ω ^ s)) ∂latticeBondLaw d p :=
            integral_mono hint hmaj hpt
        _ = Real.exp ((81 : ℝ) ^ (α * s)) + ∫ ω, Real.exp (M ω ^ s) ∂latticeBondLaw d p := by
            rw [integral_add (integrable_const _) hMint, integral_const, probReal_univ, one_smul]
        _ ≤ A := by
            rw [hA]
            exact add_le_add le_rfl hMle
    exact IsOsBond.mono_scale (by positivity) hCT0 (le_max_left _ _) hTm
      (isOsBond_of_integral_le (by positivity) hA1' hint hle)
  · filter_upwards [hMae] with ω hω h t ht
    obtain ⟨N, hMN, hgoodN⟩ := hω
    have ht81 : 81 < t := lt_of_le_of_lt (hT81 ω) ht
    have ht0 : 0 < t := by linarith
    have ht1 : 1 ≤ t := by linarith
    have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
    have hss := Real.mul_self_sqrt ht0.le
    -- `3^N < t^α`
    have hMt : M ω < t ^ α := by
      have h1 : M ω ^ (1 / α) < t := lt_of_le_of_lt (le_max_right _ _) ht
      have h2 := Real.rpow_lt_rpow (Real.rpow_nonneg (hM0 ω) _) h1 hα
      rwa [← Real.rpow_mul (hM0 ω), one_div_mul_cancel hα.ne', Real.rpow_one] at h2
    rw [hMN, one_mul] at hMt
    -- the top scale
    set K := Nat.log 3 ⌊Real.sqrt t⌋₊ with hK
    have hfl : ⌊Real.sqrt t⌋₊ ≠ 0 := by
      have : (1 : ℝ) ≤ Real.sqrt t := by
        rw [Real.one_le_sqrt]
        linarith
      exact (Nat.floor_pos.2 this).ne'
    have hK1 : (3 : ℝ) ^ K ≤ Real.sqrt t := by
      have h1 : 3 ^ K ≤ ⌊Real.sqrt t⌋₊ := Nat.pow_log_le_self 3 hfl
      have h2 : ((3 ^ K : ℕ) : ℝ) ≤ (⌊Real.sqrt t⌋₊ : ℝ) := by exact_mod_cast h1
      push_cast at h2
      exact h2.trans (Nat.floor_le hst.le)
    have hK2 : Real.sqrt t < 3 ^ (K + 1) := by
      have h1 : ⌊Real.sqrt t⌋₊ < 3 ^ (K + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
      have h2 : ((⌊Real.sqrt t⌋₊ + 1 : ℕ) : ℝ) ≤ ((3 ^ (K + 1) : ℕ) : ℝ) := by exact_mod_cast h1
      push_cast at h2
      linarith [Nat.lt_floor_add_one (Real.sqrt t)]
    have h9K : (9 : ℝ) ^ K ≤ t := by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, ← pow_mul, mul_comm, pow_mul]
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 3) K]
    have ht9 : t < (9 : ℝ) ^ (K + 1) := by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, ← pow_mul, mul_comm, pow_mul]
      nlinarith
    set S := gaussianRegionD K (3 ^ (K + 2)) y with hS
    set u := clusterDeviationD ω θ with hu
    have hu1 : ∀ x, |u x| ≤ 1 := abs_clusterDeviation_leD hθ0 hθ1 ω
    -- the good scales
    have hgood : ∀ k ≤ K, t ^ α ≤ (3 : ℝ) ^ k → ∀ x ∈ S,
        |cubeMeanD u k (cubeIndexD k x)| ≤ ((3 : ℝ) ^ k) ^ (α - 1) := by
      intro k hk htk x hx
      have hNk : N ≤ k := by
        have h1 : (3 : ℝ) ^ N < 3 ^ k := lt_of_lt_of_le hMt htk
        exact (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).1 h1 |>.le
      have hnot := hgoodN k hNk
      have htn : t ≤ (3 : ℝ) ^ (n * k) := by
        have h1 : t = (t ^ α) ^ (1 / α) := by
          rw [← Real.rpow_mul ht0.le, mul_one_div_cancel hα.ne', Real.rpow_one]
        have h3k : (1 : ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
        calc t = (t ^ α) ^ (1 / α) := h1
          _ ≤ ((3 : ℝ) ^ k) ^ (1 / α) :=
              Real.rpow_le_rpow (Real.rpow_nonneg ht0.le _) htk (by positivity)
          _ ≤ ((3 : ℝ) ^ k) ^ (n : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le h3k (Nat.le_ceil _)
          _ = (3 : ℝ) ^ (n * k) := by
              rw [Real.rpow_natCast, ← pow_mul, mul_comm]
      have hR : (2 * 9 ^ (K + 1) : ℤ) ≤ ((18 * 3 ^ (n * k) : ℕ) : ℤ) := by
        have h : (2 * 9 ^ (K + 1) : ℝ) ≤ 18 * 3 ^ (n * k) := by
          rw [pow_succ]
          linarith
        exact_mod_cast h
      have hmem : cubeIndexD k x ∈ indexBoxD (cubeIndexD k y) ((18 * 3 ^ (n * k) : ℕ) : ℤ) :=
        mem_indexBoxD.2 fun i => (abs_cubeIndex_sub_le_of_mem_gaussianRegionD hk hx i).trans hR
      by_contra hlt
      exact hnot (Set.mem_biUnion hmem (le_of_lt (not_le.1 hlt)))
    have hD := hdet t K ht81.le hK1 hK2 y S (isCubeUnion_gaussianRegionD _ _ _) u hu1 hgood
    -- the decomposition of the series
    set f : Vertex d → ℝ := fun x => gaussianHeatD d σ t (edzD x y) with hf
    have hf0 : ∀ x, 0 ≤ f x := fun x => gaussianHeatD_nonneg' σ t (by positivity) _
    have hfs : Summable f := summable_gaussianHeatD hσ ht0 y
    set g : Vertex d → ℝ := fun x => f x * u x with hg
    have hgf : ∀ x, |g x| ≤ f x := by
      intro x
      rw [hg, abs_mul, abs_of_nonneg (hf0 x)]
      exact mul_le_of_le_one_right (hf0 x) (hu1 x)
    have hgs : Summable g :=
      (hfs.of_nonneg_of_le (fun x => abs_nonneg _) hgf).of_abs
    have hsplit1 : ∑' x : (uniqueInfiniteComponent h).supp, gaussianHeatD d σ t (edzD x.val y) - θ =
        ∑' x, g x + θ * (∑' x, f x - 1) := by
      rw [tsum_subtype (uniqueInfiniteComponent h).supp f]
      have e : ∀ x, ((uniqueInfiniteComponent h).supp).indicator f x = g x + θ * f x := by
        intro x
        simp only [hg, hu, clusterDeviationD]
        by_cases hx : ω ∈ infiniteComponentEvent x
        · rw [Set.indicator_of_mem ((mem_uniqueInfiniteComponent_iff h x).2 hx),
            Set.indicator_of_mem hx]
          ring
        · rw [Set.indicator_of_notMem (mt (mem_uniqueInfiniteComponent_iff h x).1 hx),
            Set.indicator_of_notMem hx]
          ring
      rw [tsum_congr e, hgs.tsum_add (hfs.mul_left θ), tsum_mul_left]
      ring
    have hsplit2 : ∑' x, g x = ∑ x ∈ S, g x + ∑' x, ((S : Set (Vertex d))ᶜ).indicator g x := by
      calc ∑' x, g x = ∑' x, ((S : Set (Vertex d)).indicator g x +
            ((S : Set (Vertex d))ᶜ).indicator g x) :=
            tsum_congr fun x => (Set.indicator_self_add_compl_apply _ _ _).symm
        _ = ∑' x, (S : Set (Vertex d)).indicator g x +
            ∑' x, ((S : Set (Vertex d))ᶜ).indicator g x :=
            (hgs.indicator _).tsum_add (hgs.indicator _)
        _ = ∑ x ∈ S, g x + ∑' x, ((S : Set (Vertex d))ᶜ).indicator g x := by
            congr 1
            rw [tsum_eq_sum (s := S) fun x hx => Set.indicator_of_notMem (by simpa using hx) _]
            exact Finset.sum_congr rfl fun x hx => Set.indicator_of_mem (by simpa using hx) _
    have htail : |∑' x, ((S : Set (Vertex d))ᶜ).indicator g x| ≤ Cf / Real.sqrt t := by
      have hs1 : Summable fun x => ‖((S : Set (Vertex d))ᶜ).indicator g x‖ :=
        (hgs.indicator _).norm
      calc |∑' x, ((S : Set (Vertex d))ᶜ).indicator g x|
          ≤ ∑' x, ‖((S : Set (Vertex d))ᶜ).indicator g x‖ := norm_tsum_le_tsum_norm hs1
        _ ≤ ∑' x, ((S : Set (Vertex d))ᶜ).indicator f x := by
            refine Summable.tsum_le_tsum (fun x => ?_) hs1 (hfs.indicator _)
            by_cases hx : x ∈ (S : Set (Vertex d))ᶜ
            · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Real.norm_eq_abs]
              exact hgf x
            · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, norm_zero]
        _ ≤ Cf / Real.sqrt t := by
            refine tsum_le_of_sum_le' (by positivity) fun s => ?_
            classical
            have e : ∑ x ∈ s, ((S : Set (Vertex d))ᶜ).indicator f x =
                ∑ x ∈ s.filter (fun x => x ∉ S), f x := by
              rw [Finset.sum_filter]
              refine Finset.sum_congr rfl fun x _ => ?_
              simp only [Set.indicator_apply, Set.mem_compl_iff, Finset.mem_coe]
            rw [e]
            refine hfar t ht1 y _ fun x hx => ?_
            have hxS : x ∉ S := (Finset.mem_filter.1 hx).2
            exact ht9.le.trans (le_latticeDist_of_notMem_gaussianRegionD hxS)
    have hmass' : |θ * (∑' x, f x - 1)| ≤ Cm / Real.sqrt t := by
      rw [abs_mul, abs_of_nonneg hθ0]
      calc θ * |∑' x, f x - 1| ≤ 1 * (Cm / Real.sqrt t) :=
            mul_le_mul hθ1 (hmass t ht1 y) (abs_nonneg _) zero_le_one
        _ = Cm / Real.sqrt t := one_mul _
    have hsqrt : (Real.sqrt t)⁻¹ ≤ t ^ (-(1 / 2 - α)) := by
      rw [← rpow_neg_half_eq ht0]
      exact Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
    have he0 : 0 ≤ t ^ (-(1 / 2 - α)) := Real.rpow_nonneg ht0.le _
    rw [hsplit1, hsplit2]
    calc |∑ x ∈ S, g x + ∑' x, ((S : Set (Vertex d))ᶜ).indicator g x + θ * (∑' x, f x - 1)|
        ≤ |∑ x ∈ S, g x| + |∑' x, ((S : Set (Vertex d))ᶜ).indicator g x| +
            |θ * (∑' x, f x - 1)| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ CD * t ^ (-(1 / 2 - α)) + Cf / Real.sqrt t + Cm / Real.sqrt t :=
          add_le_add (add_le_add hD htail) hmass'
      _ ≤ CD * t ^ (-(1 / 2 - α)) + Cf * t ^ (-(1 / 2 - α)) + Cm * t ^ (-(1 / 2 - α)) := by
          have h1 : Cf / Real.sqrt t ≤ Cf * t ^ (-(1 / 2 - α)) := by
            rw [div_eq_mul_inv Cf]
            exact mul_le_mul_of_nonneg_left hsqrt hCf.le
          have h2 : Cm / Real.sqrt t ≤ Cm * t ^ (-(1 / 2 - α)) := by
            rw [div_eq_mul_inv Cm]
            exact mul_le_mul_of_nonneg_left hsqrt hCm.le
          linarith
      _ = (CD + Cm + Cf) * t ^ (-(1 / 2 - α)) := by ring
      _ ≤ max CT (CD + Cm + Cf) * t ^ (-(1 / 2 - α)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) he0

/-- The Gaussian mass of a component as a sum over its vertices. -/
theorem clusterGaussMass_eq_tsum_subtype {ω : Configuration d} (K : OpenComponent ω) (σ t : ℝ)
    (y : Vertex d) :
    clusterGaussMass K σ t y = ∑' x : K.supp, gaussianHeatD d σ t (edzD x.val y) := by
  classical
  rw [clusterGaussMass, tsum_subtype K.supp (fun x => gaussianHeatD d σ t (edzD x y))]
  refine tsum_congr fun x => ?_
  simp only [clusterInd, Set.indicator_apply]

/-- **Dario–Gu, Proposition A.7** (the second part, (A.13)), on `ℤ^d`, `d ≥ 2`: the Gaussian mass
of the infinite cluster is within `C t^{-(1/2 - α)}` of `θ(p)` for `t > T_dense,α(y)`,
`T_dense,α(y) ≤ O_s(C)`. -/
theorem darioGuDensityGaussianD_holds [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hp : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) {σ : ℝ} (hσ : 0 < σ) :
    DarioGuDensityGaussianD d p σ := by
  intro α hα
  obtain ⟨C, s, hC, hs, h⟩ := darioGuDensityGaussianD_of_le_quarter hd hp hp1 hσ
    (lt_min hα (by norm_num : (0 : ℝ) < 1 / 4)) (min_le_right _ _)
  refine ⟨C, s, hC, hs, fun y => ?_⟩
  obtain ⟨T, hTm, hT81, hTos, hae⟩ := h y
  refine ⟨T, hTm, fun ω => by linarith [hT81 ω], hTos, ?_⟩
  filter_upwards [hae] with ω hω h t ht
  rw [clusterGaussMass_eq_tsum_subtype]
  refine (hω h t ht).trans (mul_le_mul_of_nonneg_left ?_ hC.le)
  exact Real.rpow_le_rpow_of_exponent_le (by linarith [hT81 ω])
    (by linarith [min_le_left α (1 / 4)])

end Rigidity.Green
