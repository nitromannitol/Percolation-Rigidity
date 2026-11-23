import Rigidity.Proofs.Green.DarioGuTwoScaleDomination
import Rigidity.Proofs.Green.DarioGuTwoScaleEquation
import Rigidity.Proofs.Green.DarioGuFluxTranslateHolds

/-!
# The function `w` of Proposition 4.3 of Dario–Gu on the cluster

Step 1 of the proof of Proposition 4.3 of Dario–Gu in the form used by the energy argument. On
the cluster `K = 𝒞_∞`, with `f = 1_K h(τ, ·, y)` (`clusterInit`), the function
`u(s, x) = 1_K(x) (h(s, x, y) - P_{s-τ} f(x))` (`clusterW`) vanishes off the cluster and:

* `clusterW_self`: `u(τ, ·) = 0`;
* `clusterW_eq_dgW`: `u(s, x) = w(s, x, τ, y)` on the cluster, for `s ≥ τ`;
* `hasDerivAt_clusterW`: `∂_s u = Δ u + G` with `G = 1_K θ^{-1} twoScaleSource` (`clusterSource`),
  the equation (4.25) of `w`;
* `abs_dgTwoScale_le`, `abs_dgTwoScale_deriv_le`: the bounds of `h` and `∂_s h` by the neighbour
  envelope of the Gaussian envelope, when the corrector grows at most linearly on the cluster;
  `summable_sq_clusterInit`: `f` is square summable.
-/

open scoped Classical
open LatticeProb LatticeProb.Percolation

namespace Rigidity.Green

theorem mem_supp_of_reachable {ω : Configuration 2} {K : OpenComponent ω} {x z : Vertex 2}
    (hx : x ∈ K.supp) (h : (openGraph ω).Reachable x z) : z ∈ K.supp := by
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hx ⊢
  rw [← hx]
  exact (SimpleGraph.ConnectedComponent.sound h).symm

theorem openHeat_eq_zero_of_mem_of_notMem {ω : Configuration 2} {K : OpenComponent ω}
    {x z : Vertex 2} (hx : x ∈ K.supp) (hz : z ∉ K.supp) (s : ℝ) : openHeat ω s x z = 0 :=
  openHeat_eq_zero_of_not_reachable ω (fun h => hz (mem_supp_of_reachable hx h)) s

theorem sq_le_sq_of_abs_le {v w : ℝ} (h : |v| ≤ w) : v ^ 2 ≤ w ^ 2 := by
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) h 2

/-- `|h(s, x, y)| ≤ |θ^{-1}| (2πσa)^{-1} (1 + 2A) nbrEnv λ_{2σb} (x)` for `s ∈ [a, b]`. -/
theorem abs_dgTwoScale_le {σ θ a b s A : ℝ} {χ : Fin 2 → Vertex 2 → ℝ} {y x : Vertex 2}
    (hσ : 0 < σ) (ha : 0 < a) (has : a ≤ s) (hsb : s ≤ b) (hA : 0 ≤ A)
    (hχ : ∀ k, |χ k x| ≤ A * (1 + latticeDist x y)) :
    |dgTwoScale σ θ χ s x y| ≤
      |θ⁻¹| * ((2 * Real.pi * σ * a)⁻¹ * (1 + 2 * A)) * nbrEnv (gaussEnv (2 * σ * b) y) x := by
  have hs : 0 < s := ha.trans_le has
  have hP : ∀ z, |latticeGaussian σ s z y| ≤ (2 * Real.pi * σ * a)⁻¹ *
      ((1 + latticeDist z y) ^ 2 * Real.exp (-(latticeDist z y ^ 2 / (2 * σ * b)))) := by
    intro z
    rw [abs_of_nonneg (latticeGaussian_nonneg' hσ hs z y)]
    refine (latticeGaussian_le_of_mem hσ ha has hsb z y).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have := latticeDist_nonneg z y
    have h1 : (1 : ℝ) ≤ (1 + latticeDist z y) ^ 2 := by nlinarith
    nlinarith [Real.exp_pos (-(latticeDist z y ^ 2 / (2 * σ * b)))]
  have h := abs_twoScale_le (P := fun z => latticeGaussian σ s z y) (χ := χ) (by positivity) hA
    hP hχ
  have e : dgTwoScale σ θ χ s x y = θ⁻¹ * (latticeGaussian σ s x y + ∑ k : Fin 2,
      (latticeGaussian σ s (x + unit k) y - latticeGaussian σ s x y) * χ k x) := rfl
  rw [e]
  calc |θ⁻¹ * (latticeGaussian σ s x y + ∑ k : Fin 2,
        (latticeGaussian σ s (x + unit k) y - latticeGaussian σ s x y) * χ k x)|
      = |θ⁻¹| * |latticeGaussian σ s x y + ∑ k : Fin 2,
        (latticeGaussian σ s (x + unit k) y - latticeGaussian σ s x y) * χ k x| := abs_mul _ _
    _ ≤ |θ⁻¹| * ((2 * Real.pi * σ * a)⁻¹ * (1 + 2 * A) * nbrEnv (gaussEnv (2 * σ * b) y) x) :=
        mul_le_mul_of_nonneg_left h (abs_nonneg _)
    _ = _ := by ring

/-- The bound of `∂_s h(s, x, y)` for `s ∈ [a, b]`. -/
theorem abs_dgTwoScale_deriv_le {σ θ a b s A : ℝ} {χ : Fin 2 → Vertex 2 → ℝ} {y x : Vertex 2}
    (hσ : 0 < σ) (ha : 0 < a) (has : a ≤ s) (hsb : s ≤ b) (hA : 0 ≤ A)
    (hχ : ∀ k, |χ k x| ≤ A * (1 + latticeDist x y)) :
    |θ⁻¹ * (latticeGaussianTimeDeriv σ s x y + ∑ k : Fin 2,
        (latticeGaussianTimeDeriv σ s (x + Pi.single k 1) y - latticeGaussianTimeDeriv σ s x y) *
          χ k x)| ≤
      |θ⁻¹| * ((2 * Real.pi * σ * a)⁻¹ * (1 / (2 * σ * a ^ 2) + 1 / a) * (1 + 2 * A)) *
        nbrEnv (gaussEnv (2 * σ * b) y) x := by
  have h := abs_twoScale_le (P := fun z => latticeGaussianTimeDeriv σ s z y) (χ := χ)
    (by positivity) hA (fun z => abs_latticeGaussianTimeDeriv_le hσ ha has hsb z y) hχ
  calc |θ⁻¹ * (latticeGaussianTimeDeriv σ s x y + ∑ k : Fin 2,
        (latticeGaussianTimeDeriv σ s (x + Pi.single k 1) y - latticeGaussianTimeDeriv σ s x y) *
          χ k x)|
      = |θ⁻¹| * |latticeGaussianTimeDeriv σ s x y + ∑ k : Fin 2,
        (latticeGaussianTimeDeriv σ s (x + unit k) y - latticeGaussianTimeDeriv σ s x y) *
          χ k x| := abs_mul _ _
    _ ≤ |θ⁻¹| * ((2 * Real.pi * σ * a)⁻¹ * (1 / (2 * σ * a ^ 2) + 1 / a) * (1 + 2 * A) *
          nbrEnv (gaussEnv (2 * σ * b) y) x) := mul_le_mul_of_nonneg_left h (abs_nonneg _)
    _ = _ := by ring

/-- `f = 1_K h(τ, ·, y)`. -/
noncomputable def clusterInit {ω : Configuration 2} (K : OpenComponent ω) (σ θ : ℝ)
    (χ : Fin 2 → Vertex 2 → ℝ) (τ : ℝ) (y z : Vertex 2) : ℝ :=
  if z ∈ K.supp then dgTwoScale σ θ χ τ z y else 0

/-- `u(s, x) = 1_K(x) (h(s, x, y) - P_{s-τ} f(x))`. -/
noncomputable def clusterW {ω : Configuration 2} (K : OpenComponent ω) (σ θ : ℝ)
    (χ : Fin 2 → Vertex 2 → ℝ) (τ : ℝ) (y : Vertex 2) (s : ℝ) (x : Vertex 2) : ℝ :=
  if x ∈ K.supp then
    dgTwoScale σ θ χ s x y - heatFlow ω (s - τ) (clusterInit K σ θ χ τ y) x else 0

/-- The source term `G = 1_K θ^{-1} twoScaleSource` of the equation of `u`. -/
noncomputable def clusterSource {ω : Configuration 2} (K : OpenComponent ω) (σ θ : ℝ)
    (χ : Fin 2 → Vertex 2 → ℝ) (y : Vertex 2) (s : ℝ) (x : Vertex 2) : ℝ :=
  if x ∈ K.supp then θ⁻¹ * twoScaleSource ω σ χ s y x else 0

/-- `f` is square summable when the corrector grows at most linearly on the cluster. -/
theorem summable_sq_clusterInit {ω : Configuration 2} {K : OpenComponent ω} {σ θ τ A : ℝ}
    {χ : Fin 2 → Vertex 2 → ℝ} {y : Vertex 2} (hσ : 0 < σ) (hτ : 0 < τ) (hA : 0 ≤ A)
    (hχ : ∀ x ∈ K.supp, ∀ k, |χ k x| ≤ A * (1 + latticeDist x y)) :
    Summable fun z => clusterInit K σ θ χ τ y z ^ 2 := by
  refine Summable.of_nonneg_of_le (fun z => sq_nonneg _) (fun z => ?_)
    ((summable_sq_nbrEnv (summable_sq_gaussEnv (c := 2 * σ * τ) (by positivity) y)).mul_left
      ((|θ⁻¹| * ((2 * Real.pi * σ * τ)⁻¹ * (1 + 2 * A))) ^ 2))
  unfold clusterInit
  split_ifs with hz
  · rw [← mul_pow]
    exact sq_le_sq_of_abs_le (abs_dgTwoScale_le hσ hτ le_rfl le_rfl hA (hχ z hz))
  · rw [zero_pow two_ne_zero]
    positivity

theorem heatFlow_zero (ω : Configuration 2) (f : Vertex 2 → ℝ) (x : Vertex 2) :
    heatFlow ω 0 f x = f x := by
  unfold heatFlow
  rw [tsum_eq_single x fun z hz => by rw [openHeat_zero, if_neg (fun h => hz h.symm), zero_mul],
    openHeat_zero, if_pos rfl, one_mul]

/-- The initial condition `u(τ, ·) = 0`. -/
theorem clusterW_self {ω : Configuration 2} (K : OpenComponent ω) (σ θ : ℝ)
    (χ : Fin 2 → Vertex 2 → ℝ) (τ : ℝ) (y x : Vertex 2) : clusterW K σ θ χ τ y τ x = 0 := by
  unfold clusterW
  split_ifs with hx
  · rw [sub_self, heatFlow_zero]
    unfold clusterInit
    rw [if_pos hx, sub_self]
  · rfl

/-- On the cluster, `u(s, ·) = w(s, ·, τ, y)` for `s ≥ τ`. -/
theorem clusterW_eq_dgW {ω : Configuration 2} {K : OpenComponent ω} {σ θ τ s : ℝ}
    {χ : Fin 2 → Vertex 2 → ℝ} {y x : Vertex 2} (hσ : 0 < σ) (hτ : 0 < τ) (hτs : τ ≤ s)
    (hf : Summable fun z => clusterInit K σ θ χ τ y z ^ 2) (hx : x ∈ K.supp) :
    clusterW K σ θ χ τ y s x = dgW ω σ θ χ s τ x y := by
  have hs : 0 ≤ s - τ := by linarith
  have hcongr : ∀ z, openHeat ω (s - τ) x z * clusterInit K σ θ χ τ y z =
      openHeat ω (s - τ) x z * dgTwoScale σ θ χ τ z y := by
    intro z
    by_cases hz : z ∈ K.supp
    · unfold clusterInit
      rw [if_pos hz]
    · rw [openHeat_eq_zero_of_mem_of_notMem hx hz, zero_mul, zero_mul]
  have hv : Summable fun z => openHeat ω (s - τ) x z *
      (dgTwoScale σ θ χ τ z y - θ⁻¹ * latticeGaussian σ τ z y) := by
    refine ((summable_openHeat_mul ω hs hf x).sub
      (summable_dgQ_term (θ := θ) ω hσ hτ hτs x y)).congr fun z => ?_
    rw [hcongr z]
    ring
  rw [dgW_eq_sub_tsum ω hσ hτ hτs χ x y hv]
  unfold clusterW heatFlow
  rw [if_pos hx]
  congr 1
  exact tsum_congr hcongr

/-- The Laplacian of `u` at a point of the cluster. -/
theorem openLaplacian_clusterW {ω : Configuration 2} {K : OpenComponent ω} {σ θ τ s : ℝ}
    {χ : Fin 2 → Vertex 2 → ℝ} {y x : Vertex 2} (hx : x ∈ K.supp) :
    openLaplacian ω (clusterW K σ θ χ τ y s) x =
      openLaplacian ω (fun z => dgTwoScale σ θ χ s z y) x -
        openLaplacian ω (heatFlow ω (s - τ) (clusterInit K σ θ χ τ y)) x := by
  unfold openLaplacian
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun z hz => ?_
  have hzK : z ∈ K.supp :=
    mem_supp_of_openAdj hx ((SimpleGraph.mem_neighborFinset _ _ _).1 hz)
  simp only [clusterW, if_pos hx, if_pos hzK]
  ring

/-- `Δ u + G` at a point of the cluster, in terms of `∂_s h`. -/
theorem openLaplacian_clusterW_add_source {ω : Configuration 2} {K : OpenComponent ω}
    {y : Vertex 2} {χ : Fin 2 → Vertex 2 → ℝ} (hχK : IsDGCorrector K y χ) {σ θ τ s : ℝ}
    (hσ : 0 < σ) (hs0 : 0 < s) {x : Vertex 2} (hx : x ∈ K.supp) :
    openLaplacian ω (clusterW K σ θ χ τ y s) x + clusterSource K σ θ χ y s x =
      θ⁻¹ * (latticeGaussianTimeDeriv σ s x y + ∑ k : Fin 2,
        (latticeGaussianTimeDeriv σ s (x + Pi.single k 1) y - latticeGaussianTimeDeriv σ s x y) *
          χ k x) - openLaplacian ω (heatFlow ω (s - τ) (clusterInit K σ θ χ τ y)) x := by
  have h1 := hasDerivAt_dgTwoScale_eq (θ := θ) hχK hσ hs0 hx
  have h2 := hasDerivAt_dgTwoScale_time (θ := θ) hσ hs0 χ x y
  have hu := h1.unique h2
  rw [openLaplacian_clusterW hx, clusterSource, if_pos hx, ← hu]
  ring

/-- **The equation (4.25) of `w` on the cluster**: `∂_s u = Δ u + G` for `s - τ ∈ (0, T)`. -/
theorem hasDerivAt_clusterW {ω : Configuration 2} {K : OpenComponent ω} {y : Vertex 2}
    {χ : Fin 2 → Vertex 2 → ℝ} (hχK : IsDGCorrector K y χ) {σ θ τ s T : ℝ} (hσ : 0 < σ)
    (hf : Summable fun z => clusterInit K σ θ χ τ y z ^ 2) (hs : s - τ ∈ Set.Ioo 0 T)
    (hs0 : 0 < s) (x : Vertex 2) :
    HasDerivAt (fun r => clusterW K σ θ χ τ y r x)
      (openLaplacian ω (clusterW K σ θ χ τ y s) x + clusterSource K σ θ χ y s x) s := by
  by_cases hx : x ∈ K.supp
  · have h1 := hasDerivAt_dgTwoScale_time (θ := θ) hσ hs0 χ x y
    have h2 := (hasDerivAt_heatFlow ω hf hs x).comp_sub_const s τ
    have e : (fun r => clusterW K σ θ χ τ y r x) = fun r =>
        dgTwoScale σ θ χ r x y - heatFlow ω (r - τ) (clusterInit K σ θ χ τ y) x :=
      funext fun r => by simp only [clusterW, if_pos hx]
    rw [e, openLaplacian_clusterW_add_source hχK hσ hs0 hx]
    exact h1.sub h2
  · have e : (fun r => clusterW K σ θ χ τ y r x) = fun _ => 0 :=
      funext fun r => by simp only [clusterW, if_neg hx]
    rw [e]
    refine (hasDerivAt_const s (0 : ℝ)).congr_deriv ?_
    rw [clusterSource, if_neg hx, add_zero]
    unfold openLaplacian
    refine (Finset.sum_eq_zero fun z hz => ?_).symm
    have hzK : z ∉ K.supp := fun hzK =>
      hx (mem_supp_of_openAdj hzK ((SimpleGraph.mem_neighborFinset _ _ _).1 hz).symm)
    simp only [clusterW, if_neg hx, if_neg hzK, sub_self]

end Rigidity.Green
