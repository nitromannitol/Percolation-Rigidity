import Rigidity.Proofs.Green.DarioGuTwoScaleCluster

/-!
# Domination and continuity of `w` on the cluster

The hypotheses of the energy argument of Step 5 (`energy_first_pass`, `energy_second_pass`) for
the function `u = 1_K w` of `DarioGuTwoScaleCluster`, when the corrector grows at most linearly on
the cluster:

* `exists_clusterW_dom`: `|u(s, x)| ≤ D(x)` for `s ∈ [τ, t]` with `D` square summable;
* `exists_clusterW_deriv_dom`: `|Δ u(s)(x) + G(s, x)| ≤ D'(x)` for `s ∈ (τ, t]`;
* `continuousOn_clusterW`, `continuousOn_tsum_sq_mul`: the weighted energy is continuous on
  `[τ, t]`.
-/

open scoped Classical
open LatticeProb LatticeProb.Percolation

namespace Rigidity.Green

theorem nbrEnv_nonneg {D : Vertex 2 → ℝ} (h : ∀ x, 0 ≤ D x) (x : Vertex 2) : 0 ≤ nbrEnv D x := by
  unfold nbrEnv
  have := h x
  have : 0 ≤ ∑ i : Fin 2, (D (x + unit i) + D (x - unit i)) :=
    Finset.sum_nonneg fun i _ => add_nonneg (h _) (h _)
  positivity

theorem heatFlow_abs_nonneg (ω : Configuration 2) {s : ℝ} (hs : 0 ≤ s) (f : Vertex 2 → ℝ)
    (x : Vertex 2) : 0 ≤ heatFlow ω s (fun z => |f z|) x :=
  tsum_nonneg fun z => mul_nonneg (openHeat_nonneg ω hs x z) (abs_nonneg _)

theorem summable_sq_add {a b : Vertex 2 → ℝ} (ha : Summable fun x => a x ^ 2)
    (hb : Summable fun x => b x ^ 2) : Summable fun x => (a x + b x) ^ 2 :=
  Summable.of_nonneg_of_le (fun x => sq_nonneg _)
    (fun x => by nlinarith [sq_nonneg (a x - b x)]) ((ha.add hb).mul_left 2)

/-- `Δ u + G = 0` off the cluster. -/
theorem openLaplacian_clusterW_add_source_of_notMem {ω : Configuration 2} {K : OpenComponent ω}
    {σ θ τ s : ℝ} {χ : Fin 2 → Vertex 2 → ℝ} {y x : Vertex 2} (hx : x ∉ K.supp) :
    openLaplacian ω (clusterW K σ θ χ τ y s) x + clusterSource K σ θ χ y s x = 0 := by
  rw [clusterSource, if_neg hx, add_zero]
  unfold openLaplacian
  refine Finset.sum_eq_zero fun z hz => ?_
  have hzK : z ∉ K.supp := fun hzK =>
    hx (mem_supp_of_openAdj hzK ((SimpleGraph.mem_neighborFinset _ _ _).1 hz).symm)
  simp only [clusterW, if_neg hx, if_neg hzK, sub_self]

/-- **Domination of `u` on `[τ, t]`.** -/
theorem exists_clusterW_dom {ω : Configuration 2} {K : OpenComponent ω} {σ θ τ t A : ℝ}
    {χ : Fin 2 → Vertex 2 → ℝ} {y : Vertex 2} (hσ : 0 < σ) (hτ : 0 < τ) (hτt : τ ≤ t)
    (hA : 0 ≤ A) (hχ : ∀ x ∈ K.supp, ∀ k, |χ k x| ≤ A * (1 + latticeDist x y)) :
    ∃ D : Vertex 2 → ℝ, Summable (fun x => D x ^ 2) ∧
      ∀ s ∈ Set.Icc τ t, ∀ x, |clusterW K σ θ χ τ y s x| ≤ D x := by
  have hf := summable_sq_clusterInit (θ := θ) hσ hτ hA hχ
  have hfa : Summable fun z => |clusterInit K σ θ χ τ y z| ^ 2 := by
    simpa only [sq_abs] using hf
  have hT : 0 ≤ 2 * (t - τ) := by linarith
  set c₁ := |θ⁻¹| * ((2 * Real.pi * σ * τ)⁻¹ * (1 + 2 * A)) with hc₁
  refine ⟨fun x => c₁ * nbrEnv (gaussEnv (2 * σ * t) y) x +
    Real.exp (8 * (t - τ)) * heatFlow ω (2 * (t - τ)) (fun z => |clusterInit K σ θ χ τ y z|) x,
    ?_, ?_⟩
  · refine summable_sq_add ?_ ?_
    · simpa only [mul_pow] using (summable_sq_nbrEnv (summable_sq_gaussEnv
        (c := 2 * σ * t) (by nlinarith) y)).mul_left (c₁ ^ 2)
    · simpa only [mul_pow] using (summable_sq_heatFlow ω hT hfa).mul_left
        (Real.exp (8 * (t - τ)) ^ 2)
  · intro s hs x
    have h0 : 0 ≤ c₁ * nbrEnv (gaussEnv (2 * σ * t) y) x +
        Real.exp (8 * (t - τ)) * heatFlow ω (2 * (t - τ))
          (fun z => |clusterInit K σ θ χ τ y z|) x := by
      have := nbrEnv_nonneg (gaussEnv_nonneg (2 * σ * t) y) x
      have := heatFlow_abs_nonneg ω hT (clusterInit K σ θ χ τ y) x
      positivity
    unfold clusterW
    split_ifs with hx
    · have h1 := abs_dgTwoScale_le (θ := θ) hσ hτ hs.1 hs.2 hA (hχ x hx)
      have h2 := abs_heatFlow_le ω (by linarith [hs.1] : 0 ≤ s - τ)
        (by linarith [hs.2] : s - τ ≤ t - τ) hf x
      have h3 := abs_sub (dgTwoScale σ θ χ s x y) (heatFlow ω (s - τ) (clusterInit K σ θ χ τ y) x)
      linarith
    · rw [abs_zero]
      exact h0

/-- **Domination of `∂_s u = Δ u + G` on `(τ, t]`.** -/
theorem exists_clusterW_deriv_dom {ω : Configuration 2} {K : OpenComponent ω} {σ θ τ t A : ℝ}
    {χ : Fin 2 → Vertex 2 → ℝ} {y : Vertex 2} (hχK : IsDGCorrector K y χ) (hσ : 0 < σ)
    (hτ : 0 < τ) (hτt : τ ≤ t) (hA : 0 ≤ A)
    (hχ : ∀ x ∈ K.supp, ∀ k, |χ k x| ≤ A * (1 + latticeDist x y)) :
    ∃ D : Vertex 2 → ℝ, Summable (fun x => D x ^ 2) ∧
      ∀ s ∈ Set.Ioc τ t, ∀ x,
        |openLaplacian ω (clusterW K σ θ χ τ y s) x + clusterSource K σ θ χ y s x| ≤ D x := by
  have hf := summable_sq_clusterInit (θ := θ) hσ hτ hA hχ
  have hfa : Summable fun z => |clusterInit K σ θ χ τ y z| ^ 2 := by
    simpa only [sq_abs] using hf
  have hT : 0 ≤ 2 * (t - τ) := by linarith
  set c₂ := |θ⁻¹| * ((2 * Real.pi * σ * τ)⁻¹ * (1 / (2 * σ * τ ^ 2) + 1 / τ) * (1 + 2 * A))
    with hc₂
  set E : Vertex 2 → ℝ := fun z => Real.exp (8 * (t - τ)) *
    heatFlow ω (2 * (t - τ)) (fun z => |clusterInit K σ θ χ τ y z|) z with hE
  have hE0 : ∀ z, 0 ≤ E z := fun z => by
    have := heatFlow_abs_nonneg ω hT (clusterInit K σ θ χ τ y) z
    simp only [hE]
    positivity
  refine ⟨fun x => c₂ * nbrEnv (gaussEnv (2 * σ * t) y) x + nbrEnv E x, ?_, ?_⟩
  · refine summable_sq_add ?_ (summable_sq_nbrEnv ?_)
    · simpa only [mul_pow] using (summable_sq_nbrEnv (summable_sq_gaussEnv
        (c := 2 * σ * t) (by nlinarith) y)).mul_left (c₂ ^ 2)
    · simpa only [hE, mul_pow] using (summable_sq_heatFlow ω hT hfa).mul_left
        (Real.exp (8 * (t - τ)) ^ 2)
  · intro s hs x
    have hs0 : 0 < s := hτ.trans hs.1
    have h0 : 0 ≤ c₂ * nbrEnv (gaussEnv (2 * σ * t) y) x + nbrEnv E x := by
      have := nbrEnv_nonneg (gaussEnv_nonneg (2 * σ * t) y) x
      have := nbrEnv_nonneg hE0 x
      positivity
    by_cases hx : x ∈ K.supp
    · rw [openLaplacian_clusterW_add_source hχK hσ hs0 hx]
      have h1 := abs_dgTwoScale_deriv_le (θ := θ) hσ hτ hs.1.le hs.2 hA (hχ x hx)
      have h2 := abs_openLaplacian_le_nbrEnv ω (u := heatFlow ω (s - τ) (clusterInit K σ θ χ τ y))
        (D := E) (fun z => abs_heatFlow_le ω (by linarith [hs.1] : 0 ≤ s - τ)
          (by linarith [hs.2] : s - τ ≤ t - τ) hf z) x
      refine (abs_sub _ _).trans ?_
      linarith
    · rw [openLaplacian_clusterW_add_source_of_notMem hx, abs_zero]
      exact h0

/-- The heat flow is continuous in time on `[0, T]`. -/
theorem continuousOn_heatFlow (ω : Configuration 2) {f : Vertex 2 → ℝ}
    (hf : Summable fun z => f z ^ 2) {T : ℝ} (hT : 0 ≤ T) (x : Vertex 2) :
    ContinuousOn (fun r => heatFlow ω r f x) (Set.Icc 0 T) := by
  have h2T : 0 ≤ 2 * T := by linarith
  refine continuousOn_tsum (fun z => ((continuous_openHeat ω x z).mul continuous_const).continuousOn)
    ((summable_openHeat_mul_abs ω h2T hf x).mul_left (Real.exp (8 * T))) fun z r hr => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (openHeat_nonneg ω hr.1 x z), ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (openHeat_le_exp_mul ω hr.1 hr.2 x z) (abs_nonneg _)

/-- `u(·, x)` is continuous on `[τ, t]`. -/
theorem continuousOn_clusterW {ω : Configuration 2} {K : OpenComponent ω} {σ θ τ t : ℝ}
    {χ : Fin 2 → Vertex 2 → ℝ} {y : Vertex 2} (hσ : 0 < σ) (hτ : 0 < τ)
    (hf : Summable fun z => clusterInit K σ θ χ τ y z ^ 2) (x : Vertex 2) :
    ContinuousOn (fun s => clusterW K σ θ χ τ y s x) (Set.Icc τ t) := by
  by_cases hx : x ∈ K.supp
  · have e : (fun s => clusterW K σ θ χ τ y s x) = fun s =>
        dgTwoScale σ θ χ s x y - heatFlow ω (s - τ) (clusterInit K σ θ χ τ y) x :=
      funext fun s => by simp only [clusterW, if_pos hx]
    rw [e]
    refine ContinuousOn.sub (fun s hs => ?_) ?_
    · exact (hasDerivAt_dgTwoScale_time (θ := θ) hσ (hτ.trans_le hs.1) χ x y).continuousAt
        |>.continuousWithinAt
    · rcases le_total τ t with hτt | hτt
      · refine (continuousOn_heatFlow ω hf (by linarith : 0 ≤ t - τ) x).comp
          (continuousOn_id.sub continuousOn_const) fun s hs => ?_
        exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
      · refine (continuousOn_heatFlow ω hf le_rfl x).comp
          (continuousOn_id.sub continuousOn_const) fun s hs => ?_
        exact ⟨by linarith [hs.1], by linarith [hs.1, hs.2]⟩
  · have e : (fun s => clusterW K σ θ χ τ y s x) = fun _ => 0 :=
      funext fun s => by simp only [clusterW, if_neg hx]
    rw [e]
    exact continuousOn_const

/-- The weighted energy is continuous when `u` and `ψ` are dominated and continuous. -/
theorem continuousOn_tsum_sq_mul {ψ u : ℝ → Vertex 2 → ℝ} {S : Set ℝ} {B : ℝ}
    {D : Vertex 2 → ℝ} (hD : Summable fun x => D x ^ 2) (hu : ∀ s ∈ S, ∀ x, |u s x| ≤ D x)
    (hψ : ∀ s ∈ S, ∀ x, |ψ s x| ≤ B) (hcu : ∀ x, ContinuousOn (fun s => u s x) S)
    (hcψ : ∀ x, ContinuousOn (fun s => ψ s x) S) :
    ContinuousOn (fun s => ∑' x, (ψ s x * u s x) ^ 2) S := by
  refine continuousOn_tsum (fun x => ((hcψ x).mul (hcu x)).pow 2) (hD.mul_left (B ^ 2))
    fun x s hs => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_pow]
  exact mul_le_mul (sq_le_sq_of_abs_le (hψ s hs x)) (sq_le_sq_of_abs_le (hu s hs x))
    (sq_nonneg _) (sq_nonneg _)

end Rigidity.Green
