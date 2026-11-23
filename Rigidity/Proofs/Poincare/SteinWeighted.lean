import Rigidity.Proofs.Poincare.SteinSquareFunction

/-!
# The weighted square function bound for the heat flow of `ℤ²`, `1 < p ≤ 2`

The conclusion of the lattice form of Armstrong, Kuusi and Mourrat, Proposition D.2, Step 2,
with the weight `ω = coshW a` of their Remark D.6: for `f ≥ 0` supported in `S`, `T ≥ 0`,
`0 ≤ a ≤ 1/6` and `a max(√T, 1) ≤ 1`,

  `Σ_x ω(x) Γ(x)^{p/2} ≤ (2/(p(p-1)))^{p/2} K_M^{(2-p)/2} K_I^{p/2} Σ_x ω f^p`,

with `K_I = λT e^{λT} + 1` (`λ = 4(cosh a - 1)`) and `K_M = (3 C e^a)^p · 18 · 2^{p-1} p/(p-1)`
from the box maximal function: the weighted AM-GM inequality replaces Hölder's inequality in
`Σ ω M^{p(2-p)/2} I^{p/2}`.

* `tsum_coshW_mul_hint_le`: `Σ_x ω H ≤ T e^{λT} Σ ω f^p`;
* `tsum_ofReal_coshW_mul_ipos_le`: `Σ_x ω I ≤ K_I Σ ω f^p`;
* `exists_steinWeighted`: the bound above.
-/

open scoped Classical
open LatticeProb LatticeProb.Percolation Rigidity.Green MeasureTheory

namespace Rigidity.Poincare

variable {S : Finset (Vertex 2)} {f : Vertex 2 → ℝ}

theorem hint_nonneg (hf : ∀ y, 0 ≤ f y) (p : ℝ) {T : ℝ} (hT : 0 ≤ T) (x : Vertex 2) :
    0 ≤ hint S f p T x :=
  intervalIntegral.integral_nonneg hT fun _ hs => Real.rpow_nonneg (heatF_nonneg hf hs.1 x) _

/-- `Σ_x ω(x) heatF g (x) = e^{4s(cosh a - 1)} Σ_y ω(y) g(y)`. -/
theorem hasSum_coshW_mul_heatF (a : ℝ) (g : Vertex 2 → ℝ) {s : ℝ} (hs : 0 ≤ s) :
    HasSum (fun x => coshW a x * heatF S g s x)
      (Real.exp (4 * s * (Real.cosh a - 1)) * ∑ y ∈ S, coshW a y * g y) := by
  have h := hasSum_sum (s := S) fun y _ => (hasSum_openHeat_mul_coshW a hs y).mul_left (g y)
  have e : ∑ y ∈ S, g y * (Real.exp (4 * s * (Real.cosh a - 1)) * coshW a y) =
      Real.exp (4 * s * (Real.cosh a - 1)) * ∑ y ∈ S, coshW a y * g y := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [← e]
  refine h.congr_fun fun x => ?_
  unfold heatF
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [openHeat_symm]
  ring

theorem heatF_le_exp_mul {g : Vertex 2 → ℝ} (hg : ∀ y, 0 ≤ g y) {s T : ℝ} (hs : 0 ≤ s)
    (hsT : s ≤ T) (x : Vertex 2) :
    heatF S g s x ≤ Real.exp (8 * T) * heatF S g (2 * T) x := by
  unfold heatF
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun y _ => ?_
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (openHeat_allOpen_le_exp_mul hs hsT x y) (hg y)

/-- **The weighted bound for `H`**: `Σ_x ω H ≤ T e^{λT} Σ ω f^p`, with summability. -/
theorem tsum_coshW_mul_hint_le (hf : ∀ y, 0 ≤ f y) {p : ℝ} (hp : 1 ≤ p) (a : ℝ)
    {T : ℝ} (hT : 0 ≤ T) :
    Summable (fun x => coshW a x * hint S f p T x) ∧
      ∑' x, coshW a x * hint S f p T x ≤
        T * Real.exp (4 * T * (Real.cosh a - 1)) * ∑ y ∈ S, coshW a y * f y ^ p := by
  set g : Vertex 2 → ℝ := fun y => f y ^ p with hg
  have hg0 : ∀ y, 0 ≤ g y := fun y => Real.rpow_nonneg (hf y) _
  set W := ∑ y ∈ S, coshW a y * g y with hW
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun y _ => mul_nonneg (coshW_pos a y).le (hg0 y)
  set J : Vertex 2 → ℝ := fun x => ∫ s in (0 : ℝ)..T, heatF S g s x with hJ
  have hcont : ∀ x, Continuous fun s => heatF S g s x := fun x => continuous_heatF S g x
  have hHJ : ∀ x, hint S f p T x ≤ J x := fun x =>
    intervalIntegral.integral_mono_on hT
      ((continuous_heatF_rpow (by linarith) x).intervalIntegrable _ _)
      ((hcont x).intervalIntegrable _ _) fun s hs => heatF_rpow_le hf hs.1 hp x
  have hJ0 : ∀ x, 0 ≤ J x := fun x =>
    intervalIntegral.integral_nonneg hT fun s hs => heatF_nonneg hg0 hs.1 x
  have hJdom : ∀ x, J x ≤ T * (Real.exp (8 * T) * heatF S g (2 * T) x) := by
    intro x
    have := intervalIntegral.integral_mono_on hT ((hcont x).intervalIntegrable _ _)
      (intervalIntegrable_const (μ := volume) (c := Real.exp (8 * T) * heatF S g (2 * T) x))
      fun s hs => heatF_le_exp_mul hg0 hs.1 hs.2 x
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at this
    exact this
  have hsJ : Summable fun x => coshW a x * J x := by
    have hs2 := (hasSum_coshW_mul_heatF (S := S) a g (by linarith : (0 : ℝ) ≤ 2 * T)).summable
    refine ((hs2.mul_left (T * Real.exp (8 * T))).of_nonneg_of_le
      (fun x => mul_nonneg (coshW_pos a x).le (hJ0 x)) fun x => ?_)
    have := mul_le_mul_of_nonneg_left (hJdom x) (coshW_pos a x).le
    nlinarith [coshW_pos a x]
  have hsH : Summable fun x => coshW a x * hint S f p T x :=
    hsJ.of_nonneg_of_le (fun x => mul_nonneg (coshW_pos a x).le (hint_nonneg hf p hT x))
      fun x => mul_le_mul_of_nonneg_left (hHJ x) (coshW_pos a x).le
  refine ⟨hsH, ?_⟩
  -- the bound for `Σ ω J`, through lower integrals
  have hlam0 : 0 ≤ 4 * (Real.cosh a - 1) := by linarith [Real.one_le_cosh a]
  have hJbound : ∑' x, coshW a x * J x ≤ T * Real.exp (4 * T * (Real.cosh a - 1)) * W := by
    have hRHS : 0 ≤ T * Real.exp (4 * T * (Real.cosh a - 1)) * W := by positivity
    rw [← ENNReal.ofReal_le_ofReal_iff hRHS,
      ENNReal.ofReal_tsum_of_nonneg (fun x => mul_nonneg (coshW_pos a x).le (hJ0 x)) hsJ]
    have hint_eq : ∀ x, ENNReal.ofReal (coshW a x * J x) =
        ∫⁻ s in Set.Ioc 0 T, ENNReal.ofReal (coshW a x * heatF S g s x) := by
      intro x
      rw [hJ, ← intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le hT,
        ofReal_integral_eq_lintegral_ofReal]
      · exact (((continuous_const.mul (hcont x)).continuousOn).integrableOn_Icc).mono_set
          Set.Ioc_subset_Icc_self
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        exact mul_nonneg (coshW_pos a x).le (heatF_nonneg hg0 hs.1.le x)
    simp only [hint_eq]
    have hmeas : ∀ x, AEMeasurable (fun s : ℝ => ENNReal.ofReal (coshW a x * heatF S g s x))
        (volume.restrict (Set.Ioc 0 T)) := fun x =>
      ((continuous_const.mul (hcont x)).measurable.ennreal_ofReal).aemeasurable
    rw [← lintegral_tsum hmeas]
    calc ∫⁻ s in Set.Ioc 0 T, ∑' x, ENNReal.ofReal (coshW a x * heatF S g s x)
        ≤ ∫⁻ _ in Set.Ioc 0 T, ENNReal.ofReal (Real.exp (4 * T * (Real.cosh a - 1)) * W) := by
          refine setLIntegral_mono' measurableSet_Ioc fun s hs => ?_
          have hs0 : 0 ≤ s := hs.1.le
          rw [← ENNReal.ofReal_tsum_of_nonneg (fun x => mul_nonneg (coshW_pos a x).le
            (heatF_nonneg hg0 hs0 x)) (hasSum_coshW_mul_heatF a g hs0).summable,
            (hasSum_coshW_mul_heatF a g hs0).tsum_eq]
          refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ hW0)
          exact Real.exp_le_exp.2 (by nlinarith [hs.2])
      _ = ENNReal.ofReal (T * Real.exp (4 * T * (Real.cosh a - 1)) * W) := by
          rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
  calc ∑' x, coshW a x * hint S f p T x ≤ ∑' x, coshW a x * J x :=
        hsH.tsum_le_tsum (fun x => mul_le_mul_of_nonneg_left (hHJ x) (coshW_pos a x).le) hsJ
    _ ≤ T * Real.exp (4 * T * (Real.cosh a - 1)) * W := hJbound

/-- **The weighted bound for `I`**: `Σ_x ω I ≤ (λT e^{λT} + 1) Σ ω f^p`. -/
theorem tsum_ofReal_coshW_mul_ipos_le (hf : ∀ y, 0 ≤ f y) (hfS : ∀ y ∉ S, f y = 0) {p : ℝ}
    (hp1 : 1 < p) (hp2 : p ≤ 2) {a : ℝ} (ha : 0 ≤ a) {T : ℝ} (hT : 0 ≤ T) :
    ∑' x, ENNReal.ofReal (coshW a x * ipos S f p T x) ≤
      ENNReal.ofReal ((4 * (Real.cosh a - 1) * T * Real.exp (4 * T * (Real.cosh a - 1)) + 1) *
        ∑ y ∈ S, coshW a y * f y ^ p) := by
  obtain ⟨hsH, hbH⟩ := tsum_coshW_mul_hint_le (S := S) hf hp1.le a hT
  set W := ∑ y ∈ S, coshW a y * f y ^ p with hW
  set lam := 4 * (Real.cosh a - 1) with hlam
  have hlam0 : 0 ≤ lam := by linarith [Real.one_le_cosh a]
  have h1 := hasSum_coshW_mul_lap ha (hint_nonneg hf p hT) hsH
  have h2 : HasSum (fun x => coshW a x * f x ^ p) W := by
    refine hasSum_sum_of_ne_finset_zero fun x hx => ?_
    rw [hfS x hx, Real.zero_rpow (by linarith), mul_zero]
  have hh := h1.add h2
  have hle : ∀ x, coshW a x * ipos S f p T x ≤
      coshW a x * lap (hint S f p T) x + coshW a x * f x ^ p := by
    intro x
    rw [ipos_eq hfS hp1 T x, ← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ (coshW_pos a x).le
    have := Real.rpow_nonneg (heatF_nonneg (S := S) hf hT x) p
    linarith
  have hge : ∀ x, 0 ≤ coshW a x * ipos S f p T x := fun x =>
    mul_nonneg (coshW_pos a x).le (ipos_nonneg hf hp1 hp2 hT x)
  calc ∑' x, ENNReal.ofReal (coshW a x * ipos S f p T x)
      ≤ ∑' x, ENNReal.ofReal (coshW a x * lap (hint S f p T) x + coshW a x * f x ^ p) :=
        ENNReal.tsum_le_tsum fun x => ENNReal.ofReal_le_ofReal (hle x)
    _ = ENNReal.ofReal (lam * ∑' x, coshW a x * hint S f p T x + W) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun x => (hge x).trans (hle x)) hh.summable,
          hh.tsum_eq]
    _ ≤ ENNReal.ofReal ((lam * T * Real.exp (4 * T * (Real.cosh a - 1)) + 1) * W) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have := mul_le_mul_of_nonneg_left hbH hlam0
        nlinarith

end Rigidity.Poincare
