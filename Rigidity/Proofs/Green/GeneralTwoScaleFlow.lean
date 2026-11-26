import Rigidity.Proofs.Green.GeneralTwoScaleError
import Rigidity.Proofs.Green.GeneralTwoScaleInitial
import Rigidity.Proofs.Green.NamedInputsD
import Rigidity.Proofs.Green.GaussFlowTailD

/-!
# The whole-cluster estimate of Dario–Gu on `ℤ^d` from Propositions 2.12 and 2.13

`darioGuGaussianFlowD_of_inputs` proves `DarioGuGaussianFlowD d p σ` (the whole-cluster estimate of
Dario–Gu, Proposition 4.3, Step 5, (4.40), with initial time `τ` and final time `3τ`, combined with
the initial error of Proposition 2.12) for `d ≥ 2`, from the quantitative corrector estimate
(Proposition 2.12, `CorrectorQuantitativeInput`) and the weak norm of the centered flux
(Proposition 2.13, `DarioGuFluxWeakNormD d p σ`). For `H_s = θ^{-1} p̄(s, · - y)` on the cluster,
`f = 1_𝒞 h(τ, ·, y)` and `u = 1_𝒞 (h(3τ, ·, y) - P_{2τ} f)` (`clusterWD`),

`P_{2τ} H_τ - H_{3τ} = P_{2τ}(H_τ - f) - u + 1_𝒞 (h(3τ, ·, y) - H_{3τ})`,

`P_{2τ}` is a contraction of `ℓ²`, the two initial errors are bounded by `l2norm_initialErrorD_le`
and `u` by (4.40) (`tsum_sq_clusterWD_le`): `‖P_{2τ} H_τ - H_{3τ}‖ ≤ C τ^{α_0/2 - d/4 - 1/2}` with
`α_0 = min(α, 1)`, above the minimal time `M = max(M_corr², M_flux², 1) ≤ O_s(C)`, where `M_corr`
and `M_flux` are the minimal scales of Propositions 2.12 and 2.13 at the exponent `α_0`.
`exists_darioGuGaussianFlowD_of_inputs` is the form used by `darioGuHeatKernelD_of_gaussianFlow`.
-/

open scoped Classical
open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External

namespace Rigidity.Green.GeneralDim

variable {d : ℕ}

theorem le_sqrt_of_sq_le' {a b : ℝ} (ha : 0 ≤ a) (h : a ^ 2 ≤ b) : a ≤ Real.sqrt b := by
  rw [← Real.sqrt_sq ha]
  exact Real.sqrt_le_sqrt h

/-- **The whole-cluster estimate of Dario–Gu on `ℤ^d`** ((4.40) with Proposition 2.12) from
Propositions 2.12 and 2.13. -/
theorem darioGuGaussianFlowD_of_inputs (hCQ : CorrectorQuantitativeInput) [NeZero d]
    (hd : 2 ≤ d) {p : unitInterval} (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    {σ : ℝ} (hσ : 0 < σ) (hflux : DarioGuFluxWeakNormD d p σ) : DarioGuGaussianFlowD d p σ := by
  intro α hα
  set θ := theta d p with hθdef
  have hθ : 0 < θ := Rigidity.Percolation.theta_pos_of_criticalProbability_lt d p hpc
  set α₀ := min α 1 with hα₀
  have hα₀0 : 0 < α₀ := lt_min hα one_pos
  have hα₀1 : α₀ ≤ 1 := min_le_right _ _
  have hα₀α : α₀ ≤ α := min_le_left _ _
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨C₁, s₁, hC₁, hs₁, hgrow⟩ := correctorGrowthD_of_input hCQ hd hpc hp1 hα₀0
  obtain ⟨C₂, s₂, hC₂, hs₂, hfl⟩ := hflux α₀ hα₀0
  obtain ⟨CA, hCA0, hA⟩ := tsum_sq_clusterWD_le hd hσ hθ hC₁.le hC₂.le hα₀0 hα₀1
  obtain ⟨CI, hCI, hI⟩ := l2norm_initialErrorD_le (d := d) hσ hθ
  set Cb := 2 * (CI * C₁) + Real.sqrt CA with hCb
  have hCb0 : 0 ≤ Cb := by positivity
  set s := min (s₁ / 2) (s₂ / 2) with hs
  have hs0 : 0 < s := lt_min (by positivity) (by positivity)
  set θ1 := C₁ ^ 2 * (6 : ℝ) ^ (1 / s) with hθ1
  set θ2 := C₂ ^ 2 * (6 : ℝ) ^ (1 / s) with hθ2
  set θ3 := (1 : ℝ) * (3 : ℝ) ^ (1 / s) with hθ3
  set θM := max (max θ1 θ2 * (4 : ℝ) ^ (1 / s)) θ3 * (4 : ℝ) ^ (1 / s) with hθM
  have hθM0 : 0 < θM := by positivity
  refine ⟨max Cb θM, s, lt_max_of_lt_right hθM0, hs0, fun y => ?_⟩
  obtain ⟨M₁, hM1m, hM10, hM1os, hM1ae⟩ := hgrow y
  obtain ⟨M₂, hM2m, hM20, hM2os, hM2ae⟩ := hfl y
  set M : Configuration d → ℝ := fun ω => max (max (M₁ ω ^ 2) (M₂ ω ^ 2)) 1 with hM
  have hMm : Measurable M := ((hM1m.pow_const 2).max (hM2m.pow_const 2)).max measurable_const
  have hos1 : IsOsBond d p (fun ω => M₁ ω ^ 2) s θ1 :=
    Rigidity.Proofs.S2.IsOsBond.mono_exponent hs0 (min_le_left _ _) (hM1m.pow_const 2)
      (IsOsBond.sq_of_nonnegD hC₁ hM10 hM1os)
  have hos2 : IsOsBond d p (fun ω => M₂ ω ^ 2) s θ2 :=
    Rigidity.Proofs.S2.IsOsBond.mono_exponent hs0 (min_le_right _ _) (hM2m.pow_const 2)
      (IsOsBond.sq_of_nonnegD hC₂ hM20 hM2os)
  have hos12 := Rigidity.Proofs.S2.IsOsBond.max hs0 (by positivity) (by positivity)
    (hM1m.pow_const 2) (hM2m.pow_const 2) hos1 hos2
  have hosM : IsOsBond d p M s θM :=
    Rigidity.Proofs.S2.IsOsBond.max hs0 (by positivity) (by positivity)
      ((hM1m.pow_const 2).max (hM2m.pow_const 2)) measurable_const hos12
      (Rigidity.Proofs.S2.isOsBond_const one_pos hs0)
  refine ⟨M, hMm, fun ω => le_max_of_le_right zero_le_one,
    Rigidity.Proofs.S2.IsOsBond.mono_scale hs0 hθM0 (le_max_right _ _) hMm hosM, ?_⟩
  filter_upwards [hM1ae, hM2ae, exists_isDGCorrectorD hd hpc hp1] with ω hω1 hω2 hω3
  intro h hy τ hτ
  set K := uniqueInfiniteComponent h with hK
  obtain ⟨χ, hχ⟩ := hω3 h y hy
  have hτ1 : 1 ≤ τ := (le_max_right _ _).trans hτ
  have hτ0 : 0 < τ := by linarith
  have hM1τ : M₁ ω ≤ Real.sqrt τ :=
    le_sqrt_of_sq_le' (hM10 ω) ((le_max_left _ _).trans ((le_max_left _ _).trans hτ))
  have hM2τ : M₂ ω ≤ Real.sqrt τ :=
    le_sqrt_of_sq_le' (hM20 ω) ((le_max_right _ _).trans ((le_max_left _ _).trans hτ))
  -- the growth of the corrector and the weak norms at every scale `r ≥ τ`
  have hgr : ∀ r, τ ≤ r → ∀ z ∈ K.supp, ∀ k,
      |χ k z| ≤ C₁ * (Real.sqrt r + ‖edzD z y‖ + 2) ^ α₀ := fun r hr z hz k =>
    hω1 h hy χ hχ (Real.sqrt r) (hM1τ.trans (Real.sqrt_le_sqrt hr)) z hz k
  have hW : ∀ r, τ ≤ r → ∀ k i : Fin d, ∀ m : ℕ,
      WeakNormLeD ω (dgClusterBallD K y (2 ^ (m + 2) * Real.sqrt r))
        (centeredFluxD ω σ χ k i) (C₂ * (2 ^ (m + 2) * Real.sqrt r) ^ α₀) := by
    intro r hr k i m
    refine hω2 h hy χ hχ _ ?_ k i
    have h1 : (1 : ℝ) ≤ 2 ^ (m + 2) := one_le_pow₀ (by norm_num)
    have h2 := Real.sqrt_le_sqrt hr
    have h3 := Real.sqrt_nonneg r
    nlinarith
  obtain ⟨hus, hut⟩ := hA ω K y χ τ hχ hτ1 hgr hW
  obtain ⟨hf1s, hf1⟩ := hI ω K y χ C₁ α₀ τ hC₁.le hα₀0.le hα₀1 hτ1 (hgr τ le_rfl)
  obtain ⟨hg3s, hg3⟩ := hI ω K y χ C₁ α₀ (3 * τ) hC₁.le hα₀0.le hα₀1 (by linarith)
    (hgr (3 * τ) (by linarith))
  -- the decomposition
  have hHs : Summable fun x => (θ⁻¹ * clusterInd K σ τ y x) ^ 2 := by
    simpa only [mul_pow] using (summable_sq_clusterInd hσ hτ0).mul_left (θ⁻¹ ^ 2)
  have hfs : Summable fun x => clusterInitD K σ θ χ τ y x ^ 2 :=
    (summable_sq_addD hHs hf1s).congr fun x => by ring
  have hHf : Summable fun x => (θ⁻¹ * clusterInd K σ τ y x - clusterInitD K σ θ χ τ y x) ^ 2 :=
    hf1s.congr fun x => by ring
  have hpt : ∀ x, heatFlowG (openGraph ω) (2 * d) (2 * τ)
      (fun z => θ⁻¹ * clusterInd K σ τ y z) x - θ⁻¹ * clusterInd K σ (3 * τ) y x =
      (heatFlowG (openGraph ω) (2 * d) (2 * τ)
          (fun z => θ⁻¹ * clusterInd K σ τ y z - clusterInitD K σ θ χ τ y z) x +
        -clusterWD K σ θ χ τ y (3 * τ) x) +
      (clusterInitD K σ θ χ (3 * τ) y x - θ⁻¹ * clusterInd K σ (3 * τ) y x) := by
    intro x
    rw [heatFlowG_sub two_mul_pos_d (openGraph_degree_le ω) (by linarith) hHs hfs x]
    by_cases hx : x ∈ K.supp
    · simp only [clusterWD, if_pos hx, show 3 * τ - τ = 2 * τ by ring]
      unfold clusterInitD
      rw [if_pos hx]
      ring
    · rw [heatFlowG_eq_zero_of_notMem (f := fun z => θ⁻¹ * clusterInd K σ τ y z)
        (fun w hw => by simp [clusterInd_eq_zero hw]) hx,
        heatFlowG_eq_zero_of_notMem (f := clusterInitD K σ θ χ τ y)
        (fun w hw => by simp [clusterInitD, hw]) hx]
      simp [clusterWD, hx, clusterInitD, clusterInd_eq_zero hx]
  set a : Vertex d → ℝ := fun x => heatFlowG (openGraph ω) (2 * d) (2 * τ)
    (fun z => θ⁻¹ * clusterInd K σ τ y z - clusterInitD K σ θ χ τ y z) x with ha
  set u : Vertex d → ℝ := fun x => clusterWD K σ θ χ τ y (3 * τ) x with hu
  set g : Vertex d → ℝ := fun x =>
    clusterInitD K σ θ χ (3 * τ) y x - θ⁻¹ * clusterInd K σ (3 * τ) y x with hg
  have has : Summable fun x => a x ^ 2 :=
    summable_sq_heatFlowG two_mul_pos_d (openGraph_degree_le ω) (by linarith) hHf
  have hnus : Summable fun x => (-u x) ^ 2 := by simpa only [neg_sq] using hus
  obtain ⟨hs1, hn1⟩ := l2norm_add_le (f := a) (g := fun x => -u x) has hnus
  obtain ⟨-, hn2⟩ := l2norm_add_le (f := fun x => a x + -u x) (g := g) hs1 hg3s
  have hT : l2norm (fun x => heatFlowG (openGraph ω) (2 * d) (2 * τ)
      (fun z => θ⁻¹ * clusterInd K σ τ y z) x - θ⁻¹ * clusterInd K σ (3 * τ) y x) =
      l2norm (fun x => a x + -u x + g x) := by
    congr 1
    funext x
    exact hpt x
  -- the three norms
  set e := α₀ / 2 - (d : ℝ) / 4 - 1 / 2 with he
  have he0 : e ≤ 0 := by rw [he]; linarith
  have hneg : l2norm (fun x => -u x) = l2norm u := by
    unfold l2norm
    simp only [neg_sq]
  have hna : l2norm a ≤ CI * C₁ * τ ^ e := by
    refine (l2norm_heatFlowG_le two_mul_pos_d (openGraph_degree_le ω) (by linarith) hHf).trans ?_
    have hc : l2norm (fun z => θ⁻¹ * clusterInd K σ τ y z - clusterInitD K σ θ χ τ y z) =
        l2norm (fun x => clusterInitD K σ θ χ τ y x - θ⁻¹ * clusterInd K σ τ y x) := by
      unfold l2norm
      congr 1
      exact tsum_congr fun x => by ring
    rw [hc]
    exact hf1
  have hnu : l2norm u ≤ Real.sqrt CA * τ ^ e := by
    unfold l2norm
    refine (Real.sqrt_le_sqrt hut).trans (le_of_eq ?_)
    rw [Real.sqrt_mul hCA0, Real.sqrt_eq_rpow (τ ^ _), ← Real.rpow_mul hτ0.le, he]
    congr 2
    ring
  have hng : l2norm g ≤ CI * C₁ * τ ^ e := by
    refine hg3.trans ?_
    have h3 : (3 * τ) ^ e ≤ τ ^ e := by
      rw [Real.mul_rpow (by norm_num) hτ0.le]
      have : (3 : ℝ) ^ e ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) he0
      have : 0 ≤ τ ^ e := by positivity
      nlinarith
    exact mul_le_mul_of_nonneg_left h3 (by positivity)
  have hτe : τ ^ e ≤ τ ^ (α - (d : ℝ) / 4 - 1 / 2) :=
    Real.rpow_le_rpow_of_exponent_le hτ1 (by rw [he]; linarith)
  rw [hT]
  have hsum : l2norm (fun x => a x + -u x + g x) ≤ Cb * τ ^ e := by
    calc l2norm (fun x => a x + -u x + g x) ≤ l2norm (fun x => a x + -u x) + l2norm g := hn2
      _ ≤ l2norm a + l2norm (fun x => -u x) + l2norm g := by linarith
      _ ≤ CI * C₁ * τ ^ e + Real.sqrt CA * τ ^ e + CI * C₁ * τ ^ e := by
          rw [hneg]
          linarith
      _ = Cb * τ ^ e := by rw [hCb]; ring
  calc l2norm (fun x => a x + -u x + g x) ≤ Cb * τ ^ e := hsum
    _ ≤ Cb * τ ^ (α - (d : ℝ) / 4 - 1 / 2) := mul_le_mul_of_nonneg_left hτe hCb0
    _ ≤ max Cb θM * τ ^ (α - (d : ℝ) / 4 - 1 / 2) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

/-- **The whole-cluster estimate of Dario–Gu on `ℤ^d`** in the form used by Theorem 1
(`darioGuHeatKernelD_of_gaussianFlow`): at every supercritical `p < 1` some `σ > 0` satisfies
`DarioGuGaussianFlowD d p σ`, namely the `σ = σ̄²` of Proposition 2.13. -/
theorem exists_darioGuGaussianFlowD_of_inputs (hCQ : CorrectorQuantitativeInput) [NeZero d]
    (hd : 2 ≤ d)
    (hflux : ∀ p : unitInterval, criticalProbability d < (p : ℝ) → (p : ℝ) < 1 →
      ∃ σ : ℝ, 0 < σ ∧ DarioGuFluxWeakNormD d p σ) :
    ∀ p : unitInterval, criticalProbability d < (p : ℝ) → (p : ℝ) < 1 →
      ∃ σ : ℝ, 0 < σ ∧ DarioGuGaussianFlowD d p σ := by
  intro p hpc hp1
  obtain ⟨σ, hσ, hf⟩ := hflux p hpc hp1
  exact ⟨σ, hσ, darioGuGaussianFlowD_of_inputs hCQ hd hpc hp1 hσ hf⟩

end Rigidity.Green.GeneralDim
