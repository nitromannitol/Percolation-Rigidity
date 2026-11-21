import Rigidity.Proofs.Percolation.PlanarNuConvergence

/-!
# The homogenized matrix in the plane

For every configuration and triadic cube, `ν(U, ·)` is a quadratic form: if `v_p`, `v_q` solve
the first-variation equations for `p` and `q`, then `a v_p + b v_q` solves it for `a p + b q`, and
`ν` is half the energy of any solution. Hence `ν(U, a p + b q)` is determined by `ν(U, p)`,
`ν(U, q)` and `ν(U, p + q)`, and the same identity passes to the expectations `E[ν(□_m, ·)]` and to
their limit as `m → ∞`.

This defines the homogenized matrix `ā` of Armstrong and Dario, Definition 5.1, in dimension two:
`(1/2) ξ · ā ξ = lim_m E[ν(□_m, ξ); P, □_m res]`, and gives the bounds (5.1) in the form
`c |ξ|² ≤ (1/2) ξ · ā ξ ≤ (9/4) |ξ|₁²`.
-/

open MeasureTheory Filter Topology LatticeProb.Percolation Rigidity.External
  Rigidity.Proofs.Section5
open scoped ENNReal Classical

namespace Rigidity.Percolation

variable {ω : Configuration 2}

/-- The flux pairing is linear in the slope. -/
theorem fluxPairing_smul_add_smul {U : TriadicCube 2} (p q : Fin 2 → ℝ) (a b : ℝ)
    (w : ClusterFun ω U) :
    fluxPairing ω U (a • p + b • q) w = a * fluxPairing ω U p w + b * fluxPairing ω U q w := by
  simp only [fluxPairing_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  split_ifs
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_two]
    ring
  · ring

/-- `ν` is half the energy, per vertex, of any solution of its first-variation equation. -/
theorem planarNu_eq_of_forall_clusterForm_eq {U : TriadicCube 2} {p : Fin 2 → ℝ}
    {v : ClusterFun ω U} (hv : v ∈ clusterHarmonic ω U)
    (hsol : ∀ w ∈ clusterHarmonic ω U, clusterForm ω U w v = fluxPairing ω U p w) :
    planarNu ω U p = clusterForm ω U v v / 2 / U.volume := by
  obtain ⟨v', hv', -, hν⟩ := exists_planarNu_maximizer (ω := ω) (U := U) p
  have hvol := U.volume_pos
  have h1 := le_planarNu p hv
  have hF' : fluxPairing ω U p v' = clusterForm ω U v' v := (hsol v' hv').symm
  rw [← hsol v hv, hν, hF'] at h1
  have hsymm := clusterForm_symm v' v
  have hpos := clusterForm_self_nonneg (v - v')
  simp only [map_sub, LinearMap.sub_apply] at hpos
  rw [hν, hF']
  apply le_antisymm
  · refine div_le_div_of_nonneg_right ?_ hvol.le
    linarith
  · calc clusterForm ω U v v / 2 / U.volume =
        (clusterForm ω U v v - clusterForm ω U v v / 2) / U.volume := by ring
      _ ≤ _ := h1

/-- **`ν` is a quadratic form in the slope.** -/
theorem planarNu_smul_add_smul (U : TriadicCube 2) (p q : Fin 2 → ℝ) (a b : ℝ) :
    planarNu ω U (a • p + b • q) = a ^ 2 * planarNu ω U p + b ^ 2 * planarNu ω U q +
      a * b * (planarNu ω U (p + q) - planarNu ω U p - planarNu ω U q) := by
  obtain ⟨vp, hvp, hsp, -⟩ := exists_planarNu_maximizer (ω := ω) (U := U) p
  obtain ⟨vq, hvq, hsq, -⟩ := exists_planarNu_maximizer (ω := ω) (U := U) q
  have hν : ∀ a b : ℝ, planarNu ω U (a • p + b • q) =
      clusterForm ω U (a • vp + b • vq) (a • vp + b • vq) / 2 / U.volume := by
    intro a b
    refine planarNu_eq_of_forall_clusterForm_eq
      (Submodule.add_mem _ (Submodule.smul_mem _ a hvp) (Submodule.smul_mem _ b hvq))
      fun w hw => ?_
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hsp w hw, hsq w hw,
      fluxPairing_smul_add_smul]
  have e1 := hν 1 0
  have e2 := hν 0 1
  have e3 := hν 1 1
  simp only [one_smul, zero_smul, add_zero, zero_add] at e1 e2 e3
  have hvol := U.volume_pos
  rw [hν a b, e1, e2, e3]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [clusterForm_symm vq vp]
  field_simp
  ring

/-- The integrand `1{P, V res} ν(V, ξ)` as a real function. -/
theorem measurable_planarNu_indicator_real (V : TriadicCube 2) (ξ : Fin 2 → ℝ) :
    Measurable fun ω : Configuration 2 =>
      if PlanarPartitionEvent ω ∧ PlanarResolved ω V then planarNu ω V ξ else 0 := by
  have h := (measurable_planarNu_indicator V ξ).ennreal_toReal
  have heq : (fun ω : Configuration 2 =>
      if PlanarPartitionEvent ω ∧ PlanarResolved ω V then planarNu ω V ξ else 0) = fun ω =>
      (if PlanarPartitionEvent ω ∧ PlanarResolved ω V then
        ENNReal.ofReal (planarNu ω V ξ) else 0).toReal := by
    funext ω
    split_ifs
    · exact (ENNReal.toReal_ofReal (planarNu_nonneg ξ)).symm
    · rfl
  rw [heq]
  exact h

theorem integrable_planarNu_indicator (p : unitInterval) (V : TriadicCube 2) (ξ : Fin 2 → ℝ) :
    Integrable (fun ω : Configuration 2 =>
      if PlanarPartitionEvent ω ∧ PlanarResolved ω V then planarNu ω V ξ else 0)
      (latticeBondLaw 2 p) := by
  refine (integrable_const (9 / 4 * (|ξ 0| + |ξ 1|) ^ 2)).mono'
    (measurable_planarNu_indicator_real V ξ).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
  split_ifs
  · rw [Real.norm_eq_abs, abs_of_nonneg (planarNu_nonneg ξ)]
    exact planarNu_le ξ
  · simp only [norm_zero]
    positivity

theorem planarNuMean_eq_integral (p : unitInterval) (m : ℕ) (ξ : Fin 2 → ℝ) :
    planarNuMean p m ξ = ∫ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω ⟨m, 0⟩ then
      planarNu ω ⟨m, 0⟩ ξ else 0) ∂(latticeBondLaw 2 p) := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω => by
    simp only [Pi.zero_apply]
    split_ifs
    · exact planarNu_nonneg ξ
    · exact le_rfl) (measurable_planarNu_indicator_real _ ξ).aestronglyMeasurable]
  unfold planarNuMean
  congr 2
  funext ω
  split_ifs
  · rfl
  · exact ENNReal.ofReal_zero.symm

/-- Linearity of the integral for the combination appearing in a quadratic identity. -/
theorem integral_quadratic_combination {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f₁ f₂ f₃ : Ω → ℝ} (h₁ : Integrable f₁ μ) (h₂ : Integrable f₂ μ) (h₃ : Integrable f₃ μ)
    (a b : ℝ) :
    ∫ ω, (a ^ 2 * f₁ ω + b ^ 2 * f₂ ω + a * b * (f₃ ω - f₁ ω - f₂ ω)) ∂μ =
      a ^ 2 * ∫ ω, f₁ ω ∂μ + b ^ 2 * ∫ ω, f₂ ω ∂μ +
        a * b * (∫ ω, f₃ ω ∂μ - ∫ ω, f₁ ω ∂μ - ∫ ω, f₂ ω ∂μ) := by
  have e1 : ∫ ω, (a ^ 2 * f₁ ω + b ^ 2 * f₂ ω + a * b * (f₃ ω - f₁ ω - f₂ ω)) ∂μ =
      ∫ ω, (a ^ 2 * f₁ ω + b ^ 2 * f₂ ω) ∂μ + ∫ ω, a * b * (f₃ ω - f₁ ω - f₂ ω) ∂μ :=
    integral_add ((h₁.const_mul _).add (h₂.const_mul _)) (((h₃.sub h₁).sub h₂).const_mul _)
  have e2 : ∫ ω, (a ^ 2 * f₁ ω + b ^ 2 * f₂ ω) ∂μ =
      ∫ ω, a ^ 2 * f₁ ω ∂μ + ∫ ω, b ^ 2 * f₂ ω ∂μ :=
    integral_add (h₁.const_mul _) (h₂.const_mul _)
  have e3 : ∫ ω, (f₃ ω - f₁ ω - f₂ ω) ∂μ = ∫ ω, (f₃ ω - f₁ ω) ∂μ - ∫ ω, f₂ ω ∂μ :=
    integral_sub (h₃.sub h₁) h₂
  have e4 : ∫ ω, (f₃ ω - f₁ ω) ∂μ = ∫ ω, f₃ ω ∂μ - ∫ ω, f₁ ω ∂μ := integral_sub h₃ h₁
  rw [e1, e2, integral_const_mul, integral_const_mul, integral_const_mul, e3, e4]

/-- The expectations `E[ν(□_m, ·)]` are quadratic forms in the slope. -/
theorem planarNuMean_smul_add_smul (p : unitInterval) (m : ℕ) (ξ η : Fin 2 → ℝ) (a b : ℝ) :
    planarNuMean p m (a • ξ + b • η) = a ^ 2 * planarNuMean p m ξ + b ^ 2 * planarNuMean p m η +
      a * b * (planarNuMean p m (ξ + η) - planarNuMean p m ξ - planarNuMean p m η) := by
  simp only [planarNuMean_eq_integral]
  have hpt : (fun ω : Configuration 2 =>
      if PlanarPartitionEvent ω ∧ PlanarResolved ω ⟨m, 0⟩ then
        planarNu ω ⟨m, 0⟩ (a • ξ + b • η) else 0) = fun ω =>
      a ^ 2 * (if PlanarPartitionEvent ω ∧ PlanarResolved ω ⟨m, 0⟩ then
        planarNu ω ⟨m, 0⟩ ξ else 0) +
      b ^ 2 * (if PlanarPartitionEvent ω ∧ PlanarResolved ω ⟨m, 0⟩ then
        planarNu ω ⟨m, 0⟩ η else 0) +
      a * b * ((if PlanarPartitionEvent ω ∧ PlanarResolved ω ⟨m, 0⟩ then
        planarNu ω ⟨m, 0⟩ (ξ + η) else 0) -
        (if PlanarPartitionEvent ω ∧ PlanarResolved ω ⟨m, 0⟩ then
          planarNu ω ⟨m, 0⟩ ξ else 0) -
        (if PlanarPartitionEvent ω ∧ PlanarResolved ω ⟨m, 0⟩ then
          planarNu ω ⟨m, 0⟩ η else 0)) := by
    funext ω
    split_ifs
    · exact planarNu_smul_add_smul _ ξ η a b
    · ring
  have iξ := integrable_planarNu_indicator p ⟨m, 0⟩ ξ
  have iη := integrable_planarNu_indicator p ⟨m, 0⟩ η
  have iξη := integrable_planarNu_indicator p ⟨m, 0⟩ (ξ + η)
  rw [hpt]
  exact integral_quadratic_combination iξ iη iξη a b

/-- The limit of the expectations `E[ν(□_m, ξ); P, □_m res]` as `m → ∞`. -/
noncomputable def planarNuLimit (p : unitInterval) (ξ : Fin 2 → ℝ) : ℝ :=
  limUnder atTop fun m => planarNuMean p m ξ

theorem tendsto_planarNuLimit {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (ξ : Fin 2 → ℝ) :
    Tendsto (fun m => planarNuMean p m ξ) atTop (𝓝 (planarNuLimit p ξ)) := by
  obtain ⟨c, -, h⟩ := exists_tendsto_planarNuMean hpc
  obtain ⟨L, hL, -⟩ := h ξ
  rw [planarNuLimit, hL.limUnder_eq]
  exact hL

/-- The limit is a quadratic form in the slope. -/
theorem planarNuLimit_smul_add_smul {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (ξ η : Fin 2 → ℝ) (a b : ℝ) :
    planarNuLimit p (a • ξ + b • η) = a ^ 2 * planarNuLimit p ξ + b ^ 2 * planarNuLimit p η +
      a * b * (planarNuLimit p (ξ + η) - planarNuLimit p ξ - planarNuLimit p η) := by
  have h := ((((tendsto_planarNuLimit hpc ξ).const_mul (a ^ 2)).add
    ((tendsto_planarNuLimit hpc η).const_mul (b ^ 2))).add
    ((((tendsto_planarNuLimit hpc (ξ + η)).sub (tendsto_planarNuLimit hpc ξ)).sub
      (tendsto_planarNuLimit hpc η)).const_mul (a * b)))
  have h' : Tendsto (fun m => planarNuMean p m (a • ξ + b • η)) atTop
      (𝓝 (a ^ 2 * planarNuLimit p ξ + b ^ 2 * planarNuLimit p η +
        a * b * (planarNuLimit p (ξ + η) - planarNuLimit p ξ - planarNuLimit p η))) := by
    simp only [planarNuMean_smul_add_smul]
    exact h
  exact tendsto_nhds_unique (tendsto_planarNuLimit hpc _) h'

/-- **The homogenized matrix** `ā` (Armstrong and Dario, Definition 5.1, in dimension two). -/
noncomputable def planarAhom (p : unitInterval) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![2 * planarNuLimit p ![1, 0],
    planarNuLimit p ![1, 1] - planarNuLimit p ![1, 0] - planarNuLimit p ![0, 1];
    planarNuLimit p ![1, 1] - planarNuLimit p ![1, 0] - planarNuLimit p ![0, 1],
    2 * planarNuLimit p ![0, 1]]

theorem planarAhom_symm (p : unitInterval) (i j : Fin 2) : planarAhom p i j = planarAhom p j i := by
  fin_cases i <;> fin_cases j <;> rfl

/-- **Definition of `ā`** (Armstrong and Dario, Definition 5.1, in dimension two):
`(1/2) ξ · ā ξ = lim_m E[ν(□_m, ξ); P, □_m res]`. -/
theorem planarNuLimit_eq_planarAhom {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (ξ : Fin 2 → ℝ) :
    planarNuLimit p ξ = 1 / 2 * ∑ i, ∑ j, ξ i * planarAhom p i j * ξ j := by
  have h := planarNuLimit_smul_add_smul hpc ![1, 0] ![0, 1] (ξ 0) (ξ 1)
  have hξ : ξ 0 • (![1, 0] : Fin 2 → ℝ) + ξ 1 • ![0, 1] = ξ := by
    funext i
    fin_cases i <;> simp
  have h11 : (![1, 0] : Fin 2 → ℝ) + ![0, 1] = ![1, 1] := by
    funext i
    fin_cases i <;> simp
  rw [hξ, h11] at h
  rw [h]
  simp only [planarAhom, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

/-- **Bounds on `ā`** (Armstrong and Dario, (5.1), in dimension two). -/
theorem exists_planarAhom_bounds {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ ξ : Fin 2 → ℝ,
      c * (ξ 0 ^ 2 + ξ 1 ^ 2) ≤ 1 / 2 * ∑ i, ∑ j, ξ i * planarAhom p i j * ξ j ∧
        1 / 2 * ∑ i, ∑ j, ξ i * planarAhom p i j * ξ j ≤ 9 / 4 * (|ξ 0| + |ξ 1|) ^ 2 := by
  obtain ⟨c, hc, h⟩ := exists_tendsto_planarNuMean hpc
  refine ⟨c, hc, fun ξ => ?_⟩
  obtain ⟨L, hL, hlow, hup⟩ := h ξ
  have hLeq : planarNuLimit p ξ = L := tendsto_nhds_unique (tendsto_planarNuLimit hpc ξ) hL
  rw [← planarNuLimit_eq_planarAhom hpc, hLeq]
  exact ⟨hlow, hup⟩

end Rigidity.Percolation
