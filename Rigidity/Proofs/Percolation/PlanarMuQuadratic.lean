import Rigidity.Proofs.Percolation.PlanarMuConvergence
import Rigidity.Proofs.Percolation.PlanarNuQuadratic

/-!
# The limit of `-μ` is a quadratic form

On the partition event and for a resolved cube, `μ(U, ·)` is a quadratic form: if `u_q`, `u_r`
solve the first-variation equations for `q` and `r`, then `a u_q + b u_r` solves it for
`a q + b r`, and `μ` is minus half the energy of any solution. The identity passes to the
expectations `E[-μ(□_m, ·); P, □_m res]` and to their limit as `m → ∞`, which is therefore a
quadratic form in the slope (Armstrong and Dario, Section 5, after Definition 5.1, in dimension
two).
-/

open MeasureTheory Filter Topology LatticeProb.Percolation Rigidity.External
  Rigidity.Proofs.Section5
open scoped ENNReal Classical

namespace Rigidity.Percolation

variable {ω : Configuration 2}

/-- The coarse pairing is linear in the slope. -/
theorem coarsePairing_smul_add_smul {U : TriadicCube 2} (q r : Fin 2 → ℝ) (a b : ℝ)
    (w : ClusterFun ω U) :
    coarsePairing ω U (a • q + b • r) w =
      a * coarsePairing ω U q w + b * coarsePairing ω U r w := by
  simp only [coarsePairing_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
  split_ifs
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · ring

/-- `μ` is minus half the energy, per vertex, of any solution of its first-variation
equation. -/
theorem planarMu_eq_of_forall_clusterForm_eq (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) {q : Fin 2 → ℝ} {u : ClusterFun ω U}
    (hu : u ∈ clusterHarmonic ω U)
    (hsol : ∀ w ∈ clusterHarmonic ω U, clusterForm ω U w u = coarsePairing ω U q w) :
    planarMu ω U q = -(clusterForm ω U u u / 2) / U.volume := by
  obtain ⟨u', hu', -, hμ⟩ := exists_planarMu_minimizer hP hU q
  have hvol := U.volume_pos
  have h1 := planarMu_le hP hU q hu
  rw [← hsol u hu] at h1
  have hF' : coarsePairing ω U q u' = clusterForm ω U u' u := (hsol u' hu').symm
  have hsymm := clusterForm_symm u' u
  have hpos := clusterForm_self_nonneg (u - u')
  simp only [map_sub, LinearMap.sub_apply] at hpos
  apply le_antisymm
  · calc planarMu ω U q ≤ _ := h1
      _ = _ := by ring
  · rw [hμ, hF']
    refine div_le_div_of_nonneg_right ?_ hvol.le
    linarith

/-- **`μ` is a quadratic form in the slope** on resolved cubes. -/
theorem planarMu_smul_add_smul (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) (q r : Fin 2 → ℝ) (a b : ℝ) :
    planarMu ω U (a • q + b • r) = a ^ 2 * planarMu ω U q + b ^ 2 * planarMu ω U r +
      a * b * (planarMu ω U (q + r) - planarMu ω U q - planarMu ω U r) := by
  obtain ⟨uq, huq, hsq, -⟩ := exists_planarMu_minimizer hP hU q
  obtain ⟨ur, hur, hsr, -⟩ := exists_planarMu_minimizer hP hU r
  have hμ : ∀ a b : ℝ, planarMu ω U (a • q + b • r) =
      -(clusterForm ω U (a • uq + b • ur) (a • uq + b • ur) / 2) / U.volume := by
    intro a b
    refine planarMu_eq_of_forall_clusterForm_eq hP hU
      (Submodule.add_mem _ (Submodule.smul_mem _ a huq) (Submodule.smul_mem _ b hur))
      fun w hw => ?_
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hsq w hw, hsr w hw,
      coarsePairing_smul_add_smul]
  have e1 := hμ 1 0
  have e2 := hμ 0 1
  have e3 := hμ 1 1
  simp only [one_smul, zero_smul, add_zero, zero_add] at e1 e2 e3
  have hvol := U.volume_pos
  rw [hμ a b, e1, e2, e3]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [clusterForm_symm ur uq]
  field_simp
  ring

/-- The integrand `1{P, V res} (-μ(V, q))` as a real function. -/
theorem measurable_neg_planarMu_indicator_real (V : TriadicCube 2) (q : Fin 2 → ℝ) :
    Measurable fun ω : Configuration 2 =>
      if PlanarPartitionEvent ω ∧ PlanarResolved ω V then -planarMu ω V q else 0 := by
  have h := (measurable_planarMu_indicator V q).ennreal_toReal
  have heq : (fun ω : Configuration 2 =>
      if PlanarPartitionEvent ω ∧ PlanarResolved ω V then -planarMu ω V q else 0) = fun ω =>
      (if PlanarPartitionEvent ω ∧ PlanarResolved ω V then
        ENNReal.ofReal (-planarMu ω V q) else 0).toReal := by
    funext ω
    split_ifs with hω
    · exact (ENNReal.toReal_ofReal (neg_nonneg.2 (planarMu_nonpos hω.1 hω.2 q))).symm
    · rfl
  rw [heq]
  exact h

theorem integrable_neg_planarMu_indicator {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (V : TriadicCube 2) (q : Fin 2 → ℝ) :
    Integrable (fun ω : Configuration 2 =>
      if PlanarPartitionEvent ω ∧ PlanarResolved ω V then -planarMu ω V q else 0)
      (latticeBondLaw 2 p) := by
  obtain ⟨C, hC, h⟩ := exists_lintegral_neg_planarMu_le hpc
  have hi := integrable_toReal_of_lintegral_ne_top
    (measurable_planarMu_indicator V q).aemeasurable
    (ne_top_of_le_ne_top (ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top) (h V q))
  have heq : (fun ω : Configuration 2 =>
      if PlanarPartitionEvent ω ∧ PlanarResolved ω V then -planarMu ω V q else 0) = fun ω =>
      (if PlanarPartitionEvent ω ∧ PlanarResolved ω V then
        ENNReal.ofReal (-planarMu ω V q) else 0).toReal := by
    funext ω
    split_ifs with hω
    · exact (ENNReal.toReal_ofReal (neg_nonneg.2 (planarMu_nonpos hω.1 hω.2 q))).symm
    · rfl
  rw [heq]
  exact hi

theorem planarMuMean_eq_integral (p : unitInterval) (m : ℕ) (q : Fin 2 → ℝ) :
    planarMuMean p m q = ∫ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω ⟨m, 0⟩ then
      -planarMu ω ⟨m, 0⟩ q else 0) ∂(latticeBondLaw 2 p) := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω => by
    simp only [Pi.zero_apply]
    split_ifs with hω
    · exact neg_nonneg.2 (planarMu_nonpos hω.1 hω.2 q)
    · exact le_rfl) (measurable_neg_planarMu_indicator_real _ q).aestronglyMeasurable]
  unfold planarMuMean
  congr 2
  funext ω
  split_ifs
  · rfl
  · exact ENNReal.ofReal_zero.symm

/-- The expectations `E[-μ(□_m, ·)]` are quadratic forms in the slope. -/
theorem planarMuMean_smul_add_smul {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (m : ℕ) (q r : Fin 2 → ℝ) (a b : ℝ) :
    planarMuMean p m (a • q + b • r) = a ^ 2 * planarMuMean p m q + b ^ 2 * planarMuMean p m r +
      a * b * (planarMuMean p m (q + r) - planarMuMean p m q - planarMuMean p m r) := by
  simp only [planarMuMean_eq_integral]
  have hpt : (fun ω : Configuration 2 =>
      if PlanarPartitionEvent ω ∧ PlanarResolved ω ⟨m, 0⟩ then
        -planarMu ω ⟨m, 0⟩ (a • q + b • r) else 0) = fun ω =>
      a ^ 2 * (if PlanarPartitionEvent ω ∧ PlanarResolved ω ⟨m, 0⟩ then
        -planarMu ω ⟨m, 0⟩ q else 0) +
      b ^ 2 * (if PlanarPartitionEvent ω ∧ PlanarResolved ω ⟨m, 0⟩ then
        -planarMu ω ⟨m, 0⟩ r else 0) +
      a * b * ((if PlanarPartitionEvent ω ∧ PlanarResolved ω ⟨m, 0⟩ then
        -planarMu ω ⟨m, 0⟩ (q + r) else 0) -
        (if PlanarPartitionEvent ω ∧ PlanarResolved ω ⟨m, 0⟩ then
          -planarMu ω ⟨m, 0⟩ q else 0) -
        (if PlanarPartitionEvent ω ∧ PlanarResolved ω ⟨m, 0⟩ then
          -planarMu ω ⟨m, 0⟩ r else 0)) := by
    funext ω
    split_ifs with hω
    · rw [planarMu_smul_add_smul hω.1 hω.2 q r a b]
      ring
    · ring
  rw [hpt]
  exact integral_quadratic_combination (integrable_neg_planarMu_indicator hpc _ q)
    (integrable_neg_planarMu_indicator hpc _ r) (integrable_neg_planarMu_indicator hpc _ (q + r))
    a b

/-- The limit of the expectations `E[-μ(□_m, q); P, □_m res]` as `m → ∞`. -/
noncomputable def planarMuLimit (p : unitInterval) (q : Fin 2 → ℝ) : ℝ :=
  limUnder atTop fun m => planarMuMean p m q

theorem tendsto_planarMuLimit {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (q : Fin 2 → ℝ) :
    Tendsto (fun m => planarMuMean p m q) atTop (𝓝 (planarMuLimit p q)) := by
  obtain ⟨C, -, h⟩ := exists_tendsto_planarMuMean hpc
  obtain ⟨L, hL, -⟩ := h q
  rw [planarMuLimit, hL.limUnder_eq]
  exact hL

/-- **The limit of `-μ` is a quadratic form in the slope.** -/
theorem planarMuLimit_smul_add_smul {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (q r : Fin 2 → ℝ) (a b : ℝ) :
    planarMuLimit p (a • q + b • r) = a ^ 2 * planarMuLimit p q + b ^ 2 * planarMuLimit p r +
      a * b * (planarMuLimit p (q + r) - planarMuLimit p q - planarMuLimit p r) := by
  have h := ((((tendsto_planarMuLimit hpc q).const_mul (a ^ 2)).add
    ((tendsto_planarMuLimit hpc r).const_mul (b ^ 2))).add
    ((((tendsto_planarMuLimit hpc (q + r)).sub (tendsto_planarMuLimit hpc q)).sub
      (tendsto_planarMuLimit hpc r)).const_mul (a * b)))
  have h' : Tendsto (fun m => planarMuMean p m (a • q + b • r)) atTop
      (𝓝 (a ^ 2 * planarMuLimit p q + b ^ 2 * planarMuLimit p r +
        a * b * (planarMuLimit p (q + r) - planarMuLimit p q - planarMuLimit p r))) := by
    simp only [planarMuMean_smul_add_smul hpc]
    exact h
  exact tendsto_nhds_unique (tendsto_planarMuLimit hpc _) h'

/-- **Bounds on the limit of `-μ`.** -/
theorem exists_planarMuLimit_bounds {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : Fin 2 → ℝ,
      0 ≤ planarMuLimit p q ∧ planarMuLimit p q ≤ C * (|q 0| + |q 1|) ^ 2 := by
  obtain ⟨C, hC, h⟩ := exists_tendsto_planarMuMean hpc
  refine ⟨C, hC, fun q => ?_⟩
  obtain ⟨L, hL, hlow, hup⟩ := h q
  rw [tendsto_nhds_unique (tendsto_planarMuLimit hpc q) hL]
  exact ⟨hlow, hup⟩

end Rigidity.Percolation
