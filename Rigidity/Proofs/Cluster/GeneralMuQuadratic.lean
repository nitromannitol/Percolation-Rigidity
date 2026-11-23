import Rigidity.Proofs.Cluster.GeneralMuConvergence
import Rigidity.Proofs.Percolation.PlanarNuQuadratic

/-!
# The limit of `-μ` is a quadratic form, in every dimension

On the partition event and for a resolved cube, `μ(U, ·)` is a quadratic form in the slope
(`cubeMu_smul_add_smul`). The identity passes to the expectations `E[-μ(□_m, ·); P, □_m res]` and
to their limit as `m → ∞`, which is therefore a quadratic form in the slope, bounded by
`C |q|₁²` (Armstrong and Dario, Section 5, after Definition 5.1).
-/

open MeasureTheory Filter Topology LatticeProb.Percolation Rigidity.External
open scoped ENNReal Classical

namespace Rigidity.Percolation

variable {d : ℕ}

theorem neg_cubeMu_indicator_eq_toReal (hd : 0 < d) (V : TriadicCube d) (q : Fin d → ℝ) :
    (fun ω : Configuration d =>
      if PartitionEvent ω ∧ PartitionResolved ω V then -cubeMu ω V q else 0) = fun ω =>
      (if PartitionEvent ω ∧ PartitionResolved ω V then
        ENNReal.ofReal (-cubeMu ω V q) else 0).toReal := by
  funext ω
  split_ifs with hω
  · exact (ENNReal.toReal_ofReal (neg_nonneg.2 (cubeMu_nonpos hd hω.1 hω.2 q))).symm
  · rfl

/-- The integrand `1{P, V res} (-μ(V, q))` as a real function is measurable. -/
theorem measurable_neg_cubeMu_indicator_real (hd : 0 < d) (V : TriadicCube d)
    (q : Fin d → ℝ) :
    Measurable fun ω : Configuration d =>
      if PartitionEvent ω ∧ PartitionResolved ω V then -cubeMu ω V q else 0 := by
  rw [neg_cubeMu_indicator_eq_toReal hd]
  exact (measurable_cubeMu_indicator V q).ennreal_toReal

theorem integrable_neg_cubeMu_indicator [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (V : TriadicCube d) (q : Fin d → ℝ) :
    Integrable (fun ω : Configuration d =>
      if PartitionEvent ω ∧ PartitionResolved ω V then -cubeMu ω V q else 0)
      (latticeBondLaw d p) := by
  obtain ⟨C, hC, h⟩ := exists_lintegral_neg_cubeMu_le hd hpc
  rw [neg_cubeMu_indicator_eq_toReal (by omega)]
  exact integrable_toReal_of_lintegral_ne_top
    (measurable_cubeMu_indicator V q).aemeasurable
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h V q))

theorem cubeMuMean_eq_integral (hd : 0 < d) (p : unitInterval) (m : ℕ) (q : Fin d → ℝ) :
    cubeMuMean p m q = ∫ ω, (if PartitionEvent ω ∧ PartitionResolved ω ⟨m, 0⟩ then
      -cubeMu ω ⟨m, 0⟩ q else 0) ∂(latticeBondLaw d p) := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω => by
    simp only [Pi.zero_apply]
    split_ifs with hω
    · exact neg_nonneg.2 (cubeMu_nonpos hd hω.1 hω.2 q)
    · exact le_rfl) (measurable_neg_cubeMu_indicator_real hd _ q).aestronglyMeasurable]
  unfold cubeMuMean
  congr 2
  funext ω
  split_ifs
  · rfl
  · exact ENNReal.ofReal_zero.symm

/-- The expectations `E[-μ(□_m, ·)]` are quadratic forms in the slope. -/
theorem cubeMuMean_smul_add_smul [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (m : ℕ) (q r : Fin d → ℝ) (a b : ℝ) :
    cubeMuMean p m (a • q + b • r) = a ^ 2 * cubeMuMean p m q + b ^ 2 * cubeMuMean p m r +
      a * b * (cubeMuMean p m (q + r) - cubeMuMean p m q - cubeMuMean p m r) := by
  have hd0 : 0 < d := by omega
  simp only [cubeMuMean_eq_integral hd0]
  have hpt : (fun ω : Configuration d =>
      if PartitionEvent ω ∧ PartitionResolved ω ⟨m, 0⟩ then
        -cubeMu ω ⟨m, 0⟩ (a • q + b • r) else 0) = fun ω =>
      a ^ 2 * (if PartitionEvent ω ∧ PartitionResolved ω ⟨m, 0⟩ then
        -cubeMu ω ⟨m, 0⟩ q else 0) +
      b ^ 2 * (if PartitionEvent ω ∧ PartitionResolved ω ⟨m, 0⟩ then
        -cubeMu ω ⟨m, 0⟩ r else 0) +
      a * b * ((if PartitionEvent ω ∧ PartitionResolved ω ⟨m, 0⟩ then
        -cubeMu ω ⟨m, 0⟩ (q + r) else 0) -
        (if PartitionEvent ω ∧ PartitionResolved ω ⟨m, 0⟩ then
          -cubeMu ω ⟨m, 0⟩ q else 0) -
        (if PartitionEvent ω ∧ PartitionResolved ω ⟨m, 0⟩ then
          -cubeMu ω ⟨m, 0⟩ r else 0)) := by
    funext ω
    split_ifs with hω
    · rw [cubeMu_smul_add_smul hd0 hω.1 hω.2 q r a b]
      ring
    · ring
  rw [hpt]
  exact integral_quadratic_combination (integrable_neg_cubeMu_indicator hd hpc _ q)
    (integrable_neg_cubeMu_indicator hd hpc _ r) (integrable_neg_cubeMu_indicator hd hpc _ (q + r))
    a b

/-- **The limit of `-μ` is a quadratic form in the slope.** -/
theorem cubeMuLimit_smul_add_smul [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (q r : Fin d → ℝ) (a b : ℝ) :
    cubeMuLimit p (a • q + b • r) = a ^ 2 * cubeMuLimit p q + b ^ 2 * cubeMuLimit p r +
      a * b * (cubeMuLimit p (q + r) - cubeMuLimit p q - cubeMuLimit p r) := by
  have h := ((((tendsto_cubeMuLimit hd hpc q).const_mul (a ^ 2)).add
    ((tendsto_cubeMuLimit hd hpc r).const_mul (b ^ 2))).add
    ((((tendsto_cubeMuLimit hd hpc (q + r)).sub (tendsto_cubeMuLimit hd hpc q)).sub
      (tendsto_cubeMuLimit hd hpc r)).const_mul (a * b)))
  have h' : Tendsto (fun m => cubeMuMean p m (a • q + b • r)) atTop
      (𝓝 (a ^ 2 * cubeMuLimit p q + b ^ 2 * cubeMuLimit p r +
        a * b * (cubeMuLimit p (q + r) - cubeMuLimit p q - cubeMuLimit p r))) := by
    simp only [cubeMuMean_smul_add_smul hd hpc]
    exact h
  exact tendsto_nhds_unique (tendsto_cubeMuLimit hd hpc _) h'

/-- **Bounds on the limit of `-μ`.** -/
theorem exists_cubeMuLimit_bounds [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : Fin d → ℝ,
      0 ≤ cubeMuLimit p q ∧ cubeMuLimit p q ≤ C * (∑ i, |q i|) ^ 2 := by
  obtain ⟨C, hC, h⟩ := exists_tendsto_cubeMuMean hd hpc
  refine ⟨C, hC, fun q => ?_⟩
  obtain ⟨L, hL, hlow, hup⟩ := h q
  rw [tendsto_nhds_unique (tendsto_cubeMuLimit hd hpc q) hL]
  exact ⟨hlow, hup⟩

end Rigidity.Percolation
