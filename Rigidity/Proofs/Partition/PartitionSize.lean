import Rigidity.Proofs.Partition.AlmostSure
import Rigidity.Percolation.TriadicStochasticBound

/-!
# The size of the partition cubes

Armstrong and Dario, the first bound displayed after Definition 2.9: the size of the partition
cube of a vertex satisfies `size(𝒫(x)) ≤ 𝒪₁(C)` uniformly in `x`, in the tail form of the
stochastic notation: `P[size(𝒫(x)) > t θ] ≤ exp(-t)` for every `t ≥ 1`. The size is the stopping
size, the side of the partition cube on the partition event. Consequently all its moments are
finite: `E[size(𝒫(x))^τ] ≤ 2 τ! θ^τ`, and `E[∑_{x ∈ U} size(𝒫(x))^τ] ≤ 2 τ! θ^τ |U|`.
-/

namespace Rigidity.Percolation

open LatticeProb LatticeProb.Percolation MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-- **The size of the partition cubes is `𝒪₁(θ)`** uniformly in the vertex. -/
theorem exists_osBound_stoppingSize [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ x : Vertex d, OsBound (latticeBondLaw d p) 1 θ
      (fun ω => TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x) := by
  obtain ⟨C1, c, hC1, hc, hq⟩ := exists_measure_not_mem_goodCubes_le hd hpc
  have hprob : ∀ R : TriadicCube d, latticeBondLaw d p {ω | R ∉ TriadicCube.goodCubes ω} ≤
      ENNReal.ofReal C1 * ENNReal.ofReal (Real.exp (-c * ((3 : ℝ) ^ R.scale) ^ (1 : ℝ))) := by
    intro R
    rw [Real.rpow_one, ← ENNReal.ofReal_mul hC1]
    exact hq R
  obtain ⟨θ, hθ, h⟩ := TriadicCube.uniform_osBound_of_stopping_side (latticeBondLaw d p)
    TriadicCube.goodCubes (ENNReal.ofReal C1) ENNReal.ofReal_ne_top 1 c one_pos hc hprob
  exact ⟨θ, hθ, fun x => h x _ (fun ω => TriadicCube.stoppingSize_nonneg _ x)
    (fun ω => TriadicCube.exists_stopping_of_stoppingSize_pos _ x)⟩

/-- On the partition event the stopping size is the side of the partition cube. -/
theorem stoppingSize_goodCubes_eq {ω : Configuration d} (hP : PartitionEvent ω) (x : Vertex d) :
    TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x = (3 : ℝ) ^ (partitionCube ω x).scale :=
  TriadicCube.stoppingSize_eq_of_mem (mem_partitionCube hP x) (partitionCube_spec hP x).2

/-- **Moments from an exponential moment.** If `E[exp(X / θ)] ≤ 2` for a nonnegative measurable
`X`, then `X^τ` is integrable with `E[X^τ] ≤ 2 τ! θ^τ`. -/
theorem integrable_pow_of_exp_moment {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {X : Ω → ℝ} (hXm : Measurable X) (hX0 : ∀ ω, 0 ≤ X ω) {θ : ℝ} (hθ : 0 < θ)
    (hint : Integrable (fun ω => Real.exp (X ω / θ)) μ)
    (hle : (∫ ω, Real.exp (X ω / θ) ∂μ) ≤ 2) (τ : ℕ) :
    Integrable (fun ω => X ω ^ τ) μ ∧
      (∫ ω, X ω ^ τ ∂μ) ≤ 2 * (τ.factorial : ℝ) * θ ^ τ := by
  have hpt : ∀ ω, X ω ^ τ ≤ (τ.factorial : ℝ) * θ ^ τ * Real.exp (X ω / θ) := by
    intro ω
    have h := Real.pow_div_factorial_le_exp (X ω / θ) (div_nonneg (hX0 ω) hθ.le) τ
    have hfac : (0 : ℝ) < τ.factorial := by exact_mod_cast Nat.factorial_pos τ
    rw [div_le_iff₀ hfac, div_pow] at h
    have hθτ : (0 : ℝ) < θ ^ τ := pow_pos hθ τ
    rw [div_le_iff₀ hθτ] at h
    nlinarith [Real.exp_pos (X ω / θ)]
  have hdom : Integrable (fun ω => (τ.factorial : ℝ) * θ ^ τ * Real.exp (X ω / θ)) μ :=
    hint.const_mul _
  have hint' : Integrable (fun ω => X ω ^ τ) μ := by
    refine hdom.mono' (hXm.pow_const τ).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hX0 ω) τ)]
    exact hpt ω
  refine ⟨hint', ?_⟩
  calc (∫ ω, X ω ^ τ ∂μ) ≤ ∫ ω, (τ.factorial : ℝ) * θ ^ τ * Real.exp (X ω / θ) ∂μ :=
        integral_mono hint' hdom hpt
    _ = (τ.factorial : ℝ) * θ ^ τ * ∫ ω, Real.exp (X ω / θ) ∂μ := integral_const_mul _ _
    _ ≤ (τ.factorial : ℝ) * θ ^ τ * 2 := by
        apply mul_le_mul_of_nonneg_left hle
        positivity
    _ = 2 * (τ.factorial : ℝ) * θ ^ τ := by ring

/-- **Moments of the partition sizes.** For supercritical bond percolation on `ℤᵈ`, `d ≥ 2`, there
is `θ > 0` such that for every `τ ∈ ℕ` and every finite set `U` of vertices,
`E[∑_{x ∈ U} size(𝒫(x))^τ] ≤ 2 τ! θ^τ |U|`, the sum being integrable. -/
theorem exists_integral_sum_stoppingSize_pow_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ (τ : ℕ) (U : Finset (Vertex d)),
      Integrable (fun ω => ∑ x ∈ U,
        TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x ^ τ) (latticeBondLaw d p) ∧
      (∫ ω, ∑ x ∈ U, TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x ^ τ
        ∂(latticeBondLaw d p)) ≤ 2 * (τ.factorial : ℝ) * θ ^ τ * U.card := by
  obtain ⟨-, ⟨θ, hθ, hmom⟩, -⟩ := partition_estimates hd hpc
  refine ⟨θ, hθ, fun τ U => ?_⟩
  have h : ∀ x, Integrable (fun ω => TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x ^ τ)
      (latticeBondLaw d p) ∧
      (∫ ω, TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x ^ τ ∂(latticeBondLaw d p)) ≤
        2 * (τ.factorial : ℝ) * θ ^ τ := fun x =>
    integrable_pow_of_exp_moment _
      (TriadicCube.measurable_stoppingSize _ TriadicCube.measurableSet_mem_goodCubes x)
      (fun ω => TriadicCube.stoppingSize_nonneg _ x) hθ (hmom x).1 (hmom x).2 τ
  refine ⟨integrable_finsetSum U fun x _ => (h x).1, ?_⟩
  rw [integral_finsetSum U fun x _ => (h x).1]
  calc ∑ x ∈ U, ∫ ω, TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x ^ τ
        ∂(latticeBondLaw d p)
      ≤ ∑ _x ∈ U, 2 * (τ.factorial : ℝ) * θ ^ τ := Finset.sum_le_sum fun x _ => (h x).2
    _ = 2 * (τ.factorial : ℝ) * θ ^ τ * U.card := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring

end Rigidity.Percolation
