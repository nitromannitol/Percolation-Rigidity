import Rigidity.Proofs.Partition.AlmostSure
import Rigidity.Percolation.TriadicExceptionalSupremum
import Rigidity.Percolation.IntegerCubeCoalescenceScales
import Rigidity.Percolation.PolynomialExponential

/-!
# The largest partition cube in a triadic cube

Part of Armstrong and Dario, Proposition 2.4 (the second bound in its conclusion): for every
`α > 0` there is a random scale `M` with a stretched-exponential moment of order `α` such that,
whenever `3ᵐ > M`, every partition cube meeting the triadic cube of scale `m` has side at most
`3^{α m}`. Armstrong and Dario take `α = d / (d + t)`.

The proof is a union bound: by Markov's inequality and the uniform exponential moment of the
size of partition cubes, a fixed vertex lies in a partition cube of side larger than `3^{α m}`
with probability at most `2 exp(-3^{α m} / θ)`; the `3^{d m}` vertices of the cube contribute a
polynomial factor, absorbed into the exponential, and the supremum of the exceptional scales has
a stretched-exponential moment.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-- Markov's inequality for an exponential moment bounded by two. -/
theorem measure_lt_le_of_exp_moment {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] {f : Ω → ℝ} {θ : ℝ} (hθ : 0 < θ)
    (hint : Integrable (fun ω => Real.exp (f ω / θ)) μ)
    (hle : (∫ ω, Real.exp (f ω / θ) ∂μ) ≤ 2) (t : ℝ) :
    μ {ω | t < f ω} ≤ ENNReal.ofReal (2 * Real.exp (-(t / θ))) := by
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun ω => (Real.exp_pos (f ω / θ)).le) hint (Real.exp (t / θ))
  have hsub : {ω | t < f ω} ⊆ {ω | Real.exp (t / θ) ≤ Real.exp (f ω / θ)} := by
    intro ω hω
    exact Real.exp_le_exp.2 (div_le_div_of_nonneg_right (le_of_lt hω) hθ.le)
  have hpos := Real.exp_pos (t / θ)
  have hreal : μ.real {ω | Real.exp (t / θ) ≤ Real.exp (f ω / θ)} ≤
      2 * Real.exp (-(t / θ)) := by
    rw [Real.exp_neg, le_mul_inv_iff₀ hpos]
    linarith
  calc μ {ω | t < f ω} ≤ μ {ω | Real.exp (t / θ) ≤ Real.exp (f ω / θ)} := measure_mono hsub
    _ = ENNReal.ofReal (μ.real {ω | Real.exp (t / θ) ≤ Real.exp (f ω / θ)}) := by
      rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top μ _)]
    _ ≤ ENNReal.ofReal (2 * Real.exp (-(t / θ))) := ENNReal.ofReal_le_ofReal hreal

/-- A polynomial in `3ᵐ` of degree `d` times `exp(-3^{α m} / θ)` is at most a constant times
`exp(-3^{α m} / (2θ))`. -/
theorem pow_mul_exp_neg_rpow_le {α θ : ℝ} (hα : 0 < α) (hθ : 0 < θ) (m : ℕ) :
    ((3 : ℝ) ^ m) ^ d * (2 * Real.exp (-(((3 : ℝ) ^ m) ^ α / θ))) ≤
      2 * (((⌈(d : ℝ) / α⌉₊).factorial : ℝ) / (1 / θ / 2) ^ ⌈(d : ℝ) / α⌉₊) *
        Real.exp (-(1 / θ / 2) * ((3 : ℝ) ^ m) ^ α) := by
  set K : ℕ := ⌈(d : ℝ) / α⌉₊
  set y : ℝ := (3 : ℝ) ^ m
  have hy : 1 ≤ y := one_le_pow₀ (by norm_num)
  set t : ℝ := y ^ α
  have ht : 0 ≤ t := by positivity
  have hdK : (d : ℝ) ≤ α * K := by
    have h := Nat.le_ceil ((d : ℝ) / α)
    rw [div_le_iff₀ hα] at h
    linarith
  have hyd : y ^ d ≤ t ^ K := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    exact Real.rpow_le_rpow_of_exponent_le hy hdK
  have hexp : Real.exp (-(t / θ)) = Real.exp (-(1 / θ) * t) := by
    congr 1
    ring
  have hc : 0 < 1 / θ := by positivity
  calc y ^ d * (2 * Real.exp (-(t / θ))) = 2 * (y ^ d * Real.exp (-(1 / θ) * t)) := by
        rw [hexp]; ring
    _ ≤ 2 * (t ^ K * Real.exp (-(1 / θ) * t)) := by gcongr
    _ ≤ 2 * ((K.factorial : ℝ) / (1 / θ / 2) ^ K * Real.exp (-(1 / θ / 2) * t)) :=
        mul_le_mul_of_nonneg_left (pow_mul_exp_neg_le K hc ht) (by norm_num)
    _ = _ := by ring

/-- **The largest partition cube in a triadic cube** (Armstrong and Dario, Proposition 2.4, the
second bound). Given a uniform exponential moment of the size of the partition cubes, for every
family of triadic cubes `A m` of scale `m` and every `α > 0` there is a measurable random scale
`M` with a stretched-exponential moment of order `α` such that, whenever `M < 3ᵐ`, the
stopping size at every vertex of `A m` is at most `3^{α m}`. -/
theorem exists_scale_stoppingSize_le (μ : Measure (Configuration d)) [IsProbabilityMeasure μ]
    {θ : ℝ} (hθ : 0 < θ)
    (hmom : ∀ x : Vertex d,
      Integrable (fun ω => Real.exp (TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x / θ))
        μ ∧
      (∫ ω, Real.exp (TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x / θ) ∂μ) ≤ 2)
    (A : ℕ → TriadicCube d) (hA : ∀ m, (A m).scale = m) {α : ℝ} (hα : 0 < α) :
    ∃ M : Configuration d → ℝ≥0∞, Measurable M ∧
      (∃ θ' : ℝ, 0 < θ' ∧ Integrable (fun ω => Real.exp (((M ω).toReal / θ') ^ α)) μ ∧
        (∫ ω, Real.exp (((M ω).toReal / θ') ^ α) ∂μ) ≤ 2) ∧
      ∀ (ω : Configuration d) (m : ℕ), M ω < 3 ^ m → ∀ x ∈ (A m).vertices,
        TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x ≤ ((3 : ℝ) ^ m) ^ α := by
  classical
  set f : Vertex d → Configuration d → ℝ :=
    fun x ω => TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x with hfdef
  have hfm : ∀ x, Measurable (f x) := fun x =>
    TriadicCube.measurable_stoppingSize _ TriadicCube.measurableSet_mem_goodCubes x
  set E : ℕ → Set (Configuration d) :=
    fun m => {ω | ∃ x ∈ (A m).vertices, ((3 : ℝ) ^ m) ^ α < f x ω} with hEdef
  have hE_eq : ∀ m, E m =
      ⋃ x ∈ (A m).toIntegerCube.vertices, {ω | ((3 : ℝ) ^ m) ^ α < f x ω} := by
    intro m
    ext ω
    simp only [hEdef, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop,
      TriadicCube.mem_toIntegerCube_vertices]
  have hEm : ∀ m, MeasurableSet (E m) := by
    intro m
    rw [hE_eq]
    exact Finset.measurableSet_biUnion _ fun x _ => measurableSet_lt measurable_const (hfm x)
  set C' : ℝ := 2 * (((⌈(d : ℝ) / α⌉₊).factorial : ℝ) / (1 / θ / 2) ^ ⌈(d : ℝ) / α⌉₊)
    with hC'def
  have hE : ∀ m, μ (E m) ≤
      ENNReal.ofReal C' * ENNReal.ofReal (Real.exp (-(1 / θ / 2) * ((3 : ℝ) ^ m) ^ α)) := by
    intro m
    have hcard : ((A m).toIntegerCube.vertices.card : ℝ) = ((3 : ℝ) ^ m) ^ d := by
      rw [IntegerCube.card_vertices]
      change (((3 ^ (A m).scale) ^ d : ℕ) : ℝ) = _
      rw [hA m]
      push_cast
      ring
    calc μ (E m) ≤ ∑ x ∈ (A m).toIntegerCube.vertices, μ {ω | ((3 : ℝ) ^ m) ^ α < f x ω} := by
          rw [hE_eq]
          exact measure_biUnion_finset_le _ _
      _ ≤ ∑ x ∈ (A m).toIntegerCube.vertices,
            ENNReal.ofReal (2 * Real.exp (-(((3 : ℝ) ^ m) ^ α / θ))) :=
          Finset.sum_le_sum fun x _ =>
            measure_lt_le_of_exp_moment μ hθ (hmom x).1 (hmom x).2 _
      _ = ENNReal.ofReal (((3 : ℝ) ^ m) ^ d * (2 * Real.exp (-(((3 : ℝ) ^ m) ^ α / θ)))) := by
          rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (Nat.cast_nonneg _), hcard]
      _ ≤ ENNReal.ofReal (C' * Real.exp (-(1 / θ / 2) * ((3 : ℝ) ^ m) ^ α)) :=
          ENNReal.ofReal_le_ofReal (pow_mul_exp_neg_rpow_le hα hθ m)
      _ = _ := by
          rw [ENNReal.ofReal_mul (by positivity)]
  obtain ⟨θ', hθ', hint, hle⟩ := exceptionalScale_exp_moment μ E hEm (ENNReal.ofReal C')
    ENNReal.ofReal_ne_top α (1 / θ / 2) hα (by positivity) hE
  refine ⟨exceptionalScale E, measurable_exceptionalScale E hEm, ⟨θ', hθ', hint, hle⟩, ?_⟩
  intro ω m hM x hx
  by_contra hlt
  have hωE : ω ∈ E m := ⟨x, hx, not_le.1 hlt⟩
  have h3 : (3 : ℝ≥0∞) ^ m ≤ exceptionalScale E ω := by
    unfold exceptionalScale
    exact le_iSup_of_le m (by rw [if_pos hωE])
  exact absurd hM (not_lt.2 h3)

/-- **The largest partition cube in a triadic cube** for supercritical bond percolation on
`ℤᵈ`, `d ≥ 2` (Armstrong and Dario, Proposition 2.4, the second bound): for every `α > 0` there
is a measurable random scale `M` with a stretched-exponential moment of order `α` such that,
almost surely, whenever `M < 3ᵐ`, every vertex of the triadic cube of scale `m` centred at the
origin lies in a partition cube of side at most `3^{α m}`. -/
theorem exists_scale_partitionCube_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) {α : ℝ} (hα : 0 < α) :
    ∃ M : Configuration d → ℝ≥0∞, Measurable M ∧
      (∃ θ' : ℝ, 0 < θ' ∧
        Integrable (fun ω => Real.exp (((M ω).toReal / θ') ^ α)) (latticeBondLaw d p) ∧
        (∫ ω, Real.exp (((M ω).toReal / θ') ^ α) ∂(latticeBondLaw d p)) ≤ 2) ∧
      ∀ᵐ ω ∂(latticeBondLaw d p), ∀ m : ℕ, M ω < 3 ^ m →
        ∀ x ∈ (⟨m, 0⟩ : TriadicCube d).vertices,
          (3 : ℝ) ^ (partitionCube ω x).scale ≤ ((3 : ℝ) ^ m) ^ α := by
  obtain ⟨hae, ⟨θ, hθ, hmom⟩, -⟩ := partition_estimates hd hpc
  obtain ⟨M, hMm, hMmom, hM⟩ := exists_scale_stoppingSize_le (latticeBondLaw d p) hθ hmom
    (fun m => ⟨m, 0⟩) (fun _ => rfl) hα
  refine ⟨M, hMm, hMmom, ?_⟩
  filter_upwards [hae] with ω hP m hm x hx
  rw [← TriadicCube.stoppingSize_eq_of_mem (mem_partitionCube hP x) (partitionCube_spec hP x).2]
  exact hM ω m hm x hx

end Rigidity.Percolation
