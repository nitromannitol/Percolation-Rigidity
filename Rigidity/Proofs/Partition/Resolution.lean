import Rigidity.Proofs.Partition.PartitionSize
import Rigidity.Percolation.PolynomialExponential
import Rigidity.Percolation.IntegerCubeCoalescenceScales

/-!
# Triadic cubes resolved by the partition

A triadic cube `R` is resolved by the partition `𝒫` when the partition cubes of its vertices have
scale at most the scale of `R`, so that they are contained in `R` and `cl_𝒫(R) = R`. Since the
partition size is `𝒪₁(C)` (the first bound displayed after Armstrong and Dario, Definition 2.9),
a union bound over the `3^{d n}` vertices of a cube of scale `n` shows that `R` fails to be resolved
with probability at most `C exp(-c 3ⁿ)`.
-/

namespace Rigidity.Percolation

open LatticeProb LatticeProb.Percolation MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-- **Cubes are resolved by the partition outside a small event.** For supercritical bond
percolation on `ℤᵈ`, `d ≥ 2`, there are `C` and `c > 0` such that every triadic cube `R` of scale
`n` contains a vertex whose partition cube has scale larger than `n` with probability at most
`C exp(-c 3ⁿ)`. -/
theorem exists_measure_not_resolved_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ C c : ℝ, 0 < c ∧ ∀ R : TriadicCube d,
      latticeBondLaw d p {ω | ∃ z ∈ R.vertices, R.scale < (partitionCube ω z).scale} ≤
        ENNReal.ofReal (C * Real.exp (-c * (3 : ℝ) ^ R.scale)) := by
  obtain ⟨θ, hθ, hO⟩ := exists_osBound_stoppingSize hd hpc
  set C1 : ℝ := (d.factorial : ℝ) / (1 / θ / 2) ^ d with hC1def
  have hC1 : 0 ≤ C1 := by positivity
  refine ⟨C1 + Real.exp (1 / 2), 1 / θ / 2, by positivity, fun R => ?_⟩
  set y : ℝ := (3 : ℝ) ^ R.scale with hydef
  have hy0 : 0 ≤ y := by positivity
  by_cases hyθ : θ ≤ y
  · set t : ℝ := y / θ with htdef
    have ht : 1 ≤ t := by rw [htdef, le_div_iff₀ hθ, one_mul]; exact hyθ
    have htθ : t * θ = y := by rw [htdef]; field_simp
    set F := R.toIntegerCube.vertices
    have hsub : {ω | ∃ z ∈ R.vertices, R.scale < (partitionCube ω z).scale} ≤ᵐ[latticeBondLaw d p]
        ⋃ z ∈ F, {ω | t * θ < max (TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z) 0} := by
      filter_upwards [ae_partitionEvent hd hpc] with ω hP
      rintro ⟨z, hzR, hlt⟩
      show ω ∈ ⋃ z ∈ F,
        {ω | t * θ < max (TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z) 0}
      refine Set.mem_iUnion₂.2 ⟨z, (R.mem_toIntegerCube_vertices z).2 hzR, ?_⟩
      show t * θ < max (TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z) 0
      rw [stoppingSize_goodCubes_eq hP z, htθ, max_eq_left (by positivity)]
      exact pow_lt_pow_right₀ (by norm_num) hlt
    have hcard : ((F.card : ℕ) : ℝ) = y ^ d := by
      rw [IntegerCube.card_vertices]
      change (((3 ^ R.scale) ^ d : ℕ) : ℝ) = _
      push_cast
      rfl
    calc latticeBondLaw d p {ω | ∃ z ∈ R.vertices, R.scale < (partitionCube ω z).scale}
        ≤ latticeBondLaw d p (⋃ z ∈ F,
            {ω | t * θ < max (TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z) 0}) :=
          measure_mono_ae hsub
      _ ≤ ∑ z ∈ F, latticeBondLaw d p
            {ω | t * θ < max (TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z) 0} :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ _z ∈ F, ENNReal.ofReal (Real.exp (-(t ^ (1 : ℝ)))) :=
          Finset.sum_le_sum fun z _ => hO z t ht
      _ = ENNReal.ofReal (y ^ d * Real.exp (-(1 / θ) * y)) := by
          rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (Nat.cast_nonneg _), hcard, Real.rpow_one, htdef,
            show -(y / θ) = -(1 / θ) * y by ring]
      _ ≤ ENNReal.ofReal ((C1 + Real.exp (1 / 2)) * Real.exp (-(1 / θ / 2) * y)) := by
          apply ENNReal.ofReal_le_ofReal
          have h := pow_mul_exp_neg_le d (c := 1 / θ) (by positivity) hy0
          rw [← hC1def] at h
          have he : 0 ≤ Real.exp (-(1 / θ / 2) * y) := Real.exp_nonneg _
          nlinarith [Real.exp_pos (1 / 2)]
  · have hyθ' : y < θ := not_le.1 hyθ
    refine (prob_le_one).trans ?_
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    have h1 : 1 ≤ Real.exp (1 / 2) * Real.exp (-(1 / θ / 2) * y) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      have : (1 / θ / 2) * y ≤ 1 / 2 := by
        rw [div_div, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith
      linarith
    have he : 0 ≤ Real.exp (-(1 / θ / 2) * y) := Real.exp_nonneg _
    nlinarith

end Rigidity.Percolation
