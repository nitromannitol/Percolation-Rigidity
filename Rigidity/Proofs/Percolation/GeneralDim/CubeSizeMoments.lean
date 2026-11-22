import Rigidity.Proofs.Percolation.GeneralDim.CubeBoundaryWeightBound
import Rigidity.Proofs.Partition.PartitionSize
import Rigidity.Percolation.PolynomialExponential

/-!
# Moments of the partition sizes on triadic cubes and on their faces

For supercritical bond percolation on `ℤ^d`, `d ≥ 2`, the partition size `s_x = size(□_𝒫(x))`
has exponential moments uniformly in `x` (Armstrong and Dario, Proposition 2.1 and the bound
after Definition 2.9). Consequently, for a triadic cube `U` of side `L`,

* `E[∑_{x ∈ U} s_x^{2d-2}] ≤ C |U|`;
* `E[∑_{x ∈ ∂U} s_x] ≤ C L^{d-1}`, the faces being counted with multiplicity;
* `E[∑_{z ∈ U} ∑_i s_z^{2d-2} 1{margin_i(z) < s_z}] ≤ C L^{d-1}`,

where the last bound uses `s^k 1{m < s} ≤ k! (4θ)^k exp(s/θ) exp(-m/(2θ))` and the exponential
sums of the margins. These are the bounds on the boundary terms in the proofs of Lemmas 4.5 and
4.7 of Armstrong and Dario.
-/

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External
open scoped Classical ENNReal

namespace Rigidity.Percolation

variable {d : ℕ}

theorem stoppingSize_nonneg (G : Set (TriadicCube d)) (x : Vertex d) :
    0 ≤ TriadicCube.stoppingSize G x := by
  unfold TriadicCube.stoppingSize
  exact ENNReal.toReal_nonneg

theorem measurable_stoppingSize_goodCubes (x : Vertex d) :
    Measurable fun ω : Configuration d =>
      TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x :=
  TriadicCube.measurable_stoppingSize (fun ω => TriadicCube.goodCubes ω)
    (fun Q => Q.measurableSet_mem_goodCubes) x

/-- `y^k 1{m < y} ≤ k! (4θ)^k exp(y/θ) exp(-m/(2θ))` for `y ≥ 0`. -/
theorem pow_mul_ite_lt_le (k : ℕ) {θ y : ℝ} (hθ : 0 < θ) (hy : 0 ≤ y) (m : ℝ) :
    y ^ k * (if m < y then 1 else 0) ≤
      (k.factorial : ℝ) * (4 * θ) ^ k * Real.exp (y / θ) * Real.exp (-m / (2 * θ)) := by
  have hpos : 0 ≤ (k.factorial : ℝ) * (4 * θ) ^ k * Real.exp (y / θ) * Real.exp (-m / (2 * θ)) :=
    by positivity
  split_ifs with hm
  · rw [mul_one]
    have h1 := pow_mul_exp_neg_le k (c := 1 / (2 * θ)) (by positivity) hy
    have h2 : Real.exp (-(1 / (2 * θ) / 2) * y) ≤ 1 :=
      Real.exp_le_one_iff.2 (by
        have : 0 ≤ 1 / (2 * θ) / 2 * y := by positivity
        linarith)
    have hθ' : θ ≠ 0 := hθ.ne'
    have hc : (k.factorial : ℝ) / (1 / (2 * θ) / 2) ^ k = (k.factorial : ℝ) * (4 * θ) ^ k := by
      rw [show (1 : ℝ) / (2 * θ) / 2 = (4 * θ)⁻¹ by field_simp; ring, inv_pow, div_inv_eq_mul]
    have h3 : y ^ k * Real.exp (-(1 / (2 * θ)) * y) ≤ (k.factorial : ℝ) * (4 * θ) ^ k := by
      calc y ^ k * Real.exp (-(1 / (2 * θ)) * y)
          ≤ (k.factorial : ℝ) / (1 / (2 * θ) / 2) ^ k * Real.exp (-(1 / (2 * θ) / 2) * y) := h1
        _ ≤ (k.factorial : ℝ) / (1 / (2 * θ) / 2) ^ k * 1 :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = _ := by rw [mul_one, hc]
    have h4 : 1 ≤ Real.exp (y / (2 * θ)) * Real.exp (-m / (2 * θ)) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      rw [← add_div]
      exact div_nonneg (by linarith) (by positivity)
    have e : Real.exp (y / θ) = Real.exp (y / (2 * θ)) * Real.exp (y / (2 * θ)) := by
      rw [← Real.exp_add]
      congr 1
      field_simp
      ring
    have e2 : y ^ k = y ^ k * Real.exp (-(1 / (2 * θ)) * y) * Real.exp (y / (2 * θ)) := by
      rw [mul_assoc, ← Real.exp_add]
      rw [show -(1 / (2 * θ)) * y + y / (2 * θ) = 0 by field_simp; ring, Real.exp_zero, mul_one]
    calc y ^ k = y ^ k * Real.exp (-(1 / (2 * θ)) * y) * Real.exp (y / (2 * θ)) := e2
      _ ≤ (k.factorial : ℝ) * (4 * θ) ^ k * Real.exp (y / (2 * θ)) :=
          mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
      _ = (k.factorial : ℝ) * (4 * θ) ^ k * Real.exp (y / (2 * θ)) * 1 := by ring
      _ ≤ (k.factorial : ℝ) * (4 * θ) ^ k * Real.exp (y / (2 * θ)) *
          (Real.exp (y / (2 * θ)) * Real.exp (-m / (2 * θ))) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = _ := by rw [e]; ring
  · rw [mul_zero]
    exact hpos

/-- **The tail-weighted moments on the margins of a triadic cube.** -/
theorem exists_integral_sum_margin_le [NeZero d] (hd : 2 ≤ d) {prob : unitInterval}
    (hpc : criticalProbability d < (prob : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U : TriadicCube d,
      Integrable (fun ω => ∑ z ∈ U.toIntegerCube.vertices, ∑ i : Fin d,
        TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z ^ (2 * (d - 1)) *
          (if (U.margin z i : ℝ) < TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z
            then 1 else 0)) (latticeBondLaw d prob) ∧
      ∫ ω, ∑ z ∈ U.toIntegerCube.vertices, ∑ i : Fin d,
        TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z ^ (2 * (d - 1)) *
          (if (U.margin z i : ℝ) < TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z
            then 1 else 0) ∂(latticeBondLaw d prob) ≤ C * ((3 : ℝ) ^ U.scale) ^ (d - 1) := by
  obtain ⟨-, ⟨θ, hθ, hmom⟩, -⟩ := partition_estimates hd hpc
  set k := 2 * (d - 1)
  set A := (k.factorial : ℝ) * (4 * θ) ^ k
  have hA : 0 ≤ A := by positivity
  set a := 2 * θ
  have ha : 0 < a := by positivity
  set K := (1 - Real.exp (-1 / a))⁻¹
  have hK : 0 ≤ K := by
    have : Real.exp (-1 / a) < 1 := by
      have h := Real.exp_lt_exp.2 (div_neg_of_neg_of_pos (by norm_num : (-1 : ℝ) < 0) ha)
      rwa [Real.exp_zero] at h
    exact inv_nonneg.2 (by linarith)
  refine ⟨d * (2 * A * (2 * K)), by positivity, fun U => ?_⟩
  set μ := latticeBondLaw d prob
  set f : Vertex d → Configuration d → ℝ := fun z ω =>
    TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z with hf
  have hfm : ∀ z, Measurable (f z) := measurable_stoppingSize_goodCubes
  have hterm_meas : ∀ z (i : Fin d), Measurable fun ω => f z ω ^ k *
      (if (U.margin z i : ℝ) < f z ω then (1 : ℝ) else 0) := fun z i =>
    ((hfm z).pow_const k).mul (Measurable.ite (measurableSet_lt measurable_const (hfm z))
      measurable_const measurable_const)
  have hterm_le : ∀ z (i : Fin d) ω, f z ω ^ k *
      (if (U.margin z i : ℝ) < f z ω then (1 : ℝ) else 0) ≤
      A * Real.exp (f z ω / θ) * Real.exp (-(U.margin z i : ℝ) / a) := fun z i ω =>
    pow_mul_ite_lt_le k hθ (stoppingSize_nonneg _ _) _
  have hterm_int : ∀ z (i : Fin d), Integrable (fun ω => f z ω ^ k *
      (if (U.margin z i : ℝ) < f z ω then (1 : ℝ) else 0)) μ := fun z i =>
    (((hmom z).1.const_mul A).mul_const _).mono' (hterm_meas z i).aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (stoppingSize_nonneg _ _) _)
          (by split_ifs <;> norm_num))]
        exact hterm_le z i ω)
  have hterm_bound : ∀ z (i : Fin d), ∫ ω, f z ω ^ k *
      (if (U.margin z i : ℝ) < f z ω then (1 : ℝ) else 0) ∂μ ≤
      2 * A * Real.exp (-(U.margin z i : ℝ) / a) := by
    intro z i
    calc ∫ ω, f z ω ^ k * (if (U.margin z i : ℝ) < f z ω then (1 : ℝ) else 0) ∂μ
        ≤ ∫ ω, A * Real.exp (f z ω / θ) * Real.exp (-(U.margin z i : ℝ) / a) ∂μ :=
          integral_mono (hterm_int z i) (((hmom z).1.const_mul A).mul_const _)
            (hterm_le z i)
      _ = A * (∫ ω, Real.exp (f z ω / θ) ∂μ) * Real.exp (-(U.margin z i : ℝ) / a) := by
          rw [integral_mul_const, integral_const_mul]
      _ ≤ A * 2 * Real.exp (-(U.margin z i : ℝ) / a) := by
          gcongr
          exact (hmom z).2
      _ = 2 * A * Real.exp (-(U.margin z i : ℝ) / a) := by ring
  have hint : Integrable (fun ω => ∑ z ∈ U.toIntegerCube.vertices, ∑ i : Fin d,
      f z ω ^ k * (if (U.margin z i : ℝ) < f z ω then (1 : ℝ) else 0)) μ :=
    integrable_finsetSum _ fun z _ => integrable_finsetSum _ fun i _ => hterm_int z i
  refine ⟨hint, ?_⟩
  rw [integral_finsetSum _ fun z _ => integrable_finsetSum _ fun i _ => hterm_int z i]
  calc ∑ z ∈ U.toIntegerCube.vertices, ∫ ω, ∑ i : Fin d,
        f z ω ^ k * (if (U.margin z i : ℝ) < f z ω then (1 : ℝ) else 0) ∂μ
      ≤ ∑ z ∈ U.toIntegerCube.vertices, ∑ i : Fin d,
          2 * A * Real.exp (-(U.margin z i : ℝ) / a) :=
        Finset.sum_le_sum fun z _ => by
          rw [integral_finsetSum _ fun i _ => hterm_int z i]
          exact Finset.sum_le_sum fun i _ => hterm_bound z i
    _ = 2 * A * ∑ i : Fin d, ∑ z ∈ U.toIntegerCube.vertices,
          Real.exp (-(U.margin z i : ℝ) / a) := by
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
    _ ≤ 2 * A * ∑ _i : Fin d, 2 * ((3 : ℝ) ^ U.scale) ^ (d - 1) * K :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => sum_exp_neg_margin_le U i ha)
          (by positivity)
    _ = d * (2 * A * (2 * K)) * ((3 : ℝ) ^ U.scale) ^ (d - 1) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- **Moments of the partition sizes on the faces of a cube.** -/
theorem exists_integral_sum_faces_le [NeZero d] (hd : 2 ≤ d) {prob : unitInterval}
    (hpc : criticalProbability d < (prob : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U : TriadicCube d,
      Integrable (fun ω => ∑ i : Fin d,
        (∑ x ∈ U.toIntegerCube.upperFace i, TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x +
          ∑ x ∈ U.toIntegerCube.lowerFace i,
            TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x)) (latticeBondLaw d prob) ∧
      ∫ ω, ∑ i : Fin d,
        (∑ x ∈ U.toIntegerCube.upperFace i, TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x +
          ∑ x ∈ U.toIntegerCube.lowerFace i,
            TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x) ∂(latticeBondLaw d prob) ≤
        C * ((3 : ℝ) ^ U.scale) ^ (d - 1) := by
  obtain ⟨θ, hθ, hmom⟩ := exists_integral_sum_stoppingSize_pow_le hd hpc
  refine ⟨d * (2 * (2 * θ)), by positivity, fun U => ?_⟩
  set μ := latticeBondLaw d prob
  have hs : (U.toIntegerCube.size : ℝ) = (3 : ℝ) ^ U.scale := by
    change ((3 ^ U.scale : ℕ) : ℝ) = _
    push_cast
    rfl
  have hF : ∀ F : Finset (Vertex d), F.card ≤ U.toIntegerCube.size ^ (d - 1) →
      Integrable (fun ω => ∑ x ∈ F, TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x) μ ∧
      ∫ ω, ∑ x ∈ F, TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x ∂μ ≤
        2 * θ * ((3 : ℝ) ^ U.scale) ^ (d - 1) := by
    intro F hFc
    obtain ⟨hi, hb⟩ := hmom 1 F
    simp only [pow_one, Nat.factorial_one, Nat.cast_one, mul_one] at hi hb
    refine ⟨hi, hb.trans ?_⟩
    have hc : (F.card : ℝ) ≤ ((3 : ℝ) ^ U.scale) ^ (d - 1) := by
      rw [← hs]
      exact_mod_cast hFc
    nlinarith
  have hup := fun i => hF _ (U.toIntegerCube.card_upperFace_le i)
  have hlow := fun i => hF _ (U.toIntegerCube.card_lowerFace_le i)
  have hsi : ∀ i, Integrable (fun ω => ∑ x ∈ U.toIntegerCube.upperFace i,
      TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x + ∑ x ∈ U.toIntegerCube.lowerFace i,
        TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x) μ := fun i =>
    (hup i).1.add (hlow i).1
  refine ⟨integrable_finsetSum _ fun i _ => hsi i, ?_⟩
  rw [integral_finsetSum _ fun i _ => hsi i]
  calc ∑ i : Fin d, ∫ ω, (∑ x ∈ U.toIntegerCube.upperFace i,
        TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x + ∑ x ∈ U.toIntegerCube.lowerFace i,
          TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x) ∂μ
      ≤ ∑ _i : Fin d, (2 * θ * ((3 : ℝ) ^ U.scale) ^ (d - 1) +
          2 * θ * ((3 : ℝ) ^ U.scale) ^ (d - 1)) :=
        Finset.sum_le_sum fun i _ => by
          rw [integral_add (hup i).1 (hlow i).1]
          exact add_le_add (hup i).2 (hlow i).2
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end Rigidity.Percolation
