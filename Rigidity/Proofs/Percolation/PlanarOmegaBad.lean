import Rigidity.Proofs.Percolation.PlanarOmegaMajorants

/-!
# The boundary term and the exceptional events in the proof of Lemma 5.9

* `exists_boundaryMajorant`: the boundary error of the maximizer of `ν(V, p)` divided by `|V|` has a
  measurable majorant of expectation at most `C |p|₁ 3^{-n/2}`, `n` the scale of `V`.
* `lintegral_not_resolved_le`: the probability that a cube of scale `n` is not resolved (or the
  partition event fails) is at most `C 9^n 3^{-6(n+1)}`.
* `exists_badMajorant`: on the event that `□_n` is resolved and `□_{n+1}` is not, `ν(□_n, p) - μ(□_n, q)`
  has a measurable majorant of expectation at most `C (1 + |p|₁² + |q|₁⁴) 9^{-n}`, by the inequality
  `y ≤ λ + λ⁻¹ y²` with `λ = 9^n` and the moments of the reach.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped Classical ENNReal

namespace Rigidity.Percolation

variable {ω : Configuration 2}

/-- **The boundary term of quadratic response with a measurable majorant.** -/
theorem exists_boundaryMajorant {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : TriadicCube 2) (ξ : Fin 2 → ℝ), 0 < |ξ 0| + |ξ 1| →
      ∃ M : Configuration 2 → ℝ, Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧
        (∀ ω, PlanarPartitionEvent ω → PlanarResolved ω V →
          boundaryError ω V ξ (planarNuMaximizer ω V ξ) / V.volume ≤ M ω) ∧
        ∫⁻ ω, ENNReal.ofReal (M ω) ∂(latticeBondLaw 2 p) ≤
          ENNReal.ofReal (C * (|ξ 0| + |ξ 1|) / Real.sqrt (V.toIntegerCube.size : ℝ)) := by
  obtain ⟨C4, hC4, h4⟩ := exists_lintegral_partSideP_pow_le hpc 3
  refine ⟨9 * (162001 * 4 * C4 + 1 / 2), by positivity, fun V ξ hξ => ?_⟩
  set L : ℝ := (V.toIntegerCube.size : ℝ) with hL
  have hL1 : 1 ≤ L := one_le_cast_size V
  have hL0 : 0 < L := by linarith
  have hsL : 0 < Real.sqrt L := Real.sqrt_pos.2 hL0
  set P₁ := |ξ 0| + |ξ 1| with hP₁
  set a : ℝ := 9 * P₁ * 162001 / (L * Real.sqrt L) with ha
  set b : ℝ := 9 * P₁ * (1 / 2 / Real.sqrt L) with hb
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  refine ⟨fun ω => a * ∑ k ∈ boundaryIndex V, partSideP ω k.2.2 ^ (3 + 1) + b,
    (Finset.measurable_fun_sum _ fun k _ => (measurable_partSideP k.2.2).pow_const _).const_mul
      _ |>.add measurable_const,
    fun ω => add_nonneg (mul_nonneg ha0 (Finset.sum_nonneg fun k _ =>
      pow_nonneg (partSideP_nonneg _ _) _)) hb0, fun ω hP hV => ?_, ?_⟩
  · have h := boundaryError_div_le hP hV ξ hξ
    have hps : ∀ x, partSideP ω x = partSide ω x := fun x => by rw [partSideP, if_pos hP]
    simp only [hps]
    refine h.trans (le_of_eq ?_)
    rw [ha, hb, ← hL]
    field_simp
    ring
  · have hm : ∀ k : Fin 2 × Bool × Vertex 2,
        Measurable fun ω => ENNReal.ofReal (partSideP ω k.2.2 ^ (3 + 1)) := fun k =>
      ((measurable_partSideP k.2.2).pow_const _).ennreal_ofReal
    have hpt : ∀ ω, ENNReal.ofReal (a * ∑ k ∈ boundaryIndex V, partSideP ω k.2.2 ^ (3 + 1) + b) =
        ENNReal.ofReal a * ∑ k ∈ boundaryIndex V, ENNReal.ofReal (partSideP ω k.2.2 ^ (3 + 1)) +
          ENNReal.ofReal b := fun ω => by
      rw [ENNReal.ofReal_add (mul_nonneg ha0 (Finset.sum_nonneg fun k _ =>
        pow_nonneg (partSideP_nonneg _ _) _)) hb0, ENNReal.ofReal_mul ha0,
        ENNReal.ofReal_sum_of_nonneg fun k _ => pow_nonneg (partSideP_nonneg _ _) _]
    simp_rw [hpt]
    have hms : Measurable fun ω => ENNReal.ofReal a *
        ∑ k ∈ boundaryIndex V, ENNReal.ofReal (partSideP ω k.2.2 ^ (3 + 1)) :=
      (Finset.measurable_fun_sum _ fun k _ => hm k).const_mul _
    rw [lintegral_add_left hms, lintegral_const, measure_univ, mul_one,
      lintegral_const_mul _ (Finset.measurable_fun_sum _ fun k _ => hm k),
      lintegral_finsetSum _ fun k _ => hm k]
    have hbI : ((boundaryIndex V).card : ℝ) ≤ 4 * L := card_boundaryIndex_le V
    calc ENNReal.ofReal a * ∑ k ∈ boundaryIndex V,
          ∫⁻ ω, ENNReal.ofReal (partSideP ω k.2.2 ^ (3 + 1)) ∂(latticeBondLaw 2 p) +
          ENNReal.ofReal b
        ≤ ENNReal.ofReal a * ∑ _k ∈ boundaryIndex V, ENNReal.ofReal C4 + ENNReal.ofReal b := by
          gcongr with k hk
          exact h4 k.2.2
      _ = ENNReal.ofReal (a * ((boundaryIndex V).card * C4) + b) := by
          rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_mul ha0,
            ← ENNReal.ofReal_add (by positivity) hb0]
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          have k1 : a * ((boundaryIndex V).card * C4) ≤ a * (4 * L * C4) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hbI hC4) ha0
          have e1 : a * (4 * L * C4) = 9 * 162001 * 4 * C4 * P₁ / Real.sqrt L := by
            rw [ha]
            field_simp
          have e2 : b = 9 * (1 / 2) * P₁ / Real.sqrt L := by
            rw [hb]
            ring
          have e3 : 9 * (162001 * 4 * C4 + 1 / 2) * P₁ / Real.sqrt L =
              9 * 162001 * 4 * C4 * P₁ / Real.sqrt L + 9 * (1 / 2) * P₁ / Real.sqrt L := by ring
          rw [e3, ← e1, ← e2]
          linarith

/-- **The probability that a cube is not resolved.** -/
theorem exists_lintegral_not_resolved_le {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ W : TriadicCube 2,
      ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω W then 0 else 1) ∂(latticeBondLaw 2 p) ≤
        ENNReal.ofReal (C * W.volume / (3 : ℝ) ^ (6 * (W.scale + 1))) := by
  obtain ⟨C6, hC6, h6⟩ := exists_lintegral_partSideP_pow_le hpc 5
  refine ⟨C6, hC6, fun W => ?_⟩
  set t : ℝ := 1 / (3 : ℝ) ^ (6 * (W.scale + 1)) with ht
  have ht0 : 0 ≤ t := by positivity
  have hae : ∀ᵐ ω ∂(latticeBondLaw 2 p),
      (if PlanarPartitionEvent ω ∧ PlanarResolved ω W then (0 : ℝ≥0∞) else 1) ≤
        ∑ z ∈ W.toIntegerCube.vertices, ENNReal.ofReal t *
          ENNReal.ofReal (partSideP ω z ^ (5 + 1)) := by
    filter_upwards [ae_planarPartitionEvent hpc] with ω hP
    split_ifs with h
    · exact zero_le
    · have hres : ¬ PlanarResolved ω W := fun hW => h ⟨hP, hW⟩
      have h1 := one_le_sum_of_not_resolved hres
      have hps : ∀ x, partSideP ω x = partSide ω x := fun x => by rw [partSideP, if_pos hP]
      calc (1 : ℝ≥0∞) = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
        _ ≤ ENNReal.ofReal (∑ z ∈ W.toIntegerCube.vertices,
            (partSide ω z / 3 ^ (W.scale + 1)) ^ 6) := ENNReal.ofReal_le_ofReal h1
        _ = _ := by
            rw [ENNReal.ofReal_sum_of_nonneg fun z _ => by
              have := one_le_partSide (ω := ω) z; positivity]
            refine Finset.sum_congr rfl fun z _ => ?_
            rw [← ENNReal.ofReal_mul ht0, hps, ht, div_pow, ← pow_mul, mul_comm (W.scale + 1) 6]
            congr 1
            ring
  have hm : ∀ z, Measurable fun ω => ENNReal.ofReal (partSideP ω z ^ (5 + 1)) := fun z =>
    ((measurable_partSideP z).pow_const _).ennreal_ofReal
  refine (lintegral_mono_ae hae).trans ?_
  rw [lintegral_finsetSum _ fun z _ => (hm z).const_mul _]
  calc ∑ z ∈ W.toIntegerCube.vertices, ∫⁻ ω, ENNReal.ofReal t *
        ENNReal.ofReal (partSideP ω z ^ (5 + 1)) ∂(latticeBondLaw 2 p)
      ≤ ∑ _z ∈ W.toIntegerCube.vertices, ENNReal.ofReal t * ENNReal.ofReal C6 := by
        gcongr with z hz
        rw [lintegral_const_mul _ (hm z)]
        gcongr
        exact h6 z
    _ = _ := by
        rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_mul ht0, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _), card_toIntegerCube_vertices_eq]
        congr 1
        rw [ht]
        change (9 : ℝ) ^ W.scale * (1 / (3 : ℝ) ^ (6 * (W.scale + 1)) * C6) =
          C6 * (9 : ℝ) ^ W.scale / (3 : ℝ) ^ (6 * (W.scale + 1))
        ring

end Rigidity.Percolation
