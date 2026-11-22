import Rigidity.Proofs.Percolation.PlanarNablaAffineSq

/-!
# Display (4.26) of Armstrong and Dario in `L²(P)`, in dimension two

The pointwise bounds of `PlanarNablaAffineSq` are collected in a measurable majorant of
`∑_j (|V|⁻¹ ⟨e_j, ∇[v(·, V, p)]_P⟩_V - p_j)²`, whose expectation is at most `C |p|² 3^{-n/4}` for
every cube `V` of scale `n`, the moments of the sides of the partition cubes being bounded.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped Classical ENNReal

namespace Rigidity.Percolation

variable {ω : Configuration 2}

/-- The measurable majorant of the squared deviation of the spatial average of the coarsened
gradient of `v(·, V, p)` from `p`. -/
noncomputable def nablaAffineMajorant (ω : Configuration 2) (V : TriadicCube 2) (p : Fin 2 → ℝ) :
    ℝ :=
  if PlanarPartitionEvent ω ∧ PlanarResolved ω V then
    1296 * 162001 ^ 2 * (p 0 ^ 2 + p 1 ^ 2) *
      (4 * ((∑ k ∈ boundaryIndex V, partSideP ω k.2.2 ^ 8) /
          ((V.toIntegerCube.size : ℝ) * (V.toIntegerCube.size : ℝ))) +
        1 / (V.toIntegerCube.size : ℝ))
  else if PlanarPartitionEvent ω then
    (p 0 ^ 2 + p 1 ^ 2) * ∑ z ∈ V.toIntegerCube.vertices, (partSideP ω z / 3 ^ (V.scale + 1)) ^ 6
  else p 0 ^ 2 + p 1 ^ 2

theorem planarNuGradAvg_of_not {V : TriadicCube 2} (h : ¬ (PlanarPartitionEvent ω ∧ PlanarResolved ω V))
    (p : Fin 2 → ℝ) (j : Fin 2) : planarNuGradAvg ω V p j = 0 := by
  rw [planarNuGradAvg, planarNuSolution, if_neg h, map_zero, zero_div]

theorem le_nablaAffineMajorant (V : TriadicCube 2) (p : Fin 2 → ℝ) (ω : Configuration 2) :
    ∑ j : Fin 2, (planarNuGradAvg ω V p j - p j) ^ 2 ≤ nablaAffineMajorant ω V p := by
  unfold nablaAffineMajorant
  by_cases h : PlanarPartitionEvent ω ∧ PlanarResolved ω V
  · rw [if_pos h]
    have hps : ∀ x, partSideP ω x = partSide ω x := fun x => by rw [partSideP, if_pos h.1]
    simp only [hps]
    exact sum_sq_planarNuGradAvg_sub_le h.1 h.2 p
  · rw [if_neg h, Fin.sum_univ_two, planarNuGradAvg_of_not h, planarNuGradAvg_of_not h]
    by_cases hP : PlanarPartitionEvent ω
    · rw [if_pos hP]
      have hps : ∀ x, partSideP ω x = partSide ω x := fun x => by rw [partSideP, if_pos hP]
      simp only [hps]
      have hres : ¬ PlanarResolved ω V := fun hV => h ⟨hP, hV⟩
      have h1 := one_le_sum_of_not_resolved hres
      have hq : 0 ≤ p 0 ^ 2 + p 1 ^ 2 := by positivity
      nlinarith
    · rw [if_neg hP]
      simp

theorem nablaAffineMajorant_nonneg (V : TriadicCube 2) (p : Fin 2 → ℝ) (ω : Configuration 2) :
    0 ≤ nablaAffineMajorant ω V p :=
  le_trans (Finset.sum_nonneg fun _ _ => sq_nonneg _) (le_nablaAffineMajorant V p ω)

theorem measurable_nablaAffineMajorant (V : TriadicCube 2) (p : Fin 2 → ℝ) :
    Measurable fun ω => nablaAffineMajorant ω V p := by
  unfold nablaAffineMajorant
  refine Measurable.ite (measurableSet_planarPartitionEvent_resolved V) ?_
    (Measurable.ite measurableSet_planarPartitionEvent ?_ measurable_const)
  · refine measurable_const.mul (Measurable.add (measurable_const.mul ?_) measurable_const)
    exact (Finset.measurable_fun_sum (boundaryIndex V) fun k _ =>
      (measurable_partSideP k.2.2).pow_const 8).div_const _
  · exact measurable_const.mul (Finset.measurable_fun_sum V.toIntegerCube.vertices fun z _ =>
      ((measurable_partSideP z).div_const _).pow_const 6)

/-- The moments of the sides of the partition cubes. -/
theorem exists_lintegral_partSideP_pow_le {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Vertex 2,
      ∫⁻ ω, ENNReal.ofReal (partSideP ω x ^ (m + 1)) ∂(latticeBondLaw 2 p) ≤ ENNReal.ofReal C := by
  obtain ⟨C, hC, h⟩ := exists_lintegral_tsum_ninefold_le hpc (m + 1)
  refine ⟨C.toReal, ENNReal.toReal_nonneg, fun x => ?_⟩
  rw [ENNReal.ofReal_toReal hC]
  refine le_trans (lintegral_mono fun ω => ?_) (h x)
  by_cases hP : PlanarPartitionEvent ω
  · rw [partSideP, if_pos hP]
    exact ofReal_partSide_pow_le hP x m
  · rw [partSideP, if_neg hP, zero_pow (Nat.succ_ne_zero m), ENNReal.ofReal_zero]
    exact zero_le

/-- **Display (4.26) of Armstrong and Dario in `L²`, with a measurable majorant.** -/
theorem exists_nablaAffineMajorant_le {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : TriadicCube 2) (ξ : Fin 2 → ℝ),
      ∫⁻ ω, ENNReal.ofReal (nablaAffineMajorant ω V ξ) ∂(latticeBondLaw 2 p) ≤
        ENNReal.ofReal (C * (ξ 0 ^ 2 + ξ 1 ^ 2) * (3 : ℝ) ^ (-(V.scale : ℝ) / 4)) := by
  obtain ⟨C8, hC8, h8⟩ := exists_lintegral_partSideP_pow_le hpc 7
  obtain ⟨C6, hC6, h6⟩ := exists_lintegral_partSideP_pow_le hpc 5
  refine ⟨1296 * 162001 ^ 2 * (16 * C8 + 1) + C6, by positivity, fun V ξ => ?_⟩
  set L : ℝ := (V.toIntegerCube.size : ℝ) with hL
  have hL1 : 1 ≤ L := one_le_cast_size V
  have hL0 : 0 < L := by linarith
  set Q := ξ 0 ^ 2 + ξ 1 ^ 2 with hQ
  have hQ0 : 0 ≤ Q := by positivity
  set c₁ := 1296 * 162001 ^ 2 * Q with hc₁
  have hc₁0 : 0 ≤ c₁ := by positivity
  set t : ℝ := 1 / (3 : ℝ) ^ (V.scale + 1) with ht
  have ht0 : 0 ≤ t := by positivity
  set F : Configuration 2 → ℝ := fun ω =>
    c₁ * (4 / (L * L)) * ∑ k ∈ boundaryIndex V, partSideP ω k.2.2 ^ (7 + 1) + c₁ / L +
      Q * t ^ 6 * ∑ z ∈ V.toIntegerCube.vertices, partSideP ω z ^ (5 + 1) with hF
  -- the majorant is below `F` on the partition event
  have hae : ∀ᵐ ω ∂(latticeBondLaw 2 p), ENNReal.ofReal (nablaAffineMajorant ω V ξ) ≤
      ENNReal.ofReal (F ω) := by
    filter_upwards [ae_planarPartitionEvent hpc] with ω hP
    refine ENNReal.ofReal_le_ofReal ?_
    have hA : 0 ≤ c₁ * (4 / (L * L)) * ∑ k ∈ boundaryIndex V, partSideP ω k.2.2 ^ (7 + 1) :=
      mul_nonneg (by positivity) (Finset.sum_nonneg fun k _ => pow_nonneg (partSideP_nonneg _ _) _)
    have hB : 0 ≤ Q * t ^ 6 * ∑ z ∈ V.toIntegerCube.vertices, partSideP ω z ^ (5 + 1) :=
      mul_nonneg (by positivity) (Finset.sum_nonneg fun z _ => pow_nonneg (partSideP_nonneg _ _) _)
    have hcL : 0 ≤ c₁ / L := by positivity
    unfold nablaAffineMajorant
    split_ifs with h
    · simp only [hF]
      have e : c₁ * (4 * ((∑ k ∈ boundaryIndex V, partSideP ω k.2.2 ^ 8) / (L * L)) + 1 / L) =
          c₁ * (4 / (L * L)) * ∑ k ∈ boundaryIndex V, partSideP ω k.2.2 ^ (7 + 1) + c₁ / L := by
        field_simp
      rw [e]
      linarith
    · simp only [hF]
      have e : Q * ∑ z ∈ V.toIntegerCube.vertices, (partSideP ω z / 3 ^ (V.scale + 1)) ^ 6 =
          Q * t ^ 6 * ∑ z ∈ V.toIntegerCube.vertices, partSideP ω z ^ (5 + 1) := by
        have hz : ∀ z, (partSideP ω z / 3 ^ (V.scale + 1)) ^ 6 =
            t ^ 6 * partSideP ω z ^ (5 + 1) := fun z => by
          rw [ht, div_pow, one_div, inv_pow]
          ring
        rw [Finset.sum_congr rfl fun z _ => hz z, ← Finset.mul_sum]
        ring
      rw [e]
      linarith
  -- the expectation of `F`
  have hF' : ∀ ω, ENNReal.ofReal (F ω) =
      ENNReal.ofReal (c₁ * (4 / (L * L))) *
        ∑ k ∈ boundaryIndex V, ENNReal.ofReal (partSideP ω k.2.2 ^ (7 + 1)) +
      ENNReal.ofReal (c₁ / L) +
      ENNReal.ofReal (Q * t ^ 6) *
        ∑ z ∈ V.toIntegerCube.vertices, ENNReal.ofReal (partSideP ω z ^ (5 + 1)) := by
    intro ω
    have hs1 : 0 ≤ ∑ k ∈ boundaryIndex V, partSideP ω k.2.2 ^ (7 + 1) :=
      Finset.sum_nonneg fun k _ => pow_nonneg (partSideP_nonneg _ _) _
    have hs2 : 0 ≤ ∑ z ∈ V.toIntegerCube.vertices, partSideP ω z ^ (5 + 1) :=
      Finset.sum_nonneg fun z _ => pow_nonneg (partSideP_nonneg _ _) _
    simp only [hF]
    have hA0 : 0 ≤ c₁ * (4 / (L * L)) := by positivity
    have hB0 : 0 ≤ Q * t ^ 6 := by positivity
    have hcL : 0 ≤ c₁ / L := by positivity
    rw [ENNReal.ofReal_add (add_nonneg (mul_nonneg hA0 hs1) hcL) (mul_nonneg hB0 hs2),
      ENNReal.ofReal_add (mul_nonneg hA0 hs1) hcL,
      ENNReal.ofReal_mul (p := c₁ * (4 / (L * L))) hA0, ENNReal.ofReal_mul (p := Q * t ^ 6) hB0,
      ENNReal.ofReal_sum_of_nonneg fun k _ => pow_nonneg (partSideP_nonneg _ _) _,
      ENNReal.ofReal_sum_of_nonneg fun z _ => pow_nonneg (partSideP_nonneg _ _) _]
  have m8 : ∀ x, Measurable fun ω => ENNReal.ofReal (partSideP ω x ^ (7 + 1)) := fun x =>
    ((measurable_partSideP x).pow_const _).ennreal_ofReal
  have m6 : ∀ x, Measurable fun ω => ENNReal.ofReal (partSideP ω x ^ (5 + 1)) := fun x =>
    ((measurable_partSideP x).pow_const _).ennreal_ofReal
  have hint : ∫⁻ ω, ENNReal.ofReal (F ω) ∂(latticeBondLaw 2 p) ≤
      ENNReal.ofReal (c₁ * (4 / (L * L))) * ∑ _k ∈ boundaryIndex V, ENNReal.ofReal C8 +
      ENNReal.ofReal (c₁ / L) +
      ENNReal.ofReal (Q * t ^ 6) * ∑ _z ∈ V.toIntegerCube.vertices, ENNReal.ofReal C6 := by
    simp_rw [hF']
    have mS8 : Measurable fun ω => ∑ k ∈ boundaryIndex V,
        ENNReal.ofReal (partSideP ω k.2.2 ^ (7 + 1)) :=
      Finset.measurable_fun_sum (boundaryIndex V) fun k _ => m8 k.2.2
    have mS6 : Measurable fun ω => ∑ z ∈ V.toIntegerCube.vertices,
        ENNReal.ofReal (partSideP ω z ^ (5 + 1)) :=
      Finset.measurable_fun_sum V.toIntegerCube.vertices fun z _ => m6 z
    have mA : Measurable fun ω => ENNReal.ofReal (c₁ * (4 / (L * L))) *
        ∑ k ∈ boundaryIndex V, ENNReal.ofReal (partSideP ω k.2.2 ^ (7 + 1)) := mS8.const_mul _
    have mAB : Measurable fun ω => ENNReal.ofReal (c₁ * (4 / (L * L))) *
        ∑ k ∈ boundaryIndex V, ENNReal.ofReal (partSideP ω k.2.2 ^ (7 + 1)) +
        ENNReal.ofReal (c₁ / L) := mA.add measurable_const
    rw [lintegral_add_left mAB, lintegral_add_left mA, lintegral_const_mul _ mS8,
      lintegral_const, measure_univ, mul_one, lintegral_const_mul _ mS6,
      lintegral_finsetSum _ fun k _ => m8 k.2.2, lintegral_finsetSum _ fun z _ => m6 z]
    gcongr with k hk z hz
    · exact h8 k.2.2
    · exact h6 z
  have hC80 : (0 : ℝ) ≤ ((boundaryIndex V).card : ℝ) * C8 := by positivity
  have hC60 : (0 : ℝ) ≤ (V.toIntegerCube.vertices.card : ℝ) * C6 := by positivity
  have hcL : 0 ≤ c₁ / L := by positivity
  have hA0 : 0 ≤ c₁ * (4 / (L * L)) := by positivity
  have hB0 : 0 ≤ Q * t ^ 6 := by positivity
  have heq : ENNReal.ofReal (c₁ * (4 / (L * L))) * ∑ _k ∈ boundaryIndex V, ENNReal.ofReal C8 +
      ENNReal.ofReal (c₁ / L) +
      ENNReal.ofReal (Q * t ^ 6) * ∑ _z ∈ V.toIntegerCube.vertices, ENNReal.ofReal C6 =
      ENNReal.ofReal (c₁ * (4 / (L * L)) * ((boundaryIndex V).card * C8) + c₁ / L +
        Q * t ^ 6 * ((V.toIntegerCube.vertices.card : ℝ) * C6)) := by
    rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul,
      ENNReal.ofReal_add (add_nonneg (mul_nonneg hA0 hC80) hcL) (mul_nonneg hB0 hC60),
      ENNReal.ofReal_add (mul_nonneg hA0 hC80) hcL, ENNReal.ofReal_mul hA0,
      ENNReal.ofReal_mul hB0, ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  refine (lintegral_mono_ae hae).trans (hint.trans (heq.le.trans (ENNReal.ofReal_le_ofReal ?_)))
  -- the arithmetic
  have hbI : ((boundaryIndex V).card : ℝ) ≤ 4 * L := card_boundaryIndex_le V
  have hcard : (V.toIntegerCube.vertices.card : ℝ) = L * L := by
    rw [card_toIntegerCube_vertices_eq, cast_size_mul_self V]
    rfl
  have hL3 : L = (3 : ℝ) ^ V.scale := by
    rw [hL]
    change ((3 ^ V.scale : ℕ) : ℝ) = _
    push_cast
    rfl
  have ht6 : t ^ 6 * (L * L) ≤ 1 / L := by
    rw [ht, hL3, div_pow, one_pow, ← pow_mul, div_mul_eq_mul_div, one_mul,
      div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    have : (3 : ℝ) ^ V.scale * 3 ^ V.scale * 3 ^ V.scale ≤ 3 ^ ((V.scale + 1) * 6) := by
      rw [← pow_add, ← pow_add]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have hLr : 1 / L ≤ (3 : ℝ) ^ (-(V.scale : ℝ) / 4) := by
    rw [hL3, one_div, ← Real.rpow_natCast, ← Real.rpow_neg (by norm_num)]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have : (0 : ℝ) ≤ V.scale := Nat.cast_nonneg _
    linarith
  have k1 : c₁ * (4 / (L * L)) * ((boundaryIndex V).card * C8) ≤ c₁ * (16 * C8) * (1 / L) := by
    have : (4 / (L * L)) * ((boundaryIndex V).card * C8) ≤ (4 / (L * L)) * (4 * L * C8) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hbI hC8) (by positivity)
    have e : (4 / (L * L)) * (4 * L * C8) = 16 * C8 * (1 / L) := by field_simp; ring
    rw [e] at this
    have := mul_le_mul_of_nonneg_left this hc₁0
    linarith
  have k2 : Q * t ^ 6 * ((V.toIntegerCube.vertices.card : ℝ) * C6) ≤ Q * C6 * (1 / L) := by
    rw [hcard]
    have := mul_le_mul_of_nonneg_left ht6 (mul_nonneg hQ0 hC6)
    nlinarith
  have k3 : c₁ / L = c₁ * (1 / L) := by ring
  have hsum : c₁ * (4 / (L * L)) * ((boundaryIndex V).card * C8) + c₁ / L +
      Q * t ^ 6 * ((V.toIntegerCube.vertices.card : ℝ) * C6) ≤
      (1296 * 162001 ^ 2 * (16 * C8 + 1) + C6) * Q * (1 / L) := by
    rw [hc₁] at k1 k3 ⊢
    linarith
  refine hsum.trans ?_
  exact mul_le_mul_of_nonneg_left hLr (by positivity)

/-- **Display (4.26) of Armstrong and Dario in `L²`** (in dimension two): for every cube `V` of
scale `n`, `E[∑_j (|V|⁻¹ ⟨e_j, ∇[v(·, V, p)]_P⟩_V - p_j)²] ≤ C |p|² 3^{-n/4}`. -/
theorem exists_lintegral_planarNuGradAvg_sub_le {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : TriadicCube 2) (ξ : Fin 2 → ℝ),
      ∫⁻ ω, ENNReal.ofReal (∑ j : Fin 2, (planarNuGradAvg ω V ξ j - ξ j) ^ 2)
          ∂(latticeBondLaw 2 p) ≤
        ENNReal.ofReal (C * (ξ 0 ^ 2 + ξ 1 ^ 2) * (3 : ℝ) ^ (-(V.scale : ℝ) / 4)) := by
  obtain ⟨C, hC, h⟩ := exists_nablaAffineMajorant_le hpc
  exact ⟨C, hC, fun V ξ => (lintegral_mono fun ω =>
    ENNReal.ofReal_le_ofReal (le_nablaAffineMajorant V ξ ω)).trans (h V ξ)⟩

end Rigidity.Percolation
