import Rigidity.Proofs.Percolation.PlanarReachMoments
import Rigidity.Proofs.Percolation.PlanarSubcubes

/-!
# Large planar partition cubes are rare

On the planar partition event, a vertex `x` whose partition cube has scale `s` lies in the
maximal stopping cube of scale `s` containing it, which is a partition cube with probability at
most `2 exp(-3^s/θ)` (`exists_measure_isMaximalStopping_le`). Summing over the vertices of a finite
set `S` and the scales `s > j`, for every `m` there is `C < ∞` with
`P[some vertex of S has a partition cube of scale > j] ≤ C |S| 3^{-(j+1)(m+1)}`
(`exists_measure_partitionScale_gt_le`). With `S` a triadic cube of scale `m₀` and `j = ⌈n/2⌉`,
`n ≥ 9 m₀ / 10`, this is the event `Γ` of the proof of Lemma 5.5 of Armstrong and Dario (all
partition cubes at most `3^{n/2}`), on which the inner squares of the subcubes are resolved.
-/

namespace Rigidity.Percolation

open MeasureTheory LatticeProb.Percolation
open scoped ENNReal Nat

/-- **Large planar partition cubes are rare.** For every `m` there is `C < ∞` such that for every
finite set `S` of vertices and every `j`, the probability that some vertex of `S` has a planar
partition cube of scale larger than `j` is at most `C |S| 3^{-(j+1)(m+1)}`. -/
theorem exists_measure_partitionScale_gt_le {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (m : ℕ) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (S : Finset (Vertex 2)) (j : ℕ),
      latticeBondLaw 2 p {ω | PlanarPartitionEvent ω ∧ ∃ x ∈ S, j < (planarPartCube ω x).scale} ≤
        C * S.card * (3⁻¹ : ℝ≥0∞) ^ ((j + 1) * (m + 1)) := by
  obtain ⟨θ, hθ, hQ⟩ := exists_measure_isMaximalStopping_le hpc
  set K : ℝ := 2 * θ ^ (m + 1) * (m + 1)! with hK
  set r : ℝ≥0∞ := (3⁻¹ : ℝ≥0∞) ^ (m + 1) with hr
  have hr1 : r < 1 := by
    rw [hr]
    exact pow_lt_one₀ zero_le (ENNReal.inv_lt_one.2 (by norm_num)) (Nat.succ_ne_zero m)
  have hgeo : ∑' t : ℕ, r ^ t = (1 - r)⁻¹ := ENNReal.tsum_geometric r
  have hrne : (1 - r)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 (tsub_pos_iff_lt.2 hr1).ne'
  refine ⟨ENNReal.ofReal K * (1 - r)⁻¹, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hrne,
    fun S j => ?_⟩
  set μ := latticeBondLaw 2 p with hμ
  -- the event lies in a union of events of maximal stopping cubes
  have hsub : {ω | PlanarPartitionEvent ω ∧ ∃ x ∈ S, j < (planarPartCube ω x).scale} ⊆
      ⋃ x ∈ S, ⋃ t : ℕ,
        {ω | (scaleCube (t + j + 1) x).IsMaximalStopping (planarGoodCubes ω)} := by
    rintro ω ⟨hP, x, hx, hjx⟩
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    refine ⟨x, hx, (planarPartCube ω x).scale - (j + 1), ?_⟩
    have hs : (planarPartCube ω x).scale - (j + 1) + j + 1 = (planarPartCube ω x).scale := by
      omega
    rw [hs]
    have heq : scaleCube (planarPartCube ω x).scale x = planarPartCube ω x :=
      TriadicCube.eq_of_mem_of_scale_eq (by rw [scale_scaleCube]) (mem_scaleCube _ x)
        (planarPartCube_spec hP x).1
    rw [heq]
    exact (planarPartCube_spec hP x).2
  -- the bound on each scale
  have hterm : ∀ s : ℕ, ENNReal.ofReal (2 * Real.exp (-((3 : ℝ) ^ s / θ))) ≤
      ENNReal.ofReal K * (3⁻¹ : ℝ≥0∞) ^ (s * (m + 1)) := by
    intro s
    have h := three_pow_mul_exp_neg_le hθ m s
    have h3 : (0 : ℝ) < (3 : ℝ) ^ (m * s) := by positivity
    have hreal : 2 * Real.exp (-((3 : ℝ) ^ s / θ)) ≤ K * (1 / 3 : ℝ) ^ (s * (m + 1)) := by
      have he : (1 / 3 : ℝ) ^ (s * (m + 1)) = (1 / 3) ^ s / (3 : ℝ) ^ (m * s) := by
        rw [show s * (m + 1) = m * s + s by ring, pow_add, div_pow, div_pow, one_pow, one_pow]
        field_simp
      rw [he, mul_div_assoc', le_div_iff₀ h3, mul_comm]
      exact h
    refine (ENNReal.ofReal_le_ofReal hreal).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num), one_div,
      ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
  calc μ {ω | PlanarPartitionEvent ω ∧ ∃ x ∈ S, j < (planarPartCube ω x).scale}
      ≤ μ (⋃ x ∈ S, ⋃ t : ℕ,
          {ω | (scaleCube (t + j + 1) x).IsMaximalStopping (planarGoodCubes ω)}) :=
        measure_mono hsub
    _ ≤ ∑ x ∈ S, μ (⋃ t : ℕ,
          {ω | (scaleCube (t + j + 1) x).IsMaximalStopping (planarGoodCubes ω)}) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ x ∈ S, ∑' t : ℕ,
          μ {ω | (scaleCube (t + j + 1) x).IsMaximalStopping (planarGoodCubes ω)} :=
        Finset.sum_le_sum fun x _ => measure_iUnion_le _
    _ ≤ ∑ _x ∈ S, ∑' t : ℕ,
          ENNReal.ofReal K * ((3⁻¹ : ℝ≥0∞) ^ ((j + 1) * (m + 1)) * r ^ t) := by
        refine Finset.sum_le_sum fun x _ => ENNReal.tsum_le_tsum fun t => ?_
        refine (hQ _).trans ?_
        rw [scale_scaleCube]
        refine (hterm _).trans (le_of_eq ?_)
        rw [hr, ← pow_mul, ← pow_add]
        congr 2
        ring
    _ = ENNReal.ofReal K * (1 - r)⁻¹ * S.card * (3⁻¹ : ℝ≥0∞) ^ ((j + 1) * (m + 1)) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, hgeo]
        ring

end Rigidity.Percolation
