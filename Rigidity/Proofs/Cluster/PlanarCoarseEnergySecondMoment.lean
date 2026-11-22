import Rigidity.Proofs.Cluster.PlanarCoarseEnergyMoments

/-!
# The second moment of the energy of the coarsened minimizer of `μ`

For every `a ≥ 3` there is `C < ∞` such that for every triadic cube `V` and slope `q`,
`E[(∑_{x ∈ V} |∇[u(·, V, q)]_𝒫|²(x))²] ≤ C |q|₁⁴ |V|² |V|^{2/a}`
(`exists_lintegral_coarse_minimizer_sq_le`), on the planar partition event and the resolution of
`V`. As for the first moment (`exists_lintegral_coarse_minimizer_le`), the energy is at most
`c |q|₁² |V| (∑_V R^{7a})^{1/a}` pointwise, and Jensen's inequality for the concave power `2/a`
gives the factor `|V|^{2/a}`. Together with the probability of a bad event `A`, this bounds
`E[(∑_V |∇[u]_𝒫|²) 1_A]` by the Cauchy–Schwarz inequality, as in the estimates off the good events
in the proof of Lemma 5.5 of Armstrong and Dario.
-/

namespace Rigidity.Proofs.Cluster

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Proofs.Section5
open scoped BigOperators Classical ENNReal

/-- **The second moment of the energy of the coarsened minimizer of `μ`**, in dimension two. -/
theorem exists_lintegral_coarse_minimizer_sq_le {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) {a : ℕ} (ha : 3 ≤ a) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (V : TriadicCube 2) (q : Fin 2 → ℝ),
      ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω V then
          ENNReal.ofReal (∑ x ∈ V.toIntegerCube.vertices,
            gradNormIn (nearestNeighborGraph 2) V.toIntegerCube.vertices
              (fun x => clusterExtend ω V (planarMuMinimizer ω V q) (planarCoarseAnchor ω x)) x ^ 2)
              ^ 2
          else 0) ∂(latticeBondLaw 2 p) ≤
        C * ENNReal.ofReal ((|q 0| + |q 1|) ^ 2) ^ 2 * (V.toIntegerCube.vertices.card : ℝ≥0∞) ^ 2 *
          (V.toIntegerCube.vertices.card : ℝ≥0∞) ^ (2 / (a : ℝ)) := by
  obtain ⟨CT, hCT, hT⟩ := exists_lintegral_tsum_ninefold_le hpc (7 * a)
  set K : ℝ≥0∞ := ENNReal.ofReal ((2 * ((2 : ℕ) : ℝ) * (3 / 2 * (2 * ((4 : ℕ) : ℝ) + 2) ^ 2) *
    (2 * ((4 : ℕ) : ℝ) + 1) ^ 2 * (2 * √((2 : ℕ) : ℝ))) ^ 2) * (27 * 234256) *
    ENNReal.ofReal 18 with hK
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have ha2 : (1 : ℝ) < (a : ℝ) / 2 := by
    rw [lt_div_iff₀ (by norm_num)]
    have : (3 : ℝ) ≤ a := by exact_mod_cast ha
    linarith
  refine ⟨K ^ 2 * CT ^ (2 / (a : ℝ)), ENNReal.mul_ne_top (by rw [hK]; finiteness)
    (ENNReal.rpow_ne_top_of_nonneg (by positivity) hCT), fun V q => ?_⟩
  set μ := latticeBondLaw 2 p with hμ
  set X : Configuration 2 → ℝ≥0∞ := fun ω =>
    ∑ z ∈ V.toIntegerCube.vertices, reachSum ω (7 * a) z with hX
  have hXm : Measurable X := Finset.measurable_sum _ fun z _ => measurable_reachSum (7 * a) z
  have hXam : Measurable fun ω => X ω ^ (2 / (a : ℝ)) := hXm.pow_const _
  set c : ℝ≥0∞ := K * ENNReal.ofReal ((|q 0| + |q 1|) ^ 2) *
    (V.toIntegerCube.vertices.card : ℝ≥0∞) with hc
  have hpoint : ∀ ω : Configuration 2, (if PlanarPartitionEvent ω ∧ PlanarResolved ω V then
      ENNReal.ofReal (∑ x ∈ V.toIntegerCube.vertices,
        gradNormIn (nearestNeighborGraph 2) V.toIntegerCube.vertices
          (fun x => clusterExtend ω V (planarMuMinimizer ω V q) (planarCoarseAnchor ω x)) x ^ 2)
          ^ 2
      else 0) ≤ c ^ 2 * X ω ^ (2 / (a : ℝ)) := by
    intro ω
    split_ifs with h
    · have h1 := ofReal_coarse_minimizer_le_reachSum h.1 h.2 q (by omega : 1 ≤ a)
      have h2 : ENNReal.ofReal (∑ x ∈ V.toIntegerCube.vertices,
          gradNormIn (nearestNeighborGraph 2) V.toIntegerCube.vertices
            (fun x => clusterExtend ω V (planarMuMinimizer ω V q) (planarCoarseAnchor ω x))
              x ^ 2) ≤ c * X ω ^ (1 / (a : ℝ)) := by
        refine h1.trans (le_of_eq ?_)
        rw [hc, hK, ENNReal.ofReal_mul (by norm_num)]
        ring
      calc _ ≤ (c * X ω ^ (1 / (a : ℝ))) ^ 2 := pow_le_pow_left₀ zero_le h2 2
        _ = c ^ 2 * X ω ^ (2 / (a : ℝ)) := by
          rw [mul_pow, ← ENNReal.rpow_natCast (X ω ^ (1 / (a : ℝ))) 2, ← ENNReal.rpow_mul]
          congr 2
          push_cast
          ring
    · exact zero_le
  -- Jensen's inequality for the power `2/a`
  have hJ : ∫⁻ ω, X ω ^ (2 / (a : ℝ)) ∂μ ≤ (∫⁻ ω, X ω ∂μ) ^ (2 / (a : ℝ)) := by
    have hpq := Real.HolderConjugate.conjExponent ha2
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hXam.aemeasurable
      (aemeasurable_const (b := (1 : ℝ≥0∞)))
    simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, measure_univ,
      ENNReal.one_rpow] at h
    refine h.trans (le_of_eq ?_)
    rw [show 1 / ((a : ℝ) / 2) = 2 / (a : ℝ) by field_simp]
    congr 1
    refine lintegral_congr fun ω => ?_
    rw [← ENNReal.rpow_mul, show 2 / (a : ℝ) * ((a : ℝ) / 2) = 1 by field_simp, ENNReal.rpow_one]
  have hEX : ∫⁻ ω, X ω ∂μ ≤ (V.toIntegerCube.vertices.card : ℝ≥0∞) * CT := by
    rw [hX, lintegral_finsetSum _ fun z _ => measurable_reachSum (7 * a) z]
    calc ∑ z ∈ V.toIntegerCube.vertices, ∫⁻ ω, reachSum ω (7 * a) z ∂μ
        ≤ ∑ _z ∈ V.toIntegerCube.vertices, CT := Finset.sum_le_sum fun z _ => hT z
      _ = (V.toIntegerCube.vertices.card : ℝ≥0∞) * CT := by rw [Finset.sum_const, nsmul_eq_mul]
  calc ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω V then
          ENNReal.ofReal (∑ x ∈ V.toIntegerCube.vertices,
            gradNormIn (nearestNeighborGraph 2) V.toIntegerCube.vertices
              (fun x => clusterExtend ω V (planarMuMinimizer ω V q) (planarCoarseAnchor ω x)) x ^ 2)
              ^ 2
          else 0) ∂μ
      ≤ ∫⁻ ω, c ^ 2 * X ω ^ (2 / (a : ℝ)) ∂μ := lintegral_mono hpoint
    _ = c ^ 2 * ∫⁻ ω, X ω ^ (2 / (a : ℝ)) ∂μ := lintegral_const_mul _ hXam
    _ ≤ c ^ 2 * ((V.toIntegerCube.vertices.card : ℝ≥0∞) * CT) ^ (2 / (a : ℝ)) := by
        gcongr
        exact hJ.trans (ENNReal.rpow_le_rpow hEX (by positivity))
    _ = K ^ 2 * CT ^ (2 / (a : ℝ)) * ENNReal.ofReal ((|q 0| + |q 1|) ^ 2) ^ 2 *
          (V.toIntegerCube.vertices.card : ℝ≥0∞) ^ 2 *
          (V.toIntegerCube.vertices.card : ℝ≥0∞) ^ (2 / (a : ℝ)) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), hc]
        ring

end Rigidity.Proofs.Cluster
