import Rigidity.Proofs.Cluster.PlanarCoarseMinimizer
import Rigidity.Proofs.Percolation.PlanarReachMoments

/-!
# The expected energy of the coarsened minimizer of `μ`

Armstrong and Dario, display (4.10), in expectation, in dimension two: for every `a ≥ 2` there is
`C < ∞` such that for every triadic cube `V` and slope `q`,
`E[∑_{x ∈ V} |∇[u(·, V, q)]_𝒫|²(x)] ≤ C |q|₁² |V|^{1 + 1/a}`
(`exists_lintegral_coarse_minimizer_le`), the expectation being taken on the planar partition event
and the resolution of `V`. Pointwise, the energy is at most a constant times
`|q|₁² |V| (max_V R)⁷` (`ofReal_sum_gradNormIn_coarse_planarMuMinimizer_le`), and
`(max_V R)⁷ ≤ (∑_V R^{7a})^{1/a}`; the `7a`-th moments of the reach are bounded uniformly
(`exists_lintegral_tsum_ninefold_le`), and Jensen's inequality for the concave power `1/a` gives the
factor `|V|^{1/a}`. Armstrong and Dario state the bound with the loss `3^{δ n}`, `δ > 0` arbitrary,
which is the factor `|V|^{1/a}` for `a` large.
-/

namespace Rigidity.Proofs.Cluster

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Proofs.Section5
open scoped BigOperators Classical ENNReal

variable {ω : Configuration 2}

theorem TriadicCube.toIntegerCube_vertices_nonempty (V : TriadicCube 2) :
    V.toIntegerCube.vertices.Nonempty := by
  refine ⟨V.toIntegerCube.corner, ?_⟩
  rw [IntegerCube.mem_vertices]
  intro i
  have : (0 : ℤ) < ((V.toIntegerCube.size : ℕ) : ℤ) := by
    rw [V.cast_toIntegerCube_size]
    positivity
  omega

/-- The seventh power of the largest reach on a cube is at most the `a`-th root of the sum over the
cube of the `7a`-th powers. -/
theorem sup_planarReach_pow_seven_le (V : TriadicCube 2) {a : ℕ} (ha : 1 ≤ a) :
    (V.toIntegerCube.vertices.sup (planarReach ω)) ^ 7 ≤
      (∑ z ∈ V.toIntegerCube.vertices, reachSum ω (7 * a) z) ^ (1 / (a : ℝ)) := by
  obtain ⟨z, hz, hzs⟩ := Finset.exists_mem_eq_sup _ (TriadicCube.toIntegerCube_vertices_nonempty V)
    (planarReach ω)
  rw [hzs]
  have h1 : planarReach ω z ^ (7 * a) ≤ ∑ z ∈ V.toIntegerCube.vertices, reachSum ω (7 * a) z := by
    obtain ⟨k, hk⟩ : ∃ k, 7 * a = k + 1 := ⟨7 * a - 1, by omega⟩
    calc planarReach ω z ^ (7 * a) ≤ reachSum ω (7 * a) z := by
          rw [hk]
          exact planarReach_pow_le ω z k
      _ ≤ ∑ z ∈ V.toIntegerCube.vertices, reachSum ω (7 * a) z :=
          Finset.single_le_sum (f := fun z => reachSum ω (7 * a) z) (fun _ _ => zero_le) hz
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  calc planarReach ω z ^ 7 = (planarReach ω z ^ (7 * a)) ^ (1 / (a : ℝ)) := by
        rw [pow_mul, ← ENNReal.rpow_natCast (planarReach ω z ^ 7) a, ← ENNReal.rpow_mul,
          mul_one_div_cancel ha0.ne', ENNReal.rpow_one]
    _ ≤ (∑ z ∈ V.toIntegerCube.vertices, reachSum ω (7 * a) z) ^ (1 / (a : ℝ)) :=
        ENNReal.rpow_le_rpow h1 (by positivity)

/-- **The coarsened minimizer of `μ`, by the moments of the reach**, pointwise:
`∑_{x ∈ V} |∇[u]_𝒫|²(x) ≤ C² · 27 · 234256 · 18 |q|₁² |V| (∑_V R^{7a})^{1/a}`. -/
theorem ofReal_coarse_minimizer_le_reachSum (hP : PlanarPartitionEvent ω) {V : TriadicCube 2}
    (hV : PlanarResolved ω V) (q : Fin 2 → ℝ) {a : ℕ} (ha : 1 ≤ a) :
    ENNReal.ofReal (∑ x ∈ V.toIntegerCube.vertices,
        gradNormIn (nearestNeighborGraph 2) V.toIntegerCube.vertices
          (fun x => clusterExtend ω V (planarMuMinimizer ω V q) (planarCoarseAnchor ω x)) x ^ 2) ≤
      ENNReal.ofReal ((2 * ((2 : ℕ) : ℝ) * (3 / 2 * (2 * ((4 : ℕ) : ℝ) + 2) ^ 2) *
        (2 * ((4 : ℕ) : ℝ) + 1) ^ 2 * (2 * √((2 : ℕ) : ℝ))) ^ 2) * (27 * 234256) *
        ENNReal.ofReal (18 * (|q 0| + |q 1|) ^ 2) * (V.toIntegerCube.vertices.card : ℝ≥0∞) *
          (∑ z ∈ V.toIntegerCube.vertices, reachSum ω (7 * a) z) ^ (1 / (a : ℝ)) := by
  set S := V.toIntegerCube.vertices.sup (planarReach ω) with hS
  have h := ofReal_sum_gradNormIn_coarse_planarMuMinimizer_le hP hV q
  rw [← hS] at h
  have hsum : ∑ z ∈ V.toIntegerCube.vertices, 234256 * planarReach ω z ^ 4 ≤
      (V.toIntegerCube.vertices.card : ℝ≥0∞) * (234256 * S ^ 4) := by
    calc ∑ z ∈ V.toIntegerCube.vertices, 234256 * planarReach ω z ^ 4
        ≤ ∑ _z ∈ V.toIntegerCube.vertices, 234256 * S ^ 4 := by
          gcongr with z hz
          exact Finset.le_sup (f := planarReach ω) hz
      _ = (V.toIntegerCube.vertices.card : ℝ≥0∞) * (234256 * S ^ 4) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have h7 := sup_planarReach_pow_seven_le (ω := ω) V ha
  rw [← hS] at h7
  refine h.trans ?_
  calc ENNReal.ofReal ((2 * ((2 : ℕ) : ℝ) * (3 / 2 * (2 * ((4 : ℕ) : ℝ) + 2) ^ 2) *
          (2 * ((4 : ℕ) : ℝ) + 1) ^ 2 * (2 * √((2 : ℕ) : ℝ))) ^ 2) * (3 * S) ^ 3 *
        (ENNReal.ofReal (18 * (|q 0| + |q 1|) ^ 2) *
          ∑ z ∈ V.toIntegerCube.vertices, 234256 * planarReach ω z ^ 4)
      ≤ ENNReal.ofReal ((2 * ((2 : ℕ) : ℝ) * (3 / 2 * (2 * ((4 : ℕ) : ℝ) + 2) ^ 2) *
          (2 * ((4 : ℕ) : ℝ) + 1) ^ 2 * (2 * √((2 : ℕ) : ℝ))) ^ 2) * (3 * S) ^ 3 *
        (ENNReal.ofReal (18 * (|q 0| + |q 1|) ^ 2) *
          ((V.toIntegerCube.vertices.card : ℝ≥0∞) * (234256 * S ^ 4))) := by
        gcongr
    _ = ENNReal.ofReal ((2 * ((2 : ℕ) : ℝ) * (3 / 2 * (2 * ((4 : ℕ) : ℝ) + 2) ^ 2) *
          (2 * ((4 : ℕ) : ℝ) + 1) ^ 2 * (2 * √((2 : ℕ) : ℝ))) ^ 2) * (27 * 234256) *
        ENNReal.ofReal (18 * (|q 0| + |q 1|) ^ 2) * (V.toIntegerCube.vertices.card : ℝ≥0∞) *
          S ^ 7 := by ring
    _ ≤ _ := by gcongr

/-- **The expected energy of the coarsened minimizer of `μ`** (Armstrong and Dario, (4.10), in
expectation, in dimension two). For every `a ≥ 2` there is `C < ∞` with
`E[∑_{x ∈ V} |∇[u(·, V, q)]_𝒫|²(x)] ≤ C |q|₁² |V| |V|^{1/a}` for every triadic cube `V` and slope
`q`, on the partition event and the resolution of `V`. -/
theorem exists_lintegral_coarse_minimizer_le {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) {a : ℕ} (ha : 2 ≤ a) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (V : TriadicCube 2) (q : Fin 2 → ℝ),
      ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω V then
          ENNReal.ofReal (∑ x ∈ V.toIntegerCube.vertices,
            gradNormIn (nearestNeighborGraph 2) V.toIntegerCube.vertices
              (fun x => clusterExtend ω V (planarMuMinimizer ω V q) (planarCoarseAnchor ω x)) x ^ 2)
          else 0) ∂(latticeBondLaw 2 p) ≤
        C * ENNReal.ofReal ((|q 0| + |q 1|) ^ 2) * (V.toIntegerCube.vertices.card : ℝ≥0∞) *
          (V.toIntegerCube.vertices.card : ℝ≥0∞) ^ (1 / (a : ℝ)) := by
  obtain ⟨CT, hCT, hT⟩ := exists_lintegral_tsum_ninefold_le hpc (7 * a)
  set K : ℝ≥0∞ := ENNReal.ofReal ((2 * ((2 : ℕ) : ℝ) * (3 / 2 * (2 * ((4 : ℕ) : ℝ) + 2) ^ 2) *
    (2 * ((4 : ℕ) : ℝ) + 1) ^ 2 * (2 * √((2 : ℕ) : ℝ))) ^ 2) * (27 * 234256) *
    ENNReal.ofReal 18 with hK
  have ha1 : (1 : ℝ) < a := by exact_mod_cast (show 1 < a by omega)
  have ha0 : (0 : ℝ) < a := by linarith
  refine ⟨K * CT ^ (1 / (a : ℝ)), ENNReal.mul_ne_top (by rw [hK]; finiteness)
    (ENNReal.rpow_ne_top_of_nonneg (by positivity) hCT), fun V q => ?_⟩
  set μ := latticeBondLaw 2 p with hμ
  set X : Configuration 2 → ℝ≥0∞ := fun ω =>
    ∑ z ∈ V.toIntegerCube.vertices, reachSum ω (7 * a) z with hX
  have hXm : Measurable X := Finset.measurable_sum _ fun z _ => measurable_reachSum (7 * a) z
  have hXam : Measurable fun ω => X ω ^ (1 / (a : ℝ)) := hXm.pow_const _
  set c : ℝ≥0∞ := K * ENNReal.ofReal ((|q 0| + |q 1|) ^ 2) *
    (V.toIntegerCube.vertices.card : ℝ≥0∞) with hc
  have hpoint : ∀ ω : Configuration 2, (if PlanarPartitionEvent ω ∧ PlanarResolved ω V then
      ENNReal.ofReal (∑ x ∈ V.toIntegerCube.vertices,
        gradNormIn (nearestNeighborGraph 2) V.toIntegerCube.vertices
          (fun x => clusterExtend ω V (planarMuMinimizer ω V q) (planarCoarseAnchor ω x)) x ^ 2)
      else 0) ≤ c * X ω ^ (1 / (a : ℝ)) := by
    intro ω
    split_ifs with h
    · refine (ofReal_coarse_minimizer_le_reachSum h.1 h.2 q (by omega : 1 ≤ a)).trans
        (le_of_eq ?_)
      rw [hc, hK, ENNReal.ofReal_mul (by norm_num)]
      ring
    · exact zero_le
  -- Jensen's inequality for the power `1/a`
  have hJ : ∫⁻ ω, X ω ^ (1 / (a : ℝ)) ∂μ ≤ (∫⁻ ω, X ω ∂μ) ^ (1 / (a : ℝ)) := by
    have hpq := Real.HolderConjugate.conjExponent ha1
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hXam.aemeasurable
      (aemeasurable_const (b := (1 : ℝ≥0∞)))
    simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, measure_univ,
      ENNReal.one_rpow] at h
    refine h.trans (le_of_eq ?_)
    congr 1
    refine lintegral_congr fun ω => ?_
    rw [← ENNReal.rpow_mul, one_div_mul_cancel ha0.ne', ENNReal.rpow_one]
  have hEX : ∫⁻ ω, X ω ∂μ ≤ (V.toIntegerCube.vertices.card : ℝ≥0∞) * CT := by
    rw [hX, lintegral_finsetSum _ fun z _ => measurable_reachSum (7 * a) z]
    calc ∑ z ∈ V.toIntegerCube.vertices, ∫⁻ ω, reachSum ω (7 * a) z ∂μ
        ≤ ∑ _z ∈ V.toIntegerCube.vertices, CT := Finset.sum_le_sum fun z _ => hT z
      _ = (V.toIntegerCube.vertices.card : ℝ≥0∞) * CT := by rw [Finset.sum_const, nsmul_eq_mul]
  calc ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω V then
          ENNReal.ofReal (∑ x ∈ V.toIntegerCube.vertices,
            gradNormIn (nearestNeighborGraph 2) V.toIntegerCube.vertices
              (fun x => clusterExtend ω V (planarMuMinimizer ω V q) (planarCoarseAnchor ω x)) x ^ 2)
          else 0) ∂μ
      ≤ ∫⁻ ω, c * X ω ^ (1 / (a : ℝ)) ∂μ := lintegral_mono hpoint
    _ = c * ∫⁻ ω, X ω ^ (1 / (a : ℝ)) ∂μ := lintegral_const_mul _ hXam
    _ ≤ c * ((V.toIntegerCube.vertices.card : ℝ≥0∞) * CT) ^ (1 / (a : ℝ)) := by
        gcongr
        exact hJ.trans (ENNReal.rpow_le_rpow hEX (by positivity))
    _ = K * CT ^ (1 / (a : ℝ)) * ENNReal.ofReal ((|q 0| + |q 1|) ^ 2) *
          (V.toIntegerCube.vertices.card : ℝ≥0∞) *
          (V.toIntegerCube.vertices.card : ℝ≥0∞) ^ (1 / (a : ℝ)) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), hc]
        ring

end Rigidity.Proofs.Cluster
