import Rigidity.Proofs.Percolation.PlanarFlatnessInputs
import Rigidity.Proofs.Cluster.PlanarCoarseEnergyMoments
import Rigidity.Proofs.S3.Divergence
import Rigidity.Proofs.Percolation.PlanarFiniteVolumeBounds
import Rigidity.Proofs.Percolation.PlanarOmegaPointwise

/-!
# The energy of the coarsened minimizers of `μ` with a measurable majorant

The squared gradient `|∇w|²(x)` on the lattice points of a cube is the squared norm
`gradNormIn` of the nearest-neighbour graph. By the pointwise bound of the energy of the coarsened
minimizer of `μ` by the moments of the reach (`ofReal_coarse_minimizer_le_reachSum`) and Jensen's
inequality, for every `δ > 0` the normalized energy `|□|⁻¹ ∑_{x ∈ □} |∇[u(·, □, q)]_P|²(x)` is
almost surely below a measurable function of expectation at most `C(δ) |q|² size(□)^δ`
(Armstrong and Dario, (4.24), in expectation, in dimension two).
-/

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped Classical ENNReal

namespace Rigidity.Percolation

/-- `|∇u|²(x)` is the squared norm of the gradient for the nearest-neighbour graph. -/
theorem gradNormSq_eq_gradNormIn_sq (A : Finset (Vertex 2)) (u : Vertex 2 → ℝ) (x : Vertex 2) :
    Rigidity.Proofs.Multiscale.gradNormSq A u x =
      Rigidity.Percolation.gradNormIn (nearestNeighborGraph 2) A u x ^ 2 := by
  rw [gradNormIn, Real.sq_sqrt (mul_nonneg (by norm_num) (Finset.sum_nonneg fun y _ => by
    split_ifs <;> positivity))]
  rw [Rigidity.Proofs.Multiscale.gradNormSq]
  congr 1
  rw [← Finset.sum_filter]
  have hset : A.filter (fun y => (nearestNeighborGraph 2).Adj x y) =
      ((lattice 2).neighborFinset x).filter (· ∈ A) := by
    ext y
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  rw [hset, Finset.sum_filter, Rigidity.Proofs.S3.sum_lattice_neighborFinset_eq_nbrSum, nbrSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Rigidity.Proofs.Multiscale.unitVec, unit]

theorem coarseEnergy_eq (ω : Configuration 2) (U : TriadicCube 2) (w : ClusterFun ω U) :
    coarseEnergy ω U w = U.volume⁻¹ * ∑ x ∈ U.toIntegerCube.vertices,
      Rigidity.Percolation.gradNormIn (nearestNeighborGraph 2) U.toIntegerCube.vertices
        (fun x => clusterExtend ω U w (planarCoarseAnchor ω x)) x ^ 2 := by
  rw [coarseEnergy]
  congr 1
  exact Finset.sum_congr rfl fun x _ => gradNormSq_eq_gradNormIn_sq _ _ x

theorem coarseEnergy_zero (ω : Configuration 2) (U : TriadicCube 2) :
    coarseEnergy ω U 0 = 0 := by
  rw [coarseEnergy]
  simp [coarsen, Rigidity.Proofs.Multiscale.gradNormSq]

/-- **The energy of the coarsened minimizers of `μ` with a measurable majorant** (Armstrong and
Dario, (4.24), in expectation, in dimension two). -/
theorem exists_coarseEnergyMu_majorant {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : TriadicCube 2) (q : Fin 2 → ℝ),
      ∃ F : Configuration 2 → ℝ, Measurable F ∧ (∀ ω, 0 ≤ F ω) ∧
        (∀ᵐ ω ∂(latticeBondLaw 2 p), coarseEnergy ω U (planarMuMinimizer ω U q) ≤ F ω) ∧
        ∫⁻ ω, ENNReal.ofReal (F ω) ∂(latticeBondLaw 2 p) ≤
          ENNReal.ofReal (C * (q 0 ^ 2 + q 1 ^ 2) * (3 : ℝ) ^ (δ * U.scale)) := by
  set a : ℕ := ⌈2 / δ⌉₊ + 2 with ha
  have ha2 : 2 ≤ a := by omega
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have haδ : 2 / (a : ℝ) ≤ δ := by
    rw [div_le_iff₀ ha0]
    have h1 : 2 / δ ≤ (⌈2 / δ⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈2 / δ⌉₊ : ℝ) ≤ a := by rw [ha]; push_cast; linarith
    have h3 : 2 / δ ≤ a := h1.trans h2
    rw [div_le_iff₀ hδ] at h3
    linarith
  obtain ⟨CT, hCT, hT⟩ := exists_lintegral_tsum_ninefold_le hpc (7 * a)
  set K : ℝ≥0∞ := ENNReal.ofReal ((2 * ((2 : ℕ) : ℝ) * (3 / 2 * (2 * ((4 : ℕ) : ℝ) + 2) ^ 2) *
    (2 * ((4 : ℕ) : ℝ) + 1) ^ 2 * (2 * √((2 : ℕ) : ℝ))) ^ 2) * (27 * 234256) with hK
  have hKt : K ≠ ∞ := by rw [hK]; finiteness
  set Kr : ℝ := (K * CT ^ (1 / (a : ℝ))).toReal with hKr
  refine ⟨2 * 18 * Kr, by positivity, fun U q => ?_⟩
  set μ := latticeBondLaw 2 p with hμ
  set N : ℝ := (U.toIntegerCube.vertices.card : ℝ) with hN
  have hNvol : N = U.volume := card_toIntegerCube_vertices_eq U
  have hN0 : 0 < N := by rw [hNvol]; exact U.volume_pos
  set X : Configuration 2 → ℝ≥0∞ := fun ω =>
    ∑ z ∈ U.toIntegerCube.vertices, reachSum ω (7 * a) z with hX
  have hXm : Measurable X := Finset.measurable_fun_sum _ fun z _ => measurable_reachSum (7 * a) z
  set c : ℝ≥0∞ := K * ENNReal.ofReal (18 * (|q 0| + |q 1|) ^ 2) *
    (U.toIntegerCube.vertices.card : ℝ≥0∞) with hc
  set M : Configuration 2 → ℝ≥0∞ := fun ω => c * X ω ^ (1 / (a : ℝ)) with hM
  have hMm : Measurable M := (hXm.pow_const _).const_mul _
  -- the integral of the majorant
  have hJ : ∫⁻ ω, X ω ^ (1 / (a : ℝ)) ∂μ ≤ (∫⁻ ω, X ω ∂μ) ^ (1 / (a : ℝ)) := by
    have ha1 : (1 : ℝ) < a := by exact_mod_cast (show 1 < a by omega)
    have hpq := Real.HolderConjugate.conjExponent ha1
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq (hXm.pow_const (1 / (a : ℝ))).aemeasurable
      (aemeasurable_const (b := (1 : ℝ≥0∞)))
    simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, measure_univ,
      ENNReal.one_rpow] at h
    refine h.trans (le_of_eq ?_)
    congr 1
    refine lintegral_congr fun ω => ?_
    rw [← ENNReal.rpow_mul, one_div_mul_cancel ha0.ne', ENNReal.rpow_one]
  have hEX : ∫⁻ ω, X ω ∂μ ≤ (U.toIntegerCube.vertices.card : ℝ≥0∞) * CT := by
    rw [hX, lintegral_finsetSum _ fun z _ => measurable_reachSum (7 * a) z]
    calc ∑ z ∈ U.toIntegerCube.vertices, ∫⁻ ω, reachSum ω (7 * a) z ∂μ
        ≤ ∑ _z ∈ U.toIntegerCube.vertices, CT := Finset.sum_le_sum fun z _ => hT z
      _ = (U.toIntegerCube.vertices.card : ℝ≥0∞) * CT := by rw [Finset.sum_const, nsmul_eq_mul]
  have hIM : ∫⁻ ω, M ω ∂μ ≤ K * CT ^ (1 / (a : ℝ)) * ENNReal.ofReal (18 * (|q 0| + |q 1|) ^ 2) *
      (U.toIntegerCube.vertices.card : ℝ≥0∞) *
      (U.toIntegerCube.vertices.card : ℝ≥0∞) ^ (1 / (a : ℝ)) := by
    calc ∫⁻ ω, M ω ∂μ = c * ∫⁻ ω, X ω ^ (1 / (a : ℝ)) ∂μ :=
          lintegral_const_mul _ (hXm.pow_const _)
      _ ≤ c * ((U.toIntegerCube.vertices.card : ℝ≥0∞) * CT) ^ (1 / (a : ℝ)) := by
          gcongr
          exact hJ.trans (ENNReal.rpow_le_rpow hEX (by positivity))
      _ = _ := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), hc]
          ring
  have hfin : ∫⁻ ω, M ω ∂μ ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ hIM
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top hKt
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) hCT)) ENNReal.ofReal_ne_top)
      (ENNReal.natCast_ne_top _)) (ENNReal.rpow_ne_top_of_nonneg (by positivity)
      (ENNReal.natCast_ne_top _))
  refine ⟨fun ω => U.volume⁻¹ * (M ω).toReal, measurable_const.mul hMm.ennreal_toReal,
    fun ω => mul_nonneg (inv_nonneg.2 U.volume_pos.le) ENNReal.toReal_nonneg, ?_, ?_⟩
  · filter_upwards [ae_lt_top hMm hfin] with ω hω
    by_cases h : PlanarPartitionEvent ω ∧ PlanarResolved ω U
    · rw [coarseEnergy_eq]
      refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 U.volume_pos.le)
      have h1 := Rigidity.Proofs.Cluster.ofReal_coarse_minimizer_le_reachSum h.1 h.2 q
        (show 1 ≤ a by omega)
      have h2 : ENNReal.ofReal (∑ x ∈ U.toIntegerCube.vertices,
          Rigidity.Percolation.gradNormIn (nearestNeighborGraph 2) U.toIntegerCube.vertices
            (fun x => clusterExtend ω U (planarMuMinimizer ω U q) (planarCoarseAnchor ω x)) x ^ 2) ≤
          M ω := by
        refine h1.trans (le_of_eq ?_)
        rw [hM, hc, hK]
      exact (ENNReal.ofReal_le_iff_le_toReal hω.ne).1 h2
    · have h0 : planarMuMinimizer ω U q = 0 := by rw [planarMuMinimizer, dif_neg h]
      rw [h0, coarseEnergy_zero]
      exact mul_nonneg (inv_nonneg.2 U.volume_pos.le) ENNReal.toReal_nonneg
  · have hpt : ∀ ω, ENNReal.ofReal (U.volume⁻¹ * (M ω).toReal) ≤
        ENNReal.ofReal U.volume⁻¹ * M ω := fun ω => by
      rw [ENNReal.ofReal_mul (inv_nonneg.2 U.volume_pos.le)]
      exact mul_le_mul_of_nonneg_left ENNReal.ofReal_toReal_le zero_le
    refine (lintegral_mono hpt).trans ?_
    rw [lintegral_const_mul _ hMm]
    refine (mul_le_mul_of_nonneg_left hIM zero_le).trans ?_
    -- back to real numbers
    have hcard : (U.toIntegerCube.vertices.card : ℝ≥0∞) = ENNReal.ofReal N := by
      rw [hN, ENNReal.ofReal_natCast]
    have hKC : K * CT ^ (1 / (a : ℝ)) = ENNReal.ofReal Kr := by
      rw [hKr, ENNReal.ofReal_toReal (ENNReal.mul_ne_top hKt
        (ENNReal.rpow_ne_top_of_nonneg (by positivity) hCT))]
    have hKr0 : 0 ≤ Kr := ENNReal.toReal_nonneg
    rw [hcard, hKC, ENNReal.ofReal_rpow_of_nonneg hN0.le (by positivity)]
    have hv0 : 0 ≤ U.volume⁻¹ := inv_nonneg.2 U.volume_pos.le
    have hA0 : 0 ≤ 18 * (|q 0| + |q 1|) ^ 2 := by positivity
    have hB0 : 0 ≤ N ^ (1 / (a : ℝ)) := Real.rpow_nonneg hN0.le _
    have hcomb : ENNReal.ofReal U.volume⁻¹ * (ENNReal.ofReal Kr *
        ENNReal.ofReal (18 * (|q 0| + |q 1|) ^ 2) * ENNReal.ofReal N *
        ENNReal.ofReal (N ^ (1 / (a : ℝ)))) = ENNReal.ofReal (U.volume⁻¹ *
          (Kr * (18 * (|q 0| + |q 1|) ^ 2) * N * N ^ (1 / (a : ℝ)))) := by
      rw [ENNReal.ofReal_mul (p := U.volume⁻¹) hv0,
        ENNReal.ofReal_mul (p := Kr * (18 * (|q 0| + |q 1|) ^ 2) * N)
          (mul_nonneg (mul_nonneg hKr0 hA0) hN0.le),
        ENNReal.ofReal_mul (p := Kr * (18 * (|q 0| + |q 1|) ^ 2)) (mul_nonneg hKr0 hA0),
        ENNReal.ofReal_mul (p := Kr) hKr0]
    rw [hcomb]
    refine ENNReal.ofReal_le_ofReal ?_
    have hNa : N ^ (1 / (a : ℝ)) ≤ (3 : ℝ) ^ (δ * U.scale) := by
      rw [hNvol]
      change ((9 : ℝ) ^ U.scale) ^ (1 / (a : ℝ)) ≤ _
      rw [show (9 : ℝ) = 3 ^ (2 : ℝ) by norm_num, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
        ← Real.rpow_mul (by norm_num)]
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      have hs : (0 : ℝ) ≤ U.scale := Nat.cast_nonneg _
      have : 2 * ((U.scale : ℝ) * (1 / a)) = 2 / a * U.scale := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right haδ hs
    have hq1 : (|q 0| + |q 1|) ^ 2 ≤ 2 * (q 0 ^ 2 + q 1 ^ 2) := abs_add_abs_sq_le q
    have e : U.volume⁻¹ * (Kr * (18 * (|q 0| + |q 1|) ^ 2) * N * N ^ (1 / (a : ℝ))) =
        Kr * (18 * (|q 0| + |q 1|) ^ 2) * N ^ (1 / (a : ℝ)) := by
      rw [← hNvol]
      field_simp
    rw [e]
    have hNa0 : 0 ≤ N ^ (1 / (a : ℝ)) := hB0
    calc Kr * (18 * (|q 0| + |q 1|) ^ 2) * N ^ (1 / (a : ℝ))
        ≤ Kr * (18 * (2 * (q 0 ^ 2 + q 1 ^ 2))) * (3 : ℝ) ^ (δ * U.scale) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hKr0) hNa hNa0 (by positivity)
      _ = 2 * 18 * Kr * (q 0 ^ 2 + q 1 ^ 2) * (3 : ℝ) ^ (δ * U.scale) := by ring

/-- **The energy of the coarsened maximizers of `ν` with a measurable majorant** (Armstrong and
Dario, (4.25), in expectation, in dimension two). -/
theorem exists_coarseEnergyNu_majorant {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : TriadicCube 2) (q : Fin 2 → ℝ),
      ∃ F : Configuration 2 → ℝ, Measurable F ∧ (∀ ω, 0 ≤ F ω) ∧
        (∀ᵐ ω ∂(latticeBondLaw 2 p), coarseEnergy ω U (planarNuSolution ω U q) ≤ F ω) ∧
        ∫⁻ ω, ENNReal.ofReal (F ω) ∂(latticeBondLaw 2 p) ≤
          ENNReal.ofReal (C * (q 0 ^ 2 + q 1 ^ 2) * (3 : ℝ) ^ (δ * U.scale)) := by
  set a : ℕ := ⌈2 / δ⌉₊ + 2 with ha
  have ha2 : 2 ≤ a := by omega
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have haδ : 2 / (a : ℝ) ≤ δ := by
    rw [div_le_iff₀ ha0]
    have h1 : 2 / δ ≤ (⌈2 / δ⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈2 / δ⌉₊ : ℝ) ≤ a := by rw [ha]; push_cast; linarith
    have h3 : 2 / δ ≤ a := h1.trans h2
    rw [div_le_iff₀ hδ] at h3
    linarith
  obtain ⟨CT, hCT, hT⟩ := exists_lintegral_tsum_ninefold_le hpc (7 * a)
  set K : ℝ≥0∞ := ENNReal.ofReal ((2 * ((2 : ℕ) : ℝ) * (3 / 2 * (2 * ((4 : ℕ) : ℝ) + 2) ^ 2) *
    (2 * ((4 : ℕ) : ℝ) + 1) ^ 2 * (2 * √((2 : ℕ) : ℝ))) ^ 2) * 27 with hK
  have hKt : K ≠ ∞ := by rw [hK]; finiteness
  set Kr : ℝ := (K * CT ^ (1 / (a : ℝ))).toReal with hKr
  refine ⟨2 * 18 * Kr, by positivity, fun U q => ?_⟩
  set μ := latticeBondLaw 2 p with hμ
  set N : ℝ := (U.toIntegerCube.vertices.card : ℝ) with hN
  have hNvol : N = U.volume := card_toIntegerCube_vertices_eq U
  have hN0 : 0 < N := by rw [hNvol]; exact U.volume_pos
  set X : Configuration 2 → ℝ≥0∞ := fun ω =>
    ∑ z ∈ U.toIntegerCube.vertices, reachSum ω (7 * a) z with hX
  have hXm : Measurable X := Finset.measurable_fun_sum _ fun z _ => measurable_reachSum (7 * a) z
  set c : ℝ≥0∞ := K * ENNReal.ofReal (9 / 2 * (|q 0| + |q 1|) ^ 2) *
    (U.toIntegerCube.vertices.card : ℝ≥0∞) with hc
  set M : Configuration 2 → ℝ≥0∞ := fun ω => c * X ω ^ (1 / (a : ℝ)) with hM
  have hMm : Measurable M := (hXm.pow_const _).const_mul _
  -- the integral of the majorant
  have hJ : ∫⁻ ω, X ω ^ (1 / (a : ℝ)) ∂μ ≤ (∫⁻ ω, X ω ∂μ) ^ (1 / (a : ℝ)) := by
    have ha1 : (1 : ℝ) < a := by exact_mod_cast (show 1 < a by omega)
    have hpq := Real.HolderConjugate.conjExponent ha1
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq (hXm.pow_const (1 / (a : ℝ))).aemeasurable
      (aemeasurable_const (b := (1 : ℝ≥0∞)))
    simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, measure_univ,
      ENNReal.one_rpow] at h
    refine h.trans (le_of_eq ?_)
    congr 1
    refine lintegral_congr fun ω => ?_
    rw [← ENNReal.rpow_mul, one_div_mul_cancel ha0.ne', ENNReal.rpow_one]
  have hEX : ∫⁻ ω, X ω ∂μ ≤ (U.toIntegerCube.vertices.card : ℝ≥0∞) * CT := by
    rw [hX, lintegral_finsetSum _ fun z _ => measurable_reachSum (7 * a) z]
    calc ∑ z ∈ U.toIntegerCube.vertices, ∫⁻ ω, reachSum ω (7 * a) z ∂μ
        ≤ ∑ _z ∈ U.toIntegerCube.vertices, CT := Finset.sum_le_sum fun z _ => hT z
      _ = (U.toIntegerCube.vertices.card : ℝ≥0∞) * CT := by rw [Finset.sum_const, nsmul_eq_mul]
  have hIM : ∫⁻ ω, M ω ∂μ ≤ K * CT ^ (1 / (a : ℝ)) * ENNReal.ofReal (9 / 2 * (|q 0| + |q 1|) ^ 2) *
      (U.toIntegerCube.vertices.card : ℝ≥0∞) *
      (U.toIntegerCube.vertices.card : ℝ≥0∞) ^ (1 / (a : ℝ)) := by
    calc ∫⁻ ω, M ω ∂μ = c * ∫⁻ ω, X ω ^ (1 / (a : ℝ)) ∂μ :=
          lintegral_const_mul _ (hXm.pow_const _)
      _ ≤ c * ((U.toIntegerCube.vertices.card : ℝ≥0∞) * CT) ^ (1 / (a : ℝ)) := by
          gcongr
          exact hJ.trans (ENNReal.rpow_le_rpow hEX (by positivity))
      _ = _ := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), hc]
          ring
  have hfin : ∫⁻ ω, M ω ∂μ ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ hIM
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top hKt
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) hCT)) ENNReal.ofReal_ne_top)
      (ENNReal.natCast_ne_top _)) (ENNReal.rpow_ne_top_of_nonneg (by positivity)
      (ENNReal.natCast_ne_top _))
  refine ⟨fun ω => U.volume⁻¹ * (M ω).toReal, measurable_const.mul hMm.ennreal_toReal,
    fun ω => mul_nonneg (inv_nonneg.2 U.volume_pos.le) ENNReal.toReal_nonneg, ?_, ?_⟩
  · filter_upwards [ae_lt_top hMm hfin] with ω hω
    by_cases h : PlanarPartitionEvent ω ∧ PlanarResolved ω U
    · rw [coarseEnergy_eq]
      refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 U.volume_pos.le)
      have hsol : planarNuSolution ω U q = planarNuMaximizer ω U q := by
        rw [planarNuSolution, if_pos h]
      have h1 := Rigidity.Proofs.Cluster.ofReal_sum_gradNormIn_coarse_sq_le h.1 h.2
        (planarNuMaximizer ω U q)
      have hB : ENNReal.ofReal (clusterForm ω U (planarNuMaximizer ω U q)
          (planarNuMaximizer ω U q)) ≤ ENNReal.ofReal (9 / 2 * (|q 0| + |q 1|) ^ 2) *
          (U.toIntegerCube.vertices.card : ℝ≥0∞) := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have hν := planarNu_le (ω := ω) (U := U) q
        have he := planarNu_eq_planarNuMaximizer (ω := ω) U q
        have hv := U.volume_pos
        rw [← hN, hNvol]
        rw [he] at hν
        rw [div_div, div_le_iff₀ (by positivity)] at hν
        linarith
      have hsup : (3 * U.toIntegerCube.vertices.sup (planarReach ω)) ^ 3 ≤
          27 * X ω ^ (1 / (a : ℝ)) := by
        have h7 := Rigidity.Proofs.Cluster.sup_planarReach_pow_seven_le (ω := ω) U
          (show 1 ≤ a by omega)
        have h1R : 1 ≤ U.toIntegerCube.vertices.sup (planarReach ω) := by
          obtain ⟨z, hz⟩ := Rigidity.Proofs.Cluster.TriadicCube.toIntegerCube_vertices_nonempty U
          exact (one_le_planarReach h.1 z).trans (Finset.le_sup (f := planarReach ω) hz)
        rw [mul_pow]
        have : (3 : ℝ≥0∞) ^ 3 = 27 := by norm_num
        rw [this]
        refine mul_le_mul_of_nonneg_left ((pow_le_pow_right₀ h1R (by norm_num : 3 ≤ 7)).trans h7)
          zero_le
      have h2 : ENNReal.ofReal (∑ x ∈ U.toIntegerCube.vertices,
          Rigidity.Percolation.gradNormIn (nearestNeighborGraph 2) U.toIntegerCube.vertices
            (fun x => clusterExtend ω U (planarNuSolution ω U q) (planarCoarseAnchor ω x)) x ^ 2) ≤
          M ω := by
        rw [hsol]
        refine h1.trans ?_
        rw [hM, hc, hK]
        calc _ ≤ ENNReal.ofReal ((2 * ((2 : ℕ) : ℝ) * (3 / 2 * (2 * ((4 : ℕ) : ℝ) + 2) ^ 2) *
              (2 * ((4 : ℕ) : ℝ) + 1) ^ 2 * (2 * √((2 : ℕ) : ℝ))) ^ 2) *
              (27 * X ω ^ (1 / (a : ℝ))) * (ENNReal.ofReal (9 / 2 * (|q 0| + |q 1|) ^ 2) *
                (U.toIntegerCube.vertices.card : ℝ≥0∞)) := by gcongr
          _ = _ := by ring
      exact (ENNReal.ofReal_le_iff_le_toReal hω.ne).1 h2
    · have h0 : planarNuSolution ω U q = 0 := by rw [planarNuSolution, if_neg h]
      rw [h0, coarseEnergy_zero]
      exact mul_nonneg (inv_nonneg.2 U.volume_pos.le) ENNReal.toReal_nonneg
  · have hpt : ∀ ω, ENNReal.ofReal (U.volume⁻¹ * (M ω).toReal) ≤
        ENNReal.ofReal U.volume⁻¹ * M ω := fun ω => by
      rw [ENNReal.ofReal_mul (inv_nonneg.2 U.volume_pos.le)]
      exact mul_le_mul_of_nonneg_left ENNReal.ofReal_toReal_le zero_le
    refine (lintegral_mono hpt).trans ?_
    rw [lintegral_const_mul _ hMm]
    refine (mul_le_mul_of_nonneg_left hIM zero_le).trans ?_
    -- back to real numbers
    have hcard : (U.toIntegerCube.vertices.card : ℝ≥0∞) = ENNReal.ofReal N := by
      rw [hN, ENNReal.ofReal_natCast]
    have hKC : K * CT ^ (1 / (a : ℝ)) = ENNReal.ofReal Kr := by
      rw [hKr, ENNReal.ofReal_toReal (ENNReal.mul_ne_top hKt
        (ENNReal.rpow_ne_top_of_nonneg (by positivity) hCT))]
    have hKr0 : 0 ≤ Kr := ENNReal.toReal_nonneg
    rw [hcard, hKC, ENNReal.ofReal_rpow_of_nonneg hN0.le (by positivity)]
    have hv0 : 0 ≤ U.volume⁻¹ := inv_nonneg.2 U.volume_pos.le
    have hA0 : 0 ≤ 9 / 2 * (|q 0| + |q 1|) ^ 2 := by positivity
    have hB0 : 0 ≤ N ^ (1 / (a : ℝ)) := Real.rpow_nonneg hN0.le _
    have hcomb : ENNReal.ofReal U.volume⁻¹ * (ENNReal.ofReal Kr *
        ENNReal.ofReal (9 / 2 * (|q 0| + |q 1|) ^ 2) * ENNReal.ofReal N *
        ENNReal.ofReal (N ^ (1 / (a : ℝ)))) = ENNReal.ofReal (U.volume⁻¹ *
          (Kr * (9 / 2 * (|q 0| + |q 1|) ^ 2) * N * N ^ (1 / (a : ℝ)))) := by
      rw [ENNReal.ofReal_mul (p := U.volume⁻¹) hv0,
        ENNReal.ofReal_mul (p := Kr * (9 / 2 * (|q 0| + |q 1|) ^ 2) * N)
          (mul_nonneg (mul_nonneg hKr0 hA0) hN0.le),
        ENNReal.ofReal_mul (p := Kr * (9 / 2 * (|q 0| + |q 1|) ^ 2)) (mul_nonneg hKr0 hA0),
        ENNReal.ofReal_mul (p := Kr) hKr0]
    rw [hcomb]
    refine ENNReal.ofReal_le_ofReal ?_
    have hNa : N ^ (1 / (a : ℝ)) ≤ (3 : ℝ) ^ (δ * U.scale) := by
      rw [hNvol]
      change ((9 : ℝ) ^ U.scale) ^ (1 / (a : ℝ)) ≤ _
      rw [show (9 : ℝ) = 3 ^ (2 : ℝ) by norm_num, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
        ← Real.rpow_mul (by norm_num)]
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      have hs : (0 : ℝ) ≤ U.scale := Nat.cast_nonneg _
      have : 2 * ((U.scale : ℝ) * (1 / a)) = 2 / a * U.scale := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right haδ hs
    have hq1 : (|q 0| + |q 1|) ^ 2 ≤ 2 * (q 0 ^ 2 + q 1 ^ 2) := abs_add_abs_sq_le q
    have e : U.volume⁻¹ * (Kr * (9 / 2 * (|q 0| + |q 1|) ^ 2) * N * N ^ (1 / (a : ℝ))) =
        Kr * (9 / 2 * (|q 0| + |q 1|) ^ 2) * N ^ (1 / (a : ℝ)) := by
      rw [← hNvol]
      field_simp
    rw [e]
    have hNa0 : 0 ≤ N ^ (1 / (a : ℝ)) := hB0
    calc Kr * (9 / 2 * (|q 0| + |q 1|) ^ 2) * N ^ (1 / (a : ℝ))
        ≤ Kr * (9 / 2 * (2 * (q 0 ^ 2 + q 1 ^ 2))) * (3 : ℝ) ^ (δ * U.scale) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hKr0) hNa hNa0 (by positivity)
      _ = 2 * 18 * Kr * (q 0 ^ 2 + q 1 ^ 2) * (3 : ℝ) ^ (δ * U.scale) / 4 := by ring
      _ ≤ 2 * 18 * Kr * (q 0 ^ 2 + q 1 ^ 2) * (3 : ℝ) ^ (δ * U.scale) := by
          have : 0 ≤ 2 * 18 * Kr * (q 0 ^ 2 + q 1 ^ 2) * (3 : ℝ) ^ (δ * U.scale) := by positivity
          linarith

end Rigidity.Percolation
