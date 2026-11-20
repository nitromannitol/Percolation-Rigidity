import Rigidity.Proofs.Section5.SparseOpenPaths
import Rigidity.Proofs.Section5.PlanarRenormalizedDomination

/-!
# Sparse paths in the renormalized field

For sufficiently large blocks, long star paths with few very-good blocks satisfy a uniform
exponential probability bound.
-/

open MeasureTheory Filter Topology LatticeProb.Percolation Rigidity.Section5 Rigidity.Steps.Section5

namespace Rigidity.Proofs.Section5

/-- For every supercritical bond density, sufficiently large block sizes give an exponential
bound for sparse star paths starting in any finite set. -/
theorem planar_renormalized_sparse_paths {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∀ᶠ R : ℕ in atTop, ∀ (T : Finset PlanarCarrier) (N : ℕ),
      ((latticeBondLaw 2 p).map (renormField R))
        (⋃ j : ℕ, ⋃ z ∈ T, ⋃ l ∈ starWalkLists (N + j) z,
          {η | l.Nodup ∧ 2 * l.countP η ≤ N + j}) ≤
            ENNReal.ofReal (4 * (T.card : ℝ) * (1 / 8 : ℝ) ^ N) := by
  obtain ⟨C, c, s, hC, hc, hs, hbound⟩ := veryGoodProbabilityStep_two
    Rigidity.Percolation.wellConnected_input_two Rigidity.Percolation.kesten_rectangle_crossing p hpc
  have htend : Tendsto (fun R : ℕ => C * Real.exp (-(c * (R : ℝ) ^ s))) atTop (𝓝 0) := by
    have hpow : Tendsto (fun R : ℕ => (R : ℝ) ^ s) atTop atTop :=
      (tendsto_rpow_atTop hs).comp tendsto_natCast_atTop_atTop
    simpa only [mul_zero, Function.comp_def] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp (hpow.const_mul_atTop hc)).const_mul C
  filter_upwards [htend.eventually_lt_const (show (0 : ℝ) < (1 / 144 : ℝ) ^ 18 by positivity)]
    with R hsmall T N
  have hmeas := renormFieldMeasurableStep R
  haveI : IsProbabilityMeasure ((latticeBondLaw 2 p).map (renormField R)) :=
    Measure.isProbabilityMeasure_map hmeas.aemeasurable
  refine measure_exists_sparse_star_path_le (renormFieldOneDependentStep p R) (fun z => ?_) T N
  have hz : MeasurableSet {ω : PlanarCarrier → Bool | ω z = false} :=
    measurableSet_eq_fun (measurable_pi_apply z) measurable_const
  rw [Measure.map_apply hmeas hz]
  have hsite := hbound (renormCentre R z) (11 * R / 10)
  have hRr : (R : ℝ) ^ s ≤ ((11 * R / 10 : ℕ) : ℝ) ^ s :=
    Real.rpow_le_rpow (Nat.cast_nonneg _)
      (by exact_mod_cast (show R ≤ 11 * R / 10 by omega)) hs.le
  have hexp : Real.exp (-(c * ((11 * R / 10 : ℕ) : ℝ) ^ s)) ≤
      Real.exp (-(c * (R : ℝ) ^ s)) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hRr hc.le])
  have hsite' : (latticeBondLaw 2 p) (renormField R ⁻¹' {ω | ω z = false}) ≤
      ENNReal.ofReal (C * Real.exp (-(c * ((11 * R / 10 : ℕ) : ℝ) ^ s))) := by
    convert hsite using 2
    ext ω
    simp [renormField]
  refine hsite'.trans (ENNReal.ofReal_le_ofReal ?_)
  exact (mul_le_mul_of_nonneg_left hexp hC.le).trans hsmall.le

end Rigidity.Proofs.Section5
