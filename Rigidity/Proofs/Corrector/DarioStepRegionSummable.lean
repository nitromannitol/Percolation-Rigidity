import Rigidity.Proofs.Corrector.DarioCaseThreeClosed
import Rigidity.Proofs.Corrector.PlanarPartitionComparison
import Rigidity.Proofs.Corrector.PlanarCoarseningError
import Rigidity.Proofs.Corrector.DarioFlipSumReduce

/-!
# Convergence of the heat series of the sizes of the anchor regions, for the flips

The results of Case 3 of Step 2 (`ae_heatComp_coarse_sub_eq_walkSum_closed`) assume the
convergence of `Σ_z Φ_{r²}(x, z) |stepRegion(z)|`, `stepRegion(z)` the square of side `9s` around
the smaller of the partition cubes of `z` and `z + e_j`. Here:

* `card_stepRegion_le`: `|stepRegion(z)| ≤ 81 size(□_𝒫(z))²`;
* `exists_lintegral_stoppingSize_sq_setBond_le`: `E[size(□_{𝒫(ω^{e,b})}(v))²] ≤ K` uniformly in
  the bond, the flip and the point, from the exponential moments of the partition sizes and the
  quasi-invariance of the bond law under flips;
* `ae_summable_heat_stepRegion`: almost surely, for every bond, flip, point, direction and
  radius `r > 0`, `Σ_z Φ_{r²}(x, z) |stepRegion_{ω^{e,b}}(z)|` converges, since
  `Φ_{r²}(x, z) ≤ 3 e^{r²/18} e^{-|z - x|/18}` and the means of the sizes are bounded.
-/

namespace Rigidity.Corrector

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.External
open scoped Classical ENNReal

/-- The anchor region has at most `81 size(□_𝒫(z))²` points. -/
theorem card_stepRegion_le {ω : Configuration 2} (hP : PlanarPartitionEvent ω) (z : Vertex 2)
    (j : Fin 2) :
    ((stepRegion ω z j).card : ℝ) ≤ 81 * TriadicCube.stoppingSize (planarGoodCubes ω) z ^ 2 := by
  rw [TriadicCube.stoppingSize_eq_of_mem (planarPartCube_spec hP z).1 (planarPartCube_spec hP z).2]
  have hcard : ∀ Q : TriadicCube 2, (Q.ninefold.vertices.card : ℝ) = 81 * ((3 : ℝ) ^ Q.scale) ^ 2 :=
    fun Q => by
      rw [IntegerCube.card_vertices_eq]
      change (((9 * 3 ^ Q.scale) ^ 2 : ℕ) : ℝ) = _
      push_cast
      ring
  unfold stepRegion
  split_ifs with h
  · rw [hcard]
  · rw [hcard]
    have hlt : (planarPartCube ω (z + LatticeProb.unit j)).scale ≤ (planarPartCube ω z).scale := by
      omega
    have := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hlt
    have h0 : (0 : ℝ) ≤ 3 ^ (planarPartCube ω (z + LatticeProb.unit j)).scale := by positivity
    nlinarith

theorem sq_le_two_mul_sq_mul_exp {θ y : ℝ} (hθ : 0 < θ) (hy : 0 ≤ y) :
    y ^ 2 ≤ 2 * θ ^ 2 * Real.exp (y / θ) := by
  have h := Real.quadratic_le_exp_of_nonneg (div_nonneg hy hθ.le)
  have h1 : (y / θ) ^ 2 ≤ 2 * Real.exp (y / θ) := by nlinarith [div_nonneg hy hθ.le]
  have e : y ^ 2 = θ ^ 2 * (y / θ) ^ 2 := by field_simp
  rw [e]
  nlinarith [sq_nonneg θ]

/-- **Second moments of the partition sizes of the flips**, uniformly in the bond, the flip and
the point. -/
theorem exists_lintegral_stoppingSize_sq_setBond_le {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (e : Bond 2) (b : Bool) (v : Vertex 2),
      ∫⁻ ω, ENNReal.ofReal (TriadicCube.stoppingSize (planarGoodCubes (setBond e b ω)) v ^ 2)
        ∂latticeBondLaw 2 p ≤ ENNReal.ofReal K := by
  obtain ⟨θ, hθ, hexp⟩ := (planar_meshed_partition_estimates hpc).2.1
  have hp0 : 0 < (p : ℝ) := (criticalProbability_nonneg 2).trans_lt hpc
  have hw : ∀ b, 0 < bondWeight p b := fun b => by
    unfold bondWeight
    split_ifs <;> linarith
  set w := min (bondWeight p true) (bondWeight p false) with hwdef
  have hw0 : 0 < w := lt_min (hw true) (hw false)
  have hwb : ∀ b, w ≤ bondWeight p b := fun b => by
    cases b
    · exact min_le_right _ _
    · exact min_le_left _ _
  refine ⟨4 * θ ^ 2 / w, by positivity, fun e b v => ?_⟩
  set S : Configuration 2 → ℝ := fun ω => TriadicCube.stoppingSize (planarGoodCubes ω) v with hS
  have hSm : Measurable S := measurable_stoppingSize_planar v
  have hbase : ∫⁻ ω, ENNReal.ofReal (S ω ^ 2) ∂latticeBondLaw 2 p ≤ ENNReal.ofReal (4 * θ ^ 2) := by
    calc ∫⁻ ω, ENNReal.ofReal (S ω ^ 2) ∂latticeBondLaw 2 p
        ≤ ∫⁻ ω, ENNReal.ofReal (2 * θ ^ 2) * ENNReal.ofReal (Real.exp (S ω / θ))
            ∂latticeBondLaw 2 p := lintegral_mono fun ω => by
          rw [← ENNReal.ofReal_mul (by positivity)]
          exact ENNReal.ofReal_le_ofReal
            (sq_le_two_mul_sq_mul_exp hθ (stoppingSize_nonneg' _ _))
      _ = ENNReal.ofReal (2 * θ ^ 2) * ∫⁻ ω, ENNReal.ofReal (Real.exp (S ω / θ))
            ∂latticeBondLaw 2 p :=
          lintegral_const_mul _ (ENNReal.measurable_ofReal.comp
            (Real.measurable_exp.comp (hSm.div_const θ)))
      _ ≤ ENNReal.ofReal (2 * θ ^ 2) * ENNReal.ofReal 2 := by
          have hI := ofReal_integral_eq_lintegral_ofReal (hexp v).1
            (Eventually.of_forall fun ω => (Real.exp_pos _).le)
          exact mul_le_mul' le_rfl (hI.symm.trans_le (ENNReal.ofReal_le_ofReal (hexp v).2))
      _ = ENNReal.ofReal (4 * θ ^ 2) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          ring_nf
  have hflip := ofReal_bondWeight_mul_lintegral_setBond_le p
    (f := fun ω => ENNReal.ofReal (S ω ^ 2))
    (ENNReal.measurable_ofReal.comp (hSm.pow_const 2)) e b
  have hq' : ENNReal.ofReal (bondWeight p b) ≠ 0 := by simp [hw b]
  have hq'' : ENNReal.ofReal (bondWeight p b) ≠ ∞ := ENNReal.ofReal_ne_top
  calc ∫⁻ ω, ENNReal.ofReal (S (setBond e b ω) ^ 2) ∂latticeBondLaw 2 p
      = (ENNReal.ofReal (bondWeight p b))⁻¹ * (ENNReal.ofReal (bondWeight p b) *
          ∫⁻ ω, ENNReal.ofReal (S (setBond e b ω) ^ 2) ∂latticeBondLaw 2 p) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hq' hq'', one_mul]
    _ ≤ (ENNReal.ofReal (bondWeight p b))⁻¹ * ENNReal.ofReal (4 * θ ^ 2) :=
        mul_le_mul' le_rfl (hflip.trans hbase)
    _ = ENNReal.ofReal (4 * θ ^ 2 / bondWeight p b) := by
        rw [ENNReal.ofReal_div_of_pos (hw b), div_eq_mul_inv, mul_comm]
    _ ≤ ENNReal.ofReal (4 * θ ^ 2 / w) :=
        ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left (by positivity) hw0 (hwb b))

/-- **The heat series of the anchor regions converge for the flips**: almost surely, for every
bond, flip, point, direction and radius `r > 0`, `Σ_z Φ_{r²}(x, z) |stepRegion_{ω^{e,b}}(z)|`
converges. -/
theorem ae_summable_heat_stepRegion {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) :
    ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ (e : Bond 2) (b : Bool) (x : Vertex 2) (j : Fin 2) (r : ℝ),
      0 < r → Summable fun z => latticeHeat (r ^ 2) x z * (stepRegion (setBond e b ω) z j).card := by
  have hp0 : 0 < (p : ℝ) := (criticalProbability_nonneg 2).trans_lt hpc
  obtain ⟨K, hK, hmom⟩ := exists_lintegral_stoppingSize_sq_setBond_le hpc hp1
  set wt : Vertex 2 → Vertex 2 → ℝ := fun x z =>
    Real.exp (-‖latticeEuclideanEmbedding (z - x)‖ / 18) with hwt
  have hfin : ∀ (e : Bond 2) (b : Bool) (x : Vertex 2), ∀ᵐ ω ∂latticeBondLaw 2 p,
      ∑' z, ENNReal.ofReal (wt x z) *
        ENNReal.ofReal (TriadicCube.stoppingSize (planarGoodCubes (setBond e b ω)) z ^ 2) < ∞ := by
    intro e b x
    have hm : ∀ z, Measurable fun ω =>
        ENNReal.ofReal (TriadicCube.stoppingSize (planarGoodCubes (setBond e b ω)) z ^ 2) :=
      fun z => ENNReal.measurable_ofReal.comp
        (((measurable_stoppingSize_planar z).comp (measurable_setBond e b)).pow_const 2)
    refine ae_lt_top (Measurable.tsum fun z => (hm z).const_mul _) ?_
    rw [lintegral_tsum fun z => ((hm z).const_mul _).aemeasurable]
    refine ne_top_of_le_ne_top (b := ∑' z, ENNReal.ofReal (wt x z) * ENNReal.ofReal K) ?_ ?_
    · rw [ENNReal.tsum_mul_right]
      exact ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.ofReal_ne_top
        (tsum_exp_neg_norm_sub_le x (by norm_num : (0 : ℝ) < 18))) ENNReal.ofReal_ne_top
    · refine ENNReal.tsum_le_tsum fun z => ?_
      rw [lintegral_const_mul _ (hm z)]
      exact mul_le_mul' le_rfl (hmom e b z)
  have hfin' : ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ (e : Bond 2) (b : Bool) (x : Vertex 2),
      ∑' z, ENNReal.ofReal (wt x z) *
        ENNReal.ofReal (TriadicCube.stoppingSize (planarGoodCubes (setBond e b ω)) z ^ 2) < ∞ :=
    ae_all_iff.2 fun e => ae_all_iff.2 fun b => ae_all_iff.2 fun x => hfin e b x
  filter_upwards [hfin', ae_setBond hp0 hp1 (ae_planarPartitionEvent hpc)] with ω hf hP e b x j r hr
  have hs : Summable fun z => wt x z *
      TriadicCube.stoppingSize (planarGoodCubes (setBond e b ω)) z ^ 2 := by
    refine (ENNReal.summable_toReal (ne_top_of_le_ne_top (hf e b x).ne
      (ENNReal.tsum_le_tsum fun z => ?_))).congr fun z => ENNReal.toReal_ofReal (by positivity)
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
  refine Summable.of_nonneg_of_le (fun z => mul_nonneg (latticeHeat_nonneg (sq_nonneg r) x z)
    (Nat.cast_nonneg _)) (fun z => ?_) (hs.mul_left (3 * Real.exp (r ^ 2 / 18) * 81))
  have h1 := latticeHeat_le_exp (by positivity : 0 < r ^ 2) le_rfl x z
  have h2 := card_stepRegion_le (hP e b) z j
  have h0 := latticeHeat_nonneg (sq_nonneg r) x z
  have hc0 : (0 : ℝ) ≤ (stepRegion (setBond e b ω) z j).card := Nat.cast_nonneg _
  have hwt0 : 0 ≤ wt x z := (Real.exp_pos _).le
  calc latticeHeat (r ^ 2) x z * (stepRegion (setBond e b ω) z j).card
      ≤ (3 * Real.exp (r ^ 2 / 18) * wt x z) *
          (81 * TriadicCube.stoppingSize (planarGoodCubes (setBond e b ω)) z ^ 2) :=
        mul_le_mul h1 h2 hc0 (by positivity)
    _ = 3 * Real.exp (r ^ 2 / 18) * 81 *
          (wt x z * TriadicCube.stoppingSize (planarGoodCubes (setBond e b ω)) z ^ 2) := by ring

end Rigidity.Corrector
