import Rigidity.Proofs.Corrector.GeneralFlipCluster
import Rigidity.Proofs.Corrector.GeneralStepOneGrowth
import Rigidity.Proofs.Poincare.GeneralHeatKernelBounds

/-!
# Convergence of the heat series of the sizes of the anchor regions of `ℤᵈ`, for the flips

The results of Case 3 of Step 2 (`ae_heatComp_coarse_sub_eq_walkSum_closed`) assume the
convergence of `Σ_z Φ_{r²}(x, z) |stepRegion(z)|`, `stepRegion(z)` the union of the partition cubes
of `z` and `z + e_j`. As in the planar file `DarioStepRegionSummable`:

* `card_stepRegion_le`: `|stepRegion(z)| ≤ (1 + 3^d) size(□_𝒫(z))^d`, since neighbouring partition
  cubes differ by at most one scale;
* `exists_lintegral_stoppingSize_pow_setBond_le`: `E[size(□_{𝒫(ω^{e,b})}(v))^d] ≤ K` uniformly in
  the bond, the flip and the point, from the exponential moments of the partition sizes and the
  quasi-invariance of the bond law under flips;
* `ae_summable_heat_stepRegion`: almost surely, for every bond, flip, point, direction and
  radius `r > 0`, `Σ_z Φ_{r²}(x, z) |stepRegion_{ω^{e,b}}(z)|` converges, since
  `Φ_{r²}(x, z) ≤ C^d e^{-|z - x|/n}` for every integer `n ≥ max(r, 1)` and the means of the sizes
  are bounded.
-/

namespace Rigidity.Corrector.GeneralDim

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Poincare.GeneralDim
open scoped Classical ENNReal

variable {d : ℕ}

/-- The anchor region has at most `(1 + 3^d) size(□_𝒫(z))^d` points. -/
theorem card_stepRegion_le {ω : Configuration d} (hP : PartitionEvent ω) (z : Vertex d)
    (j : Fin d) :
    ((stepRegion ω z j).card : ℝ) ≤
      (1 + 3 ^ d) * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z ^ d := by
  rw [TriadicCube.stoppingSize_eq_of_mem (mem_partitionCube hP z) (partitionCube_spec hP z).2]
  have hcard : ∀ Q : TriadicCube d,
      (Q.toIntegerCube.vertices.card : ℝ) = ((3 : ℝ) ^ Q.scale) ^ d := fun Q => by
    rw [IntegerCube.card_vertices]
    change (((3 ^ Q.scale) ^ d : ℕ) : ℝ) = _
    push_cast
    ring
  have hnear : ∀ i, |z i - (z + LatticeProb.unit j) i| ≤ 1 := fun i =>
    (abs_sub_add_unit_le z j i).1
  obtain ⟨-, h2⟩ := partitionCube_scales_close hP hnear
  unfold stepRegion
  refine (Nat.cast_le.2 (Finset.card_union_le _ _)).trans ?_
  push_cast
  rw [hcard, hcard]
  have h3 : ((3 : ℝ) ^ (partitionCube ω (z + LatticeProb.unit j)).scale) ^ d ≤
      3 ^ d * ((3 : ℝ) ^ (partitionCube ω z).scale) ^ d := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ d
    calc (3 : ℝ) ^ (partitionCube ω (z + LatticeProb.unit j)).scale
        ≤ 3 ^ ((partitionCube ω z).scale + 1) := pow_le_pow_right₀ (by norm_num) h2
      _ = 3 * 3 ^ (partitionCube ω z).scale := by ring
  linarith

theorem pow_le_factorial_mul_exp {θ y : ℝ} (hθ : 0 < θ) (hy : 0 ≤ y) (n : ℕ) :
    y ^ n ≤ n.factorial * θ ^ n * Real.exp (y / θ) := by
  have hx : 0 ≤ y / θ := div_nonneg hy hθ.le
  have h : (y / θ) ^ n / n.factorial ≤ Real.exp (y / θ) := Real.pow_div_factorial_le_exp _ hx n
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  have h' : (y / θ) ^ n ≤ Real.exp (y / θ) * n.factorial := (div_le_iff₀ hf).1 h
  have e : y ^ n = θ ^ n * (y / θ) ^ n := by
    rw [div_pow, mul_div_cancel₀ _ (pow_ne_zero n hθ.ne')]
  rw [e]
  calc θ ^ n * (y / θ) ^ n ≤ θ ^ n * (Real.exp (y / θ) * n.factorial) :=
        mul_le_mul_of_nonneg_left h' (by positivity)
    _ = n.factorial * θ ^ n * Real.exp (y / θ) := by ring

/-- **Moments of order `d` of the partition sizes of the flips**, uniformly in the bond, the flip
and the point. -/
theorem exists_lintegral_stoppingSize_pow_setBond_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (e : Bond d) (b : Bool) (v : Vertex d),
      ∫⁻ ω, ENNReal.ofReal
          (TriadicCube.stoppingSize (TriadicCube.goodCubes (setBond e b ω)) v ^ d)
        ∂latticeBondLaw d p ≤ ENNReal.ofReal K := by
  obtain ⟨θ, hθ, hexp⟩ := (partition_estimates hd hpc).2.1
  have hp0 : 0 < (p : ℝ) := (criticalProbability_nonneg d).trans_lt hpc
  have hw : ∀ b, 0 < Rigidity.Corrector.bondWeight p b := fun b => by
    unfold Rigidity.Corrector.bondWeight
    split_ifs <;> linarith
  set w := min (Rigidity.Corrector.bondWeight p true) (Rigidity.Corrector.bondWeight p false)
    with hwdef
  have hw0 : 0 < w := lt_min (hw true) (hw false)
  have hwb : ∀ b, w ≤ Rigidity.Corrector.bondWeight p b := fun b => by
    cases b
    · exact min_le_right _ _
    · exact min_le_left _ _
  set c : ℝ := d.factorial * θ ^ d with hc
  refine ⟨2 * c / w, by positivity, fun e b v => ?_⟩
  set S : Configuration d → ℝ := fun ω => TriadicCube.stoppingSize (TriadicCube.goodCubes ω) v
    with hS
  have hSm : Measurable S := measurable_stoppingSize_goodCubes v
  have hbase : ∫⁻ ω, ENNReal.ofReal (S ω ^ d) ∂latticeBondLaw d p ≤ ENNReal.ofReal (2 * c) := by
    calc ∫⁻ ω, ENNReal.ofReal (S ω ^ d) ∂latticeBondLaw d p
        ≤ ∫⁻ ω, ENNReal.ofReal c * ENNReal.ofReal (Real.exp (S ω / θ))
            ∂latticeBondLaw d p := lintegral_mono fun ω => by
          rw [← ENNReal.ofReal_mul (by positivity)]
          exact ENNReal.ofReal_le_ofReal
            (pow_le_factorial_mul_exp hθ (stoppingSize_nonneg _ _) d)
      _ = ENNReal.ofReal c * ∫⁻ ω, ENNReal.ofReal (Real.exp (S ω / θ))
            ∂latticeBondLaw d p :=
          lintegral_const_mul _ (ENNReal.measurable_ofReal.comp
            (Real.measurable_exp.comp (hSm.div_const θ)))
      _ ≤ ENNReal.ofReal c * ENNReal.ofReal 2 := by
          have hI := ofReal_integral_eq_lintegral_ofReal (hexp v).1
            (Eventually.of_forall fun ω => (Real.exp_pos _).le)
          exact mul_le_mul' le_rfl (hI.symm.trans_le (ENNReal.ofReal_le_ofReal (hexp v).2))
      _ = ENNReal.ofReal (2 * c) := by
          rw [← ENNReal.ofReal_mul (by positivity), mul_comm]
  have hflip := ofReal_bondWeight_mul_lintegral_setBond_le p
    (f := fun ω => ENNReal.ofReal (S ω ^ d))
    (ENNReal.measurable_ofReal.comp (hSm.pow_const d)) e b
  have hq' : ENNReal.ofReal (Rigidity.Corrector.bondWeight p b) ≠ 0 := by simp [hw b]
  have hq'' : ENNReal.ofReal (Rigidity.Corrector.bondWeight p b) ≠ ∞ := ENNReal.ofReal_ne_top
  calc ∫⁻ ω, ENNReal.ofReal (S (setBond e b ω) ^ d) ∂latticeBondLaw d p
      = (ENNReal.ofReal (Rigidity.Corrector.bondWeight p b))⁻¹ *
          (ENNReal.ofReal (Rigidity.Corrector.bondWeight p b) *
            ∫⁻ ω, ENNReal.ofReal (S (setBond e b ω) ^ d) ∂latticeBondLaw d p) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hq' hq'', one_mul]
    _ ≤ (ENNReal.ofReal (Rigidity.Corrector.bondWeight p b))⁻¹ * ENNReal.ofReal (2 * c) :=
        mul_le_mul' le_rfl (hflip.trans hbase)
    _ = ENNReal.ofReal (2 * c / Rigidity.Corrector.bondWeight p b) := by
        rw [ENNReal.ofReal_div_of_pos (hw b), div_eq_mul_inv, mul_comm]
    _ ≤ ENNReal.ofReal (2 * c / w) :=
        ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left (by positivity) hw0 (hwb b))

/-- The Euclidean norm of a lattice vector is at most its `ℓ¹` norm. -/
theorem norm_latticeEuclideanEmbedding_le_sum_abs (v : Vertex d) :
    ‖latticeEuclideanEmbedding v‖ ≤ ∑ i, |((v i : ℤ) : ℝ)| := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_le_left (Finset.sum_nonneg fun i _ => abs_nonneg _)]
  calc ∑ i, ‖latticeEuclideanEmbedding v i‖ ^ 2 = ∑ i, |((v i : ℤ) : ℝ)| * |((v i : ℤ) : ℝ)| := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show ‖latticeEuclideanEmbedding v i‖ = |((v i : ℤ) : ℝ)| from Real.norm_eq_abs _, sq]
    _ ≤ ∑ i, |((v i : ℤ) : ℝ)| * ∑ j, |((v j : ℤ) : ℝ)| :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
          (Finset.single_le_sum (f := fun j => |((v j : ℤ) : ℝ)|) (fun j _ => abs_nonneg _)
            (Finset.mem_univ i)) (abs_nonneg _)
    _ = (∑ i, |((v i : ℤ) : ℝ)|) ^ 2 := by rw [← Finset.sum_mul, sq]

/-- The heat kernel of `ℤᵈ` at time `r²`, `r ≥ 0`, decays like `e^{-|z - x|/n}` for every integer
`n ≥ max(r, 1)`. -/
theorem exists_zdHeat_le_exp_norm [NeZero d] :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℝ), 0 ≤ r → ∀ (n : ℕ), max r 1 ≤ n → ∀ x z : Vertex d,
      zdHeat d (r ^ 2) x z ≤ C * Real.exp (-‖latticeEuclideanEmbedding (z - x)‖ / n) := by
  obtain ⟨C, hC, h⟩ := exists_zdHeat_mul_exp_le (d := d)
  refine ⟨C ^ d, by positivity, fun r hr n hn x z => ?_⟩
  have hσ : max (Real.sqrt (r ^ 2)) 1 = max r 1 := by rw [Real.sqrt_sq hr]
  have h1 := h (r ^ 2) (sq_nonneg r) 0 le_rfl (by norm_num) (by rw [zero_mul]; norm_num) x z
  rw [zero_mul, Real.exp_zero, mul_one, hσ] at h1
  have hσ1 : (1 : ℝ) ≤ max r 1 := le_max_right _ _
  have hσ0 : (0 : ℝ) < max r 1 := lt_of_lt_of_le one_pos hσ1
  have hσd : C ^ d / max r 1 ^ d ≤ C ^ d := div_le_self (by positivity) (one_le_pow₀ hσ1)
  have hnorm := norm_latticeEuclideanEmbedding_le_sum_abs (z - x)
  have hexp : Real.exp (-(∑ i, |(((z - x) i : ℤ) : ℝ)|) / max r 1) ≤
      Real.exp (-‖latticeEuclideanEmbedding (z - x)‖ / n) := by
    refine Real.exp_le_exp.2 ?_
    rw [neg_div, neg_div, neg_le_neg_iff]
    calc ‖latticeEuclideanEmbedding (z - x)‖ / n
        ≤ ‖latticeEuclideanEmbedding (z - x)‖ / max r 1 :=
          div_le_div_of_nonneg_left (norm_nonneg _) hσ0 hn
      _ ≤ (∑ i, |(((z - x) i : ℤ) : ℝ)|) / max r 1 := div_le_div_of_nonneg_right hnorm hσ0.le
  calc zdHeat d (r ^ 2) x z
      ≤ C ^ d / max r 1 ^ d * Real.exp (-(∑ i, |(((z - x) i : ℤ) : ℝ)|) / max r 1) := h1
    _ ≤ C ^ d * Real.exp (-‖latticeEuclideanEmbedding (z - x)‖ / n) :=
        mul_le_mul hσd hexp (Real.exp_pos _).le (by positivity)

/-- **The heat series of the anchor regions converge for the flips**: almost surely, for every
bond, flip, point, direction and radius `r > 0`, `Σ_z Φ_{r²}(x, z) |stepRegion_{ω^{e,b}}(z)|`
converges. -/
theorem ae_summable_heat_stepRegion [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∀ᵐ ω ∂latticeBondLaw d p, ∀ (e : Bond d) (b : Bool) (x : Vertex d) (j : Fin d) (r : ℝ),
      0 < r → Summable fun z => zdHeat d (r ^ 2) x z * (stepRegion (setBond e b ω) z j).card := by
  have hp0 : 0 < (p : ℝ) := (criticalProbability_nonneg d).trans_lt hpc
  obtain ⟨K, hK, hmom⟩ := exists_lintegral_stoppingSize_pow_setBond_le hd hpc hp1
  obtain ⟨CH, hCH, hheat⟩ := exists_zdHeat_le_exp_norm (d := d)
  set wt : ℕ → Vertex d → Vertex d → ℝ := fun n x z =>
    Real.exp (-‖latticeEuclideanEmbedding (z - x)‖ / ((n : ℝ) + 1)) with hwt
  have hfin : ∀ (n : ℕ) (e : Bond d) (b : Bool) (x : Vertex d), ∀ᵐ ω ∂latticeBondLaw d p,
      ∑' z, ENNReal.ofReal (wt n x z) * ENNReal.ofReal
        (TriadicCube.stoppingSize (TriadicCube.goodCubes (setBond e b ω)) z ^ d) < ∞ := by
    intro n e b x
    have hm : ∀ z, Measurable fun ω => ENNReal.ofReal
        (TriadicCube.stoppingSize (TriadicCube.goodCubes (setBond e b ω)) z ^ d) :=
      fun z => ENNReal.measurable_ofReal.comp
        (((measurable_stoppingSize_goodCubes z).comp (measurable_setBond e b)).pow_const d)
    refine ae_lt_top (Measurable.tsum fun z => (hm z).const_mul _) ?_
    rw [lintegral_tsum fun z => ((hm z).const_mul _).aemeasurable]
    refine ne_top_of_le_ne_top (b := ∑' z, ENNReal.ofReal (wt n x z) * ENNReal.ofReal K) ?_ ?_
    · rw [ENNReal.tsum_mul_right]
      exact ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.ofReal_ne_top
        (tsum_exp_neg_norm_sub_le x (by positivity : (0 : ℝ) < (n : ℝ) + 1)))
        ENNReal.ofReal_ne_top
    · refine ENNReal.tsum_le_tsum fun z => ?_
      rw [lintegral_const_mul _ (hm z)]
      exact mul_le_mul' le_rfl (hmom e b z)
  have hfin' : ∀ᵐ ω ∂latticeBondLaw d p, ∀ (n : ℕ) (e : Bond d) (b : Bool) (x : Vertex d),
      ∑' z, ENNReal.ofReal (wt n x z) * ENNReal.ofReal
        (TriadicCube.stoppingSize (TriadicCube.goodCubes (setBond e b ω)) z ^ d) < ∞ :=
    ae_all_iff.2 fun n => ae_all_iff.2 fun e => ae_all_iff.2 fun b => ae_all_iff.2 fun x =>
      hfin n e b x
  filter_upwards [hfin', ae_setBond hp0 hp1 (ae_partitionEvent hd hpc)] with ω hf hP e b x j r hr
  obtain ⟨n, hn⟩ := exists_nat_ge (max r 1)
  have hn' : max r 1 ≤ ((n : ℝ) + 1) := hn.trans (by linarith)
  have hs : Summable fun z => wt n x z *
      TriadicCube.stoppingSize (TriadicCube.goodCubes (setBond e b ω)) z ^ d := by
    refine (ENNReal.summable_toReal (ne_top_of_le_ne_top (hf n e b x).ne
      (ENNReal.tsum_le_tsum fun z => ?_))).congr fun z => ENNReal.toReal_ofReal (by
        have := stoppingSize_nonneg (TriadicCube.goodCubes (setBond e b ω)) z
        positivity)
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
  refine Summable.of_nonneg_of_le (fun z => mul_nonneg (zdHeat_nonneg (sq_nonneg r) x z)
    (Nat.cast_nonneg _)) (fun z => ?_) (hs.mul_left (CH * (1 + 3 ^ d)))
  have h1 : zdHeat d (r ^ 2) x z ≤ CH * wt n x z := by
    have := hheat r hr.le (n + 1) (by exact_mod_cast hn') x z
    simpa [hwt] using this
  have h2 := card_stepRegion_le (hP e b) z j
  have hc0 : (0 : ℝ) ≤ (stepRegion (setBond e b ω) z j).card := Nat.cast_nonneg _
  have hS0 := stoppingSize_nonneg (TriadicCube.goodCubes (setBond e b ω)) z
  calc zdHeat d (r ^ 2) x z * (stepRegion (setBond e b ω) z j).card
      ≤ (CH * wt n x z) *
          ((1 + 3 ^ d) * TriadicCube.stoppingSize (TriadicCube.goodCubes (setBond e b ω)) z ^ d) :=
        mul_le_mul h1 h2 hc0 (by positivity)
    _ = CH * (1 + 3 ^ d) *
          (wt n x z * TriadicCube.stoppingSize (TriadicCube.goodCubes (setBond e b ω)) z ^ d) := by
        ring

end Rigidity.Corrector.GeneralDim
