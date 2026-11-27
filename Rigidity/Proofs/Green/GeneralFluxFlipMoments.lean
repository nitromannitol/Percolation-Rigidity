import Rigidity.Proofs.Green.GeneralFluxFlipSum

/-!
# The variance bound of Gu on `ℤ^d`, `d ≥ 3`, from the boundaries of the flip chain

Part 4 of the port to `ℤ^d` of the proof of the variance bound (3.4) of Gu's proof of his
Proposition 1.1 (*An efficient algorithm for solving elliptic problems on percolation clusters*),
after the second half of `DarioGuFluxFlipMoments.lean`. Let
`X = Σ_z Φ_{r²}(x, z) flux_{e_k}(z, i)` be the heat average of the flux (`fluxObsD`). From the
bound of each squared flip difference (`FluxFlipWeightBoundD`, part 2), the flip sum through a
partition into good cubes (`FluxFlipSumPartitionD`, part 3) and the probabilistic part of Step 2
of the proof of Lemma 3.3 of Dario (*Optimal corrector estimates on percolation clusters*) in
dimension `d ≥ 3` (`DarioStepTwoWeightThree`: almost surely the good cubes of Step 2 partition
`ℤ^d`, and `W₂(y) + pathWeight(y) ≤ W(y)` with moments of polynomial growth uniformly in `y`),
`Σ_e (D_e X)² ≤ Σ_y Φ_{r²}(x, y)² W'(y)` with a weight `W'` with such moments
(`exists_fluxFlipD_weight_data`).

The cell factor `c(y) = ((3^d)^{n(y)})^{1 - 1/(1 + ε/2)}` of part 3 is at most the path weight
`pathWeight(c)(y) = |R(y)| Σ_{z ∈ R(y)} c(z) N(z)` (`ofReal_le_pathWeight`, since `y ∈ R(y)` and
`N(y) ≥ |R(y)| ≥ 1`); the planar proof bounds it instead by the squared size of the stopping cube
of `y`. Hence `Σ_e (D_e X)² = O_s(C r^{-d})` (`fluxFlipSumD_isOsBond`, by
`isOsBond_heatSqSum_of_moments`), and since the resampling variance is at most the sum of the
squared flip differences (`ae_resampleVar_le_tsum_bondFlipDiff`), `FluxVarianceBoundD d p` for
every `d ≥ 3` and supercritical `p < 1` (`fluxVarianceBoundThree_of_weight`). Since part 3 is
proved (`fluxFlipSumPartitionD_holds`), the variance bound follows from part 2 and
`DarioStepTwoWeightThree` (`fluxVarianceBoundThree_of_weightBound`); part 2 is proved as well
(`fluxFlipWeightBoundD_holds`), so the variance bound rests on `DarioStepTwoWeightThree` alone
(`fluxVarianceBoundThree_of_stepTwoWeight`).
-/

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Corrector.GeneralDim
open Rigidity.Poincare.GeneralDim (zdHeat)
open scoped Classical ENNReal

namespace Rigidity.Green.GeneralFlux

variable {d : ℕ}

/-- **The cell factor is at most the path weight**: on the event of the partition into good
cubes, `c(y) ≤ |R(y)| Σ_{z ∈ R(y)} c(z) N(z)` for every weight `c` on the vertices, since `y` lies
in the region `R(y) = stepRegion ω y j` and `N(y) ≥ |R(y)| ≥ 1`. -/
theorem ofReal_le_pathWeight {ω : Configuration d} (hP : PartitionEvent ω) (c : Vertex d → ℝ)
    (j : Fin d) (y : Vertex d) : ENNReal.ofReal (c y) ≤ pathWeight c ω j y := by
  have hy : y ∈ stepRegion ω y j := (mem_stepRegion_iff ω).2 (Or.inl (mem_partitionCube hP y))
  have hcard : (1 : ℝ≥0∞) ≤ ((stepRegion ω y j).card : ℝ≥0∞) := by
    exact_mod_cast Finset.one_le_card.2 ⟨y, hy⟩
  have hN : (1 : ℝ≥0∞) ≤ regionWeight ω j y := by
    refine hcard.trans ?_
    calc ((stepRegion ω y j).card : ℝ≥0∞) = if y ∈ stepRegion ω y j then
          ((stepRegion ω y j).card : ℝ≥0∞) else 0 := (if_pos hy).symm
      _ ≤ regionWeight ω j y := ENNReal.le_tsum (f := fun y' => if y ∈ stepRegion ω y' j then
          ((stepRegion ω y' j).card : ℝ≥0∞) else 0) y
  unfold pathWeight
  calc ENNReal.ofReal (c y) = 1 * (ENNReal.ofReal (c y) * 1) := by rw [one_mul, mul_one]
    _ ≤ ((stepRegion ω y j).card : ℝ≥0∞) * (ENNReal.ofReal (c y) * regionWeight ω j y) := by
        gcongr
    _ ≤ _ := mul_le_mul' le_rfl (Finset.single_le_sum
        (f := fun z => ENNReal.ofReal (c z) * regionWeight ω j z) (fun _ _ => bot_le) hy)

section Good

variable {G : Set (Configuration d)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent d)

/-- **The weight of the flip sum of the flux on `ℤ^d`, `d ≥ 3`, with moments of polynomial
growth** (planar: `Rigidity.Green.exists_fluxFlip_weight_data`): almost surely
`Σ_e (D_e X)² ≤ Σ_y Φ_{r²}(x, y)² W(y)` with `E[W(y)^q] ≤ (A q^κ)^q` uniformly in `y`. The planar
statement builds `W` from the Lipschitz bounds of the corrector and the sizes of the stopping
cubes; here `W` is a constant multiple of the majorant of `DarioStepTwoWeightThree`, and the
moments are stated with `∫⁻` in place of `GrowthMoments`. -/
theorem exists_fluxFlipD_weight_data [NeZero d] (hd3 : 3 ≤ d) (hW : DarioStepTwoWeightThree)
    {p : unitInterval} (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hWB : FluxFlipWeightBoundD d p) (hFS : FluxFlipSumPartitionD d p)
    (hGae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) (k : Fin d) :
    ∃ (W : Vertex d → Configuration d → ℝ≥0∞) (A κ : ℝ), 0 < A ∧ 0 < κ ∧
      (∀ y, Measurable (W y)) ∧
      (∀ y (q : ℝ), 1 ≤ q →
        ∫⁻ ω, W y ω ^ q ∂latticeBondLaw d p ≤ ENNReal.ofReal ((A * q ^ κ) ^ q)) ∧
      ∀ᵐ ω ∂latticeBondLaw d p, ∀ (i : Fin d) (r : ℝ), 0 < r → ∀ x : Vertex d,
        fluxFlipSumD hG hGv k i r x ω ≤
          ∑' y, ENNReal.ofReal (zdHeat d (r ^ 2) x y ^ 2) * W y ω := by
  obtain ⟨K₀, hK₀, κ, hκ, hflip⟩ := hWB G hG hGv hGae
  obtain ⟨ε, CM, M, hε, hCM, hM, hdata⟩ := hW d hd3 p hpc hp1 G hG hGv hGae κ hκ
  obtain ⟨hpart, W, A, m, hA, hm, hWm, hWmom, hWae⟩ := hdata k
  obtain ⟨Kc, -, hsum⟩ := hFS G hG hGv K₀ κ hK₀ hflip ε CM M hε hCM hM
  set c : ℝ := K₀ * max 1 Kc with hc
  have hc0 : 0 < c := mul_pos hK₀ (lt_max_of_lt_left one_pos)
  refine ⟨fun y ω => ENNReal.ofReal c * W y ω, c * A, m, mul_pos hc0 hA, hm,
    fun y => measurable_const.mul (hWm y),
    fun y q hq => lintegral_const_mul_rpow_le (hWm y) hc0.le hA.le hq (hWmom y q hq), ?_⟩
  filter_upwards [hsum, hpart, hWae, ae_partitionEvent (by omega : 2 ≤ d) hpc]
    with ω hs hp hWb hP
  intro i r hr x
  refine (hs k i r hr x hp hP).trans (ENNReal.tsum_le_tsum fun y => mul_le_mul' le_rfl ?_)
  have hcell := ofReal_le_pathWeight hP
    (fun z => (((3 : ℝ) ^ d) ^ partScale hp z) ^ (1 - 1 / (1 + ε / 2))) k y
  have hm1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (max 1 Kc) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have hm2 : ENNReal.ofReal Kc ≤ ENNReal.ofReal (max 1 Kc) :=
    ENNReal.ofReal_le_ofReal (le_max_right _ _)
  calc ENNReal.ofReal K₀ * (stepTwoWeight hG hGv κ k ω y + ENNReal.ofReal Kc *
        ENNReal.ofReal ((((3 : ℝ) ^ d) ^ partScale hp y) ^ (1 - 1 / (1 + ε / 2))))
      ≤ ENNReal.ofReal K₀ * (ENNReal.ofReal (max 1 Kc) * (stepTwoWeight hG hGv κ k ω y +
          pathWeight (fun z => (((3 : ℝ) ^ d) ^ partScale hp z) ^ (1 - 1 / (1 + ε / 2)))
            ω k y)) := by
        refine mul_le_mul' le_rfl ?_
        rw [mul_add]
        exact add_le_add (le_mul_of_one_le_left bot_le hm1) (mul_le_mul' hm2 hcell)
    _ ≤ ENNReal.ofReal K₀ * (ENNReal.ofReal (max 1 Kc) * W y ω) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl (hWb hp k y))
    _ = ENNReal.ofReal c * W y ω := by
        rw [hc, ← mul_assoc, ← ENNReal.ofReal_mul hK₀.le]

/-- **The flip sum of the heat average of the flux on `ℤ^d`, `d ≥ 3`, is `O_s(C r^{-d})`**
(planar: `Rigidity.Green.fluxFlipSum_isOsBond`, with `C/r²`), from the boundaries of parts 2
and 3 and the probabilistic part of Step 2 in dimension `d ≥ 3`. -/
theorem fluxFlipSumD_isOsBond [NeZero d] (hd3 : 3 ≤ d) (hW : DarioStepTwoWeightThree)
    {p : unitInterval} (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hWB : FluxFlipWeightBoundD d p) (hFS : FluxFlipSumPartitionD d p)
    (hGae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) :
    ∃ s C : ℝ, 0 < s ∧ 0 < C ∧ ∀ (k i : Fin d) (r : ℝ), 1 ≤ r → ∀ x : Vertex d,
      (∀ᵐ ω ∂latticeBondLaw d p, fluxFlipSumD hG hGv k i r x ω < ∞) ∧
      IsOsBond d p (fun ω => (fluxFlipSumD hG hGv k i r x ω).toReal) s (C / r ^ (d : ℝ)) := by
  choose W A κ hA hκ hWm hWmom hWae using fun k =>
    exists_fluxFlipD_weight_data hG hGv hd3 hW hpc hp1 hWB hFS hGae k
  obtain ⟨s, C, hs, hC, hOs⟩ := isOsBond_heatSqSum_of_moments (d := d) (p := p)
    (A := ∑ k, A k) (k := ∑ k, κ k) (Finset.sum_pos (fun k _ => hA k) Finset.univ_nonempty)
    (Finset.sum_pos (fun k _ => hκ k) Finset.univ_nonempty)
  refine ⟨s, C, hs, hC, fun k i r hr x => ?_⟩
  have hAk : A k ≤ ∑ k, A k :=
    Finset.single_le_sum (fun k _ => (hA k).le) (Finset.mem_univ k)
  have hκk : κ k ≤ ∑ k, κ k :=
    Finset.single_le_sum (fun k _ => (hκ k).le) (Finset.mem_univ k)
  have hr0 : 0 < r := by linarith
  have hYm : Measurable (fluxFlipSumD hG hGv k i r x) := by
    unfold fluxFlipSumD
    exact Measurable.tsum fun e => ENNReal.measurable_ofReal.comp
      ((measurable_bondFlipDiff (measurable_fluxObsD hG hGv k i r x) e).pow_const 2)
  exact hOs r hr x (W k) (hWm k)
    (fun y q hq => (hWmom k y q hq).trans
      (ENNReal.ofReal_le_ofReal (rpow_moment_mono (hA k).le hAk hκk hq)))
    (fluxFlipSumD hG hGv k i r x) hYm
    (by filter_upwards [hWae k] with ω h using h i r hr0 x)

end Good

/-- **The variance bound (3.4) of Gu's proof of Proposition 1.1 in dimension `d ≥ 3`**
(`FluxVarianceBoundThree`), from the bound of each flip difference (part 2,
`FluxFlipWeightBoundD`), the flip sum through a partition into good cubes (part 3,
`FluxFlipSumPartitionD`) and the probabilistic part of Step 2 of the proof of Lemma 3.3 of Dario
in dimension `d ≥ 3` (`DarioStepTwoWeightThree`). The planar route is `fluxVarianceBoundD_two`;
the hypotheses on parts 2 and 3 are required only for `d ≥ 3` and supercritical `p < 1`. -/
theorem fluxVarianceBoundThree_of_weight (hW : DarioStepTwoWeightThree)
    (h2 : ∀ (d : ℕ) [NeZero d], 3 ≤ d → ∀ p : unitInterval, criticalProbability d < (p : ℝ) →
      (p : ℝ) < 1 → FluxFlipWeightBoundD d p)
    (h3 : ∀ (d : ℕ) [NeZero d], 3 ≤ d → ∀ p : unitInterval, criticalProbability d < (p : ℝ) →
      (p : ℝ) < 1 → FluxFlipSumPartitionD d p) :
    FluxVarianceBoundThree := by
  intro d _ hd3 p hpc hp1 G hG hGv hGae
  obtain ⟨s, C, hs, hC, hV⟩ := fluxFlipSumD_isOsBond hG hGv hd3 hW hpc hp1
    (h2 d hd3 p hpc hp1) (h3 d hd3 p hpc hp1) hGae
  obtain ⟨abar, -, habar⟩ := exists_fluxMeanD (p := p) (by omega : 2 ≤ d) hpc hp1
  refine ⟨s, C, hs, hC, fun k i r hr x => ?_⟩
  obtain ⟨hfin, hOs⟩ := hV k i r hr x
  have hr0 : 0 < r := by linarith
  have hXm := measurable_fluxObsD hG hGv k i r x
  have hres := ae_resampleVar_le_tsum_bondFlipDiff p hXm
    (integral_fluxObsD hG hGv hGae habar k i r x).1
  refine ⟨?_, ?_⟩
  · filter_upwards [hres, hfin] with ω hl hu
    exact hl.trans_lt hu
  · refine isOsBond_of_ae_le hs (by positivity) (measurable_resampleVar p hXm).ennreal_toReal ?_
      hOs
    filter_upwards [hres, hfin] with ω hl hu
    exact ENNReal.toReal_mono hu.ne hl

/-- **The variance bound (3.4) of Gu's proof of Proposition 1.1 in dimension `d ≥ 3`**
(`FluxVarianceBoundThree`), from the bound of each flip difference (part 2,
`FluxFlipWeightBoundD`) and the probabilistic part of Step 2 of the proof of Lemma 3.3 of Dario in
dimension `d ≥ 3` (`DarioStepTwoWeightThree`); the flip sum through a partition into good cubes
(part 3) is `fluxFlipSumPartitionD_holds`. The hypothesis on part 2 is required only for `d ≥ 3`
and supercritical `p < 1`; it holds by `fluxFlipWeightBoundD_holds`, which gives
`fluxVarianceBoundThree_of_stepTwoWeight`. -/
theorem fluxVarianceBoundThree_of_weightBound (hW : DarioStepTwoWeightThree)
    (h2 : ∀ (d : ℕ) [NeZero d], 3 ≤ d → ∀ p : unitInterval, criticalProbability d < (p : ℝ) →
      (p : ℝ) < 1 → FluxFlipWeightBoundD d p) :
    FluxVarianceBoundThree :=
  fluxVarianceBoundThree_of_weight hW h2 fun d _ _ p _ _ => fluxFlipSumPartitionD_holds (d := d) p

end Rigidity.Green.GeneralFlux
