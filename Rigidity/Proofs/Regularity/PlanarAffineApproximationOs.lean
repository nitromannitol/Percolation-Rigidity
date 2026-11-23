import Rigidity.Proofs.Regularity.PlanarFlatnessOs
import Rigidity.Proofs.Regularity.PlanarAffineApproximationHolds

/-!
# The approximation of affine functions and (1.18) with a minimal scale of class `O_s`

* `affineApproximation_of_scales`: for one configuration, at a scale `3^{j+1}` above the minimal
  scales of Proposition 2.4 of Armstrong and Dario (arXiv:1609.09431v2) and of the density of the
  cluster, and with the flatness (5.33) of the maximizers of `ν(□_{j+3}, e_i)`, the affine function
  `q · x` is approximated on `B_{3^{j+1}}` by a harmonic function with the error
  `K |q|₁ (3^{j+1})^{1-δ}` (the argument of `planarAffineApproximationAeTwo_of_nuFlatness`);
* `planarAffineApproximationTwo_of_subaddOs`: `PlanarAffineApproximationTwo`, with a minimal scale of
  class `O_s`, from Proposition 5.2 for `ν` in the form `O_s` (`PlanarNuSubaddOsTwo`) through
  (5.33) with an `O_s` scale (`exists_planarNuFlatness_os`) and the minimal scales;
* `planarCorrectorSublinearL2Two_of_subaddOs`: (1.18) in the form `O_s`
  (`PlanarCorrectorSublinearL2Two`), by Step 3 of Proposition 3.1 of Armstrong, Kuusi and Mourrat
  (arXiv:1602.00512v1), with the order-zero regularity.
-/

namespace Rigidity.Proofs.Regularity

open Finset Filter MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.Percolation
open Rigidity.External Rigidity.Proofs.S2 Rigidity.Proofs.Cluster
open scoped Classical ENNReal

/-- **The approximation at one scale above the minimal scales.** -/
theorem affineApproximation_of_scales {ω : Configuration 2} (hP : PlanarPartitionEvent ω)
    (h : HasUniqueInfiniteOpenComponent ω) {j : ℕ} (hj3 : 3 ≤ j) {μ δ κ ℓ : ℝ} (hμ0 : 0 < μ)
    (hμ1 : μ ≤ 1) (hμδ : Real.sqrt μ ≤ (3 : ℝ) ^ (-δ)) (hδ2 : δ ≤ 1 / 2) (hκ : 0 < κ)
    (hsize : ∀ x ∈ Rigidity.Proofs.Cluster.cube (j + 3) (0 : Vertex 2),
      (3 : ℝ) ^ (planarPartCube ω x).scale ≤ ((3 : ℝ) ^ (j + 3)) ^ (1 / 4 : ℝ))
    (hreach : ∀ x ∈ Rigidity.Proofs.Cluster.cube (j + 3) (0 : Vertex 2),
      planarReach ω x ≤ ENNReal.ofReal (((3 : ℝ) ^ (j + 3)) ^ (1 / 4 : ℝ)))
    (hcube : ClusterCubeDensity (uniqueInfiniteComponent h) 0 54 ℓ κ) (hℓ : ℓ ≤ 3 ^ (j - 1))
    (hfl : ∀ i : Fin 2, planarFlatnessError ⟨j + 3, 0⟩
      (coarsen ω ⟨j + 3, 0⟩ (planarNuSolution ω ⟨j + 3, 0⟩ (Pi.single i 1))) (Pi.single i 1) ≤
        2 * 9 ^ (j + 2) * μ ^ (j + 2))
    (q : Fin 2 → ℝ) :
    ∃ v : uniqueInfiniteComponent h → ℝ,
      HarmonicOnBall (uniqueInfiniteComponent h) v (3 ^ (j + 1)) ∧
      componentBallL2 (uniqueInfiniteComponent h) 0 (3 ^ (j + 1))
          (fun x => v x - componentSlope (uniqueInfiniteComponent h) q x) ≤
        Real.sqrt ((8 * 9 ^ 5 + 18 * 9 ^ 5 * planarCoarseConst ^ 2) / κ) * (|q 0| + |q 1|) *
          ((3 : ℝ) ^ (j + 1)) ^ (1 - δ) := by
  have hinf := uniqueInfiniteComponent_infinite h
  have hscale : ∀ z ∈ triadicCubeFinset 2 (j + 3) 0, (planarPartCube ω z).scale * 4 ≤ j + 3 :=
    fun z hz => four_mul_le_of_three_pow_le_rpow_quarter (hsize z (mem_cube_of_mem_square hz))
  have hres : PlanarResolved ω ⟨j + 3, 0⟩ := by
    intro z hz
    have hz' : z ∈ triadicCubeFinset 2 (j + 3) 0 :=
      mem_square_iff_int.2 (mem_triadicCube_zero_iff.1 hz)
    have := hscale z hz'
    show (planarPartCube ω z).scale ≤ j + 3
    omega
  have hsc : ∀ x ∈ triadicCubeFinset 2 (j + 3) 0, (planarPartCube ω x).scale ≤ j := by
    intro x hx; have := hscale x hx; omega
  have hD : ∀ z ∈ clusterVertices ω ⟨j + 3, 0⟩,
      (3 : ℝ) ^ (planarCoarseData hP ⟨j + 3, 0⟩ hres).reachScale z ≤
        ((3 : ℝ) ^ (j + 3)) ^ (1 / 4 : ℝ) := by
    intro z hz
    refine three_pow_le_of_planarReach_le (by positivity)
      ((three_pow_reachScale_le_planarReach hP hres z).trans (hreach z ?_))
    exact mem_cube_of_mem_square (mem_square_of_mem_clusterVertices hz)
  have hcard := card_componentEuclideanBall_ge (uniqueInfiniteComponent h) hcube
    (m := j - 1) hℓ (x := (0 : Vertex 2)) fun i => by
      simp only [Pi.zero_apply, abs_zero]; positivity
  have e9 : (9 : ℝ) * 3 ^ (j - 1) = 3 ^ (j + 1) := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, ← pow_add]; congr 1; omega
  rw [e9] at hcard
  obtain ⟨v, hvH, hvL2⟩ := affineApproximation_at_scale hP (uniqueInfiniteComponent h) hinf hres hsc
    hD hfl (κ' := κ * 9 ^ (j - 1)) (by positivity) hcard q
  refine ⟨v, hvH, hvL2.trans ?_⟩
  have hvol : (⟨j + 3, 0⟩ : TriadicCube 2).volume = 9 ^ (j + 3) := rfl
  rw [hvol]
  have hQQ : q 0 ^ 2 + q 1 ^ 2 ≤ (|q 0| + |q 1|) ^ 2 := by
    have h0 := abs_nonneg (q 0)
    have h1 := abs_nonneg (q 1)
    nlinarith [sq_abs (q 0), sq_abs (q 1)]
  have hr := radicand_le (j := j) (by omega) (Q := q 0 ^ 2 + q 1 ^ 2) (Q₁ := |q 0| + |q 1|)
    (KL := planarCoarseConst) hQQ hμ0 hμ1 hμδ hδ2 hκ
  have hnonneg : 0 ≤ Real.sqrt ((8 * 9 ^ 5 + 18 * 9 ^ 5 * planarCoarseConst ^ 2) / κ) *
      (|q 0| + |q 1|) * ((3 : ℝ) ^ (j + 1)) ^ (1 - δ) := by positivity
  calc Real.sqrt (2 * (2 * 9 ^ (j + 3) * ((q 0 ^ 2 + q 1 ^ 2) * (2 * 9 ^ (j + 2) * μ ^ (j + 2))) +
        planarCoarseConst ^ 2 * (((3 : ℝ) ^ (j + 3)) ^ (1 / 4 : ℝ)) ^ 4 *
          (9 * (q 0 ^ 2 + q 1 ^ 2) * 9 ^ (j + 3))) / (κ * 9 ^ (j - 1)))
      ≤ Real.sqrt ((Real.sqrt ((8 * 9 ^ 5 + 18 * 9 ^ 5 * planarCoarseConst ^ 2) / κ) *
          (|q 0| + |q 1|) * ((3 : ℝ) ^ (j + 1)) ^ (1 - δ)) ^ 2) := Real.sqrt_le_sqrt hr
    _ = _ := Real.sqrt_sq hnonneg

/-- From `81 max(Y, 1) ≤ 3^m`: `m ≥ 4` and `Y ≤ 3^{m-4}`. -/
theorem le_three_pow_sub_four {Y : ℝ} {m : ℕ} (h : 81 * max Y 1 ≤ (3 : ℝ) ^ m) :
    4 ≤ m ∧ Y ≤ 3 ^ (m - 4) := by
  have h81 : (3 : ℝ) ^ 4 ≤ 3 ^ m := by
    have : (81 : ℝ) ≤ 81 * max Y 1 := le_mul_of_one_le_right (by norm_num) (le_max_right _ _)
    norm_num; linarith
  have hm : 4 ≤ m := (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).1 h81
  refine ⟨hm, ?_⟩
  have e : (3 : ℝ) ^ m = 81 * 3 ^ (m - 4) := by
    rw [show (81 : ℝ) = 3 ^ 4 by norm_num, ← pow_add]; congr 1; omega
  rw [e] at h
  have := le_of_mul_le_mul_left h (by norm_num)
  exact (le_max_left _ _).trans this

/-- **The approximation of affine functions with a minimal scale of class `O_s`**, from
Proposition 5.2 for `ν` in the form `O_s` and the minimal scales of Proposition 2.4. -/
theorem planarAffineApproximationTwo_of_subaddOs
    (hsub : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      PlanarNuSubaddOsTwo p)
    (hM5 : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      PlanarMinimalScalesTwo p) :
    PlanarAffineApproximationTwo := by
  intro p hpc hp1
  obtain ⟨μ, hμ0, hμ1, sY, θY, hsY, hθY, Y, hYm, hY0, hYos, hYae⟩ :=
    exists_planarNuFlatness_os hpc (hsub p hpc hp1)
  have hlog : 0 < Real.log μ⁻¹ := Real.log_pos (one_lt_inv_iff₀.2 ⟨hμ0, hμ1⟩)
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  set δ : ℝ := min (Real.log μ⁻¹ / (2 * Real.log 3)) (1 / 2) with hδdef
  have hδ0 : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδ2 : δ ≤ 1 / 2 := min_le_right _ _
  have hμδ : Real.sqrt μ ≤ (3 : ℝ) ^ (-δ) :=
    (sqrt_le_three_rpow_neg hμ0).trans (Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (neg_le_neg (min_le_left _ _)))
  obtain ⟨A₀, sc, -, hmoms⟩ := hM5 p hpc hp1
  obtain ⟨K₆, r₆, θ₆, -, hr₆, hθ₆, M₆, hM₆m, hM₆0, hM₆os, hM₆ae⟩ :=
    hmoms 1 one_pos (1 / 4) (by norm_num)
  have hθp : 0 < theta 2 p := Rigidity.Percolation.theta_pos_of_criticalProbability_lt 2 p hpc
  obtain ⟨s₄, θ₄, hs₄, hθ₄, hcube⟩ := exists_clusterCubeDensity_of_concentration (d := 2) le_rfl p
    (cluster_density_concentration 2 le_rfl p hpc hp1) 54
  obtain ⟨M₄, hM₄m, hM₄0, hM₄os, hM₄ae⟩ := hcube 0
  -- the minimal scale
  obtain ⟨θa, hθa, ha⟩ := exists_isOsBond_max hr₆ hs₄ hθ₆ hθ₄ hM₆m hM₄m hM₆os hM₄os
  obtain ⟨θb, hθb, hb⟩ := exists_isOsBond_max hsY (lt_min hr₆ hs₄) hθY hθa hYm (hM₆m.max hM₄m)
    hYos ha
  have h1os := isOsBond_const (d := 2) (p := p) one_pos (lt_min hsY (lt_min hr₆ hs₄))
  obtain ⟨θc, hθc, hc⟩ := exists_isOsBond_max (lt_min hsY (lt_min hr₆ hs₄))
    (lt_min hsY (lt_min hr₆ hs₄)) hθb (by positivity) (hYm.max (hM₆m.max hM₄m))
    measurable_const hb h1os
  have hXos := IsOsBond.const_mul (by norm_num : (0 : ℝ) < 81) hc
  refine ⟨_, δ, _, Real.sqrt ((8 * 9 ^ 5 + 18 * 9 ^ 5 * planarCoarseConst ^ 2) / (theta 2 p / 2)),
    lt_min (lt_min hsY (lt_min hr₆ hs₄)) (lt_min hsY (lt_min hr₆ hs₄)), hδ0, by positivity,
    Real.sqrt_nonneg _, fun ω => 81 * max (max (Y ω) (max (M₆ ω) (M₄ ω))) 1,
    ((hYm.max (hM₆m.max hM₄m)).max measurable_const).const_mul 81,
    fun ω => by positivity, hXos, ?_⟩
  filter_upwards [hYae, hM₆ae, hM₄ae, ae_planarPartitionEvent hpc] with ω hY h6 h4 hP
  intro h q m hm
  obtain ⟨hm4, hle⟩ := le_three_pow_sub_four hm
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  have hj3 : 3 ≤ j := by omega
  have hsub' : (3 : ℝ) ^ (j + 1 - 4) ≤ 3 ^ (j - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hYj : Y ω < 3 ^ (j + 2) :=
    ((le_max_left _ _).trans hle).trans_lt (pow_lt_pow_right₀ (by norm_num) (by omega))
  have hM6 : M₆ ω ≤ 3 ^ (j + 3) :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans hle).trans
      (pow_le_pow_right₀ (by norm_num) (by omega))
  have hM4 : M₄ ω ≤ 3 ^ (j - 1) :=
    ((((le_max_right _ _).trans (le_max_right _ _)).trans hle).trans hsub')
  obtain ⟨-, -, -, hsize, -, hreach⟩ := h6 (j + 3) hM6
  exact affineApproximation_of_scales hP h hj3 hμ0 hμ1.le hμδ hδ2 (by positivity) hsize hreach
    (h4 h) hM4 (fun i => hY (j + 2) hYj i) q

/-- **(1.18) of Armstrong and Dario in dimension two with a minimal scale of class `O_s`**, from
Proposition 5.2 for `ν` in the form `O_s`, the minimal scales of Proposition 2.4 and the order-zero
regularity. -/
theorem planarCorrectorSublinearL2Two_of_subaddOs
    (hsub : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      PlanarNuSubaddOsTwo p)
    (hM5 : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      PlanarMinimalScalesTwo p)
    (hR3 : ArmstrongDarioOrderZeroTwo) : PlanarCorrectorSublinearL2Two :=
  planarCorrectorSublinearL2Two_of_affineApproximation
    (planarAffineApproximationTwo_of_subaddOs hsub hM5) hR3

end Rigidity.Proofs.Regularity
