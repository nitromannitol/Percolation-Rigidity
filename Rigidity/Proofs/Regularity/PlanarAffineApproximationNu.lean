import Rigidity.Proofs.Regularity.PlanarNuEnergy
import Rigidity.Proofs.Regularity.PlanarGradNormBound

/-!
# The approximation of affine functions on growing balls of the planar cluster

`affineApproximation_at_scale` builds, at the scale `3^{j+1}`, a function harmonic on
`𝒞_∞ ∩ B_{3^{j+1}}` close to `q · x`: the combination `q₀ v(·, □, e₀) + q₁ v(·, □, e₁)` of the
maximizers of `ν` on `□ = □_{j+3}`, minus a constant. Its distance to `q · x` is bounded by the
flatness errors (Lemma 5.8 of Armstrong and Dario, arXiv:1609.09431v2), the coarsening error
(Lemma 3.2 with bounded reach scales) and the energy bound of the maximizers.

`planarAffineApproximationAeTwo_of_nuFlatness` proves `PlanarAffineApproximationAeTwo`, the input of
Step 3 of Proposition 3.1 of Armstrong, Kuusi and Mourrat (arXiv:1602.00512v1) for `k = 1`, from
(5.33) in expectation, the decay of `τ` and the minimal scales of Proposition 2.4.
-/

namespace Rigidity.Proofs.Regularity

open Finset Filter MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.Percolation
open Rigidity.External Rigidity.Proofs.S2 Rigidity.Proofs.Cluster
open Rigidity.Proofs.Multiscale (affineFun finsetMean)
open scoped Classical ENNReal

variable {ω : Configuration 2}

/-- **The approximation at one scale.** -/
theorem affineApproximation_at_scale (hP : PlanarPartitionEvent ω) (C : OpenComponent ω)
    (hinf : C.supp.Infinite) {j : ℕ} (hres : PlanarResolved ω ⟨j + 3, 0⟩)
    (hsc : ∀ x ∈ triadicCubeFinset 2 (j + 3) 0, (planarPartCube ω x).scale ≤ j) {D Fl κ' : ℝ}
    (hD : ∀ z ∈ clusterVertices ω ⟨j + 3, 0⟩,
      (3 : ℝ) ^ (planarCoarseData hP ⟨j + 3, 0⟩ hres).reachScale z ≤ D)
    (hfl : ∀ i : Fin 2, planarFlatnessError ⟨j + 3, 0⟩
      (coarsen ω ⟨j + 3, 0⟩ (planarNuSolution ω ⟨j + 3, 0⟩ (Pi.single i 1))) (Pi.single i 1) ≤ Fl)
    (hκ' : 0 < κ') (hcard : κ' ≤ (componentEuclideanBall C 0 ((3 : ℝ) ^ (j + 1))).card)
    (q : Fin 2 → ℝ) :
    ∃ v : C → ℝ, HarmonicOnBall C v (3 ^ (j + 1)) ∧
      componentBallL2 C 0 (3 ^ (j + 1)) (fun x => v x - componentSlope C q x) ≤
        Real.sqrt (2 * (2 * (⟨j + 3, 0⟩ : TriadicCube 2).volume * ((q 0 ^ 2 + q 1 ^ 2) * Fl) +
          planarCoarseConst ^ 2 * D ^ 4 * (9 * (q 0 ^ 2 + q 1 ^ 2) *
            (⟨j + 3, 0⟩ : TriadicCube 2).volume)) / κ') := by
  set V : TriadicCube 2 := ⟨j + 3, 0⟩ with hVdef
  set v₀ := planarNuSolution ω V (Pi.single 0 1) with hv₀
  set v₁ := planarNuSolution ω V (Pi.single 1 1) with hv₁
  set v := q 0 • v₀ + q 1 • v₁ with hvdef
  set c := q 0 * finsetMean V.toIntegerCube.vertices
      (fun y => coarsen ω V v₀ y - affineFun (Pi.single 0 1) y) +
    q 1 * finsetMean V.toIntegerCube.vertices
      (fun y => coarsen ω V v₁ y - affineFun (Pi.single 1 1) y) with hc
  have hvH : v ∈ clusterHarmonic ω V :=
    Submodule.add_mem _ (Submodule.smul_mem _ _ (planarNuSolution_mem_clusterHarmonic hP hres _))
      (Submodule.smul_mem _ _ (planarNuSolution_mem_clusterHarmonic hP hres _))
  -- the inclusions
  have h3 : (0 : ℝ) < 3 ^ j := by positivity
  have hin : ∀ x : C, x ∈ componentEuclideanBall C 0 ((3 : ℝ) ^ (j + 1)) →
      x.val ∈ clusterVertices ω V ∧ V.IsInterior x.val := by
    intro x hx
    rw [mem_componentEuclideanBall] at hx
    have hcoord : ∀ k, |((x.val k : ℤ) : ℝ)| < 3 * 3 ^ j := by
      intro k
      have h1 := abs_sub_le_dist_latticeEuclideanEmbedding x.val (0 : Vertex 2) k
      have e : (((0 : Vertex 2) k : ℤ) : ℝ) = 0 := by simp
      rw [e, sub_zero] at h1
      have : (3 : ℝ) ^ (j + 1) = 3 * 3 ^ j := by ring
      linarith
    have hcoordZ : ∀ k, |x.val k| < 3 * 3 ^ j := by
      intro k
      have := hcoord k
      have h' : ((|x.val k| : ℤ) : ℝ) < ((3 * 3 ^ j : ℤ) : ℝ) := by push_cast; exact this
      exact_mod_cast h'
    refine ⟨mem_clusterVertices_inner hP C hinf hsc x.2 fun k => ?_, fun y hy => ?_⟩
    · have := hcoordZ k
      have h0 : (0 : ℤ) < 3 ^ j := by positivity
      linarith
    · rw [mem_triadicCube_zero_iff]
      intro k
      have h1 := hcoordZ k
      have h2 := hy k
      have h0 : (1 : ℤ) ≤ 3 ^ j := one_le_pow₀ (by norm_num)
      have e : (3 : ℤ) ^ (j + 3) = 27 * 3 ^ j := by ring
      have a := abs_sub_abs_le_abs_sub (y k) (x.val k)
      rw [abs_sub_comm (y k) (x.val k)] at a
      rw [e]
      linarith
  refine ⟨fun x => clusterExtend ω V v x.val - c,
    harmonicOnBall_of_clusterHarmonic hP hres C hvH c hin, ?_⟩
  -- the energy and the coarsening error
  have hE : clusterForm ω V v v ≤ 9 * (q 0 ^ 2 + q 1 ^ 2) * V.volume := by
    have h1 := clusterForm_combo_le (ω := ω) v₀ v₁ (q 0) (q 1)
    have e0 : (|(Pi.single 0 1 : Fin 2 → ℝ) 0| + |(Pi.single 0 1 : Fin 2 → ℝ) 1|) = 1 := by
      simp
    have e1 : (|(Pi.single 1 1 : Fin 2 → ℝ) 0| + |(Pi.single 1 1 : Fin 2 → ℝ) 1|) = 1 := by
      simp
    have h2' : clusterForm ω V v₀ v₀ ≤ 9 / 2 * V.volume := by
      have := clusterForm_planarNuSolution_le hP hres (Pi.single 0 1)
      rw [e0] at this; simpa using this
    have h3' : clusterForm ω V v₁ v₁ ≤ 9 / 2 * V.volume := by
      have := clusterForm_planarNuSolution_le hP hres (Pi.single 1 1)
      rw [e1] at this; simpa using this
    have hq0 : 0 ≤ q 0 ^ 2 := sq_nonneg _
    have hq1 : 0 ≤ q 1 ^ 2 := sq_nonneg _
    nlinarith
  have hG := sum_sq_extend_sub_coarsen_le hP hres v hD
  have hG' : ∑ x ∈ clusterVertices ω V, (clusterExtend ω V v x - coarsen ω V v x) ^ 2 ≤
      planarCoarseConst ^ 2 * D ^ 4 * (9 * (q 0 ^ 2 + q 1 ^ 2) * V.volume) :=
    hG.trans (mul_le_mul_of_nonneg_left hE (by positivity))
  -- the flatness
  have hF := sum_sq_coarsen_combo_le (ω := ω) v₀ v₁ q
  have hF' : ∑ x ∈ clusterVertices ω V, (coarsen ω V v x - affineFun q x - c) ^ 2 ≤
      2 * V.volume * ((q 0 ^ 2 + q 1 ^ 2) * Fl) := by
    have hsub : clusterVertices ω V ⊆ V.toIntegerCube.vertices := Finset.filter_subset _ _
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _).trans
      (hF.trans ?_)
    have hvol := V.volume_pos
    have h0 := hfl 0
    have h1 := hfl 1
    have hq0 : 0 ≤ q 0 ^ 2 := sq_nonneg _
    have hq1 : 0 ≤ q 1 ^ 2 := sq_nonneg _
    have : q 0 ^ 2 * planarFlatnessError V (coarsen ω V v₀) (Pi.single 0 1) +
        q 1 ^ 2 * planarFlatnessError V (coarsen ω V v₁) (Pi.single 1 1) ≤
        (q 0 ^ 2 + q 1 ^ 2) * Fl := by nlinarith
    nlinarith
  exact componentBallL2_le_of_sums C v q c hκ' (fun x hx => (hin x hx).1) hcard hF' hG'

theorem three_pow_le_of_planarReach_le {n : ℕ} {x : ℝ} (hx : 0 ≤ x)
    (h : (3 : ℝ≥0∞) ^ n ≤ ENNReal.ofReal x) : (3 : ℝ) ^ n ≤ x := by
  have e : (3 : ℝ≥0∞) ^ n = ENNReal.ofReal ((3 : ℝ) ^ n) := by
    rw [ENNReal.ofReal_pow (by norm_num)]; norm_num
  rw [e, ENNReal.ofReal_le_ofReal_iff hx] at h
  exact h

/-- The final bound at one scale. -/
theorem radicand_le {j : ℕ} (hj : 1 ≤ j) {Q Q₁ μ δ κ KL : ℝ} (hQQ : Q ≤ Q₁ ^ 2)
    (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) (hμδ : Real.sqrt μ ≤ (3 : ℝ) ^ (-δ))
    (hδ2 : δ ≤ 1 / 2) (hκ : 0 < κ) :
    2 * (2 * (9 : ℝ) ^ (j + 3) * (Q * (2 * 9 ^ (j + 2) * μ ^ (j + 2))) +
        KL ^ 2 * (((3 : ℝ) ^ (j + 3)) ^ (1 / 4 : ℝ)) ^ 4 * (9 * Q * 9 ^ (j + 3))) /
        (κ * 9 ^ (j - 1)) ≤
      (Real.sqrt ((8 * 9 ^ 5 + 18 * 9 ^ 5 * KL ^ 2) / κ) * Q₁ *
        ((3 : ℝ) ^ (j + 1)) ^ (1 - δ)) ^ 2 := by
  set M : ℝ := (3 : ℝ) ^ (j + 1) with hM
  set W : ℝ := (9 : ℝ) ^ (j - 1) with hW
  have hW0 : 0 < W := by positivity
  have hM1 : 1 ≤ M := one_le_pow₀ (by norm_num)
  have hD4 : (((3 : ℝ) ^ (j + 3)) ^ (1 / 4 : ℝ)) ^ 4 = 9 * M := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
    rw [hM]; ring
  have e1 : (9 : ℝ) ^ (j + 3) = 6561 * W := by
    rw [hW, show j + 3 = 4 + (j - 1) by omega, pow_add]; norm_num
  have e2 : (9 : ℝ) ^ (j + 2) = 729 * W := by
    rw [hW, show j + 2 = 3 + (j - 1) by omega, pow_add]; norm_num
  have e3 : M ^ 2 = 81 * W := by
    rw [hM, hW, ← pow_mul, show (j + 1) * 2 = 4 + 2 * (j - 1) by omega, pow_add, pow_mul]; norm_num
  rw [hD4, e1, e2]
  -- the radicand
  have hrad : 2 * (2 * (6561 * W) * (Q * (2 * (729 * W) * μ ^ (j + 2))) +
        KL ^ 2 * (9 * M) * (9 * Q * (6561 * W))) / (κ * W) =
      (8 * 9 ^ 5 * (Q * (M ^ 2 * μ ^ (j + 2))) + 18 * 9 ^ 5 * KL ^ 2 * (Q * M)) / κ := by
    rw [e3]; field_simp; ring
  rw [hrad]
  -- the powers of `M`
  set ε : ℝ := (3 : ℝ) ^ (-δ) with hε
  have hε0 : 0 < ε := by positivity
  set z : ℝ := M ^ (1 - δ) with hz
  have hzM : z = M * ε ^ (j + 1) := by rw [hz, hM, three_pow_rpow_eq]
  have hz0 : 0 ≤ z := by positivity
  have h1 : M ^ 2 * μ ^ (j + 2) ≤ z ^ 2 := by
    have hμ2 : μ ^ (j + 2) ≤ μ ^ (j + 1) := pow_le_pow_of_le_one hμ0.le hμ1 (by omega)
    have hμs : μ ^ (j + 1) = (Real.sqrt μ ^ 2) ^ (j + 1) := by rw [Real.sq_sqrt hμ0.le]
    have hμε : μ ^ (j + 1) ≤ (ε ^ 2) ^ (j + 1) := by
      rw [hμs]
      exact pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ (Real.sqrt_nonneg _) hμδ 2) _
    rw [hzM]
    calc M ^ 2 * μ ^ (j + 2) ≤ M ^ 2 * (ε ^ 2) ^ (j + 1) :=
          mul_le_mul_of_nonneg_left (hμ2.trans hμε) (by positivity)
      _ = (M * ε ^ (j + 1)) ^ 2 := by ring
  have h2 : M ≤ z ^ 2 := by
    have hhalf : M ^ (1 / 2 : ℝ) ≤ z := by
      rw [hz]; exact Real.rpow_le_rpow_of_exponent_le hM1 (by linarith)
    have := pow_le_pow_left₀ (by positivity) hhalf 2
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)] at this
    norm_num at this
    exact this
  have hrhs : (Real.sqrt ((8 * 9 ^ 5 + 18 * 9 ^ 5 * KL ^ 2) / κ) * Q₁ * z) ^ 2 =
      (8 * 9 ^ 5 + 18 * 9 ^ 5 * KL ^ 2) / κ * (Q₁ ^ 2 * z ^ 2) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]; ring
  rw [hrhs, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hκ]
  have hQ1 : Q * (M ^ 2 * μ ^ (j + 2)) ≤ Q₁ ^ 2 * z ^ 2 :=
    mul_le_mul hQQ h1 (by positivity) (sq_nonneg _)
  have hQ2 : Q * M ≤ Q₁ ^ 2 * z ^ 2 := mul_le_mul hQQ h2 (by linarith) (sq_nonneg _)
  have hKL : 0 ≤ KL ^ 2 := sq_nonneg _
  nlinarith

theorem four_mul_le_of_three_pow_le_rpow_quarter {a m : ℕ}
    (h : (3 : ℝ) ^ a ≤ ((3 : ℝ) ^ m) ^ (1 / 4 : ℝ)) : a * 4 ≤ m := by
  have hsq := pow_le_pow_left₀ (by positivity) h 4
  rw [← Real.rpow_natCast (((3 : ℝ) ^ m) ^ (1 / 4 : ℝ)), ← Real.rpow_mul (by positivity)] at hsq
  norm_num at hsq
  rw [← pow_mul] at hsq
  exact (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).1 hsq

theorem sqrt_le_three_rpow_neg {μ : ℝ} (hμ0 : 0 < μ) :
    Real.sqrt μ ≤ (3 : ℝ) ^ (-(Real.log μ⁻¹ / (2 * Real.log 3))) := by
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hμ0, Real.rpow_def_of_pos (by norm_num),
    Real.log_inv]
  apply le_of_eq
  congr 1
  field_simp

/-- **The approximation of affine functions on growing balls of the planar cluster, almost surely
above a finite scale**, from (5.33) in expectation, the geometric decay of `τ` and the minimal
scales of Proposition 2.4. -/
theorem planarAffineApproximationAeTwo_of_nuFlatness
    (hflat : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      PlanarNuFlatnessMajorantTwo p)
    (htau : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      PlanarTauGeometricTwo p)
    (hM5 : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      PlanarMinimalScalesTwo p) :
    PlanarAffineApproximationAeTwo := by
  intro p hpc hp1
  obtain ⟨μ, hμ0, hμ1, hfl⟩ := ae_eventually_planarNuFlatness_le (hflat p hpc hp1)
    (htau p hpc hp1)
  have hlog : 0 < Real.log μ⁻¹ := Real.log_pos (one_lt_inv_iff₀.2 ⟨hμ0, hμ1⟩)
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  set δ : ℝ := min (Real.log μ⁻¹ / (2 * Real.log 3)) (1 / 2) with hδdef
  have hδ0 : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδ2 : δ ≤ 1 / 2 := min_le_right _ _
  have hμδ : Real.sqrt μ ≤ (3 : ℝ) ^ (-δ) :=
    (sqrt_le_three_rpow_neg hμ0).trans (Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (neg_le_neg (min_le_left _ _)))
  obtain ⟨A₀, sc, -, hmoms⟩ := hM5 p hpc hp1
  obtain ⟨K₆, r₆, θ₆, -, -, -, M₆, -, hM₆0, -, hM₆ae⟩ := hmoms 1 one_pos (1 / 4) (by norm_num)
  have hθp : 0 < theta 2 p := Rigidity.Percolation.theta_pos_of_criticalProbability_lt 2 p hpc
  obtain ⟨s₄, θ₄, -, -, hcube⟩ := exists_clusterCubeDensity_of_concentration (d := 2) le_rfl p
    (cluster_density_concentration 2 le_rfl p hpc hp1) 54
  obtain ⟨M₄, -, hM₄0, -, hM₄ae⟩ := hcube 0
  set κ : ℝ := theta 2 p / 2 with hκdef
  have hκ : 0 < κ := by positivity
  set KL : ℝ := planarCoarseConst with hKL
  set K : ℝ := Real.sqrt ((8 * 9 ^ 5 + 18 * 9 ^ 5 * KL ^ 2) / κ) with hK
  refine ⟨δ, K, hδ0, Real.sqrt_nonneg _, ?_⟩
  filter_upwards [hfl (Pi.single 0 1), hfl (Pi.single 1 1), hM₆ae, hM₄ae,
    ae_planarPartitionEvent hpc] with ω h0 h1 h6 h4 hP
  intro h q
  have hinf := uniqueInfiniteComponent_infinite h
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 h0
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 h1
  obtain ⟨ma, hma⟩ := eventually_le_three_pow (max (M₆ ω) (M₄ ω))
  refine ⟨max (max N₀ N₁) ma + 4, fun m hm => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  have hj3 : 3 ≤ j := by omega
  have hM6 : M₆ ω ≤ 3 ^ (j + 3) := (le_max_left _ _).trans (hma (j + 3) (by omega))
  have hM4 : M₄ ω ≤ 3 ^ (j - 1) := (le_max_right _ _).trans (hma (j - 1) (by omega))
  obtain ⟨-, -, -, hsize, -, hreach⟩ := h6 (j + 3) hM6
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
  have hflat' : ∀ i : Fin 2, planarFlatnessError ⟨j + 3, 0⟩
      (coarsen ω ⟨j + 3, 0⟩ (planarNuSolution ω ⟨j + 3, 0⟩ (Pi.single i 1))) (Pi.single i 1) ≤
        2 * 9 ^ (j + 2) * μ ^ (j + 2) := by
    intro i
    fin_cases i
    · have := hN₀ (j + 2) (by omega)
      refine this.trans (le_of_eq ?_)
      norm_num
    · have := hN₁ (j + 2) (by omega)
      refine this.trans (le_of_eq ?_)
      norm_num
  have hcard := card_componentEuclideanBall_ge (uniqueInfiniteComponent h) (h4 h)
    (m := j - 1) hM4 (x := (0 : Vertex 2)) fun i => by
      simp only [Pi.zero_apply, abs_zero]; positivity
  have e9 : (9 : ℝ) * 3 ^ (j - 1) = 3 ^ (j + 1) := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, ← pow_add]; congr 1; omega
  rw [e9] at hcard
  obtain ⟨v, hvH, hvL2⟩ := affineApproximation_at_scale hP (uniqueInfiniteComponent h) hinf hres hsc
    hD hflat' (κ' := κ * 9 ^ (j - 1)) (by positivity) hcard q
  refine ⟨v, hvH, hvL2.trans ?_⟩
  have hvol : (⟨j + 3, 0⟩ : TriadicCube 2).volume = 9 ^ (j + 3) := rfl
  rw [hvol]
  have hQQ : q 0 ^ 2 + q 1 ^ 2 ≤ (|q 0| + |q 1|) ^ 2 := by
    have h0 := abs_nonneg (q 0)
    have h1 := abs_nonneg (q 1)
    nlinarith [sq_abs (q 0), sq_abs (q 1)]
  have hr := radicand_le (j := j) (by omega) (Q := q 0 ^ 2 + q 1 ^ 2) (Q₁ := |q 0| + |q 1|)
    (KL := KL) hQQ hμ0 hμ1.le hμδ hδ2 hκ
  have hnonneg : 0 ≤ K * (|q 0| + |q 1|) * ((3 : ℝ) ^ (j + 1)) ^ (1 - δ) := by positivity
  calc Real.sqrt (2 * (2 * 9 ^ (j + 3) * ((q 0 ^ 2 + q 1 ^ 2) * (2 * 9 ^ (j + 2) * μ ^ (j + 2))) +
        planarCoarseConst ^ 2 * (((3 : ℝ) ^ (j + 3)) ^ (1 / 4 : ℝ)) ^ 4 *
          (9 * (q 0 ^ 2 + q 1 ^ 2) * 9 ^ (j + 3))) / (κ * 9 ^ (j - 1)))
      ≤ Real.sqrt ((K * (|q 0| + |q 1|) * ((3 : ℝ) ^ (j + 1)) ^ (1 - δ)) ^ 2) :=
        Real.sqrt_le_sqrt hr
    _ = K * (|q 0| + |q 1|) * ((3 : ℝ) ^ (j + 1)) ^ (1 - δ) := Real.sqrt_sq hnonneg

/-- **Every slope has a corrected plane on the planar cluster** from (5.33) in expectation, the
decay of `τ`, the minimal scales of Proposition 2.4 and the order-zero regularity, by Step 3 of
Proposition 3.1 of Armstrong, Kuusi and Mourrat. -/
theorem planarCorrectedPlaneExistenceTwo_of_nuFlatness
    (hflat : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      PlanarNuFlatnessMajorantTwo p)
    (htau : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      PlanarTauGeometricTwo p)
    (hM5 : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      PlanarMinimalScalesTwo p)
    (hR3 : ArmstrongDarioOrderZeroTwo) : PlanarCorrectedPlaneExistenceTwo :=
  planarCorrectedPlaneExistenceTwo_of_affineApproximationAe
    (planarAffineApproximationAeTwo_of_nuFlatness hflat htau hM5) hR3 hM5

end Rigidity.Proofs.Regularity
