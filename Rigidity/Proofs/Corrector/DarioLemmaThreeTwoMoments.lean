import Rigidity.Proofs.Corrector.DarioLemmaThreeTwoStepOne
import Rigidity.Proofs.Corrector.RandomBallSums

/-!
# Dario, Lemma 3.2, Step 1: the moments of the discrepancy

Dario bounds the difference of the two coarsened correctors on the event that the partitions
differ by crude polynomial moment bounds (`O_s(C r^{2d})`), and the probability of that event by
(3.3). Here, at every vertex `z`:

* `measure_le_sizeSum_le`: the sum of the `N = (2·3^k + 1)²` partition sizes around `z` has the
  tail `P[t ≤ sizeSum] ≤ 2 e^{-t/(Nθ)}` (Jensen's inequality for the exponential and the uniform
  exponential moments of the sizes);
* `lintegral_sq_statDiscrepancy_le`: `E[|χ(z̄_stat(z)) - χ(z̄(z))|²] ≤ M_k`, with `M_k` polynomial in
  `θ_k = 4Nθ + 8·3^k`, from the crude bound of the discrepancy and the moments of sums over random
  balls;
* `lintegral_abs_statDiscrepancy_le`: **Step 1 at one vertex**,
  `E|χ(z̄_stat(z)) - χ(z̄(z))| ≤ e^{-c 3^k/2} (M_k + C)`, since the discrepancy vanishes outside
  the event of (3.3) for the cube of scale `k` containing `z`.
-/

namespace Rigidity.Corrector

open MeasureTheory Filter Set LatticeProb.Percolation Rigidity.Percolation Rigidity.External
open scoped Classical ENNReal

/-- The number of vertices of the square around a point used in `sizeSum`. -/
theorem card_boxAround (z : Vertex 2) (R : ℕ) :
    (boxAround z (R : ℤ)).card = (2 * R + 1) ^ 2 := by
  rw [boxAround, Fintype.card_piFinset]
  have h : ∀ i : Fin 2, (Finset.Icc (z i - (R : ℤ)) (z i + (R : ℤ))).card = 2 * R + 1 := by
    intro i
    rw [Int.card_Icc]
    omega
  simp only [h, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **The tail of the sum of the sizes**: `P[t ≤ sizeSum k z] ≤ 2 e^{-t/(Nθ)}`. -/
theorem measure_le_sizeSum_le {p : unitInterval} {θ : ℝ} (hθ : 0 < θ)
    (hexp : ∀ v : Vertex 2,
      Integrable (fun ω => Real.exp (TriadicCube.stoppingSize (planarGoodCubes ω) v / θ))
        (latticeBondLaw 2 p) ∧
      ∫ ω, Real.exp (TriadicCube.stoppingSize (planarGoodCubes ω) v / θ) ∂latticeBondLaw 2 p ≤ 2)
    (k : ℕ) (z : Vertex 2) (t : ℝ) :
    latticeBondLaw 2 p {ω | t ≤ sizeSum k z ω} ≤
      ENNReal.ofReal (2 * Real.exp (-(t / (((2 * 3 ^ k + 1) ^ 2 : ℕ) * θ)))) := by
  set F := boxAround z ((3 : ℤ) ^ k) with hF
  set N : ℕ := (2 * 3 ^ k + 1) ^ 2 with hN
  have hcard : F.card = N := by
    have e : ((3 ^ k : ℕ) : ℤ) = (3 : ℤ) ^ k := by push_cast; ring
    rw [hF, hN, ← card_boxAround z (3 ^ k), e]
  have hN0 : (0 : ℝ) < N := by positivity
  set f : Configuration 2 → ℝ≥0∞ := fun ω => ENNReal.ofReal (Real.exp (sizeSum k z ω / (N * θ)))
  -- Jensen's inequality for the exponential
  have hjensen : ∀ ω, Real.exp (sizeSum k z ω / (N * θ)) ≤
      ∑ v ∈ F, (1 / (N : ℝ)) * Real.exp (TriadicCube.stoppingSize (planarGoodCubes ω) v / θ) := by
    intro ω
    have h := (convexOn_exp).map_sum_le (t := F) (w := fun _ => 1 / (N : ℝ))
      (p := fun v => TriadicCube.stoppingSize (planarGoodCubes ω) v / θ)
      (fun v _ => by positivity)
      (by rw [Finset.sum_const, hcard, nsmul_eq_mul, mul_one_div_cancel hN0.ne'])
      (fun v _ => Set.mem_univ _)
    simp only [smul_eq_mul] at h
    refine (congrArg Real.exp ?_).trans_le h
    rw [sizeSum, ← hF, Finset.sum_div]
    refine Finset.sum_congr rfl fun v _ => ?_
    field_simp
  have hf : ∫⁻ ω, f ω ∂latticeBondLaw 2 p ≤ 2 := by
    calc ∫⁻ ω, f ω ∂latticeBondLaw 2 p
        ≤ ∫⁻ ω, ∑ v ∈ F, ENNReal.ofReal (1 / (N : ℝ)) *
            ENNReal.ofReal (Real.exp (TriadicCube.stoppingSize (planarGoodCubes ω) v / θ))
            ∂latticeBondLaw 2 p := by
          refine lintegral_mono fun ω => ?_
          calc f ω ≤ ENNReal.ofReal (∑ v ∈ F, (1 / (N : ℝ)) *
                Real.exp (TriadicCube.stoppingSize (planarGoodCubes ω) v / θ)) :=
                ENNReal.ofReal_le_ofReal (hjensen ω)
            _ = ∑ v ∈ F, ENNReal.ofReal ((1 / (N : ℝ)) *
                Real.exp (TriadicCube.stoppingSize (planarGoodCubes ω) v / θ)) :=
                ENNReal.ofReal_sum_of_nonneg fun v _ => by positivity
            _ = _ := Finset.sum_congr rfl fun v _ => ENNReal.ofReal_mul (by positivity)
      _ = ∑ v ∈ F, ENNReal.ofReal (1 / (N : ℝ)) * ∫⁻ ω,
            ENNReal.ofReal (Real.exp (TriadicCube.stoppingSize (planarGoodCubes ω) v / θ))
            ∂latticeBondLaw 2 p := by
          rw [lintegral_finsetSum' _ fun v _ =>
            ((hexp v).1.aemeasurable.ennreal_ofReal).const_mul _]
          exact Finset.sum_congr rfl fun v _ => lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ∑ _v ∈ F, ENNReal.ofReal (1 / (N : ℝ)) * 2 := by
          refine Finset.sum_le_sum fun v _ => mul_le_mul_right ?_ _
          rw [← ofReal_integral_eq_lintegral_ofReal (hexp v).1
            (Eventually.of_forall fun _ => (Real.exp_pos _).le)]
          exact (ENNReal.ofReal_le_ofReal (hexp v).2).trans_eq (ENNReal.ofReal_ofNat 2)
      _ = 2 := by
          rw [Finset.sum_const, hcard, nsmul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (by positivity), mul_one_div_cancel hN0.ne', ENNReal.ofReal_one,
            one_mul]
  have hsub : {ω | t ≤ sizeSum k z ω} ⊆ {ω | ENNReal.ofReal (Real.exp (t / (N * θ))) ≤ f ω} := by
    intro ω hω
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    exact div_le_div_of_nonneg_right hω (by positivity)
  have hfm : Measurable f :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      ((measurable_sizeSum k z).div_const _))
  refine (measure_mono hsub).trans ((meas_ge_le_lintegral_div hfm.aemeasurable
    (by simp [Real.exp_pos]) ENNReal.ofReal_ne_top).trans ?_)
  calc (∫⁻ ω, f ω ∂latticeBondLaw 2 p) / ENNReal.ofReal (Real.exp (t / (N * θ)))
      ≤ 2 / ENNReal.ofReal (Real.exp (t / (N * θ))) := ENNReal.div_le_div_right hf _
    _ = ENNReal.ofReal (2 * Real.exp (-(t / (N * θ)))) := by
        rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_div_of_pos (Real.exp_pos _), Real.exp_neg,
          div_eq_mul_inv]

/-- The scale `θ_k = 4 N θ + 8·3^k` of the tail of the radius of the crude bound. -/
noncomputable def statTailScale (θ : ℝ) (k : ℕ) : ℝ :=
  4 * (((2 * 3 ^ k + 1) ^ 2 : ℕ) : ℝ) * θ + 8 * 3 ^ k

theorem statTailScale_pos {θ : ℝ} (hθ : 0 < θ) (k : ℕ) : 0 < statTailScale θ k := by
  unfold statTailScale
  positivity

theorem statTailScale_le {θ : ℝ} (hθ : 0 < θ) (k : ℕ) :
    statTailScale θ k ≤ (36 * θ + 8) * 9 ^ k := by
  unfold statTailScale
  have h1 : (1 : ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
  have h9 : (9 : ℝ) ^ k = (3 ^ k) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hN : ((((2 * 3 ^ k + 1) ^ 2 : ℕ)) : ℝ) ≤ 9 * 9 ^ k := by
    push_cast
    rw [h9]
    nlinarith
  rw [h9] at hN ⊢
  nlinarith

/-- **The tail of the radius of the crude bound**:
`P[t ≤ 2 (3^k + sizeSum k z)] ≤ 2 e^{-t/θ_k}`. -/
theorem measure_le_statRadius_le {p : unitInterval} {θ : ℝ} (hθ : 0 < θ)
    (hexp : ∀ v : Vertex 2,
      Integrable (fun ω => Real.exp (TriadicCube.stoppingSize (planarGoodCubes ω) v / θ))
        (latticeBondLaw 2 p) ∧
      ∫ ω, Real.exp (TriadicCube.stoppingSize (planarGoodCubes ω) v / θ) ∂latticeBondLaw 2 p ≤ 2)
    (k : ℕ) (z : Vertex 2) (t : ℝ) (ht : 0 ≤ t) :
    latticeBondLaw 2 p {ω | t ≤ 2 * ((3 : ℝ) ^ k + sizeSum k z ω)} ≤
      ENNReal.ofReal (2 * Real.exp (-(t / statTailScale θ k))) := by
  set θk := statTailScale θ k with hθk
  have hθk0 : 0 < θk := statTailScale_pos hθ k
  set N : ℝ := (((2 * 3 ^ k + 1) ^ 2 : ℕ) : ℝ) with hN
  have hN0 : 0 < N := by positivity
  have h3 : (0 : ℝ) < 3 ^ k := by positivity
  by_cases hsmall : t ≤ 4 * 3 ^ k
  · refine prob_le_one.trans ?_
    have hle : t / θk ≤ 1 / 2 := by
      rw [div_le_iff₀ hθk0, hθk, statTailScale]
      have : 0 ≤ 4 * N * θ := by positivity
      nlinarith
    have he := Real.add_one_le_exp (-(t / θk))
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  · push Not at hsmall
    have hsub : {ω | t ≤ 2 * ((3 : ℝ) ^ k + sizeSum k z ω)} ⊆ {ω | t / 4 ≤ sizeSum k z ω} := by
      intro ω hω
      change t ≤ _ at hω
      change t / 4 ≤ _
      linarith
    refine (measure_mono hsub).trans ((measure_le_sizeSum_le hθ hexp k z (t / 4)).trans ?_)
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by norm_num))
    rw [neg_le_neg_iff, div_div, div_le_div_iff₀ hθk0 (by positivity)]
    have : 4 * N * θ ≤ θk := by
      rw [hθk, statTailScale]
      linarith
    nlinarith

section Carrier

variable {G : Set (Configuration 2)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2)

/-- `|e| ≤ η e² + η⁻¹ 1_{e ≠ 0}`. -/
theorem abs_le_mul_sq_add_inv {e η : ℝ} (hη : 0 < η) :
    |e| ≤ η * |e| ^ 2 + η⁻¹ * (if e = 0 then 0 else 1) := by
  by_cases he : e = 0
  · rw [he, abs_zero, if_pos rfl]
    simp
  · rw [if_neg he, mul_one]
    by_cases h : |e| ≤ η⁻¹
    · have : 0 ≤ η * |e| ^ 2 := by positivity
      linarith
    · push Not at h
      have h1 : 1 ≤ η * |e| := by
        have := mul_lt_mul_of_pos_left h hη
        rw [mul_inv_cancel₀ hη.ne'] at this
        exact this.le
      have : 0 ≤ η⁻¹ := (inv_pos.2 hη).le
      nlinarith [abs_nonneg e]

/-- **Dario, Lemma 3.2, Step 1, at one vertex**: there are `K, c, θ₀ > 0` with
`E|χ(z̄_stat(z)) - χ(z̄(z))| ≤ K (1 + θ₀ 9^k)^4 e^{-c 3^k / 2}` for every `k`, `z` and `i`. -/
theorem exists_lintegral_abs_statDiscrepancy_le (hR3 : ArmstrongDarioOrderZeroTwo)
    {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGae : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G) :
    ∃ K c θ₀ : ℝ, 0 < K ∧ 0 < c ∧ 0 < θ₀ ∧ ∀ (i : Fin 2) (k : ℕ) (z : Vertex 2),
      ∫⁻ ω, ENNReal.ofReal |statDiscrepancy hG hGv i k z ω| ∂latticeBondLaw 2 p ≤
        ENNReal.ofReal (K * (1 + θ₀ * 9 ^ k) ^ 4 * Real.exp (-(c * 3 ^ k / 2))) := by
  obtain ⟨Λ, A, κ, hA0, -, hΛm, hΛ0, hlip, hmom6⟩ := stepSix_data hG hGv hR3 hpc hp1 hGae
  obtain ⟨θ, hθ, hexp⟩ := (planar_meshed_partition_estimates hpc).2.1
  obtain ⟨C₃, hC₃, c₃, hc₃, h33⟩ := dario_errorstatpart hpc
  set M : ℝ := (A * 4 ^ κ) ^ 2 with hM
  have hM0 : 0 ≤ M := by positivity
  set θ₀ : ℝ := 36 * θ + 8 with hθ₀
  set K₁ : ℝ := 9 * (4 * 256 * (Real.sqrt 2 * 4 * 64 * M)) with hK₁
  refine ⟨K₁ + C₃.toReal + 1, c₃, θ₀, by positivity, hc₃, by positivity, fun i k z => ?_⟩
  set θk := statTailScale θ k with hθk
  have hθk0 : 0 < θk := statTailScale_pos hθ k
  have hθkle : θk ≤ θ₀ * 9 ^ k := statTailScale_le hθ k
  set ε : Configuration 2 → ℝ := statDiscrepancy hG hGv i k z with hε
  have hεm : Measurable ε := measurable_statDiscrepancy hG hGv i k z
  set T : Configuration 2 → ℝ≥0∞ := fun ω => ∑' u, if ‖latticeEuclideanEmbedding (u - z)‖ ≤
    2 * ((3 : ℝ) ^ k + sizeSum k z ω) then stepSixSum (Λ i) u ω else 0 with hT
  have hall : ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ x, ω ∈ infiniteComponentEvent x → ∀ y,
      (openGraph ω).Adj x y → |correctorDiff hG hGv (Pi.single i 1) ω x y| ≤ Λ i x ω :=
    ae_all_iff.2 fun x => hlip i x
  have hpt : ∀ᵐ ω ∂latticeBondLaw 2 p, ENNReal.ofReal |ε ω| ≤ 3 * T ω := by
    filter_upwards [hGae, ae_planarPartitionEvent hpc, hall] with ω hω hP hl
    exact ofReal_abs_statDiscrepancy_le hG hGv hω hP k z (fun x => hΛ0 i x ω) hl
  -- the second moment
  have hYm : ∀ u, ∫⁻ ω, stepSixSum (Λ i) u ω ^ (2 * (2 : ℝ)) ∂latticeBondLaw 2 p ≤
      ENNReal.ofReal (M ^ 2) := by
    intro u
    have h := hmom6 i u (2 * 2) (by norm_num)
    have e : (A * (2 * 2 : ℝ) ^ κ) ^ (2 * 2 : ℝ) = M ^ 2 := by
      rw [hM, show (2 * 2 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Nat.cast_ofNat]
      ring
    rw [e] at h
    exact h
  have hρm : Measurable fun ω => 2 * ((3 : ℝ) ^ k + sizeSum k z ω) :=
    ((measurable_sizeSum k z).const_add _).const_mul _
  have hball := lintegral_randomBallSum_le (p := p) z hθk0
    (fun t ht => measure_le_statRadius_le hθ hexp k z t ht) hρm
    (fun u => measurable_stepSixSum (hΛm i) u) (by norm_num : (1 : ℝ) ≤ 2) hM0 hYm
  have hT2 : ∫⁻ ω, T ω ^ (2 : ℝ) ∂latticeBondLaw 2 p ≤
      ENNReal.ofReal (4 * 256 * (Real.sqrt 2 * 4 * 64 * M) * (1 + θk) ^ 4) := by
    refine hball.trans (ENNReal.ofReal_le_ofReal ?_)
    have h1 : (1 + 8 * 2 * θk) ^ 2 ≤ 256 * (1 + θk) ^ 2 := by nlinarith
    have h2 : (1 + 8 * θk) ^ 2 ≤ 64 * (1 + θk) ^ 2 := by nlinarith
    rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
    have hs : 0 ≤ Real.sqrt 2 * 4 * M := by positivity
    calc 4 * (1 + 8 * 2 * θk) ^ 2 * (Real.sqrt 2 * 4 * (1 + 8 * θk) ^ 2 * M)
        = 4 * (1 + 8 * 2 * θk) ^ 2 * ((1 + 8 * θk) ^ 2 * (Real.sqrt 2 * 4 * M)) := by ring
      _ ≤ 4 * (256 * (1 + θk) ^ 2) * ((64 * (1 + θk) ^ 2) * (Real.sqrt 2 * 4 * M)) := by
          gcongr
      _ = 4 * 256 * (Real.sqrt 2 * 4 * 64 * M) * (1 + θk) ^ 4 := by ring
  have hε2 : ∫⁻ ω, ENNReal.ofReal |ε ω| ^ (2 : ℝ) ∂latticeBondLaw 2 p ≤
      ENNReal.ofReal (K₁ * (1 + θ₀ * 9 ^ k) ^ 4) := by
    calc ∫⁻ ω, ENNReal.ofReal |ε ω| ^ (2 : ℝ) ∂latticeBondLaw 2 p
        ≤ ∫⁻ ω, 9 * T ω ^ (2 : ℝ) ∂latticeBondLaw 2 p := by
          refine lintegral_mono_ae ?_
          filter_upwards [hpt] with ω hω
          calc ENNReal.ofReal |ε ω| ^ (2 : ℝ) ≤ (3 * T ω) ^ (2 : ℝ) :=
                ENNReal.rpow_le_rpow hω (by norm_num)
            _ = 9 * T ω ^ (2 : ℝ) := by
                rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
                congr 1
                rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
                norm_num
      _ = 9 * ∫⁻ ω, T ω ^ (2 : ℝ) ∂latticeBondLaw 2 p :=
          lintegral_const_mul' _ _ (by norm_num)
      _ ≤ 9 * ENNReal.ofReal (4 * 256 * (Real.sqrt 2 * 4 * 64 * M) * (1 + θk) ^ 4) :=
          mul_le_mul_right hT2 _
      _ ≤ ENNReal.ofReal (K₁ * (1 + θ₀ * 9 ^ k) ^ 4) := by
          rw [← ENNReal.ofReal_ofNat 9, ← ENNReal.ofReal_mul (by norm_num)]
          refine ENNReal.ofReal_le_ofReal ?_
          have h4 : (1 + θk) ^ 4 ≤ (1 + θ₀ * 9 ^ k) ^ 4 :=
            pow_le_pow_left₀ (by positivity) (by linarith) 4
          rw [hK₁]
          have : 0 ≤ 4 * 256 * (Real.sqrt 2 * 4 * 64 * M) := by positivity
          nlinarith
  -- the probability of a discrepancy
  obtain ⟨V, ⟨hVk, hzV⟩, -⟩ := TriadicCube.existsUnique_mem 2 k z
  have hprob : latticeBondLaw 2 p {ω | ε ω ≠ 0} ≤
      ENNReal.ofReal (C₃.toReal * Real.exp (-c₃ * (3 : ℝ) ^ k)) := by
    have h := h33 V
    rw [hVk] at h
    refine (measure_mono_ae ?_).trans (h.trans_eq ?_)
    · filter_upwards [hGae, ae_planarPartitionEvent hpc] with ω hω hP
      intro hne
      refine ⟨z, hzV, fun heq => hne ?_⟩
      exact statDiscrepancy_eq_zero hG hGv hω hP (i := i) (k := k) (z := z) heq.symm
    · rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hC₃]
  -- the inequality of the arithmetic and geometric means
  set η : ℝ := Real.exp (-(c₃ * 3 ^ k / 2)) with hη
  have hη0 : 0 < η := Real.exp_pos _
  have hAM : ∀ ω, ENNReal.ofReal |ε ω| ≤ ENNReal.ofReal η * ENNReal.ofReal |ε ω| ^ (2 : ℝ) +
      ENNReal.ofReal η⁻¹ * Set.indicator {ω | ε ω ≠ 0} 1 ω := by
    intro ω
    have h := abs_le_mul_sq_add_inv (e := ε ω) hη0
    refine (ENNReal.ofReal_le_ofReal h).trans ?_
    rw [ENNReal.ofReal_add (by positivity) (by split_ifs <;> positivity),
      ENNReal.ofReal_mul hη0.le, ENNReal.ofReal_mul (inv_pos.2 hη0).le,
      ENNReal.ofReal_pow (abs_nonneg _)]
    refine add_le_add (le_of_eq ?_) (mul_le_mul_right ?_ _)
    · rw [← ENNReal.rpow_natCast, Nat.cast_ofNat]
    · by_cases he : ε ω = 0
      · rw [if_pos he]
        simp
      · rw [if_neg he, Set.indicator_of_mem (show ω ∈ {ω | ε ω ≠ 0} from he)]
        simp
  calc ∫⁻ ω, ENNReal.ofReal |ε ω| ∂latticeBondLaw 2 p
      ≤ ∫⁻ ω, (ENNReal.ofReal η * ENNReal.ofReal |ε ω| ^ (2 : ℝ) +
          ENNReal.ofReal η⁻¹ * Set.indicator {ω | ε ω ≠ 0} 1 ω) ∂latticeBondLaw 2 p :=
        lintegral_mono hAM
    _ = ENNReal.ofReal η * ∫⁻ ω, ENNReal.ofReal |ε ω| ^ (2 : ℝ) ∂latticeBondLaw 2 p +
          ENNReal.ofReal η⁻¹ * latticeBondLaw 2 p {ω | ε ω ≠ 0} := by
        rw [lintegral_add_left (f := fun ω => ENNReal.ofReal η * ENNReal.ofReal |ε ω| ^ (2 : ℝ))
            (((ENNReal.measurable_ofReal.comp hεm.abs).pow_const _).const_mul _),
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_indicator_one
            (show MeasurableSet {ω | ε ω ≠ 0} from hεm (measurableSet_singleton 0).compl)]
    _ ≤ ENNReal.ofReal η * ENNReal.ofReal (K₁ * (1 + θ₀ * 9 ^ k) ^ 4) +
          ENNReal.ofReal η⁻¹ * ENNReal.ofReal (C₃.toReal * Real.exp (-c₃ * (3 : ℝ) ^ k)) :=
        add_le_add (mul_le_mul_right hε2 _) (mul_le_mul_right hprob _)
    _ ≤ ENNReal.ofReal ((K₁ + C₃.toReal + 1) * (1 + θ₀ * 9 ^ k) ^ 4 *
          Real.exp (-(c₃ * 3 ^ k / 2))) := by
        rw [← ENNReal.ofReal_mul hη0.le, ← ENNReal.ofReal_mul (inv_pos.2 hη0).le,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have hinv : η⁻¹ * Real.exp (-c₃ * (3 : ℝ) ^ k) = η := by
          rw [hη, ← Real.exp_neg, ← Real.exp_add]
          congr 1
          ring
        have h1 : (1 : ℝ) ≤ (1 + θ₀ * 9 ^ k) ^ 4 := one_le_pow₀ (by
          have : 0 ≤ θ₀ * 9 ^ k := by positivity
          linarith)
        have hC0 : 0 ≤ C₃.toReal := ENNReal.toReal_nonneg
        calc η * (K₁ * (1 + θ₀ * 9 ^ k) ^ 4) + η⁻¹ * (C₃.toReal * Real.exp (-c₃ * (3 : ℝ) ^ k))
            = η * (K₁ * (1 + θ₀ * 9 ^ k) ^ 4) + C₃.toReal * η := by
              rw [mul_left_comm η⁻¹ C₃.toReal, hinv]
          _ ≤ (K₁ + C₃.toReal + 1) * (1 + θ₀ * 9 ^ k) ^ 4 * η := by
              nlinarith [mul_nonneg hC0 hη0.le, mul_le_mul_of_nonneg_left h1 (mul_nonneg hC0 hη0.le),
                mul_pos hη0 (lt_of_lt_of_le one_pos h1)]

end Carrier

end Rigidity.Corrector
