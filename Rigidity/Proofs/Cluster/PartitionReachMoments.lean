import Rigidity.Proofs.Cluster.PartitionCoarseData
import Rigidity.Proofs.Partition.Measurability
import Rigidity.Proofs.Percolation.PlanarReachMoments

/-!
# Moments of the reach of the partition into good cubes

The reach of the partition at a vertex `z` is the largest side `3^n` of a partition cube whose
`3s`-neighbourhood contains `z`. It bounds `3^{ρ(z)}` for the reach scale `ρ` of the
coarse-graining data of every resolved cube, which is the weight in Lemma 3.2 and Proposition 3.4
of Armstrong and Dario as proved here. If the partition size has a uniform exponential moment
(Armstrong and Dario, Proposition 2.1 (iii)), every moment of the reach is bounded uniformly in the
vertex: a triadic cube of scale `n` is a partition cube with probability at most `2 exp(-3^n/θ)`,
and at most `9^d` triadic cubes of each scale have a neighbourhood containing `z`.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External
open scoped ENNReal Classical Nat

namespace Rigidity.Percolation

variable {d : ℕ}

/-- The reach of the partition at `z`: the largest side of a partition cube whose
`3s`-neighbourhood contains `z`. -/
noncomputable def partitionReach (ω : Configuration d) (z : Vertex d) : ℝ≥0∞ :=
  ⨆ (Q : TriadicCube d) (_ : Q.IsMaximalStopping (TriadicCube.goodCubes ω) ∧
    z ∈ (Q.thicken 3).vertices), (3 : ℝ≥0∞) ^ Q.scale

/-- On a resolved cube, `3^{ρ(z)}` is at most the reach of the partition at `z`. -/
theorem three_pow_reachScale_le_partitionReach (hd : 0 < d) {ω : Configuration d}
    (hP : PartitionEvent ω) {U : TriadicCube d} (hU : PartitionResolved ω U) {z : Vertex d}
    (hz : z ∈ crossingClusterVertices ω U) :
    (3 : ℝ≥0∞) ^ (partitionCoarseData hd hP U hU).reachScale z ≤ partitionReach ω z := by
  set P := partitionCoarseData hd hP U hU
  have hne : (P.cluster.filter fun x => z ∈ P.region x).Nonempty :=
    ⟨z, Finset.mem_filter.2 ⟨hz, P.mem_region_self hz⟩⟩
  obtain ⟨x, hx, hxs⟩ := Finset.exists_mem_eq_sup _ hne (fun x => (P.part x).scale)
  rw [Finset.mem_filter] at hx
  unfold CoarseData.reachScale
  rw [hxs]
  unfold partitionReach
  exact le_iSup₂_of_le (partitionCube ω x)
    ⟨(partitionCube_spec hP x).2, partitionRegion_subset_thicken hP U x hx.2⟩ le_rfl

/-- Powers of the reach are bounded by sums over the partition cubes reaching the vertex. -/
theorem partitionReach_pow_le (ω : Configuration d) (z : Vertex d) (n : ℕ) :
    partitionReach ω z ^ (n + 1) ≤
      ∑' Q : TriadicCube d, if Q.IsMaximalStopping (TriadicCube.goodCubes ω) ∧
        z ∈ (Q.thicken 3).vertices then (3 : ℝ≥0∞) ^ ((n + 1) * Q.scale) else 0 := by
  unfold partitionReach
  rw [ENNReal.iSup_pow_of_ne_zero (Nat.succ_ne_zero n)]
  refine iSup_le fun Q => ?_
  rw [ENNReal.iSup_pow_of_ne_zero (Nat.succ_ne_zero n)]
  refine iSup_le fun hQ => ?_
  refine le_trans (le_of_eq ?_) (ENNReal.le_tsum Q)
  rw [if_pos hQ, ← pow_mul, mul_comm]

/-- At most `9^d` triadic cubes of a given scale have a `3s`-neighbourhood containing `z`. -/
theorem tsum_thicken_indicator_le (z : Vertex d) (s : ℕ) (b : ℝ≥0∞) :
    ∑' idx : Fin d → ℤ, (if z ∈ (TriadicCube.thicken ⟨s, idx⟩ 3).vertices then b else 0) ≤
      9 ^ d * b := by
  set t : ℤ := 3 ^ s with ht
  have htpos : 0 < t := by positivity
  set F : Finset (Fin d → ℤ) :=
    Fintype.piFinset fun i => Finset.Icc (z i / t - 4) (z i / t + 4)
  have hzero : ∀ idx ∉ F,
      (if z ∈ (TriadicCube.thicken ⟨s, idx⟩ 3).vertices then b else 0) = 0 := by
    intro idx hidx
    rw [if_neg]
    intro hz
    apply hidx
    rw [Fintype.mem_piFinset]
    intro i
    rw [IntegerCube.mem_vertices] at hz
    obtain ⟨h1, h2⟩ := hz i
    change (3 : ℤ) ^ s * idx i - (3 : ℤ) ^ s / 2 - ((3 : ℕ) : ℤ) * ((3 ^ s : ℕ) : ℤ) ≤ z i at h1
    change z i < (3 : ℤ) ^ s * idx i - (3 : ℤ) ^ s / 2 - ((3 : ℕ) : ℤ) * ((3 ^ s : ℕ) : ℤ) +
      (((2 * 3 + 1) * 3 ^ s : ℕ) : ℤ) at h2
    push_cast at h1 h2
    rw [← ht] at h1 h2
    have hdiv := Int.mul_ediv_add_emod (z i) t
    have hmod0 := Int.emod_nonneg (z i) htpos.ne'
    have hmodlt := Int.emod_lt_of_pos (z i) htpos
    have hhalf0 : 0 ≤ t / 2 := by omega
    have hhalf : t / 2 ≤ t := by omega
    set q := z i / t
    set r := z i % t
    rw [Finset.mem_Icc]
    constructor
    · have h3 : t * (q - idx i) < t * 5 := by nlinarith
      have := lt_of_mul_lt_mul_left h3 htpos.le
      omega
    · have h3 : t * (idx i - q) < t * 5 := by nlinarith
      have := lt_of_mul_lt_mul_left h3 htpos.le
      omega
  rw [tsum_eq_sum hzero]
  calc ∑ idx ∈ F, (if z ∈ (TriadicCube.thicken ⟨s, idx⟩ 3).vertices then b else 0)
      ≤ ∑ _idx ∈ F, b := Finset.sum_le_sum fun idx _ => by split_ifs <;> simp
    _ = F.card * b := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = 9 ^ d * b := by
        congr 1
        have hc : F.card = 9 ^ d := by
          simp only [F, Fintype.card_piFinset, Int.card_Icc]
          have : ∀ w : ℤ, (w + 4 + 1 - (w - 4)).toNat = 9 := by
            intro w
            omega
          simp only [this, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        rw [hc]
        norm_num

/-- A triadic cube of scale `n` is a partition cube with probability at most `2 exp(-3^n/θ)`
when the partition size has the exponential moment `∫ exp(size/θ) ≤ 2`. -/
theorem measure_isMaximalStopping_goodCubes_le (μ : Measure (Configuration d))
    [IsFiniteMeasure μ] {θ : ℝ} (hmom : ∀ x : Vertex d,
      Integrable (fun ω => Real.exp (TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x / θ))
        μ ∧
      (∫ ω, Real.exp (TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x / θ) ∂μ) ≤ 2)
    (Q : TriadicCube d) :
    μ {ω | Q.IsMaximalStopping (TriadicCube.goodCubes ω)} ≤
      ENNReal.ofReal (2 * Real.exp (-((3 : ℝ) ^ Q.scale / θ))) := by
  obtain ⟨hint, hle⟩ := hmom Q.center
  set f : Configuration d → ℝ := fun ω =>
    Real.exp (TriadicCube.stoppingSize (TriadicCube.goodCubes ω) Q.center / θ) with hf
  have hint' : Integrable f μ := hint
  have hle' : ∫ ω, f ω ∂μ ≤ 2 := hle
  set ε := Real.exp ((3 : ℝ) ^ Q.scale / θ) with hε
  have hεpos : 0 < ε := Real.exp_pos _
  have hsub : {ω : Configuration d | Q.IsMaximalStopping (TriadicCube.goodCubes ω)} ⊆
      {ω | ε ≤ f ω} := by
    intro ω hω
    have h := TriadicCube.stoppingSize_eq_of_mem (x := Q.center) Q.center_mem hω
    simp only [Set.mem_setOf_eq, hf, hε]
    rw [h]
  have hM := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all _ fun ω => (Real.exp_pos _).le) hint' ε
  calc μ {ω | Q.IsMaximalStopping (TriadicCube.goodCubes ω)}
      ≤ μ {ω | ε ≤ f ω} := measure_mono hsub
    _ = ENNReal.ofReal (μ.real {ω | ε ≤ f ω}) :=
        (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal (2 * Real.exp (-((3 : ℝ) ^ Q.scale / θ))) := by
        apply ENNReal.ofReal_le_ofReal
        rw [Real.exp_neg, ← hε, ← div_eq_mul_inv, le_div_iff₀ hεpos, mul_comm]
        linarith

/-- **Moments of the reach of the partition.** If the partition size has the exponential moment
`∫ exp(size/θ) ≤ 2` at every vertex, every moment of the reach is bounded uniformly in the
vertex. -/
theorem exists_lintegral_partitionReach_pow_le (μ : Measure (Configuration d))
    [IsFiniteMeasure μ] {θ : ℝ} (hθ : 0 < θ) (hmom : ∀ x : Vertex d,
      Integrable (fun ω => Real.exp (TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x / θ))
        μ ∧
      (∫ ω, Real.exp (TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x / θ) ∂μ) ≤ 2)
    (n : ℕ) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ z : Vertex d, ∫⁻ ω, partitionReach ω z ^ (n + 1) ∂μ ≤ C := by
  set K : ℝ := 2 * θ ^ (n + 1 + 1) * (n + 1 + 1)!
  have h3 : (1 : ℝ≥0∞) - 3⁻¹ ≠ 0 :=
    (tsub_pos_iff_lt.2 (ENNReal.inv_lt_one.2 (by norm_num))).ne'
  refine ⟨9 ^ d * (ENNReal.ofReal K * (1 - 3⁻¹)⁻¹), ?_, fun z => ?_⟩
  · exact ENNReal.mul_ne_top (ENNReal.pow_ne_top (by norm_num))
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.inv_ne_top.2 h3))
  set b : ℕ → ℝ≥0∞ := fun s =>
    (3 : ℝ≥0∞) ^ ((n + 1) * s) * ENNReal.ofReal (2 * Real.exp (-((3 : ℝ) ^ s / θ)))
  have hmeas : ∀ Q : TriadicCube d, Measurable fun ω : Configuration d =>
      if Q.IsMaximalStopping (TriadicCube.goodCubes ω) ∧ z ∈ (Q.thicken 3).vertices then
        (3 : ℝ≥0∞) ^ ((n + 1) * Q.scale) else 0 := by
    intro Q
    by_cases hz : z ∈ (Q.thicken 3).vertices
    · simp only [hz, and_true]
      exact measurable_const.ite (TriadicCube.measurableSet_isMaximalStopping_goodCubes Q)
        measurable_const
    · simp only [hz, and_false, if_false]
      exact measurable_const
  have hterm : ∀ Q : TriadicCube d,
      ∫⁻ ω, (if Q.IsMaximalStopping (TriadicCube.goodCubes ω) ∧ z ∈ (Q.thicken 3).vertices then
        (3 : ℝ≥0∞) ^ ((n + 1) * Q.scale) else 0) ∂μ ≤
      if z ∈ (Q.thicken 3).vertices then b Q.scale else 0 := by
    intro Q
    by_cases hz : z ∈ (Q.thicken 3).vertices
    · simp only [hz, and_true, if_true]
      have hfun : (fun ω : Configuration d => if Q.IsMaximalStopping (TriadicCube.goodCubes ω)
          then (3 : ℝ≥0∞) ^ ((n + 1) * Q.scale) else 0) =
          {ω | Q.IsMaximalStopping (TriadicCube.goodCubes ω)}.indicator
            (fun _ => (3 : ℝ≥0∞) ^ ((n + 1) * Q.scale)) := by
        funext ω
        simp only [Set.indicator_apply, Set.mem_setOf_eq]
      rw [hfun, lintegral_indicator_const
        (TriadicCube.measurableSet_isMaximalStopping_goodCubes Q)]
      show _ ≤ (3 : ℝ≥0∞) ^ ((n + 1) * Q.scale) *
        ENNReal.ofReal (2 * Real.exp (-((3 : ℝ) ^ Q.scale / θ)))
      gcongr
      exact measure_isMaximalStopping_goodCubes_le μ hmom Q
    · simp only [hz, and_false, if_false, lintegral_zero, le_refl]
  have hb : ∀ s : ℕ, b s ≤ ENNReal.ofReal K * 3⁻¹ ^ s := by
    intro s
    have hreal := three_pow_mul_exp_neg_le hθ (n + 1) s
    calc b s = ENNReal.ofReal ((3 : ℝ) ^ ((n + 1) * s) * (2 * Real.exp (-((3 : ℝ) ^ s / θ)))) := by
          simp only [b]
          rw [ENNReal.ofReal_mul (p := (3 : ℝ) ^ ((n + 1) * s)) (by positivity),
            ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 3), ENNReal.ofReal_ofNat]
      _ ≤ ENNReal.ofReal (K * (1 / 3) ^ s) := ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal K * 3⁻¹ ^ s := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num), one_div,
            ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
  let e : ℕ × (Fin d → ℤ) ≃ TriadicCube d :=
    { toFun := fun q => ⟨q.1, q.2⟩
      invFun := fun Q => (Q.scale, Q.index)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  refine (lintegral_mono fun ω => partitionReach_pow_le ω z n).trans ?_
  rw [lintegral_tsum fun Q => (hmeas Q).aemeasurable]
  calc ∑' Q : TriadicCube d, ∫⁻ ω, (if Q.IsMaximalStopping (TriadicCube.goodCubes ω) ∧
          z ∈ (Q.thicken 3).vertices then (3 : ℝ≥0∞) ^ ((n + 1) * Q.scale) else 0) ∂μ
      ≤ ∑' Q : TriadicCube d, (if z ∈ (Q.thicken 3).vertices then b Q.scale else 0) :=
        ENNReal.tsum_le_tsum hterm
    _ = ∑' q : ℕ × (Fin d → ℤ),
          (if z ∈ (TriadicCube.thicken ⟨q.1, q.2⟩ 3).vertices then b q.1 else 0) :=
        (e.tsum_eq (fun Q => if z ∈ (Q.thicken 3).vertices then b Q.scale else 0)).symm
    _ = ∑' s : ℕ, ∑' idx : Fin d → ℤ,
          (if z ∈ (TriadicCube.thicken ⟨s, idx⟩ 3).vertices then b s else 0) :=
        ENNReal.tsum_prod (f := fun s idx =>
          if z ∈ (TriadicCube.thicken ⟨s, idx⟩ 3).vertices then b s else 0)
    _ ≤ ∑' s : ℕ, 9 ^ d * (ENNReal.ofReal K * 3⁻¹ ^ s) :=
        ENNReal.tsum_le_tsum fun s =>
          (tsum_thicken_indicator_le z s (b s)).trans (by gcongr; exact hb s)
    _ = 9 ^ d * (ENNReal.ofReal K * (1 - 3⁻¹)⁻¹) := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ENNReal.tsum_geometric]

end Rigidity.Percolation
