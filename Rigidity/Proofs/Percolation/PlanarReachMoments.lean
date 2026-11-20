import Rigidity.Proofs.Percolation.PlanarCoarseWeights

/-!
# Moments of the reach of the planar partition

In the supercritical regime, every moment of the reach of the planar partition at a vertex is
bounded uniformly in the vertex. A triadic cube of scale `s` is a partition cube with probability
at most `2 exp (-3 ^ s / θ)`, by the exponential moment of the partition size at its centre, and
at most `121` cubes of each scale have a square of side `9s` around a given vertex.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped ENNReal Classical Nat

namespace Rigidity.Percolation

/-- Membership of a triadic cube in the partition is measurable. -/
theorem measurableSet_isMaximalStopping_planarGoodCubes (Q : TriadicCube 2) :
    MeasurableSet {ω : Configuration 2 | Q.IsMaximalStopping (planarGoodCubes ω)} :=
  TriadicCube.measurableSet_isMaximalStopping (fun ω => planarGoodCubes ω)
    (fun T => TriadicCube.measurableSet_mem_goodOfWellConnected planarMeshedFamily
      measurableSet_mem_planarMeshedFamily T) Q

/-- A triadic cube of scale `s` is a partition cube with probability at most
`2 exp (-3 ^ s / θ)`. -/
theorem exists_measure_isMaximalStopping_le {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ Q : TriadicCube 2,
      latticeBondLaw 2 p {ω | Q.IsMaximalStopping (planarGoodCubes ω)} ≤
        ENNReal.ofReal (2 * Real.exp (-((3 : ℝ) ^ Q.scale / θ))) := by
  obtain ⟨-, ⟨θ, hθ, hmom⟩, -⟩ := planar_meshed_partition_estimates hpc
  refine ⟨θ, hθ, fun Q => ?_⟩
  obtain ⟨hint, hle⟩ := hmom Q.center
  set f : Configuration 2 → ℝ := fun ω =>
    Real.exp (TriadicCube.stoppingSize (planarGoodCubes ω) Q.center / θ) with hf
  have hint' : Integrable f (latticeBondLaw 2 p) := hint
  have hle' : ∫ ω, f ω ∂(latticeBondLaw 2 p) ≤ 2 := hle
  set ε := Real.exp ((3 : ℝ) ^ Q.scale / θ) with hε
  have hεpos : 0 < ε := Real.exp_pos _
  have hsub : {ω : Configuration 2 | Q.IsMaximalStopping (planarGoodCubes ω)} ⊆
      {ω | ε ≤ f ω} := by
    intro ω hω
    have h := TriadicCube.stoppingSize_eq_of_mem (x := Q.center) Q.center_mem hω
    simp only [Set.mem_setOf_eq, hf, hε]
    rw [h]
  have hM := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all _ fun ω => (Real.exp_pos _).le) hint' ε
  calc latticeBondLaw 2 p {ω | Q.IsMaximalStopping (planarGoodCubes ω)}
      ≤ latticeBondLaw 2 p {ω | ε ≤ f ω} := measure_mono hsub
    _ = ENNReal.ofReal ((latticeBondLaw 2 p).real {ω | ε ≤ f ω}) :=
        (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal (2 * Real.exp (-((3 : ℝ) ^ Q.scale / θ))) := by
        apply ENNReal.ofReal_le_ofReal
        rw [Real.exp_neg, ← hε, ← div_eq_mul_inv, le_div_iff₀ hεpos, mul_comm]
        linarith

/-- The elementary bound `3 ^ (m s) · 2 exp (-3 ^ s / θ) ≤ 2 θ ^ (m + 1) (m + 1)! / 3 ^ s`. -/
theorem three_pow_mul_exp_neg_le {θ : ℝ} (hθ : 0 < θ) (m s : ℕ) :
    (3 : ℝ) ^ (m * s) * (2 * Real.exp (-((3 : ℝ) ^ s / θ))) ≤
      2 * θ ^ (m + 1) * (m + 1)! * (1 / 3) ^ s := by
  set T : ℝ := (3 : ℝ) ^ s with hT
  have hTpos : 0 < T := by positivity
  set x := T / θ with hx
  have hxpos : 0 < x := div_pos hTpos hθ
  have he : x ^ (m + 1) / (m + 1)! ≤ Real.exp x := Real.pow_div_factorial_le_exp x hxpos.le _
  have hfac : (0 : ℝ) < (m + 1)! := by exact_mod_cast Nat.factorial_pos _
  have key : T ^ (m + 1) ≤ (m + 1)! * θ ^ (m + 1) * Real.exp x := by
    rw [div_le_iff₀ hfac, hx, div_pow] at he
    have hθp : 0 < θ ^ (m + 1) := by positivity
    rw [div_le_iff₀ hθp] at he
    calc T ^ (m + 1) ≤ Real.exp (T / θ) * (m + 1)! * θ ^ (m + 1) := he
      _ = (m + 1)! * θ ^ (m + 1) * Real.exp x := by rw [hx]; ring
  have hexp : 0 < Real.exp x := Real.exp_pos x
  rw [Real.exp_neg, pow_mul', one_div, inv_pow, ← hT]
  rw [show T ^ m * (2 * (Real.exp x)⁻¹) = 2 * T ^ (m + 1) * ((Real.exp x)⁻¹ * T⁻¹) by
    field_simp
    ring]
  calc 2 * T ^ (m + 1) * ((Real.exp x)⁻¹ * T⁻¹)
      ≤ 2 * ((m + 1)! * θ ^ (m + 1) * Real.exp x) * ((Real.exp x)⁻¹ * T⁻¹) := by
        gcongr
    _ = 2 * θ ^ (m + 1) * (m + 1)! * T⁻¹ := by
        field_simp

/-- At most `121` triadic cubes of a given scale have their square of side `9s` around a given
vertex. -/
theorem tsum_ninefold_indicator_le (a : Vertex 2) (s : ℕ) (b : ℝ≥0∞) :
    ∑' idx : Fin 2 → ℤ, (if a ∈ (↑(TriadicCube.ninefold ⟨s, idx⟩).vertices : Set (Vertex 2))
      then b else 0) ≤ 121 * b := by
  set t : ℤ := 3 ^ s with ht
  have htpos : 0 < t := by positivity
  set F : Finset (Fin 2 → ℤ) :=
    Fintype.piFinset fun i => Finset.Icc (a i / t - 5) (a i / t + 5)
  have hzero : ∀ idx ∉ F, (if a ∈ (↑(TriadicCube.ninefold ⟨s, idx⟩).vertices : Set (Vertex 2))
      then b else 0) = 0 := by
    intro idx hidx
    rw [if_neg]
    intro ha
    apply hidx
    rw [Fintype.mem_piFinset]
    intro i
    have h1 := (TriadicCube.mem_ninefold.1 ha) i
    have h2 := (TriadicCube.two_mul_ninefoldRadius ⟨s, idx⟩)
    have hc : (TriadicCube.center ⟨s, idx⟩ : Vertex 2) i = t * idx i := rfl
    change 2 * TriadicCube.ninefoldRadius ⟨s, idx⟩ + 1 = 9 * t at h2
    rw [hc, abs_le] at h1
    have hdiv := Int.mul_ediv_add_emod (a i) t
    have hmod0 := Int.emod_nonneg (a i) htpos.ne'
    have hmodlt := Int.emod_lt_of_pos (a i) htpos
    set q := a i / t
    set ρ := a i % t
    rw [Finset.mem_Icc]
    constructor
    · have h3 : t * (q - idx i) < t * 5 := by nlinarith
      have := lt_of_mul_lt_mul_left h3 htpos.le
      omega
    · have h3 : t * (idx i - q) < t * 6 := by nlinarith
      have := lt_of_mul_lt_mul_left h3 htpos.le
      omega
  rw [tsum_eq_sum hzero]
  calc ∑ idx ∈ F, (if a ∈ (↑(TriadicCube.ninefold ⟨s, idx⟩).vertices : Set (Vertex 2))
        then b else 0)
      ≤ ∑ _idx ∈ F, b := Finset.sum_le_sum fun idx _ => by split_ifs <;> simp
    _ = F.card * b := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = 121 * b := by
        congr 1
        have hc : F.card = 121 := by
          simp only [F, Fintype.card_piFinset, Int.card_Icc, Fin.prod_univ_two]
          have : ∀ z : ℤ, (z + 5 + 1 - (z - 5)).toNat = 11 := by
            intro z
            omega
          rw [this, this]
          norm_num
        rw [hc]
        norm_num

/-- The expected number of partition cubes reaching a vertex, weighted by `s ^ m`, is bounded
uniformly in the vertex. -/
theorem exists_lintegral_tsum_ninefold_le {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (m : ℕ) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ a : Vertex 2,
      ∫⁻ ω, (∑' Q : TriadicCube 2, if Q.IsMaximalStopping (planarGoodCubes ω) ∧
          a ∈ (↑Q.ninefold.vertices : Set (Vertex 2)) then (3 : ℝ≥0∞) ^ (m * Q.scale) else 0)
        ∂(latticeBondLaw 2 p) ≤ C := by
  obtain ⟨θ, hθ, hQ⟩ := exists_measure_isMaximalStopping_le hpc
  set K : ℝ := 2 * θ ^ (m + 1) * (m + 1)!
  have h3 : (1 : ℝ≥0∞) - 3⁻¹ ≠ 0 :=
    (tsub_pos_iff_lt.2 (ENNReal.inv_lt_one.2 (by norm_num))).ne'
  refine ⟨121 * (ENNReal.ofReal K * (1 - 3⁻¹)⁻¹), ?_, fun a => ?_⟩
  · exact ENNReal.mul_ne_top (by norm_num)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.inv_ne_top.2 h3))
  set b : ℕ → ℝ≥0∞ := fun s =>
    (3 : ℝ≥0∞) ^ (m * s) * ENNReal.ofReal (2 * Real.exp (-((3 : ℝ) ^ s / θ)))
  have hmeas : ∀ Q : TriadicCube 2, Measurable fun ω : Configuration 2 =>
      if Q.IsMaximalStopping (planarGoodCubes ω) ∧
        a ∈ (↑Q.ninefold.vertices : Set (Vertex 2)) then (3 : ℝ≥0∞) ^ (m * Q.scale) else 0 := by
    intro Q
    by_cases ha : a ∈ (↑Q.ninefold.vertices : Set (Vertex 2))
    · simp only [ha, and_true]
      exact measurable_const.ite (measurableSet_isMaximalStopping_planarGoodCubes Q)
        measurable_const
    · simp only [ha, and_false, if_false]
      exact measurable_const
  have hterm : ∀ Q : TriadicCube 2,
      ∫⁻ ω, (if Q.IsMaximalStopping (planarGoodCubes ω) ∧
        a ∈ (↑Q.ninefold.vertices : Set (Vertex 2)) then (3 : ℝ≥0∞) ^ (m * Q.scale) else 0)
        ∂(latticeBondLaw 2 p) ≤
      if a ∈ (↑Q.ninefold.vertices : Set (Vertex 2)) then b Q.scale else 0 := by
    intro Q
    by_cases ha : a ∈ (↑Q.ninefold.vertices : Set (Vertex 2))
    · simp only [ha, and_true, if_true]
      have hfun : (fun ω : Configuration 2 => if Q.IsMaximalStopping (planarGoodCubes ω) then
          (3 : ℝ≥0∞) ^ (m * Q.scale) else 0) =
          {ω | Q.IsMaximalStopping (planarGoodCubes ω)}.indicator
            (fun _ => (3 : ℝ≥0∞) ^ (m * Q.scale)) := by
        funext ω
        simp only [Set.indicator_apply, Set.mem_setOf_eq]
      rw [hfun, lintegral_indicator_const (measurableSet_isMaximalStopping_planarGoodCubes Q)]
      show _ ≤ (3 : ℝ≥0∞) ^ (m * Q.scale) *
        ENNReal.ofReal (2 * Real.exp (-((3 : ℝ) ^ Q.scale / θ)))
      gcongr
      exact hQ Q
    · simp only [ha, and_false, if_false, lintegral_zero, le_refl]
  have hb : ∀ s : ℕ, b s ≤ ENNReal.ofReal K * 3⁻¹ ^ s := by
    intro s
    have hreal := three_pow_mul_exp_neg_le hθ m s
    calc b s = ENNReal.ofReal ((3 : ℝ) ^ (m * s) * (2 * Real.exp (-((3 : ℝ) ^ s / θ)))) := by
          simp only [b]
          rw [ENNReal.ofReal_mul (p := (3 : ℝ) ^ (m * s)) (by positivity),
            ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 3), ENNReal.ofReal_ofNat]
      _ ≤ ENNReal.ofReal (K * (1 / 3) ^ s) := ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal K * 3⁻¹ ^ s := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num), one_div,
            ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
  let e : ℕ × (Fin 2 → ℤ) ≃ TriadicCube 2 :=
    { toFun := fun q => ⟨q.1, q.2⟩
      invFun := fun Q => (Q.scale, Q.index)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [lintegral_tsum fun Q => (hmeas Q).aemeasurable]
  calc ∑' Q : TriadicCube 2, ∫⁻ ω, (if Q.IsMaximalStopping (planarGoodCubes ω) ∧
          a ∈ (↑Q.ninefold.vertices : Set (Vertex 2)) then (3 : ℝ≥0∞) ^ (m * Q.scale) else 0)
          ∂(latticeBondLaw 2 p)
      ≤ ∑' Q : TriadicCube 2,
          (if a ∈ (↑Q.ninefold.vertices : Set (Vertex 2)) then b Q.scale else 0) :=
        ENNReal.tsum_le_tsum hterm
    _ = ∑' q : ℕ × (Fin 2 → ℤ),
          (if a ∈ (↑(TriadicCube.ninefold ⟨q.1, q.2⟩).vertices : Set (Vertex 2)) then b q.1
            else 0) :=
        (e.tsum_eq (fun Q => if a ∈ (↑Q.ninefold.vertices : Set (Vertex 2)) then b Q.scale
          else 0)).symm
    _ = ∑' s : ℕ, ∑' idx : Fin 2 → ℤ,
          (if a ∈ (↑(TriadicCube.ninefold ⟨s, idx⟩).vertices : Set (Vertex 2)) then b s
            else 0) :=
        ENNReal.tsum_prod (f := fun s idx =>
          if a ∈ (↑(TriadicCube.ninefold ⟨s, idx⟩).vertices : Set (Vertex 2)) then b s else 0)
    _ ≤ ∑' s : ℕ, 121 * (ENNReal.ofReal K * 3⁻¹ ^ s) :=
        ENNReal.tsum_le_tsum fun s =>
          (tsum_ninefold_indicator_le a s (b s)).trans (by gcongr; exact hb s)
    _ = 121 * (ENNReal.ofReal K * (1 - 3⁻¹)⁻¹) := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ENNReal.tsum_geometric]

/-- **Moments of the reach.** Every moment of the reach of the planar partition is bounded
uniformly in the vertex. -/
theorem exists_lintegral_planarReach_pow_le {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (n : ℕ) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ a : Vertex 2,
      ∫⁻ ω, planarReach ω a ^ (n + 1) ∂(latticeBondLaw 2 p) ≤ C := by
  obtain ⟨C, hC, hle⟩ := exists_lintegral_tsum_ninefold_le hpc (n + 1)
  exact ⟨C, hC, fun a => (lintegral_mono fun ω => planarReach_pow_le ω a n).trans (hle a)⟩

end Rigidity.Percolation
