import Rigidity.Proofs.Corrector.GeneralLemmaThreeTwoStepOne
import Rigidity.Proofs.Corrector.GeneralPeriodicHeatDecay
import Rigidity.Proofs.Corrector.DarioMoments
import PercolationClusterHomogenization.Proofs.Regularity.GeneralCorrectorOsc

/-!
# Dario, Lemma 3.2, Step 2, in every dimension

Step 2 of the proof of Lemma 3.2 uses the quantitative sublinearity of the corrector (Dario,
(2.1), from Armstrong and Dario, (1.22), proved in every dimension as
`Rigidity.Proofs.Regularity.GeneralDim.correctorOscSublinear_holds`). With it, the sum of
`∇_j[χ]_{𝒫_stat^k}` along a segment of length `N` in the direction `e_j`, which telescopes to
`χ(z̄_stat(y + N e_j)) - χ(z̄_stat(y))`, has expectation `O(N^{1-δ})`; by the stationarity under
`3^k ℤᵈ`, the sum over `m` periods is `m` times the sum over one period, which therefore vanishes.

* `exists_lintegral_abs_coarseSegment_le`: `E|[χ]_𝒫(y + N e_j) - [χ]_𝒫(y)| ≤ C₂ N^{1-δ} + C₃`,
  by (1.22) where the two partition cubes have size at most `N`, and a crude second moment bound
  elsewhere;
* `exists_lintegral_abs_statSegment_le`: the same for the anchors of `𝒫_stat^k`, by Step 1;
* `statMean i k y j = E[∇_j[χ_{e_i}]_{𝒫_stat^k}(y)]`, its periodicity (`statMean_add`) and
  `sum_statMean_period_eq_zero`: its sum over a period vanishes.
-/

namespace Rigidity.Corrector.GeneralDim

open MeasureTheory Filter Set LatticeProb.Percolation Rigidity.Percolation Rigidity.External
open scoped Classical ENNReal Topology

variable {d : ℕ}

/-- `y^n e^{-a y} ≤ n! / a^n` for `y ≥ 0` and `a > 0`. -/
theorem pow_mul_exp_neg_le_factorial {a y : ℝ} (ha : 0 < a) (hy : 0 ≤ y) (n : ℕ) :
    y ^ n * Real.exp (-(a * y)) ≤ n.factorial / a ^ n := by
  have h := Real.pow_div_factorial_le_exp (a * y) (by positivity) n
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have han : 0 < a ^ n := pow_pos ha n
  rw [div_le_iff₀ hf, mul_pow] at h
  rw [le_div_iff₀ han]
  have he : Real.exp (-(a * y)) * Real.exp (a * y) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hpos := Real.exp_pos (-(a * y))
  calc y ^ n * Real.exp (-(a * y)) * a ^ n = (a ^ n * y ^ n) * Real.exp (-(a * y)) := by ring
    _ ≤ (Real.exp (a * y) * n.factorial) * Real.exp (-(a * y)) :=
        mul_le_mul_of_nonneg_right h hpos.le
    _ = n.factorial * (Real.exp (-(a * y)) * Real.exp (a * y)) := by ring
    _ = n.factorial := by rw [he, mul_one]

/-- `Y ≤ η Y² + η⁻¹` in `[0, ∞]`. -/
theorem le_ofReal_mul_rpow_two_add_inv {η : ℝ} (hη : 0 < η) (Y : ℝ≥0∞) :
    Y ≤ ENNReal.ofReal η * Y ^ (2 : ℝ) + ENNReal.ofReal η⁻¹ := by
  by_cases hY : Y ≤ ENNReal.ofReal η⁻¹
  · exact hY.trans le_add_self
  · push Not at hY
    have h1 : 1 ≤ ENNReal.ofReal η * Y := by
      calc (1 : ℝ≥0∞) = ENNReal.ofReal η * ENNReal.ofReal η⁻¹ := by
            rw [← ENNReal.ofReal_mul hη.le, mul_inv_cancel₀ hη.ne', ENNReal.ofReal_one]
        _ ≤ ENNReal.ofReal η * Y := mul_le_mul_right hY.le _
    calc Y = 1 * Y := (one_mul Y).symm
      _ ≤ ENNReal.ofReal η * Y * Y := mul_le_mul_left h1 _
      _ = ENNReal.ofReal η * Y ^ (2 : ℝ) := by rw [ENNReal.rpow_two, sq, mul_assoc]
      _ ≤ _ := le_self_add

/-- The sum over the residue classes modulo `L` of an `L`-periodic function is invariant under
translations. -/
theorem sum_residueRep_add_eq {L : ℕ} [NeZero L] {f : Vertex d → ℝ}
    (hper : ∀ y z : Vertex d, (∀ i, (L : ℤ) ∣ y i - z i) → f y = f z) (c : Vertex d) :
    ∑ w : Fin d → ZMod L, f (zdResidueRep w + c) = ∑ w : Fin d → ZMod L, f (zdResidueRep w) := by
  have h : ∀ w : Fin d → ZMod L,
      f (zdResidueRep w + c) = f (zdResidueRep (w + fun i => (c i : ZMod L))) := by
    intro w
    refine hper _ _ fun i => ?_
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp [zdResidueRep]
  rw [Finset.sum_congr rfl fun w _ => h w]
  exact Fintype.sum_equiv (Equiv.addRight _) _ _ fun w => rfl

/-- **The sums over the lines give the sum over a period**: an `L`-periodic function whose sums
over the periods of the lines in the direction `e_j` vanish has sum zero over a period. -/
theorem sum_residueRep_eq_zero_of_line {L : ℕ} [NeZero L] {f : Vertex d → ℝ}
    (hper : ∀ y z : Vertex d, (∀ i, (L : ℤ) ∣ y i - z i) → f y = f z) (j : Fin d)
    (hline : ∀ y, ∑ t ∈ Finset.range L, f (y + (t : ℤ) • LatticeProb.unit j) = 0) :
    ∑ w : Fin d → ZMod L, f (zdResidueRep w) = 0 := by
  have hL : (0 : ℝ) < L := by exact_mod_cast NeZero.pos L
  have h : (L : ℝ) * ∑ w : Fin d → ZMod L, f (zdResidueRep w) = 0 := by
    calc (L : ℝ) * ∑ w : Fin d → ZMod L, f (zdResidueRep w)
        = ∑ _t ∈ Finset.range L, ∑ w : Fin d → ZMod L, f (zdResidueRep w) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = ∑ t ∈ Finset.range L, ∑ w : Fin d → ZMod L,
            f (zdResidueRep w + (t : ℤ) • LatticeProb.unit j) :=
          Finset.sum_congr rfl fun t _ => (sum_residueRep_add_eq hper _).symm
      _ = ∑ w : Fin d → ZMod L, ∑ t ∈ Finset.range L,
            f (zdResidueRep w + (t : ℤ) • LatticeProb.unit j) := Finset.sum_comm
      _ = 0 := Finset.sum_eq_zero fun w _ => hline _
  rcases mul_eq_zero.1 h with h | h
  · exact absurd h hL.ne'
  · exact h

section Carrier

variable {G : Set (Configuration d)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent d)

/-- (1.22) for the corrector increments of the carrier. -/
theorem exists_osc_correctorDiff [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∃ s δ C : ℝ, 0 < s ∧ 0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧ ∀ (i : Fin d) (R : ℝ), 1 ≤ R →
      ∃ Z : Configuration d → ℝ, Measurable Z ∧ (∀ ω, 0 ≤ Z ω) ∧
        IsOsBond d p Z s (C * R ^ (1 - δ)) ∧
        ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G → ∀ a b : Vertex d, ω ∈ infiniteComponentEvent a →
          ω ∈ infiniteComponentEvent b → ‖latticeEuclideanEmbedding a‖ < R →
          ‖latticeEuclideanEmbedding b‖ < R →
          |correctorDiff hG hGv (Pi.single i 1) ω a b| ≤ Z ω := by
  obtain ⟨s, δ, C, hs, hδ, hδ1, hC, h⟩ :=
    Rigidity.Proofs.Regularity.GeneralDim.correctorOscSublinear_holds hd p hpc hp1
  refine ⟨s, δ, C, hs, hδ, hδ1, hC, fun i R hR => ?_⟩
  obtain ⟨Z, hZm, hZ0, hZO, hZ⟩ := h R hR
  refine ⟨Z, hZm, hZ0, hZO, ?_⟩
  filter_upwards [hZ] with ω hω hωG a b ha hb haR hbR
  obtain ⟨hu, -⟩ := hGv hωG
  have hinf := uniqueInfiniteComponent_infinite hu
  obtain ⟨ℓ, hℓ⟩ := exists_correctedPlane_of_valid (hGv hωG) hinf (Pi.single i 1)
  set a' : uniqueInfiniteComponent hu := ⟨a, (mem_uniqueInfiniteComponent_iff hu a).2 ha⟩
  set b' : uniqueInfiniteComponent hu := ⟨b, (mem_uniqueInfiniteComponent_iff hu b).2 hb⟩
  have e := correctorDiff_eq hG hGv hωG hinf hℓ a' b'
  have hq : ∑ i', |(Pi.single i (1 : ℝ) : Fin d → ℝ) i'| = 1 := by
    rw [Finset.sum_eq_single i (fun b _ hb => by rw [Pi.single_eq_of_ne hb, abs_zero])
      (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same, abs_one]
  have := hω hu (Pi.single i 1) ℓ hℓ a' b' haR hbR
  rw [hq, one_mul] at this
  change |correctorDiff hG hGv (Pi.single i 1) ω a'.val b'.val| ≤ Z ω
  rw [e]
  exact this

/-- **Dario, Lemma 3.2, Step 2, the segments for the partition**: from (1.22),
`E|[χ_{e_i}]_𝒫(y + N e_j) - [χ_{e_i}]_𝒫(y)| ≤ C₂ N^{1-δ} + C₃` for `N ≥ 1`. -/
theorem exists_lintegral_abs_coarseSegment_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ (i : Fin d) (y : Vertex d) (j : Fin d), ∃ C₂ C₃ : ℝ,
      0 ≤ C₂ ∧ 0 ≤ C₃ ∧ ∀ N : ℕ, 1 ≤ N →
        ∫⁻ ω, ENNReal.ofReal |coarseField hG hGv i 0 (y + (N : ℤ) • LatticeProb.unit j) ω -
          coarseField hG hGv i 0 y ω| ∂latticeBondLaw d p ≤
          ENNReal.ofReal (C₂ * (N : ℝ) ^ (1 - δ) + C₃) := by
  obtain ⟨Λ, A, κ, hA0, -, hΛm, hΛ0, hlip, hmom6⟩ := stepSix_data hG hGv hd hpc hp1 hGae
  obtain ⟨θ, hθ, hexp⟩ := (partition_estimates hd hpc).2.1
  obtain ⟨s, δ, C, hs, hδ, hδ1, hC, hosc⟩ := exists_osc_correctorDiff hG hGv hd hpc hp1
  have hd0 : 0 < d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  refine ⟨δ, hδ, hδ1, fun i y j => ?_⟩
  set b : ℝ := ‖latticeEuclideanEmbedding y‖ with hb
  have hb0 : 0 ≤ b := norm_nonneg _
  set CZ : ℝ := 2 * C * ((1 / s) ^ (1 / s) * Real.exp (-(1 / s))) with hCZ
  have hCZ0 : 0 ≤ CZ := by positivity
  set M : ℝ := (A * 2 ^ κ) ^ (2 : ℝ) with hM
  have hM0 : 0 ≤ M := by positivity
  refine ⟨CZ * (b + 2 * d + 1) ^ (1 - δ), 32 * M * θ ^ 2 + 4, by positivity, by positivity,
    fun N hN => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  set a' : Vertex d := y + (N : ℤ) • LatticeProb.unit j with ha'
  set R : ℝ := b + 2 * d * N + 1 with hR
  have hR1 : 1 ≤ R := by
    have : 0 ≤ 2 * d * (N : ℝ) := by positivity
    linarith
  obtain ⟨Z, hZm, hZ0, hZO, hZ⟩ := hosc i R hR1
  set F : ℕ → Configuration d → ℝ := fun t =>
    coarseField hG hGv i 0 (y + (t : ℤ) • LatticeProb.unit j) with hF
  set S : Vertex d → Configuration d → ℝ≥0∞ := stepSixSum (Λ i) with hS
  set Y : Configuration d → ℝ≥0∞ := fun ω => ∑ t ∈ Finset.range N,
    (S (y + ((t + 1 : ℕ) : ℤ) • LatticeProb.unit j) ω + S (y + (t : ℤ) • LatticeProb.unit j) ω)
    with hY
  have hYm : Measurable Y := Finset.measurable_sum _ fun t _ =>
    (measurable_stepSixSum (hΛm i) _).add (measurable_stepSixSum (hΛm i) _)
  set Gd : Set (Configuration d) := {ω | TriadicCube.stoppingSize (TriadicCube.goodCubes ω) y ≤ N ∧
    TriadicCube.stoppingSize (TriadicCube.goodCubes ω) a' ≤ N} with hGd
  have hGdm : MeasurableSet Gd :=
    (measurableSet_le (measurable_stoppingSize_goodCubes y) measurable_const).inter
      (measurableSet_le (measurable_stoppingSize_goodCubes a') measurable_const)
  set η : ℝ := Real.exp (-(1 / (2 * θ) * N)) with hη
  have hη0 : 0 < η := Real.exp_pos _
  have hall : ∀ᵐ ω ∂latticeBondLaw d p, ∀ x, ω ∈ infiniteComponentEvent x → ∀ y,
      (openGraph ω).Adj x y → |correctorDiff hG hGv (Pi.single i 1) ω x y| ≤ Λ i x ω :=
    ae_all_iff.2 fun x => hlip i x
  have he0 : y + ((0 : ℕ) : ℤ) • LatticeProb.unit j = y := by simp
  -- the crude bound
  have hcrude : ∀ᵐ ω ∂latticeBondLaw d p, ENNReal.ofReal |F N ω - F 0 ω| ≤ Y ω := by
    filter_upwards [hGae, ae_partitionEvent hd hpc, hall] with ω hω hP hl
    rw [← Finset.sum_range_sub (fun t => F t ω) N]
    refine (ENNReal.ofReal_le_ofReal (Finset.abs_sum_le_sum_abs _ _)).trans ?_
    rw [ENNReal.ofReal_sum_of_nonneg fun t _ => abs_nonneg _]
    refine Finset.sum_le_sum fun t _ => ?_
    have e : y + ((t + 1 : ℕ) : ℤ) • LatticeProb.unit j =
        (y + (t : ℤ) • LatticeProb.unit j) + LatticeProb.unit j := by
      push_cast
      rw [add_smul, one_smul, add_assoc]
    simp only [hF]
    rw [e]
    have h := ofReal_abs_coarseField_step_le hG hGv hd0 hω hP (Λ := Λ i) (fun x => hΛ0 i x ω) hl
      (y + (t : ℤ) • LatticeProb.unit j) j
    rw [← e] at h ⊢
    exact h
  -- the pointwise bound
  have hpt : ∀ᵐ ω ∂latticeBondLaw d p, ENNReal.ofReal |F N ω - F 0 ω| ≤
      ENNReal.ofReal (Z ω) + (ENNReal.ofReal η * Y ω ^ (2 : ℝ) +
        ENNReal.ofReal η⁻¹ * Gdᶜ.indicator 1 ω) := by
    filter_upwards [hGae, ae_partitionEvent hd hpc, hZ, hcrude] with ω hω hP hZω hcr
    have hinf := infinite_partitionAnchor hd0 hP
    by_cases hg : ω ∈ Gd
    · obtain ⟨hg1, hg2⟩ := hg
      have hA0 : ∀ v, shiftedAnchor 0 ω v = partitionAnchor ω v := fun v => by
        rw [shiftedAnchor_zero, guardAnchor_of_event hP]
      have hFD : F N ω - F 0 ω =
          correctorDiff hG hGv (Pi.single i 1) ω (partitionAnchor ω a') (partitionAnchor ω y) := by
        simp only [hF, coarseField, hA0]
        rw [he0]
        exact correctorDiff_sub_eq hG hGv hω (hinf _) (hinf _) (hinf _)
      have hnorm : ∀ v : Vertex d, TriadicCube.stoppingSize (TriadicCube.goodCubes ω) v ≤ N →
          ‖latticeEuclideanEmbedding (partitionAnchor ω v)‖ ≤
            ‖latticeEuclideanEmbedding v‖ + d * N := by
        intro v hv
        have h1 := norm_le_insert' (latticeEuclideanEmbedding (partitionAnchor ω v))
          (latticeEuclideanEmbedding v)
        rw [← LatticeProb.Percolation.latticeEuclideanEmbedding_sub] at h1
        have h2 : ‖latticeEuclideanEmbedding (partitionAnchor ω v - v)‖ ≤ d * N :=
          norm_latticeEuclideanEmbedding_le_of_abs_le (by positivity) fun k => by
            rw [Pi.sub_apply]
            exact (abs_partitionAnchor_sub_le hP v k).trans hv
        linarith
      have hya : ‖latticeEuclideanEmbedding a'‖ ≤ b + d * N := by
        have h1 := norm_le_insert' (latticeEuclideanEmbedding a') (latticeEuclideanEmbedding y)
        rw [← LatticeProb.Percolation.latticeEuclideanEmbedding_sub] at h1
        have e : a' - y = (N : ℤ) • LatticeProb.unit j := by rw [ha']; abel
        have h2 : ‖latticeEuclideanEmbedding (a' - y)‖ ≤ d * N := by
          rw [e]
          refine norm_latticeEuclideanEmbedding_le_of_abs_le (by positivity) fun k => ?_
          by_cases hk : k = j
          · subst hk
            simp [LatticeProb.unit]
          · simp [LatticeProb.unit, Pi.single_eq_of_ne hk]
        linarith
      have hDZ : |F N ω - F 0 ω| ≤ Z ω := by
        rw [hFD]
        have h1 := hnorm a' hg2
        have h2 := hnorm y hg1
        have : (0 : ℝ) ≤ d * N := by positivity
        exact hZω hω _ _ (hinf _) (hinf _) (by linarith) (by linarith)
      calc ENNReal.ofReal |F N ω - F 0 ω| ≤ ENNReal.ofReal (Z ω) := ENNReal.ofReal_le_ofReal hDZ
        _ ≤ _ := le_self_add
    · rw [Set.indicator_of_mem (show ω ∈ Gdᶜ from hg), Pi.one_apply, mul_one]
      exact hcr.trans ((le_ofReal_mul_rpow_two_add_inv hη0 (Y ω)).trans le_add_self)
  -- the expectation of `Z`
  have hθR : 0 < C * R ^ (1 - δ) := by positivity
  obtain ⟨hZi, hZle⟩ := IsOsBond.integral_rpow_le hs hθR one_pos hZm hZ0 hZO
  simp only [Real.rpow_one] at hZi hZle
  have hEZ : ∫⁻ ω, ENNReal.ofReal (Z ω) ∂latticeBondLaw d p ≤
      ENNReal.ofReal (CZ * R ^ (1 - δ)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hZi (Eventually.of_forall hZ0)]
    refine ENNReal.ofReal_le_ofReal (hZle.trans_eq ?_)
    rw [hCZ]
    ring
  -- the second moment of the crude bound
  have hS2 : ∀ v, ∫⁻ ω, S v ω ^ (2 : ℝ) ∂latticeBondLaw d p ≤ ENNReal.ofReal M := fun v =>
    hmom6 i v 2 (by norm_num)
  have hY2 : ∫⁻ ω, Y ω ^ (2 : ℝ) ∂latticeBondLaw d p ≤ ENNReal.ofReal (4 * M * (N : ℝ) ^ 2) := by
    have hpt2 : ∀ ω, Y ω ^ (2 : ℝ) ≤ (N : ℝ≥0∞) * ∑ t ∈ Finset.range N,
        2 * (S (y + ((t + 1 : ℕ) : ℤ) • LatticeProb.unit j) ω ^ (2 : ℝ) +
          S (y + (t : ℤ) • LatticeProb.unit j) ω ^ (2 : ℝ)) := by
      intro ω
      have h1 := ENNReal.rpow_sum_le_const_mul_sum_rpow (s := Finset.range N)
        (f := fun t => S (y + ((t + 1 : ℕ) : ℤ) • LatticeProb.unit j) ω +
          S (y + (t : ℤ) • LatticeProb.unit j) ω) (p := 2) (by norm_num)
      rw [show (2 : ℝ) - 1 = 1 by norm_num, ENNReal.rpow_one, Finset.card_range] at h1
      refine h1.trans (mul_le_mul_right (Finset.sum_le_sum fun t _ => ?_) _)
      have h2 := ENNReal.rpow_add_le_mul_rpow_add_rpow
        (S (y + ((t + 1 : ℕ) : ℤ) • LatticeProb.unit j) ω)
        (S (y + (t : ℤ) • LatticeProb.unit j) ω) (by norm_num : (1 : ℝ) ≤ 2)
      rw [show (2 : ℝ) - 1 = 1 by norm_num, ENNReal.rpow_one] at h2
      exact h2
    calc ∫⁻ ω, Y ω ^ (2 : ℝ) ∂latticeBondLaw d p
        ≤ ∫⁻ ω, (N : ℝ≥0∞) * ∑ t ∈ Finset.range N,
            2 * (S (y + ((t + 1 : ℕ) : ℤ) • LatticeProb.unit j) ω ^ (2 : ℝ) +
              S (y + (t : ℤ) • LatticeProb.unit j) ω ^ (2 : ℝ)) ∂latticeBondLaw d p :=
          lintegral_mono hpt2
      _ = (N : ℝ≥0∞) * ∑ t ∈ Finset.range N,
            2 * (∫⁻ ω, S (y + ((t + 1 : ℕ) : ℤ) • LatticeProb.unit j) ω ^ (2 : ℝ)
              ∂latticeBondLaw d p +
              ∫⁻ ω, S (y + (t : ℤ) • LatticeProb.unit j) ω ^ (2 : ℝ) ∂latticeBondLaw d p) := by
          have hm2 : ∀ v, Measurable fun ω => S v ω ^ (2 : ℝ) := fun v =>
            (measurable_stepSixSum (hΛm i) v).pow_const _
          have hmt : ∀ t : ℕ, Measurable fun ω =>
              2 * (S (y + ((t + 1 : ℕ) : ℤ) • LatticeProb.unit j) ω ^ (2 : ℝ) +
                S (y + (t : ℤ) • LatticeProb.unit j) ω ^ (2 : ℝ)) := fun t =>
            ((hm2 _).add (hm2 _)).const_mul _
          rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top N),
            lintegral_finsetSum _ fun t _ => hmt t]
          refine congrArg _ (Finset.sum_congr rfl fun t _ => ?_)
          rw [lintegral_const_mul' _ _ (by norm_num),
            lintegral_add_left (hm2 _)]
      _ ≤ (N : ℝ≥0∞) * ∑ _t ∈ Finset.range N, 2 * (ENNReal.ofReal M + ENNReal.ofReal M) := by
          gcongr with t ht
          · exact hS2 _
          · exact hS2 _
      _ = ENNReal.ofReal (4 * M * (N : ℝ) ^ 2) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_add hM0 hM0,
            ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
  -- the probability of the bad event
  have hbad : latticeBondLaw d p Gdᶜ ≤ ENNReal.ofReal (4 * Real.exp (-((N : ℝ) / (1 * θ)))) := by
    have hsub : Gdᶜ ⊆ {ω | (N : ℝ) ≤ 1 * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) y} ∪
        {ω | (N : ℝ) ≤ 1 * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) a'} := by
      intro ω hω
      simp only [hGd, Set.mem_compl_iff, Set.mem_setOf_eq, not_and_or, not_le] at hω
      rcases hω with h | h
      · left
        change (N : ℝ) ≤ 1 * _
        linarith
      · right
        change (N : ℝ) ≤ 1 * _
        linarith
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
    have h1 := measure_le_const_mul_stoppingSize_le hθ one_pos y (hexp y).1 (hexp y).2 N
    have h2 := measure_le_const_mul_stoppingSize_le hθ one_pos a' (hexp a').1 (hexp a').2 N
    refine (add_le_add h1 h2).trans ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (le_of_eq (by ring))
  -- the conclusion
  have hgoal : ∫⁻ ω, ENNReal.ofReal |coarseField hG hGv i 0 (y + (N : ℤ) • LatticeProb.unit j) ω -
      coarseField hG hGv i 0 y ω| ∂latticeBondLaw d p =
      ∫⁻ ω, ENNReal.ofReal |F N ω - F 0 ω| ∂latticeBondLaw d p := by
    simp only [hF]
    rw [he0]
  rw [hgoal]
  calc ∫⁻ ω, ENNReal.ofReal |F N ω - F 0 ω| ∂latticeBondLaw d p
      ≤ ∫⁻ ω, (ENNReal.ofReal (Z ω) + (ENNReal.ofReal η * Y ω ^ (2 : ℝ) +
          ENNReal.ofReal η⁻¹ * Gdᶜ.indicator 1 ω)) ∂latticeBondLaw d p := lintegral_mono_ae hpt
    _ = ∫⁻ ω, ENNReal.ofReal (Z ω) ∂latticeBondLaw d p +
          (ENNReal.ofReal η * ∫⁻ ω, Y ω ^ (2 : ℝ) ∂latticeBondLaw d p +
            ENNReal.ofReal η⁻¹ * latticeBondLaw d p Gdᶜ) := by
        rw [lintegral_add_left hZm.ennreal_ofReal,
          lintegral_add_left ((hYm.pow_const _).const_mul _),
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_indicator_one hGdm.compl]
    _ ≤ ENNReal.ofReal (CZ * R ^ (1 - δ)) + (ENNReal.ofReal η * ENNReal.ofReal (4 * M * (N : ℝ) ^ 2) +
          ENNReal.ofReal η⁻¹ * ENNReal.ofReal (4 * Real.exp (-((N : ℝ) / (1 * θ))))) := by
        gcongr
    _ = ENNReal.ofReal (CZ * R ^ (1 - δ) + (4 * M * ((N : ℝ) ^ 2 * η) + 4 * η)) := by
        have hinv : η⁻¹ * (4 * Real.exp (-((N : ℝ) / (1 * θ)))) = 4 * η := by
          rw [hη, ← Real.exp_neg, mul_left_comm, ← Real.exp_add]
          congr 2
          field_simp
          ring
        rw [← ENNReal.ofReal_mul hη0.le, ← ENNReal.ofReal_mul (inv_pos.2 hη0).le, hinv,
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
    _ ≤ ENNReal.ofReal (CZ * (b + 2 * d + 1) ^ (1 - δ) * (N : ℝ) ^ (1 - δ) +
          (32 * M * θ ^ 2 + 4)) := by
        refine ENNReal.ofReal_le_ofReal (add_le_add ?_ ?_)
        · have hRle : R ≤ (b + 2 * d + 1) * N := by nlinarith
          have h1 : R ^ (1 - δ) ≤ ((b + 2 * d + 1) * N) ^ (1 - δ) :=
            Real.rpow_le_rpow (by linarith) hRle (by linarith)
          rw [Real.mul_rpow (by positivity) (by positivity)] at h1
          calc CZ * R ^ (1 - δ) ≤ CZ * ((b + 2 * d + 1) ^ (1 - δ) * (N : ℝ) ^ (1 - δ)) :=
                mul_le_mul_of_nonneg_left h1 hCZ0
            _ = _ := by ring
        · have hf := pow_mul_exp_neg_le_factorial (a := 1 / (2 * θ)) (y := (N : ℝ))
            (by positivity) hN0.le 2
          have hfe : (Nat.factorial 2 : ℝ) / (1 / (2 * θ)) ^ 2 = 8 * θ ^ 2 := by
            rw [Nat.factorial_two]
            field_simp
            norm_num
          rw [hfe] at hf
          have hη1 : η ≤ 1 := Real.exp_le_one_iff.2 (by
            have : 0 ≤ 1 / (2 * θ) * (N : ℝ) := by positivity
            linarith)
          have : 4 * M * ((N : ℝ) ^ 2 * η) ≤ 4 * M * (8 * θ ^ 2) :=
            mul_le_mul_of_nonneg_left hf (by positivity)
          linarith

/-- The coarsened corrector of `𝒫_stat^k` in terms of that of the partition:
`χ(z̄_stat(a)) - χ(z̄_stat(b)) = ε(a) + ([χ]_𝒫(a) - [χ]_𝒫(b)) - ε(b)`. -/
theorem correctorDiff_statAnchor_eq (hd : 0 < d) {ω : Configuration d} (hω : ω ∈ G)
    (hP : PartitionEvent ω) (i : Fin d) (k : ℕ) (a b : Vertex d) :
    correctorDiff hG hGv (Pi.single i 1) ω (statAnchor k ω a) (statAnchor k ω b) =
      statDiscrepancy hG hGv i k a ω +
        (coarseField hG hGv i 0 a ω - coarseField hG hGv i 0 b ω) -
        statDiscrepancy hG hGv i k b ω := by
  have hinf := infinite_partitionAnchor hd hP
  have hsa := statAnchor_mem_inf k a (hinf 0)
  have hsb := statAnchor_mem_inf k b (hinf 0)
  have hA0 : ∀ v, shiftedAnchor 0 ω v = partitionAnchor ω v := fun v => by
    rw [shiftedAnchor_zero, guardAnchor_of_event hP]
  simp only [statDiscrepancy, coarseField, hA0, guardAnchor_of_event hP]
  rw [correctorDiff_sub_eq hG hGv hω (hinf a) (hinf b) (hinf 0),
    correctorDiff_add' hG hGv hω hsa (hinf a) hsb,
    correctorDiff_add' hG hGv hω (hinf a) (hinf b) hsb,
    correctorDiff_swap' hG hGv hω hsb (hinf b)]
  ring

/-- **Dario, Lemma 3.2, Step 2, the segments**: from (1.22) and Step 1,
`E|χ(z̄_stat(y + N e_j)) - χ(z̄_stat(y))| ≤ C₂ N^{1-δ} + C₃` for `N ≥ 1`. -/
theorem exists_lintegral_abs_statSegment_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ (i : Fin d) (k : ℕ) (y : Vertex d) (j : Fin d), ∃ C₂ C₃ : ℝ,
      0 ≤ C₂ ∧ 0 ≤ C₃ ∧ ∀ N : ℕ, 1 ≤ N →
        ∫⁻ ω, ENNReal.ofReal |correctorDiff hG hGv (Pi.single i 1) ω
          (statAnchor k ω (y + (N : ℤ) • LatticeProb.unit j)) (statAnchor k ω y)|
          ∂latticeBondLaw d p ≤ ENNReal.ofReal (C₂ * (N : ℝ) ^ (1 - δ) + C₃) := by
  obtain ⟨δ, hδ, hδ1, hseg⟩ := exists_lintegral_abs_coarseSegment_le hG hGv hd hpc hp1 hGae
  obtain ⟨K, c, θ₀, hK, hc, hθ₀, hε⟩ :=
    exists_lintegral_abs_statDiscrepancy_le hG hGv hd hpc hp1 hGae
  have hd0 : 0 < d := by omega
  refine ⟨δ, hδ, hδ1, fun i k y j => ?_⟩
  obtain ⟨C₂, C₃, hC₂, hC₃, hb⟩ := hseg i y j
  set B : ℝ := K * (1 + θ₀ * ((3 : ℝ) ^ k) ^ d) ^ (2 * d) * Real.exp (-(c * 3 ^ k / 2)) with hB
  have hB0 : 0 ≤ B := by positivity
  refine ⟨C₂, C₃ + 2 * B, hC₂, by positivity, fun N hN => ?_⟩
  set a' := y + (N : ℤ) • LatticeProb.unit j with ha'
  calc ∫⁻ ω, ENNReal.ofReal |correctorDiff hG hGv (Pi.single i 1) ω (statAnchor k ω a')
        (statAnchor k ω y)| ∂latticeBondLaw d p
      ≤ ∫⁻ ω, (ENNReal.ofReal |statDiscrepancy hG hGv i k a' ω| +
          ENNReal.ofReal |coarseField hG hGv i 0 a' ω - coarseField hG hGv i 0 y ω| +
          ENNReal.ofReal |statDiscrepancy hG hGv i k y ω|) ∂latticeBondLaw d p := by
        refine lintegral_mono_ae ?_
        filter_upwards [hGae, ae_partitionEvent hd hpc] with ω hω hP
        rw [correctorDiff_statAnchor_eq hG hGv hd0 hω hP i k a' y,
          ← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _),
          ← ENNReal.ofReal_add (by positivity) (abs_nonneg _)]
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 := abs_add_le (statDiscrepancy hG hGv i k a' ω +
          (coarseField hG hGv i 0 a' ω - coarseField hG hGv i 0 y ω))
          (-statDiscrepancy hG hGv i k y ω)
        have h2 := abs_add_le (statDiscrepancy hG hGv i k a' ω)
          (coarseField hG hGv i 0 a' ω - coarseField hG hGv i 0 y ω)
        rw [abs_neg, ← sub_eq_add_neg] at h1
        linarith
    _ = ∫⁻ ω, ENNReal.ofReal |statDiscrepancy hG hGv i k a' ω| ∂latticeBondLaw d p +
          ∫⁻ ω, ENNReal.ofReal |coarseField hG hGv i 0 a' ω - coarseField hG hGv i 0 y ω|
            ∂latticeBondLaw d p +
          ∫⁻ ω, ENNReal.ofReal |statDiscrepancy hG hGv i k y ω| ∂latticeBondLaw d p := by
        have m1 : Measurable fun ω => ENNReal.ofReal |statDiscrepancy hG hGv i k y ω| :=
          (measurable_statDiscrepancy hG hGv i k y).abs.ennreal_ofReal
        have m2 : Measurable fun ω =>
            ENNReal.ofReal |coarseField hG hGv i 0 a' ω - coarseField hG hGv i 0 y ω| :=
          ((measurable_coarseField hG hGv i 0 a').sub
            (measurable_coarseField hG hGv i 0 y)).abs.ennreal_ofReal
        rw [lintegral_add_right _ m1, lintegral_add_right _ m2]
    _ ≤ ENNReal.ofReal B + ENNReal.ofReal (C₂ * (N : ℝ) ^ (1 - δ) + C₃) + ENNReal.ofReal B := by
        gcongr
        · exact hε i k a'
        · exact hb N hN
        · exact hε i k y
    _ = ENNReal.ofReal (C₂ * (N : ℝ) ^ (1 - δ) + (C₃ + 2 * B)) := by
        rw [← ENNReal.ofReal_add hB0 (by positivity), ← ENNReal.ofReal_add (by positivity) hB0]
        congr 1
        ring

/-- **The telescoping of the coarsened gradient** along the segment `y, y + e_j, …, y + N e_j`. -/
theorem sum_statGrad_eq {ω : Configuration d} (hω : ω ∈ G) {v₀ : Vertex d}
    (h₀ : ω ∈ infiniteComponentEvent v₀) (i : Fin d) (k : ℕ) (y : Vertex d) (j : Fin d) (N : ℕ) :
    ∑ t ∈ Finset.range N, statGrad hG hGv i k (y + (t : ℤ) • LatticeProb.unit j) j ω =
      correctorDiff hG hGv (Pi.single i 1) ω (statAnchor k ω (y + (N : ℤ) • LatticeProb.unit j))
        (statAnchor k ω y) := by
  induction N with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, zero_smul, add_zero]
    have hb := statAnchor_mem_inf k y h₀
    have := correctorDiff_sub_eq hG hGv (q := Pi.single i 1) hω hb hb hb
    linarith
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    unfold statGrad
    have e : y + ((N + 1 : ℕ) : ℤ) • LatticeProb.unit j =
        y + (N : ℤ) • LatticeProb.unit j + LatticeProb.unit j := by
      push_cast
      rw [add_smul, one_smul, add_assoc]
    rw [e]
    have h1 := statAnchor_mem_inf k (y + (N : ℤ) • LatticeProb.unit j + LatticeProb.unit j) h₀
    have h2 := statAnchor_mem_inf k (y + (N : ℤ) • LatticeProb.unit j) h₀
    have h3 := statAnchor_mem_inf k y h₀
    rw [correctorDiff_add' hG hGv hω h1 h2 h3]
    ring

/-- The mean `E[∇_j[χ_{e_i}]_{𝒫_stat^k}(y)]` of the stationary coarsened gradient. -/
noncomputable def statMean (p : unitInterval) (i : Fin d) (k : ℕ) (y : Vertex d) (j : Fin d) : ℝ :=
  ∫ ω, statGrad hG hGv i k y j ω ∂latticeBondLaw d p

theorem ae_translation_mem {p : unitInterval} (hGae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G)
    (c : Vertex d) : ∀ᵐ ω ∂latticeBondLaw d p, configurationTranslation c ω ∈ G :=
  (measurePreserving_configurationTranslation p c).quasiMeasurePreserving.ae hGae

/-- **The mean is periodic** (Dario, Lemma 3.2, Step 3: `f` is `3^k ℤᵈ`-periodic). -/
theorem statMean_add [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hGae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) (i : Fin d)
    {k : ℕ} {c : Vertex d} (hc : ∀ i, (3 : ℤ) ^ k ∣ c i) (y : Vertex d) (j : Fin d) :
    statMean hG hGv p i k (y + c) j = statMean hG hGv p i k y j := by
  unfold statMean
  rw [← (measurePreserving_configurationTranslation p c).integral_comp
    (configurationTranslationMeasurableEquiv c).measurableEmbedding]
  refine integral_congr_ae ?_
  filter_upwards [hGae, ae_translation_mem hGae c, ae_partitionEvent hd hpc] with ω hω hω' hP
  exact statGrad_translation hG hGv hc hω hω' (infinite_partitionAnchor (by omega) hP 0) y j

/-- The stationary coarsened gradient is integrable (the segment bound for `N = 1`). -/
theorem integrable_statGrad [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) (i : Fin d) (k : ℕ) (y : Vertex d) (j : Fin d) :
    Integrable (statGrad hG hGv i k y j) (latticeBondLaw d p) := by
  obtain ⟨δ, -, -, hseg⟩ := exists_lintegral_abs_statSegment_le hG hGv hd hpc hp1 hGae
  obtain ⟨C₂, C₃, -, -, hb⟩ := hseg i k y j
  have h := hb 1 le_rfl
  simp only [Nat.cast_one, one_smul] at h
  refine ⟨(measurable_statGrad hG hGv i k y j).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  simp_rw [Real.enorm_eq_ofReal_abs]
  exact lt_of_le_of_lt h ENNReal.ofReal_lt_top

/-- **Dario, Lemma 3.2, Step 2, along a line**: from (1.22), the sum of the mean of the
stationary coarsened gradient over a period of a line in the direction `e_j` vanishes. -/
theorem sum_statMean_line_eq_zero [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) (i : Fin d) (k : ℕ) (y₀ : Vertex d) (j : Fin d) :
    ∑ t ∈ Finset.range (3 ^ k), statMean hG hGv p i k (y₀ + (t : ℤ) • LatticeProb.unit j) j =
      0 := by
  obtain ⟨δ, hδ, -, hseg⟩ := exists_lintegral_abs_statSegment_le hG hGv hd hpc hp1 hGae
  obtain ⟨C₂, C₃, hC₂, hC₃, hb⟩ := hseg i k y₀ j
  set L : ℕ := 3 ^ k with hL
  have hL1 : 1 ≤ L := Nat.one_le_pow _ _ (by norm_num)
  set S := ∑ t ∈ Finset.range L, statMean hG hGv p i k (y₀ + (t : ℤ) • LatticeProb.unit j) j
    with hS
  have hint := integrable_statGrad hG hGv hd hpc hp1 hGae i k
  have hblock : ∀ m : ℕ, ∑ t ∈ Finset.range (m * L),
      statMean hG hGv p i k (y₀ + (t : ℤ) • LatticeProb.unit j) j = m * S := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [show (m + 1) * L = m * L + L by ring, Finset.sum_range_add, ih]
      have hper : ∀ t : ℕ, statMean hG hGv p i k (y₀ + ((m * L + t : ℕ) : ℤ) •
          LatticeProb.unit j) j = statMean hG hGv p i k (y₀ + (t : ℤ) • LatticeProb.unit j) j := by
        intro t
        have e : y₀ + ((m * L + t : ℕ) : ℤ) • LatticeProb.unit j =
            (y₀ + (t : ℤ) • LatticeProb.unit j) + ((m * L : ℕ) : ℤ) • LatticeProb.unit j := by
          push_cast
          rw [add_smul]
          abel
        rw [e]
        refine statMean_add hG hGv hd hpc hGae i (fun i' => ?_) _ j
        simp only [Pi.smul_apply, smul_eq_mul]
        exact Dvd.dvd.mul_right (by rw [hL]; push_cast; exact dvd_mul_left _ _) _
      simp_rw [hper]
      push_cast
      ring
  have hsum : ∀ N : ℕ, ∑ t ∈ Finset.range N,
      statMean hG hGv p i k (y₀ + (t : ℤ) • LatticeProb.unit j) j =
      ∫ ω, correctorDiff hG hGv (Pi.single i 1) ω
        (statAnchor k ω (y₀ + (N : ℤ) • LatticeProb.unit j)) (statAnchor k ω y₀)
        ∂latticeBondLaw d p := by
    intro N
    unfold statMean
    rw [← integral_finsetSum _ fun t _ => hint _ j]
    refine integral_congr_ae ?_
    filter_upwards [hGae, ae_partitionEvent hd hpc] with ω hω hP
    exact sum_statGrad_eq hG hGv hω (infinite_partitionAnchor (by omega) hP 0) i k y₀ j N
  have hbound : ∀ m : ℕ, 1 ≤ m → (m : ℝ) * |S| ≤ C₂ * ((m * L : ℕ) : ℝ) ^ (1 - δ) + C₃ := by
    intro m hm
    have hmL : 1 ≤ m * L := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
    have h1 := hb (m * L) hmL
    have h2 := norm_integral_le_lintegral_norm (μ := latticeBondLaw d p) (fun ω =>
      correctorDiff hG hGv (Pi.single i 1) ω
        (statAnchor k ω (y₀ + ((m * L : ℕ) : ℤ) • LatticeProb.unit j)) (statAnchor k ω y₀))
    simp only [Real.norm_eq_abs] at h2
    rw [← hsum, hblock, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ m)] at h2
    exact h2.trans (ENNReal.toReal_le_of_le_ofReal (by positivity) h1)
  have hle : ∀ᶠ m : ℕ in atTop, |S| ≤ C₂ * (L : ℝ) ^ (1 - δ) * (m : ℝ) ^ (-δ) + C₃ / m := by
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    have h := hbound m hm
    rw [show ((m * L : ℕ) : ℝ) = (m : ℝ) * L by push_cast; ring,
      Real.mul_rpow hm0.le (by positivity)] at h
    have e : (m : ℝ) ^ (-δ) = (m : ℝ) ^ (1 - δ) / m := by
      rw [← Real.rpow_sub_one hm0.ne']
      ring_nf
    rw [e, mul_div_assoc', ← add_div, le_div_iff₀ hm0]
    linarith
  have hlim : Tendsto (fun m : ℕ => C₂ * (L : ℝ) ^ (1 - δ) * (m : ℝ) ^ (-δ) + C₃ / m) atTop
      (𝓝 0) := by
    have h1 : Tendsto (fun m : ℕ => (m : ℝ) ^ (-δ)) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop hδ).comp tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun m : ℕ => C₃ / (m : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat C₃
    simpa using (h1.const_mul (C₂ * (L : ℝ) ^ (1 - δ))).add h2
  have h0 := ge_of_tendsto hlim hle
  exact abs_nonpos_iff.1 h0

/-- **Dario, Lemma 3.2, Step 2**: from (1.22), the sum of the mean of the stationary coarsened
gradient over a period vanishes. -/
theorem sum_statMean_period_eq_zero [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) (i : Fin d) (k : ℕ) (j : Fin d) :
    ∑ w : Fin d → ZMod (3 ^ k), statMean hG hGv p i k (zdResidueRep w) j = 0 := by
  haveI : NeZero (3 ^ k) := ⟨pow_ne_zero k (by norm_num)⟩
  refine sum_residueRep_eq_zero_of_line (f := fun y => statMean hG hGv p i k y j) ?_ j
    (sum_statMean_line_eq_zero hG hGv hd hpc hp1 hGae i k · j)
  intro y z h
  have h' := statMean_add hG hGv hd hpc hGae i (k := k) (c := y - z)
    (fun i' => by have := h i'; push_cast at this; exact this) z j
  have e : z + (y - z) = y := by abel
  rw [e] at h'
  exact h'

end Carrier

end Rigidity.Corrector.GeneralDim
