import Rigidity.Proofs.Corrector.DarioLemmaThreeTwoStepTwo
import Rigidity.Proofs.Corrector.PeriodicHeatDecay

/-!
# Dario, Lemma 3.2, Step 2: the mean of the stationary coarsened gradient

`statMean i k y j = E[∇_j[χ_{e_i}]_{𝒫_stat^k}(y)]` is `3^k`-periodic (`statMean_add`, from the
stationarity of the coarsened corrector and the invariance of the bond law under translations),
and by (1.22) its sum over a period vanishes (`sum_statMean_period_eq_zero`): the sum over `m`
periods along a line is `m` times the sum over one period, and is the expectation of the
telescoped increment over a segment of length `m 3^k`, which is `O((m 3^k)^{1-δ})`.
-/

namespace Rigidity.Corrector

open MeasureTheory Filter Set LatticeProb.Percolation Rigidity.Percolation Rigidity.External
open scoped Classical ENNReal Topology

section Carrier

variable {G : Set (Configuration 2)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2)

/-- The mean `E[∇_j[χ_{e_i}]_{𝒫_stat^k}(y)]` of the stationary coarsened gradient. -/
noncomputable def statMean (p : unitInterval) (i : Fin 2) (k : ℕ) (y : Vertex 2) (j : Fin 2) : ℝ :=
  ∫ ω, statGrad hG hGv i k y j ω ∂latticeBondLaw 2 p

theorem ae_translation_mem {p : unitInterval} (hGae : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G)
    (c : Vertex 2) : ∀ᵐ ω ∂latticeBondLaw 2 p, configurationTranslation c ω ∈ G :=
  (measurePreserving_configurationTranslation p c).quasiMeasurePreserving.ae hGae

/-- **The mean is periodic** (Dario, Lemma 3.2, Step 3: `f` is `3^k ℤ²`-periodic). -/
theorem statMean_add {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (hGae : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G) (i : Fin 2) {k : ℕ} {c : Vertex 2}
    (hc : ∀ i, (3 : ℤ) ^ k ∣ c i) (y : Vertex 2) (j : Fin 2) :
    statMean hG hGv p i k (y + c) j = statMean hG hGv p i k y j := by
  unfold statMean
  rw [← (measurePreserving_configurationTranslation p c).integral_comp
    (configurationTranslationMeasurableEquiv c).measurableEmbedding]
  refine integral_congr_ae ?_
  filter_upwards [hGae, ae_translation_mem hGae c, ae_planarPartitionEvent hpc] with ω hω hω' hP
  exact statGrad_translation hG hGv hc hω hω' (infinite_planarCoarseAnchor hP 0) y j

/-- The stationary coarsened gradient is integrable (the segment bound for `N = 1`). -/
theorem integrable_statGrad (hR3 : ArmstrongDarioOrderZeroTwo) (h122 : CorrectorOscSublinearTwo)
    {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGae : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G) (i : Fin 2) (k : ℕ) (y : Vertex 2) (j : Fin 2) :
    Integrable (statGrad hG hGv i k y j) (latticeBondLaw 2 p) := by
  obtain ⟨δ, -, -, hseg⟩ := exists_lintegral_abs_statSegment_le hG hGv hR3 h122 hpc hp1 hGae
  obtain ⟨C₂, C₃, -, -, hb⟩ := hseg i k y j
  have h := hb 1 le_rfl
  simp only [Nat.cast_one, one_smul] at h
  refine ⟨(measurable_statGrad hG hGv i k y j).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  simp_rw [Real.enorm_eq_ofReal_abs]
  exact lt_of_le_of_lt h ENNReal.ofReal_lt_top

/-- **Dario, Lemma 3.2, Step 2, along a line**: from (1.22), the sum of the mean of the
stationary coarsened gradient over a period of a line in the direction `e_j` vanishes. -/
theorem sum_statMean_line_eq_zero (hR3 : ArmstrongDarioOrderZeroTwo)
    (h122 : CorrectorOscSublinearTwo) {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) (hGae : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G) (i : Fin 2) (k : ℕ)
    (y₀ : Vertex 2) (j : Fin 2) :
    ∑ t ∈ Finset.range (3 ^ k), statMean hG hGv p i k (y₀ + (t : ℤ) • LatticeProb.unit j) j = 0 := by
  obtain ⟨δ, hδ, -, hseg⟩ := exists_lintegral_abs_statSegment_le hG hGv hR3 h122 hpc hp1 hGae
  obtain ⟨C₂, C₃, hC₂, hC₃, hb⟩ := hseg i k y₀ j
  set L : ℕ := 3 ^ k with hL
  have hL1 : 1 ≤ L := Nat.one_le_pow _ _ (by norm_num)
  set S := ∑ t ∈ Finset.range L, statMean hG hGv p i k (y₀ + (t : ℤ) • LatticeProb.unit j) j with hS
  have hint := integrable_statGrad hG hGv hR3 h122 hpc hp1 hGae i k
  -- the sum over `m` periods
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
        refine statMean_add hG hGv hpc hGae i (fun i' => ?_) _ j
        simp only [Pi.smul_apply, smul_eq_mul]
        exact Dvd.dvd.mul_right (by rw [hL]; push_cast; exact dvd_mul_left _ _) _
      simp_rw [hper]
      push_cast
      ring
  -- the telescoped increments
  have hsum : ∀ N : ℕ, ∑ t ∈ Finset.range N,
      statMean hG hGv p i k (y₀ + (t : ℤ) • LatticeProb.unit j) j =
      ∫ ω, correctorDiff hG hGv (Pi.single i 1) ω
        (statAnchor k ω (y₀ + (N : ℤ) • LatticeProb.unit j)) (statAnchor k ω y₀)
        ∂latticeBondLaw 2 p := by
    intro N
    unfold statMean
    rw [← integral_finsetSum _ fun t _ => hint _ j]
    refine integral_congr_ae ?_
    filter_upwards [hGae, ae_planarPartitionEvent hpc] with ω hω hP
    exact sum_statGrad_eq hG hGv hω (infinite_planarCoarseAnchor hP 0) i k y₀ j N
  have hbound : ∀ m : ℕ, 1 ≤ m → (m : ℝ) * |S| ≤ C₂ * ((m * L : ℕ) : ℝ) ^ (1 - δ) + C₃ := by
    intro m hm
    have hmL : 1 ≤ m * L := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
    have h1 := hb (m * L) hmL
    have h2 := norm_integral_le_lintegral_norm (μ := latticeBondLaw 2 p) (fun ω =>
      correctorDiff hG hGv (Pi.single i 1) ω
        (statAnchor k ω (y₀ + ((m * L : ℕ) : ℤ) • LatticeProb.unit j)) (statAnchor k ω y₀))
    simp only [Real.norm_eq_abs] at h2
    rw [← hsum, hblock, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ m)] at h2
    exact h2.trans (ENNReal.toReal_le_of_le_ofReal (by positivity) h1)
  -- the limit
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

/-- `Σ_{a : ℤ/L} h(a.val) = Σ_{t < L} h(t)`. -/
theorem sum_zmod_val_eq {L : ℕ} [NeZero L] (h : ℕ → ℝ) :
    ∑ a : ZMod L, h a.val = ∑ t ∈ Finset.range L, h t := by
  refine Finset.sum_nbij' (fun a => a.val) (fun t => (t : ZMod L)) (fun a _ => ?_)
    (fun _ _ => Finset.mem_univ _) (fun a _ => ZMod.natCast_zmod_val a) (fun t ht => ?_)
    (fun _ _ => rfl)
  · exact Finset.mem_range.2 (ZMod.val_lt a)
  · exact ZMod.val_cast_of_lt (Finset.mem_range.1 ht)

/-- **Dario, Lemma 3.2, Step 2**: from (1.22), the sum of the mean of the stationary coarsened
gradient over a period vanishes. -/
theorem sum_statMean_period_eq_zero (hR3 : ArmstrongDarioOrderZeroTwo)
    (h122 : CorrectorOscSublinearTwo) {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) (hGae : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G) (i : Fin 2) (k : ℕ) (j : Fin 2) :
    ∑ w : ZMod (3 ^ k) × ZMod (3 ^ k), statMean hG hGv p i k (residueRep w) j = 0 := by
  haveI : NeZero (3 ^ k) := ⟨pow_ne_zero k (by norm_num)⟩
  have hline := sum_statMean_line_eq_zero hG hGv hR3 h122 hpc hp1 hGae i k
  rw [Fintype.sum_prod_type]
  obtain rfl | rfl : j = 0 ∨ j = 1 := by fin_cases j <;> simp
  · rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun b _ => ?_
    have hs := sum_zmod_val_eq (L := 3 ^ k)
      (fun t => statMean hG hGv p i k ![(t : ℤ), (b.val : ℤ)] 0)
    have e : ∀ t : ℕ, (![(t : ℤ), (b.val : ℤ)] : Vertex 2) =
        ![0, (b.val : ℤ)] + (t : ℤ) • LatticeProb.unit 0 := by
      intro t
      funext i'
      fin_cases i' <;> simp [LatticeProb.unit]
    simp only [residueRep]
    rw [hs]
    simp_rw [e]
    exact hline _ 0
  · refine Finset.sum_eq_zero fun a _ => ?_
    have hs := sum_zmod_val_eq (L := 3 ^ k)
      (fun t => statMean hG hGv p i k ![(a.val : ℤ), (t : ℤ)] 1)
    have e : ∀ t : ℕ, (![(a.val : ℤ), (t : ℤ)] : Vertex 2) =
        ![(a.val : ℤ), 0] + (t : ℤ) • LatticeProb.unit 1 := by
      intro t
      funext i'
      fin_cases i' <;> simp [LatticeProb.unit]
    simp only [residueRep]
    rw [hs]
    simp_rw [e]
    exact hline _ 1

end Carrier

end Rigidity.Corrector
