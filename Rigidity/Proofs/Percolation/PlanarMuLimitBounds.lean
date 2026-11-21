import Rigidity.Proofs.Percolation.PlanarMuQuadratic

/-!
# Lower bound for the limit of `-μ` in the plane

On the partition event, `|q|² / 18 ≤ -μ(U, q) + (μ(U, q) + |q|² / 18)⁺` on resolved cubes, and an
unresolved cube contains a vertex whose partition cube has side at least `3 ^ (m + 1)`, `m` the
scale of `U`. With the expected bound on `(μ + |q|² / 18)⁺` (Armstrong and Dario, (4.30)) and the
sixth moments of the partition sides, `|q|² / 18 ≤ E[-μ(U, q); P, U res] + C |q|₁² 3^(-m/2)`.
Hence the limit of `E[-μ(□_m, q)]` lies between `|q|² / 18` and `C |q|₁²`, as stated in Armstrong
and Dario, Section 5, after Definition 5.1, in dimension two.
-/

open MeasureTheory Filter Topology LatticeProb.Percolation Rigidity.External
  Rigidity.Proofs.Section5
open scoped ENNReal Classical

namespace Rigidity.Percolation

/-- The elementary bound `9ᵐ / 3^(6 (m + 1)) ≤ 3^(-m/2)`. -/
theorem nine_pow_div_three_pow_le (m : ℕ) :
    (9 : ℝ) ^ m / 3 ^ (6 * (m + 1)) ≤ 1 / Real.sqrt ((3 : ℝ) ^ m) := by
  have h3 : (1 : ℝ) ≤ 3 ^ m := one_le_pow₀ (by norm_num)
  have hsq : Real.sqrt ((3 : ℝ) ^ m) ≤ 3 ^ m := by
    calc Real.sqrt ((3 : ℝ) ^ m) ≤ Real.sqrt (((3 : ℝ) ^ m) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith)
      _ = 3 ^ m := Real.sqrt_sq (by positivity)
  have h1 : (9 : ℝ) ^ m / 3 ^ (6 * (m + 1)) ≤ 1 / 3 ^ m := by
    rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    calc (9 : ℝ) ^ m * 3 ^ m = 27 ^ m := by rw [← mul_pow]; norm_num
      _ ≤ 729 ^ m := pow_le_pow_left₀ (by norm_num) (by norm_num) m
      _ ≤ 729 ^ (m + 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ m)
      _ = 3 ^ (6 * (m + 1)) := by rw [pow_mul]; norm_num
  exact h1.trans (one_div_le_one_div_of_le (Real.sqrt_pos.2 (by positivity)) hsq)

/-- **Lower bound for `E[-μ]`.** `|q|² / 18 ≤ E[-μ(U, q); P, U res] + C |q|₁² 3^(-m/2)`. -/
theorem exists_lintegral_neg_planarMu_ge {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (U : TriadicCube 2) (q : Fin 2 → ℝ),
      ENNReal.ofReal ((q 0 ^ 2 + q 1 ^ 2) / 18) ≤
        ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
          ENNReal.ofReal (-planarMu ω U q) else 0) ∂(latticeBondLaw 2 p) +
        C * ENNReal.ofReal ((|q 0| + |q 1|) ^ 2 / Real.sqrt ((3 : ℝ) ^ U.scale)) := by
  obtain ⟨C₁, hC₁, hadd⟩ := exists_lintegral_planarMu_add_le hpc
  obtain ⟨C₆, hC₆, h6⟩ := exists_lintegral_tsum_ninefold_le hpc 6
  refine ⟨C₁ + C₆, by finiteness, fun U q => ?_⟩
  set t := (q 0 ^ 2 + q 1 ^ 2) / 18 with ht
  set s := (|q 0| + |q 1|) ^ 2 with hs
  have ht0 : 0 ≤ t := by positivity
  have hs0 : 0 ≤ s := by positivity
  have hts : t ≤ s := by
    rw [ht, hs]
    have h0 := abs_nonneg (q 0)
    have h1 := abs_nonneg (q 1)
    have e0 : q 0 ^ 2 = |q 0| ^ 2 := (sq_abs _).symm
    have e1 : q 1 ^ 2 = |q 1| ^ 2 := (sq_abs _).symm
    rw [e0, e1]
    nlinarith
  set cm : ℝ≥0∞ := ENNReal.ofReal (1 / (3 : ℝ) ^ (6 * (U.scale + 1))) with hcm
  have hpt : ∀ᵐ ω ∂(latticeBondLaw 2 p), ENNReal.ofReal t ≤
      (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
        ENNReal.ofReal (-planarMu ω U q) else 0) +
      (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
        ENNReal.ofReal (planarMu ω U q + t) else 0) +
      ENNReal.ofReal t * ∑ z ∈ U.toIntegerCube.vertices, cm * reachSum ω 6 z := by
    filter_upwards [ae_planarPartitionEvent hpc] with ω hP
    by_cases hres : PlanarResolved ω U
    · rw [if_pos ⟨hP, hres⟩, if_pos ⟨hP, hres⟩]
      refine le_add_right ?_
      calc ENNReal.ofReal t = ENNReal.ofReal (-planarMu ω U q + (planarMu ω U q + t)) := by
            congr 1
            ring
        _ ≤ _ := ENNReal.ofReal_add_le
    · rw [if_neg fun h => hres h.2, if_neg fun h => hres h.2, zero_add, zero_add]
      have h1 := one_le_sum_of_not_resolved (ω := ω) hres
      calc ENNReal.ofReal t = ENNReal.ofReal t * 1 := (mul_one _).symm
        _ ≤ ENNReal.ofReal t * ENNReal.ofReal (∑ z ∈ U.toIntegerCube.vertices,
            (partSide ω z / 3 ^ (U.scale + 1)) ^ 6) := by
            gcongr
            exact ENNReal.one_le_ofReal.2 h1
        _ ≤ _ := by
            gcongr
            exact ofReal_sum_partSide_div_pow_le hP _ U.scale
  have hmeasH : Measurable fun ω => ENNReal.ofReal t *
      ∑ z ∈ U.toIntegerCube.vertices, cm * reachSum ω 6 z :=
    (Finset.measurable_sum _ fun z _ => (measurable_reachSum 6 z).const_mul _).const_mul _
  have hsize : ((U.toIntegerCube.size : ℕ) : ℝ) = (3 : ℝ) ^ U.scale := by
    rw [show U.toIntegerCube.size = 3 ^ U.scale from rfl]
    push_cast
    ring
  have hG := hadd U q
  rw [hsize] at hG
  have hcard := card_toIntegerCube_vertices U
  have hcm : ENNReal.ofReal U.volume * cm ≤
      ENNReal.ofReal (1 / Real.sqrt ((3 : ℝ) ^ U.scale)) := by
    rw [hcm, ← ENNReal.ofReal_mul U.volume_pos.le]
    refine ENNReal.ofReal_le_ofReal ?_
    have := nine_pow_div_three_pow_le U.scale
    change (9 : ℝ) ^ U.scale * (1 / 3 ^ (6 * (U.scale + 1))) ≤ _
    rw [mul_one_div]
    exact this
  calc ENNReal.ofReal t = ∫⁻ _ω, ENNReal.ofReal t ∂(latticeBondLaw 2 p) := by
        rw [lintegral_const, measure_univ, mul_one]
    _ ≤ ∫⁻ ω, ((if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
          ENNReal.ofReal (-planarMu ω U q) else 0) +
        (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
          ENNReal.ofReal (planarMu ω U q + t) else 0) +
        ENNReal.ofReal t * ∑ z ∈ U.toIntegerCube.vertices, cm * reachSum ω 6 z)
          ∂(latticeBondLaw 2 p) := lintegral_mono_ae hpt
    _ = ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
          ENNReal.ofReal (-planarMu ω U q) else 0) ∂(latticeBondLaw 2 p) +
        ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
          ENNReal.ofReal (planarMu ω U q + t) else 0) ∂(latticeBondLaw 2 p) +
        ENNReal.ofReal t * ∑ z ∈ U.toIntegerCube.vertices,
          cm * ∫⁻ ω, reachSum ω 6 z ∂(latticeBondLaw 2 p) := by
        rw [lintegral_add_right _ hmeasH, lintegral_add_left (measurable_planarMu_indicator U q),
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_finsetSum _ fun z _ => (measurable_reachSum 6 z).const_mul _]
        refine congrArg₂ (· + ·) rfl (congrArg (_ * ·) (Finset.sum_congr rfl fun z _ => ?_))
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
          ENNReal.ofReal (-planarMu ω U q) else 0) ∂(latticeBondLaw 2 p) +
        C₁ * ENNReal.ofReal (s / Real.sqrt ((3 : ℝ) ^ U.scale)) +
        ENNReal.ofReal s * ∑ _z ∈ U.toIntegerCube.vertices, cm * C₆ := by
        gcongr with z hz
        exact h6 z
    _ = ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
          ENNReal.ofReal (-planarMu ω U q) else 0) ∂(latticeBondLaw 2 p) +
        C₁ * ENNReal.ofReal (s / Real.sqrt ((3 : ℝ) ^ U.scale)) +
        C₆ * (ENNReal.ofReal s * (ENNReal.ofReal U.volume * cm)) := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard]
        ring
    _ ≤ ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
          ENNReal.ofReal (-planarMu ω U q) else 0) ∂(latticeBondLaw 2 p) +
        C₁ * ENNReal.ofReal (s / Real.sqrt ((3 : ℝ) ^ U.scale)) +
        C₆ * (ENNReal.ofReal s * ENNReal.ofReal (1 / Real.sqrt ((3 : ℝ) ^ U.scale))) := by
        gcongr
    _ = _ := by
        rw [← ENNReal.ofReal_mul hs0, mul_one_div]
        ring

/-- **Bounds on the limit of `-μ`** (Armstrong and Dario, Section 5, after Definition 5.1, in
dimension two): `|q|² / 18 ≤ lim_m E[-μ(□_m, q); P, □_m res] ≤ C |q|₁²`. -/
theorem exists_planarMuLimit_two_sided {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : Fin 2 → ℝ,
      (q 0 ^ 2 + q 1 ^ 2) / 18 ≤ planarMuLimit p q ∧
        planarMuLimit p q ≤ C * (|q 0| + |q 1|) ^ 2 := by
  obtain ⟨C, hC, hb⟩ := exists_planarMuLimit_bounds hpc
  obtain ⟨C₀, hC₀, hlow⟩ := exists_lintegral_neg_planarMu_ge hpc
  obtain ⟨C₂, hC₂, hup⟩ := exists_lintegral_neg_planarMu_le hpc
  refine ⟨C, hC, fun q => ⟨?_, (hb q).2⟩⟩
  set s := (|q 0| + |q 1|) ^ 2 with hs
  have hs0 : 0 ≤ s := by positivity
  have hfin : ∀ m : ℕ, ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω ⟨m, 0⟩ then
      ENNReal.ofReal (-planarMu ω ⟨m, 0⟩ q) else 0) ∂(latticeBondLaw 2 p) ≠ ∞ :=
    fun m => ne_top_of_le_ne_top (ENNReal.mul_ne_top hC₂ ENNReal.ofReal_ne_top) (hup _ q)
  have hlow' : ∀ m : ℕ, (q 0 ^ 2 + q 1 ^ 2) / 18 ≤
      planarMuMean p m q + C₀.toReal * (s * (1 / Real.sqrt ((3 : ℝ) ^ m))) := by
    intro m
    have h := hlow ⟨m, 0⟩ q
    rw [← hs] at h
    have h' := ENNReal.toReal_mono
      (ENNReal.add_ne_top.2 ⟨hfin m, ENNReal.mul_ne_top hC₀ ENNReal.ofReal_ne_top⟩) h
    rw [ENNReal.toReal_add (hfin m) (ENNReal.mul_ne_top hC₀ ENNReal.ofReal_ne_top),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_ofReal (by positivity)] at h'
    calc (q 0 ^ 2 + q 1 ^ 2) / 18 ≤ _ := h'
      _ = _ := by
        unfold planarMuMean
        ring
  have hr : Tendsto (fun m : ℕ => C₀.toReal * (s * (1 / Real.sqrt ((3 : ℝ) ^ m)))) atTop
      (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_one_div_sqrt_three_pow.const_mul s).const_mul C₀.toReal
  have := ge_of_tendsto' ((tendsto_planarMuLimit hpc q).add hr) hlow'
  simpa only [add_zero] using this

end Rigidity.Percolation
