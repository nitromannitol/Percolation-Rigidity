import Rigidity.Proofs.Cluster.GeneralMuSubadditiveMoments
import Rigidity.Proofs.Cluster.GeneralMuLimits
import Rigidity.Proofs.Percolation.GeneralDim.CubeNuLimit

/-!
# Convergence of the expectation of `-μ` in every dimension

The subadditivity of `-μ` in expectation (`exists_lintegral_sum_cubeMu_subcubes_sub_le`) and the
approximate stationarity of `μ` (`exists_lintegral_neg_cubeMu_le_of_scale_eq`) give the approximate
monotonicity (Armstrong and Dario, (4.48))

`E[-μ(U, q); P, U res] ≤ E[-μ(V, q); P, V res] + C |q|₁² (3^{-n/4} + exp(-c 3ⁿ))`

for triadic cubes `V`, `U` of scales `n ≤ m`. Together with `0 ≤ E[-μ(V, q); P, V res] ≤ C |q|₁²`
(Armstrong and Dario, (4.12) in expectation), the expectations of `-μ(□_m, q)` converge as
`m → ∞` (Armstrong and Dario, Section 5, after Definition 5.1), along every sequence of triadic
cubes of scale `m`, and so do the expectations of the local and stationary local versions of `μ`.
-/

open MeasureTheory Filter Topology LatticeProb.Percolation Rigidity.External
open scoped ENNReal Classical

namespace Rigidity.Percolation

variable {d : ℕ}

/-- **Approximate monotonicity of `-μ`** (Armstrong and Dario, (4.48), in every dimension
`d ≥ 2`). For triadic cubes `V`, `U` with the scale `n` of `V` at most that of `U`,
`E[-μ(U, q); P, U res] ≤ E[-μ(V, q); P, V res] + C |q|₁² (3^{-n/4} + exp(-c 3ⁿ))`. -/
theorem exists_lintegral_neg_cubeMu_le_of_scale_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∃ c : ℝ, 0 < c ∧ ∀ (U V : TriadicCube d), V.scale ≤ U.scale →
      ∀ q : Fin d → ℝ,
      ∫⁻ ω, (if PartitionEvent ω ∧ PartitionResolved ω U then
          ENNReal.ofReal (-cubeMu ω U q) else 0) ∂(latticeBondLaw d p) ≤
        ∫⁻ ω, (if PartitionEvent ω ∧ PartitionResolved ω V then
          ENNReal.ofReal (-cubeMu ω V q) else 0) ∂(latticeBondLaw d p) +
        C * ENNReal.ofReal ((∑ i, |q i|) ^ 2 *
          (1 / √(√((3 : ℝ) ^ V.scale)) + Real.exp (-c * (3 : ℝ) ^ V.scale))) := by
  have hd0 : 0 < d := by omega
  obtain ⟨C₁, hC₁, hsub⟩ := exists_lintegral_sum_cubeMu_subcubes_sub_le hd hpc
  obtain ⟨C₂, hC₂, c, hc, hstat⟩ := exists_lintegral_neg_cubeMu_le_of_scale_eq hd hpc
  refine ⟨ENNReal.ofReal C₁ + C₂, by finiteness, c, hc, fun U V hVU q => ?_⟩
  have hvol := U.latticeVolume_pos
  set n := V.scale with hn
  set S := U.toIntegerCube.vertices with hS
  have hpt : ∀ ω, (if PartitionEvent ω ∧ PartitionResolved ω U then
      ENNReal.ofReal (-cubeMu ω U q) else 0) ≤
      ENNReal.ofReal (1 / U.latticeVolume) *
        ((if PartitionEvent ω ∧ PartitionResolved ω U then
          ENNReal.ofReal (∑ x ∈ S,
            (if PartitionResolved ω (triadicCubeAt n x) then
              cubeMu ω (triadicCubeAt n x) q else 0) - cubeMu ω U q * U.latticeVolume)
          else 0) +
        ∑ x ∈ S, (if PartitionEvent ω ∧ PartitionResolved ω (triadicCubeAt n x) then
            ENNReal.ofReal (-cubeMu ω (triadicCubeAt n x) q) else 0)) := by
    intro ω
    by_cases h : PartitionEvent ω ∧ PartitionResolved ω U
    · rw [if_pos h, if_pos h]
      have hnn : ∀ x ∈ S, 0 ≤ -(if PartitionResolved ω (triadicCubeAt n x)
          then cubeMu ω (triadicCubeAt n x) q else 0) := fun x _ => by
        split_ifs with hx
        · exact neg_nonneg.2 (cubeMu_nonpos hd0 h.1 hx q)
        · simp
      have hsum : ENNReal.ofReal (-∑ x ∈ S,
          (if PartitionResolved ω (triadicCubeAt n x) then
            cubeMu ω (triadicCubeAt n x) q else 0)) =
          ∑ x ∈ S, (if PartitionEvent ω ∧ PartitionResolved ω (triadicCubeAt n x) then
              ENNReal.ofReal (-cubeMu ω (triadicCubeAt n x) q) else 0) := by
        rw [← Finset.sum_neg_distrib, ENNReal.ofReal_sum_of_nonneg hnn]
        refine Finset.sum_congr rfl fun x _ => ?_
        by_cases hx : PartitionResolved ω (triadicCubeAt n x)
        · rw [if_pos hx, if_pos ⟨h.1, hx⟩]
        · rw [if_neg hx, if_neg fun h' => hx h'.2, neg_zero, ENNReal.ofReal_zero]
      rw [← hsum]
      set T := ∑ x ∈ S, (if PartitionResolved ω (triadicCubeAt n x) then
        cubeMu ω (triadicCubeAt n x) q else 0)
      calc ENNReal.ofReal (-cubeMu ω U q)
          = ENNReal.ofReal (1 / U.latticeVolume *
              ((T - cubeMu ω U q * U.latticeVolume) + -T)) := by
            congr 1
            field_simp
            ring
        _ = ENNReal.ofReal (1 / U.latticeVolume) *
            ENNReal.ofReal ((T - cubeMu ω U q * U.latticeVolume) + -T) :=
            ENNReal.ofReal_mul (by positivity)
        _ ≤ ENNReal.ofReal (1 / U.latticeVolume) *
            (ENNReal.ofReal (T - cubeMu ω U q * U.latticeVolume) + ENNReal.ofReal (-T)) :=
            mul_le_mul' le_rfl ENNReal.ofReal_add_le
    · rw [if_neg h]
      exact zero_le
  have hcard : ((S.card : ℕ) : ℝ≥0∞) = ENNReal.ofReal U.latticeVolume := by
    rw [← U.card_toIntegerCube_vertices, ENNReal.ofReal_natCast]
  have hinv : ENNReal.ofReal (1 / U.latticeVolume) * ENNReal.ofReal U.latticeVolume = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), one_div_mul_cancel hvol.ne', ENNReal.ofReal_one]
  set s := (∑ i, |q i|) ^ 2 with hs
  have hs0 : 0 ≤ s := by positivity
  set A := ∫⁻ ω, (if PartitionEvent ω ∧ PartitionResolved ω V then
    ENNReal.ofReal (-cubeMu ω V q) else 0) ∂(latticeBondLaw d p)
  have hX : ENNReal.ofReal (C₁ * s * U.latticeVolume / √(√((3 : ℝ) ^ n))) =
      ENNReal.ofReal U.latticeVolume * (ENNReal.ofReal C₁ *
        ENNReal.ofReal (s / √(√((3 : ℝ) ^ n)))) := by
    rw [← ENNReal.ofReal_mul hC₁, ← ENNReal.ofReal_mul hvol.le]
    congr 1
    ring
  have hXZ : ENNReal.ofReal (s * (1 / √(√((3 : ℝ) ^ n)) + Real.exp (-c * (3 : ℝ) ^ n))) =
      ENNReal.ofReal (s / √(√((3 : ℝ) ^ n))) +
        ENNReal.ofReal (s * Real.exp (-c * (3 : ℝ) ^ n)) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  have hmeas : ∀ x ∈ S, Measurable fun ω =>
      (if PartitionEvent ω ∧ PartitionResolved ω (triadicCubeAt n x) then
        ENNReal.ofReal (-cubeMu ω (triadicCubeAt n x) q) else 0) :=
    fun x _ => measurable_cubeMu_indicator _ q
  calc ∫⁻ ω, (if PartitionEvent ω ∧ PartitionResolved ω U then
        ENNReal.ofReal (-cubeMu ω U q) else 0) ∂(latticeBondLaw d p)
      ≤ ∫⁻ ω, ENNReal.ofReal (1 / U.latticeVolume) *
        ((if PartitionEvent ω ∧ PartitionResolved ω U then
          ENNReal.ofReal (∑ x ∈ S,
            (if PartitionResolved ω (triadicCubeAt n x) then
              cubeMu ω (triadicCubeAt n x) q else 0) - cubeMu ω U q * U.latticeVolume)
          else 0) +
        ∑ x ∈ S, (if PartitionEvent ω ∧ PartitionResolved ω (triadicCubeAt n x) then
            ENNReal.ofReal (-cubeMu ω (triadicCubeAt n x) q) else 0)) ∂(latticeBondLaw d p) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (1 / U.latticeVolume) *
        (∫⁻ ω, (if PartitionEvent ω ∧ PartitionResolved ω U then
          ENNReal.ofReal (∑ x ∈ S,
            (if PartitionResolved ω (triadicCubeAt n x) then
              cubeMu ω (triadicCubeAt n x) q else 0) - cubeMu ω U q * U.latticeVolume)
          else 0) ∂(latticeBondLaw d p) +
        ∑ x ∈ S, ∫⁻ ω, (if PartitionEvent ω ∧ PartitionResolved ω (triadicCubeAt n x) then
            ENNReal.ofReal (-cubeMu ω (triadicCubeAt n x) q) else 0) ∂(latticeBondLaw d p)) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_add_right _ (Finset.measurable_sum _ hmeas), lintegral_finsetSum _ hmeas]
    _ ≤ ENNReal.ofReal (1 / U.latticeVolume) *
        (ENNReal.ofReal (C₁ * s * U.latticeVolume / √(√((3 : ℝ) ^ n))) +
          ∑ _x ∈ S, (A + C₂ * ENNReal.ofReal (s * Real.exp (-c * (3 : ℝ) ^ n)))) := by
        gcongr with x hx
        · exact hsub U n hVU q
        · exact hstat V (triadicCubeAt n x) (scale_triadicCubeAt n x).symm q
    _ = (ENNReal.ofReal (1 / U.latticeVolume) * ENNReal.ofReal U.latticeVolume) *
        (ENNReal.ofReal C₁ * ENNReal.ofReal (s / √(√((3 : ℝ) ^ n))) +
          (A + C₂ * ENNReal.ofReal (s * Real.exp (-c * (3 : ℝ) ^ n)))) := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard, hX]
        ring
    _ = A + (ENNReal.ofReal C₁ * ENNReal.ofReal (s / √(√((3 : ℝ) ^ n))) +
          C₂ * ENNReal.ofReal (s * Real.exp (-c * (3 : ℝ) ^ n))) := by
        rw [hinv, one_mul]
        ring
    _ ≤ A + (ENNReal.ofReal C₁ + C₂) * ENNReal.ofReal (s * (1 / √(√((3 : ℝ) ^ n)) +
          Real.exp (-c * (3 : ℝ) ^ n))) := by
        rw [hXZ, add_mul, mul_add, mul_add]
        gcongr
        · exact le_self_add
        · exact le_add_self

/-- The expectation `E[-μ(□_m, q); P, □_m res]` on the triadic cube `□_m` of scale `m` centred at
the origin. -/
noncomputable def cubeMuMean (p : unitInterval) (m : ℕ) (q : Fin d → ℝ) : ℝ :=
  (∫⁻ ω, (if PartitionEvent ω ∧ PartitionResolved ω ⟨m, 0⟩ then
    ENNReal.ofReal (-cubeMu ω ⟨m, 0⟩ q) else 0) ∂(latticeBondLaw d p)).toReal

theorem tendsto_one_div_sqrt_sqrt_three_pow :
    Tendsto (fun n : ℕ => 1 / √(√((3 : ℝ) ^ n))) atTop (𝓝 0) := by
  simp only [one_div]
  exact (Real.tendsto_sqrt_atTop.comp (Real.tendsto_sqrt_atTop.comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 3)))).inv_tendsto_atTop

/-- **Convergence of `E[-μ(□_m, q)]`** (Armstrong and Dario, Section 5, after Definition 5.1, in
every dimension `d ≥ 2`). For `p > p_c(d)`, the expectations of `-μ(□_m, q)` converge as `m → ∞`,
and the limit lies between `0` and `C |q|₁²`, with `C` independent of `q`. -/
theorem exists_tendsto_cubeMuMean [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : Fin d → ℝ, ∃ L : ℝ,
      Tendsto (fun m => cubeMuMean p m q) atTop (𝓝 L) ∧
        0 ≤ L ∧ L ≤ C * (∑ i, |q i|) ^ 2 := by
  obtain ⟨C, hC, c₁, hc₁, hmono⟩ := exists_lintegral_neg_cubeMu_le_of_scale_le hd hpc
  obtain ⟨C₀, hC₀, hup⟩ := exists_lintegral_neg_cubeMu_le hd hpc
  refine ⟨C₀, hC₀, fun q => ?_⟩
  set s := (∑ i, |q i|) ^ 2 with hs
  have hs0 : 0 ≤ s := by positivity
  have hbound' : ∀ m : ℕ, ∫⁻ ω, (if PartitionEvent ω ∧ PartitionResolved ω ⟨m, 0⟩ then
      ENNReal.ofReal (-cubeMu ω ⟨m, 0⟩ q) else 0) ∂(latticeBondLaw d p) ≤
        ENNReal.ofReal (C₀ * s) := fun m => hup _ q
  have hfin : ∀ m : ℕ, ∫⁻ ω, (if PartitionEvent ω ∧ PartitionResolved ω ⟨m, 0⟩ then
      ENNReal.ofReal (-cubeMu ω ⟨m, 0⟩ q) else 0) ∂(latticeBondLaw d p) ≠ ∞ :=
    fun m => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hbound' m)
  have hbound : ∀ m, cubeMuMean p m q ∈ Set.Icc 0 (C₀ * s) := fun m =>
    ⟨ENNReal.toReal_nonneg, ENNReal.toReal_le_of_le_ofReal (by positivity) (hbound' m)⟩
  set ε : ℕ → ℝ := fun m => C.toReal * (s * (1 / √(√((3 : ℝ) ^ m)) +
    Real.exp (-c₁ * (3 : ℝ) ^ m))) with hεdef
  have hstep : ∀ m m', m ≤ m' → cubeMuMean p m' q ≤ cubeMuMean p m q + ε m := by
    intro m m' hmm'
    have h := hmono ⟨m', 0⟩ ⟨m, 0⟩ hmm' q
    rw [← hs] at h
    have h' := ENNReal.toReal_mono
      (ENNReal.add_ne_top.2 ⟨hfin m, ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top⟩) h
    rw [ENNReal.toReal_add (hfin m) (ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h'
    exact h'
  have hε : Tendsto ε atTop (𝓝 0) := by
    have := ((tendsto_one_div_sqrt_sqrt_three_pow.add
      (tendsto_exp_neg_mul_three_pow hc₁)).const_mul s).const_mul C.toReal
    simpa only [add_zero, mul_zero] using this
  obtain ⟨L, hL⟩ := exists_tendsto_of_le_add_of_bounded hbound hε hstep
  exact ⟨L, hL, ge_of_tendsto' hL fun m => (hbound m).1, le_of_tendsto' hL fun m => (hbound m).2⟩

/-- The limit of `E[-μ(□_m, q)]`. -/
noncomputable def cubeMuLimit (p : unitInterval) (q : Fin d → ℝ) : ℝ :=
  limUnder atTop fun m => cubeMuMean p m q

theorem tendsto_cubeMuLimit [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (q : Fin d → ℝ) :
    Tendsto (fun m => cubeMuMean p m q) atTop (𝓝 (cubeMuLimit p q)) := by
  obtain ⟨C, -, h⟩ := exists_tendsto_cubeMuMean hd hpc
  obtain ⟨L, hL, -⟩ := h q
  rw [cubeMuLimit, hL.limUnder_eq]
  exact hL

/-- **Limit of `E[-μ]` along arbitrary cubes.** Along every sequence of triadic cubes `V_m` of
scale `m`, the expectations of `1{P, V_m res} (-μ(V_m, q))` converge to the limit of
`E[-μ(□_m, q)]`. -/
theorem tendsto_lintegral_neg_cubeMu_of_scale [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (V : ℕ → TriadicCube d) (hV : ∀ m, (V m).scale = m)
    (q : Fin d → ℝ) :
    Tendsto (fun m => (∫⁻ ω, (if PartitionEvent ω ∧ PartitionResolved ω (V m) then
      ENNReal.ofReal (-cubeMu ω (V m) q) else 0) ∂(latticeBondLaw d p)).toReal) atTop
      (𝓝 (cubeMuLimit p q)) :=
  tendsto_lintegral_neg_cubeMu_of_tendsto hd hpc (fun m => ⟨m, 0⟩) V (fun _ => rfl) hV q
    (tendsto_cubeMuLimit hd hpc q)

/-- **Limit of the local version of `μ`.** -/
theorem tendsto_lintegral_cubeMuLoc_of_scale [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (V : ℕ → TriadicCube d) (hV : ∀ m, (V m).scale = m)
    (q : Fin d → ℝ) :
    Tendsto (fun m => (∫⁻ ω, cubeMuLoc (V m) q ω ∂(latticeBondLaw d p)).toReal) atTop
      (𝓝 (cubeMuLimit p q)) :=
  tendsto_lintegral_cubeMuLoc_of_tendsto hd hpc V hV q
    (tendsto_lintegral_neg_cubeMu_of_scale hd hpc V hV q)

/-- **Limit of the stationary local version of `μ`.** -/
theorem tendsto_lintegral_cubeMuStat_of_scale [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (V : ℕ → TriadicCube d) (hV : ∀ m, (V m).scale = m)
    (q : Fin d → ℝ) :
    Tendsto (fun m => (∫⁻ ω, cubeMuStat (V m) q ω ∂(latticeBondLaw d p)).toReal) atTop
      (𝓝 (cubeMuLimit p q)) :=
  tendsto_lintegral_cubeMuStat_of_tendsto hd hpc V hV q
    (tendsto_lintegral_neg_cubeMu_of_scale hd hpc V hV q)

end Rigidity.Percolation
