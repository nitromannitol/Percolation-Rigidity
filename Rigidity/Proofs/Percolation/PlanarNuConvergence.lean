import Rigidity.Proofs.Percolation.PlanarNuStationarity
import Rigidity.Proofs.Percolation.PlanarNuSubadditiveMoments
import Rigidity.Proofs.Percolation.PlanarNuLowerBound

/-!
# Convergence of the expectation of `ν` in the plane

Write `E[ν(U, ξ); P, U res]` for the expectation of `ν(U, ξ)` on the event that the planar
partition exists and `U` is resolved. The approximate subadditivity of `ν` in expectation and its
approximate stationarity give the approximate monotonicity

`E[ν(U, ξ); P, U res] ≤ E[ν(V, ξ); P, V res] + C |ξ|₁² (3^(-n/2) + exp (-c 3ⁿ))`

for triadic cubes `V`, `U` of scales `n ≤ m`. Together with the bounds
`c |ξ|² - C |ξ|₁² 3^(-n/2) ≤ E[ν(V, ξ); P, V res] ≤ (9/4) |ξ|₁²`, the expectations on the cubes
`□_m` of scale `m` centred at the origin converge, and the limit lies between `c |ξ|²` and
`(9/4) |ξ|₁²`. This is the first step of Armstrong and Dario, Section 5, before Definition 5.1, in
dimension two; the rate `3^(-n/2)` comes from the subadditivity error of `ν` in expectation.
-/

open MeasureTheory Filter Topology LatticeProb.Percolation Rigidity.External
  Rigidity.Proofs.Section5
open scoped ENNReal Classical

namespace Rigidity.Percolation

/-- The expectation of `ν` on resolved cubes is at most `(9/4) |ξ|₁²`. -/
theorem lintegral_planarNu_le (p : unitInterval) (V : TriadicCube 2) (ξ : Fin 2 → ℝ) :
    ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω V then
        ENNReal.ofReal (planarNu ω V ξ) else 0) ∂(latticeBondLaw 2 p) ≤
      ENNReal.ofReal (9 / 4 * (|ξ 0| + |ξ 1|) ^ 2) := by
  calc _ ≤ ∫⁻ _ω, ENNReal.ofReal (9 / 4 * (|ξ 0| + |ξ 1|) ^ 2) ∂(latticeBondLaw 2 p) :=
        lintegral_mono fun ω => by
          split_ifs
          · exact ENNReal.ofReal_le_ofReal (planarNu_le ξ)
          · exact zero_le
    _ = _ := by rw [lintegral_const, measure_univ, mul_one]

/-- **Approximate monotonicity of `ν`** (Armstrong and Dario, Section 5, first display, in
dimension two). For triadic cubes `V`, `U` with the scale `n` of `V` at most that of `U`,
`E[ν(U, ξ); P, U res] ≤ E[ν(V, ξ); P, V res] + C |ξ|₁² (3^(-n/2) + exp (-c 3ⁿ))`. -/
theorem exists_lintegral_planarNu_le_of_scale_le {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∃ c : ℝ, 0 < c ∧ ∀ (U V : TriadicCube 2), V.scale ≤ U.scale →
      ∀ ξ : Fin 2 → ℝ,
      ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
          ENNReal.ofReal (planarNu ω U ξ) else 0) ∂(latticeBondLaw 2 p) ≤
        ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω V then
          ENNReal.ofReal (planarNu ω V ξ) else 0) ∂(latticeBondLaw 2 p) +
        C * ENNReal.ofReal ((|ξ 0| + |ξ 1|) ^ 2 *
          (1 / Real.sqrt ((3 : ℝ) ^ V.scale) + Real.exp (-c * (3 : ℝ) ^ V.scale))) := by
  obtain ⟨C₁, hC₁, hsub⟩ := exists_lintegral_planarNu_sub_sum_subcubes_le hpc
  obtain ⟨C₂, hC₂, c, hc, hstat⟩ := exists_lintegral_planarNu_le_of_scale_eq hpc
  refine ⟨C₁ + C₂, by finiteness, c, hc, fun U V hVU ξ => ?_⟩
  have hvol := U.volume_pos
  have hpt : ∀ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
      ENNReal.ofReal (planarNu ω U ξ) else 0) ≤
      ENNReal.ofReal (1 / U.volume) *
        ((if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
          ENNReal.ofReal (planarNu ω U ξ * U.volume - ∑ x ∈ U.toIntegerCube.vertices,
            (if PlanarResolved ω (scaleCube V.scale x) then
              planarNu ω (scaleCube V.scale x) ξ else 0)) else 0) +
        ∑ x ∈ U.toIntegerCube.vertices,
          (if PlanarPartitionEvent ω ∧ PlanarResolved ω (scaleCube V.scale x) then
            ENNReal.ofReal (planarNu ω (scaleCube V.scale x) ξ) else 0)) := by
    intro ω
    by_cases h : PlanarPartitionEvent ω ∧ PlanarResolved ω U
    · rw [if_pos h, if_pos h]
      have hnn : ∀ x ∈ U.toIntegerCube.vertices, 0 ≤ (if PlanarResolved ω (scaleCube V.scale x)
          then planarNu ω (scaleCube V.scale x) ξ else 0) := fun x _ => by
        split_ifs
        · exact planarNu_nonneg ξ
        · exact le_rfl
      have hsum : ENNReal.ofReal (∑ x ∈ U.toIntegerCube.vertices,
          (if PlanarResolved ω (scaleCube V.scale x) then
            planarNu ω (scaleCube V.scale x) ξ else 0)) =
          ∑ x ∈ U.toIntegerCube.vertices,
            (if PlanarPartitionEvent ω ∧ PlanarResolved ω (scaleCube V.scale x) then
              ENNReal.ofReal (planarNu ω (scaleCube V.scale x) ξ) else 0) := by
        rw [ENNReal.ofReal_sum_of_nonneg hnn]
        refine Finset.sum_congr rfl fun x _ => ?_
        by_cases hx : PlanarResolved ω (scaleCube V.scale x)
        · rw [if_pos hx, if_pos ⟨h.1, hx⟩]
        · rw [if_neg hx, if_neg fun h' => hx h'.2, ENNReal.ofReal_zero]
      rw [← hsum]
      set T := ∑ x ∈ U.toIntegerCube.vertices, (if PlanarResolved ω (scaleCube V.scale x) then
        planarNu ω (scaleCube V.scale x) ξ else 0)
      calc ENNReal.ofReal (planarNu ω U ξ)
          = ENNReal.ofReal (1 / U.volume * ((planarNu ω U ξ * U.volume - T) + T)) := by
            congr 1
            rw [sub_add_cancel]
            field_simp
        _ = ENNReal.ofReal (1 / U.volume) *
            ENNReal.ofReal ((planarNu ω U ξ * U.volume - T) + T) :=
            ENNReal.ofReal_mul (by positivity)
        _ ≤ ENNReal.ofReal (1 / U.volume) *
            (ENNReal.ofReal (planarNu ω U ξ * U.volume - T) + ENNReal.ofReal T) :=
            mul_le_mul' le_rfl ENNReal.ofReal_add_le
    · rw [if_neg h]
      exact zero_le
  have hcard : ((U.toIntegerCube.vertices.card : ℕ) : ℝ≥0∞) = ENNReal.ofReal U.volume := by
    rw [show U.volume = ((U.toIntegerCube.vertices.card : ℕ) : ℝ) from
      (card_toIntegerCube_vertices_eq U).symm, ENNReal.ofReal_natCast]
  have hinv : ENNReal.ofReal (1 / U.volume) * ENNReal.ofReal U.volume = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), one_div_mul_cancel hvol.ne', ENNReal.ofReal_one]
  set s := (|ξ 0| + |ξ 1|) ^ 2 with hs
  have hs0 : 0 ≤ s := by positivity
  set A := ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω V then
    ENNReal.ofReal (planarNu ω V ξ) else 0) ∂(latticeBondLaw 2 p)
  have hX : ENNReal.ofReal (s * U.volume / Real.sqrt ((3 : ℝ) ^ V.scale)) =
      ENNReal.ofReal U.volume * ENNReal.ofReal (s / Real.sqrt ((3 : ℝ) ^ V.scale)) := by
    rw [← ENNReal.ofReal_mul hvol.le]
    congr 1
    ring
  have hXZ : ENNReal.ofReal (s * (1 / Real.sqrt ((3 : ℝ) ^ V.scale) +
      Real.exp (-c * (3 : ℝ) ^ V.scale))) =
      ENNReal.ofReal (s / Real.sqrt ((3 : ℝ) ^ V.scale)) +
        ENNReal.ofReal (s * Real.exp (-c * (3 : ℝ) ^ V.scale)) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  have hmeas : ∀ x ∈ U.toIntegerCube.vertices, Measurable fun ω =>
      (if PlanarPartitionEvent ω ∧ PlanarResolved ω (scaleCube V.scale x) then
        ENNReal.ofReal (planarNu ω (scaleCube V.scale x) ξ) else 0) :=
    fun x _ => measurable_planarNu_indicator _ ξ
  calc ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
        ENNReal.ofReal (planarNu ω U ξ) else 0) ∂(latticeBondLaw 2 p)
      ≤ ∫⁻ ω, ENNReal.ofReal (1 / U.volume) *
        ((if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
          ENNReal.ofReal (planarNu ω U ξ * U.volume - ∑ x ∈ U.toIntegerCube.vertices,
            (if PlanarResolved ω (scaleCube V.scale x) then
              planarNu ω (scaleCube V.scale x) ξ else 0)) else 0) +
        ∑ x ∈ U.toIntegerCube.vertices,
          (if PlanarPartitionEvent ω ∧ PlanarResolved ω (scaleCube V.scale x) then
            ENNReal.ofReal (planarNu ω (scaleCube V.scale x) ξ) else 0))
          ∂(latticeBondLaw 2 p) := lintegral_mono hpt
    _ = ENNReal.ofReal (1 / U.volume) *
        (∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
          ENNReal.ofReal (planarNu ω U ξ * U.volume - ∑ x ∈ U.toIntegerCube.vertices,
            (if PlanarResolved ω (scaleCube V.scale x) then
              planarNu ω (scaleCube V.scale x) ξ else 0)) else 0) ∂(latticeBondLaw 2 p) +
        ∑ x ∈ U.toIntegerCube.vertices,
          ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω (scaleCube V.scale x) then
            ENNReal.ofReal (planarNu ω (scaleCube V.scale x) ξ) else 0)
              ∂(latticeBondLaw 2 p)) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_add_right _ (Finset.measurable_sum _ hmeas), lintegral_finsetSum _ hmeas]
    _ ≤ ENNReal.ofReal (1 / U.volume) *
        (C₁ * ENNReal.ofReal (s * U.volume / Real.sqrt ((3 : ℝ) ^ V.scale)) +
          ∑ _x ∈ U.toIntegerCube.vertices,
            (A + C₂ * ENNReal.ofReal (s * Real.exp (-c * (3 : ℝ) ^ V.scale)))) := by
        gcongr with x hx
        · exact hsub U V.scale hVU ξ
        · exact hstat V (scaleCube V.scale x) (scale_scaleCube V.scale x).symm ξ
    _ = (ENNReal.ofReal (1 / U.volume) * ENNReal.ofReal U.volume) *
        (C₁ * ENNReal.ofReal (s / Real.sqrt ((3 : ℝ) ^ V.scale)) +
          (A + C₂ * ENNReal.ofReal (s * Real.exp (-c * (3 : ℝ) ^ V.scale)))) := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard, hX]
        ring
    _ = A + (C₁ * ENNReal.ofReal (s / Real.sqrt ((3 : ℝ) ^ V.scale)) +
          C₂ * ENNReal.ofReal (s * Real.exp (-c * (3 : ℝ) ^ V.scale))) := by
        rw [hinv, one_mul]
        ring
    _ ≤ A + (C₁ + C₂) * ENNReal.ofReal (s * (1 / Real.sqrt ((3 : ℝ) ^ V.scale) +
          Real.exp (-c * (3 : ℝ) ^ V.scale))) := by
        rw [hXZ, mul_add]
        gcongr
        · exact le_self_add
        · exact le_add_self

/-- A bounded real sequence with `a m' ≤ a m + ε m` for `m ≤ m'` and `ε m → 0` converges. -/
theorem exists_tendsto_of_le_add {a ε : ℕ → ℝ} {M : ℝ} (ha : ∀ m, a m ∈ Set.Icc 0 M)
    (hε : Tendsto ε atTop (𝓝 0)) (hmono : ∀ m m', m ≤ m' → a m' ≤ a m + ε m) :
    ∃ L, Tendsto a atTop (𝓝 L) := by
  obtain ⟨L, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded (Metric.isBounded_Icc 0 M) ha
  refine ⟨L, Metric.tendsto_atTop.2 fun δ hδ => ?_⟩
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.1 hlim (δ / 3) (by positivity)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hε (δ / 3) (by positivity)
  have hK' : ∀ k ≥ K, |a (φ k) - L| < δ / 3 := fun k hk => by
    simpa only [Real.dist_eq, Function.comp_apply] using hK k hk
  have hN' : ∀ m ≥ N, |ε m| < δ / 3 := fun m hm => by
    simpa only [Real.dist_eq, sub_zero] using hN m hm
  refine ⟨φ (max K N), fun m hm => ?_⟩
  have hk₀ := hK' (max K N) (le_max_left _ _)
  have hε₀ := hN' (φ (max K N)) ((le_max_right K N).trans (hφ.id_le _))
  have hup := hmono _ _ hm
  have hmN : N ≤ m := ((le_max_right K N).trans (hφ.id_le _)).trans hm
  have hεm := hN' m hmN
  have hk₁ := hK' (max K m) (le_max_left _ _)
  have hdown := hmono m (φ (max K m)) ((le_max_right K m).trans (hφ.id_le _))
  rw [abs_lt] at hk₀ hε₀ hεm hk₁
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- `3^(-n/2) → 0`. -/
theorem tendsto_one_div_sqrt_three_pow :
    Tendsto (fun n : ℕ => 1 / Real.sqrt ((3 : ℝ) ^ n)) atTop (𝓝 0) := by
  simp only [one_div]
  exact (Real.tendsto_sqrt_atTop.comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 3))).inv_tendsto_atTop

/-- `exp (-c 3ⁿ) → 0` for `c > 0`. -/
theorem tendsto_exp_neg_mul_three_pow {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => Real.exp (-c * (3 : ℝ) ^ n)) atTop (𝓝 0) := by
  have h := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 3)).const_mul_atTop hc
  refine Real.tendsto_exp_atBot.comp ((tendsto_neg_atTop_atBot.comp h).congr fun n => ?_)
  simp only [Function.comp_apply, neg_mul]

/-- The expectation `E[ν(□_m, ξ); P, □_m res]` on the triadic cube `□_m` of scale `m` centred at
the origin. -/
noncomputable def planarNuMean (p : unitInterval) (m : ℕ) (ξ : Fin 2 → ℝ) : ℝ :=
  (∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω ⟨m, 0⟩ then
    ENNReal.ofReal (planarNu ω ⟨m, 0⟩ ξ) else 0) ∂(latticeBondLaw 2 p)).toReal

/-- **Convergence of `E[ν(□_m, ξ)]`** (Armstrong and Dario, Section 5, before Definition 5.1, in
dimension two). For `p > p_c(2)`, the expectations of `ν(□_m, ξ)` converge as `m → ∞`, and the
limit lies between `c |ξ|²` and `(9/4) |ξ|₁²`, with `c > 0` independent of `ξ`. -/
theorem exists_tendsto_planarNuMean {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ ξ : Fin 2 → ℝ, ∃ L : ℝ,
      Tendsto (fun m => planarNuMean p m ξ) atTop (𝓝 L) ∧
        c * (ξ 0 ^ 2 + ξ 1 ^ 2) ≤ L ∧ L ≤ 9 / 4 * (|ξ 0| + |ξ 1|) ^ 2 := by
  obtain ⟨C, hC, c₁, hc₁, hmono⟩ := exists_lintegral_planarNu_le_of_scale_le hpc
  obtain ⟨c₀, hc₀, C₀, hC₀, hlow⟩ := exists_lintegral_planarNu_ge hpc
  refine ⟨c₀, hc₀, fun ξ => ?_⟩
  set s := (|ξ 0| + |ξ 1|) ^ 2 with hs
  have hs0 : 0 ≤ s := by positivity
  have hfin : ∀ m : ℕ, ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω ⟨m, 0⟩ then
      ENNReal.ofReal (planarNu ω ⟨m, 0⟩ ξ) else 0) ∂(latticeBondLaw 2 p) ≠ ∞ :=
    fun m => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (lintegral_planarNu_le p _ ξ)
  have hbound : ∀ m, planarNuMean p m ξ ∈ Set.Icc 0 (9 / 4 * s) := fun m =>
    ⟨ENNReal.toReal_nonneg, ENNReal.toReal_le_of_le_ofReal (by positivity)
      (lintegral_planarNu_le p _ ξ)⟩
  set ε : ℕ → ℝ := fun m => C.toReal * (s * (1 / Real.sqrt ((3 : ℝ) ^ m) +
    Real.exp (-c₁ * (3 : ℝ) ^ m))) with hεdef
  have hstep : ∀ m m', m ≤ m' → planarNuMean p m' ξ ≤ planarNuMean p m ξ + ε m := by
    intro m m' hmm'
    have h := hmono ⟨m', 0⟩ ⟨m, 0⟩ hmm' ξ
    rw [← hs] at h
    have h' := ENNReal.toReal_mono
      (ENNReal.add_ne_top.2 ⟨hfin m, ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top⟩) h
    rw [ENNReal.toReal_add (hfin m) (ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h'
    exact h'
  have hε : Tendsto ε atTop (𝓝 0) := by
    have := ((tendsto_one_div_sqrt_three_pow.add (tendsto_exp_neg_mul_three_pow hc₁)).const_mul
      s).const_mul C.toReal
    simpa only [add_zero, mul_zero] using this
  obtain ⟨L, hL⟩ := exists_tendsto_of_le_add hbound hε hstep
  refine ⟨L, hL, ?_, le_of_tendsto' hL fun m => (hbound m).2⟩
  have hr : Tendsto (fun m : ℕ => C₀.toReal * (s * (1 / Real.sqrt ((3 : ℝ) ^ m)))) atTop
      (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_one_div_sqrt_three_pow.const_mul s).const_mul C₀.toReal
  have hlow' : ∀ m : ℕ, c₀ * (ξ 0 ^ 2 + ξ 1 ^ 2) ≤
      planarNuMean p m ξ + C₀.toReal * (s * (1 / Real.sqrt ((3 : ℝ) ^ m))) := by
    intro m
    have h := hlow ⟨m, 0⟩ ξ
    rw [← hs] at h
    have hsize : (((⟨m, 0⟩ : TriadicCube 2).toIntegerCube.size : ℕ) : ℝ) = (3 : ℝ) ^ m := by
      rw [show (⟨m, 0⟩ : TriadicCube 2).toIntegerCube.size = 3 ^ m from rfl]
      push_cast
      ring
    rw [hsize] at h
    have h' := ENNReal.toReal_mono
      (ENNReal.add_ne_top.2 ⟨hfin m, ENNReal.mul_ne_top hC₀ ENNReal.ofReal_ne_top⟩) h
    rw [ENNReal.toReal_add (hfin m) (ENNReal.mul_ne_top hC₀ ENNReal.ofReal_ne_top),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_ofReal (by positivity)] at h'
    calc c₀ * (ξ 0 ^ 2 + ξ 1 ^ 2) ≤ _ := h'
      _ = _ := by
        unfold planarNuMean
        ring
  have := ge_of_tendsto' (hL.add hr) hlow'
  simpa only [add_zero] using this

end Rigidity.Percolation
