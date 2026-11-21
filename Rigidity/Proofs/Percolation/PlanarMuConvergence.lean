import Rigidity.Proofs.Percolation.PlanarMuStationarity
import Rigidity.Proofs.Percolation.PlanarNuConvergence

/-!
# Convergence of the expectation of `-μ` in the plane

The approximate subadditivity of `-μ` in expectation (Armstrong and Dario, (4.32)) and the
approximate stationarity of `μ` give the approximate monotonicity

`E[-μ(U, q); P, U res] ≤ E[-μ(V, q); P, V res] + C |q|₁² (3^(-n/2) + exp (-c 3ⁿ))`

for triadic cubes `V`, `U` of scales `n ≤ m`. Together with `0 ≤ E[-μ(V, q); P, V res] ≤
C |q|₁²` (Armstrong and Dario, (4.12) in expectation), the expectations of `-μ(□_m, q)` converge
as `m → ∞`, as stated in Armstrong and Dario, Section 5, after Definition 5.1, in dimension two.
-/

open MeasureTheory Filter Topology LatticeProb.Percolation Rigidity.External
  Rigidity.Proofs.Section5
open scoped ENNReal Classical

namespace Rigidity.Percolation

/-- **Approximate stationarity of `μ` between cubes of the same scale.** -/
theorem exists_lintegral_neg_planarMu_le_of_scale_eq {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∃ c : ℝ, 0 < c ∧ ∀ (V W : TriadicCube 2), V.scale = W.scale →
      ∀ q : Fin 2 → ℝ,
      ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω W then
          ENNReal.ofReal (-planarMu ω W q) else 0) ∂(latticeBondLaw 2 p) ≤
        ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω V then
          ENNReal.ofReal (-planarMu ω V q) else 0) ∂(latticeBondLaw 2 p) +
        C * ENNReal.ofReal ((|q 0| + |q 1|) ^ 2 * Real.exp (-c * (3 : ℝ) ^ V.scale)) := by
  obtain ⟨C, hC, c, hc, h⟩ := exists_lintegral_neg_planarMu_shift_le hpc
  refine ⟨C, hC, c, hc, fun V W hVW q => ?_⟩
  have hW := TriadicCube.shift_eq_of_scale_eq hVW
  have := h V (fun i => V.side * (W.index i - V.index i)) (fun i => Dvd.intro _ rfl) q
  rwa [hW] at this

/-- **Approximate monotonicity of `-μ`** (Armstrong and Dario, Section 5, in dimension two). For
triadic cubes `V`, `U` with the scale `n` of `V` at most that of `U`,
`E[-μ(U, q); P, U res] ≤ E[-μ(V, q); P, V res] + C |q|₁² (3^(-n/2) + exp (-c 3ⁿ))`. -/
theorem exists_lintegral_neg_planarMu_le_of_scale_le {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∃ c : ℝ, 0 < c ∧ ∀ (U V : TriadicCube 2), V.scale ≤ U.scale →
      ∀ q : Fin 2 → ℝ,
      ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
          ENNReal.ofReal (-planarMu ω U q) else 0) ∂(latticeBondLaw 2 p) ≤
        ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω V then
          ENNReal.ofReal (-planarMu ω V q) else 0) ∂(latticeBondLaw 2 p) +
        C * ENNReal.ofReal ((|q 0| + |q 1|) ^ 2 *
          (1 / Real.sqrt ((3 : ℝ) ^ V.scale) + Real.exp (-c * (3 : ℝ) ^ V.scale))) := by
  obtain ⟨C₁, hC₁, hsub⟩ := exists_lintegral_sum_planarMu_subcubes_sub_le hpc
  obtain ⟨C₂, hC₂, c, hc, hstat⟩ := exists_lintegral_neg_planarMu_le_of_scale_eq hpc
  refine ⟨C₁ + C₂, by finiteness, c, hc, fun U V hVU q => ?_⟩
  have hvol := U.volume_pos
  have hvol' := hvol.ne'
  have hpt : ∀ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
      ENNReal.ofReal (-planarMu ω U q) else 0) ≤
      ENNReal.ofReal (1 / U.volume) *
        ((if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
          ENNReal.ofReal (∑ x ∈ U.toIntegerCube.vertices,
            (if PlanarResolved ω (scaleCube V.scale x) then
              planarMu ω (scaleCube V.scale x) q else 0) - planarMu ω U q * U.volume)
          else 0) +
        ∑ x ∈ U.toIntegerCube.vertices,
          (if PlanarPartitionEvent ω ∧ PlanarResolved ω (scaleCube V.scale x) then
            ENNReal.ofReal (-planarMu ω (scaleCube V.scale x) q) else 0)) := by
    intro ω
    by_cases h : PlanarPartitionEvent ω ∧ PlanarResolved ω U
    · rw [if_pos h, if_pos h]
      have hnn : ∀ x ∈ U.toIntegerCube.vertices, 0 ≤ -(if PlanarResolved ω (scaleCube V.scale x)
          then planarMu ω (scaleCube V.scale x) q else 0) := fun x _ => by
        split_ifs with hx
        · exact neg_nonneg.2 (planarMu_nonpos h.1 hx q)
        · simp
      have hsum : ENNReal.ofReal (-∑ x ∈ U.toIntegerCube.vertices,
          (if PlanarResolved ω (scaleCube V.scale x) then
            planarMu ω (scaleCube V.scale x) q else 0)) =
          ∑ x ∈ U.toIntegerCube.vertices,
            (if PlanarPartitionEvent ω ∧ PlanarResolved ω (scaleCube V.scale x) then
              ENNReal.ofReal (-planarMu ω (scaleCube V.scale x) q) else 0) := by
        rw [← Finset.sum_neg_distrib, ENNReal.ofReal_sum_of_nonneg hnn]
        refine Finset.sum_congr rfl fun x _ => ?_
        by_cases hx : PlanarResolved ω (scaleCube V.scale x)
        · rw [if_pos hx, if_pos ⟨h.1, hx⟩]
        · rw [if_neg hx, if_neg fun h' => hx h'.2, neg_zero, ENNReal.ofReal_zero]
      rw [← hsum]
      set T := ∑ x ∈ U.toIntegerCube.vertices, (if PlanarResolved ω (scaleCube V.scale x) then
        planarMu ω (scaleCube V.scale x) q else 0)
      calc ENNReal.ofReal (-planarMu ω U q)
          = ENNReal.ofReal (1 / U.volume * ((T - planarMu ω U q * U.volume) + -T)) := by
            congr 1
            field_simp
            ring
        _ = ENNReal.ofReal (1 / U.volume) *
            ENNReal.ofReal ((T - planarMu ω U q * U.volume) + -T) :=
            ENNReal.ofReal_mul (by positivity)
        _ ≤ ENNReal.ofReal (1 / U.volume) *
            (ENNReal.ofReal (T - planarMu ω U q * U.volume) + ENNReal.ofReal (-T)) :=
            mul_le_mul' le_rfl ENNReal.ofReal_add_le
    · rw [if_neg h]
      exact zero_le
  have hcard : ((U.toIntegerCube.vertices.card : ℕ) : ℝ≥0∞) = ENNReal.ofReal U.volume := by
    rw [show U.volume = ((U.toIntegerCube.vertices.card : ℕ) : ℝ) from
      (card_toIntegerCube_vertices_eq U).symm, ENNReal.ofReal_natCast]
  have hinv : ENNReal.ofReal (1 / U.volume) * ENNReal.ofReal U.volume = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), one_div_mul_cancel hvol.ne', ENNReal.ofReal_one]
  set s := (|q 0| + |q 1|) ^ 2 with hs
  have hs0 : 0 ≤ s := by positivity
  set A := ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω V then
    ENNReal.ofReal (-planarMu ω V q) else 0) ∂(latticeBondLaw 2 p)
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
        ENNReal.ofReal (-planarMu ω (scaleCube V.scale x) q) else 0) :=
    fun x _ => measurable_planarMu_indicator _ q
  calc ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
        ENNReal.ofReal (-planarMu ω U q) else 0) ∂(latticeBondLaw 2 p)
      ≤ ∫⁻ ω, ENNReal.ofReal (1 / U.volume) *
        ((if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
          ENNReal.ofReal (∑ x ∈ U.toIntegerCube.vertices,
            (if PlanarResolved ω (scaleCube V.scale x) then
              planarMu ω (scaleCube V.scale x) q else 0) - planarMu ω U q * U.volume)
          else 0) +
        ∑ x ∈ U.toIntegerCube.vertices,
          (if PlanarPartitionEvent ω ∧ PlanarResolved ω (scaleCube V.scale x) then
            ENNReal.ofReal (-planarMu ω (scaleCube V.scale x) q) else 0))
          ∂(latticeBondLaw 2 p) := lintegral_mono hpt
    _ = ENNReal.ofReal (1 / U.volume) *
        (∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
          ENNReal.ofReal (∑ x ∈ U.toIntegerCube.vertices,
            (if PlanarResolved ω (scaleCube V.scale x) then
              planarMu ω (scaleCube V.scale x) q else 0) - planarMu ω U q * U.volume)
          else 0) ∂(latticeBondLaw 2 p) +
        ∑ x ∈ U.toIntegerCube.vertices,
          ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω (scaleCube V.scale x) then
            ENNReal.ofReal (-planarMu ω (scaleCube V.scale x) q) else 0)
              ∂(latticeBondLaw 2 p)) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_add_right _ (Finset.measurable_sum _ hmeas), lintegral_finsetSum _ hmeas]
    _ ≤ ENNReal.ofReal (1 / U.volume) *
        (C₁ * ENNReal.ofReal (s * U.volume / Real.sqrt ((3 : ℝ) ^ V.scale)) +
          ∑ _x ∈ U.toIntegerCube.vertices,
            (A + C₂ * ENNReal.ofReal (s * Real.exp (-c * (3 : ℝ) ^ V.scale)))) := by
        gcongr with x hx
        · exact hsub U V.scale hVU q
        · exact hstat V (scaleCube V.scale x) (scale_scaleCube V.scale x).symm q
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

/-- The expectation `E[-μ(□_m, q); P, □_m res]` on the triadic cube `□_m` of scale `m` centred at
the origin. -/
noncomputable def planarMuMean (p : unitInterval) (m : ℕ) (q : Fin 2 → ℝ) : ℝ :=
  (∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω ⟨m, 0⟩ then
    ENNReal.ofReal (-planarMu ω ⟨m, 0⟩ q) else 0) ∂(latticeBondLaw 2 p)).toReal

/-- **Convergence of `E[-μ(□_m, q)]`** (Armstrong and Dario, Section 5, after Definition 5.1, in
dimension two). For `p > p_c(2)`, the expectations of `-μ(□_m, q)` converge as `m → ∞`, and the
limit lies between `0` and `C |q|₁²`, with `C` independent of `q`. -/
theorem exists_tendsto_planarMuMean {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : Fin 2 → ℝ, ∃ L : ℝ,
      Tendsto (fun m => planarMuMean p m q) atTop (𝓝 L) ∧
        0 ≤ L ∧ L ≤ C * (|q 0| + |q 1|) ^ 2 := by
  obtain ⟨C, hC, c₁, hc₁, hmono⟩ := exists_lintegral_neg_planarMu_le_of_scale_le hpc
  obtain ⟨C₀, hC₀, hup⟩ := exists_lintegral_neg_planarMu_le hpc
  refine ⟨C₀.toReal, ENNReal.toReal_nonneg, fun q => ?_⟩
  set s := (|q 0| + |q 1|) ^ 2 with hs
  have hs0 : 0 ≤ s := by positivity
  have hbound' : ∀ m : ℕ, ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω ⟨m, 0⟩ then
      ENNReal.ofReal (-planarMu ω ⟨m, 0⟩ q) else 0) ∂(latticeBondLaw 2 p) ≤
        ENNReal.ofReal (C₀.toReal * s) := fun m => by
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hC₀]
    exact hup _ q
  have hfin : ∀ m : ℕ, ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω ⟨m, 0⟩ then
      ENNReal.ofReal (-planarMu ω ⟨m, 0⟩ q) else 0) ∂(latticeBondLaw 2 p) ≠ ∞ :=
    fun m => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hbound' m)
  have hbound : ∀ m, planarMuMean p m q ∈ Set.Icc 0 (C₀.toReal * s) := fun m =>
    ⟨ENNReal.toReal_nonneg, ENNReal.toReal_le_of_le_ofReal (by positivity) (hbound' m)⟩
  set ε : ℕ → ℝ := fun m => C.toReal * (s * (1 / Real.sqrt ((3 : ℝ) ^ m) +
    Real.exp (-c₁ * (3 : ℝ) ^ m))) with hεdef
  have hstep : ∀ m m', m ≤ m' → planarMuMean p m' q ≤ planarMuMean p m q + ε m := by
    intro m m' hmm'
    have h := hmono ⟨m', 0⟩ ⟨m, 0⟩ hmm' q
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
  exact ⟨L, hL, ge_of_tendsto' hL fun m => (hbound m).1, le_of_tendsto' hL fun m => (hbound m).2⟩

end Rigidity.Percolation
