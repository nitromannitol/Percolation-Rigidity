import Rigidity.Proofs.Corrector.DarioLinftyIteration

/-!
# Steps 5 and 6 of the proof of Dario's Theorem 1, in dimension two

* Step 5 (`isOsBond_sub_of_linftyIterationData`): the moment bound of Steps 1–4,
  `E|F_0(x) - F_0(0)|^q ≤ (K q^k)^q (m+2)^{q/2}` with `3^m ≤ |x|_∞ < 3^{m+1}`, gives
  `|F_0(x) - F_0(0)| ≤ O_s(C log^{1/2}(2 + |x|))` for every `s < 1/k` (`isOsBond_of_moment_le`),
  since `m + 2 ≤ (3 / log 2) log(2 + |x|)`.
* Step 6 and the assembly (`darioOptimalCorrectorTwo_of_coarsened`): the coarsening error
  `|χ_p(x) - [χ_p]_𝒫(x)| 1_{x ∈ 𝒞_∞} ≤ O_s(C)` of Step 6 (eq:TV10432302), taken as a hypothesis
  for the increments between two points, and the uniqueness of corrected planes, which gives the
  bound for every slope from the two coordinate slopes, give `DarioOptimalCorrectorTwo`.

The base point `y = 0` of Dario's proof ("by the stationarity of the gradient of the corrector we
can assume that `y = 0`") is kept general: the hypothesis `DarioCoarsenedCorrectorTwo` provides,
for each base point `y` and each coordinate slope, the fields of `LinftyIterationData` re-centred at
`y`.
-/

namespace Rigidity.Corrector

open MeasureTheory Filter Set LatticeProb.Percolation Rigidity.External Rigidity.Proofs.S2
open scoped ENNReal

/-- A triadic scale adapted to `x`: `m ≥ 1`, `|x|_∞ < 3^{m+1}` and
`m + 2 ≤ (3 / log 2) log(2 + |x|)`. -/
theorem exists_scale_le_log (x : Vertex 2) :
    ∃ m : ℕ, 1 ≤ m ∧ (∀ i, |x i| < ((3 ^ (m + 1) : ℕ) : ℤ)) ∧
      (m : ℝ) + 2 ≤ 3 / Real.log 2 * Real.log (2 + ‖latticeEuclideanEmbedding x‖) := by
  set r := ‖latticeEuclideanEmbedding x‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg _
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl3 : Real.log 2 < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  have hL2 : Real.log 2 ≤ Real.log (2 + r) := Real.log_le_log (by norm_num) (by linarith)
  have hcoord : ∀ i, (|x i| : ℝ) ≤ r := by
    intro i
    have h := PiLp.norm_apply_le (latticeEuclideanEmbedding x) i
    change ‖((x i : ℤ) : ℝ)‖ ≤ r at h
    rwa [Real.norm_eq_abs] at h
  set n : ℕ := max (x 0).natAbs (x 1).natAbs with hn
  have hxn : ∀ i, |x i| ≤ (n : ℤ) := by
    intro i
    fin_cases i
    · rw [Int.abs_eq_natAbs]; exact_mod_cast le_max_left _ _
    · rw [Int.abs_eq_natAbs]; exact_mod_cast le_max_right _ _
  have hnr : (n : ℝ) ≤ r := by
    have hc : ∀ i, (((x i).natAbs : ℕ) : ℝ) ≤ r := by
      intro i
      rw [Nat.cast_natAbs, Int.cast_abs]
      exact hcoord i
    rcases max_choice (x 0).natAbs (x 1).natAbs with h | h
    · rw [hn, h]
      exact hc 0
    · rw [hn, h]
      exact hc 1
  by_cases hsmall : n < 9
  · refine ⟨1, le_rfl, fun i => ?_, ?_⟩
    · have := hxn i
      norm_num
      omega
    · rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
      push_cast
      nlinarith
  · have hsmall' : 9 ≤ n := not_lt.1 hsmall
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    obtain ⟨j, hj1, hj2⟩ := exists_nat_pow_near hn1 (by norm_num : (1 : ℝ) < 3)
    have hj2' : n < 3 ^ (j + 1) := by exact_mod_cast hj2
    have hjge : 2 ≤ j := by
      by_contra h
      have h' : j < 2 := not_le.1 h
      have : 3 ^ (j + 1) ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    refine ⟨j, by omega, fun i => ?_, ?_⟩
    · have := hxn i
      have h' : ((n : ℕ) : ℤ) < ((3 ^ (j + 1) : ℕ) : ℤ) := by exact_mod_cast hj2'
      linarith
    · have hlogj : (j : ℝ) * Real.log 3 ≤ Real.log (2 + r) := by
        have h1 : Real.log ((3 : ℝ) ^ j) ≤ Real.log (2 + r) :=
          Real.log_le_log (by positivity) (by linarith)
        rwa [Real.log_pow] at h1
      have hj2r : (2 : ℝ) ≤ j := by exact_mod_cast hjge
      rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
      have hl3pos : 0 < Real.log 3 := by linarith
      nlinarith

/-- **Dario, Step 5 of the proof of Theorem 1**: under the hypotheses of Steps 1–4, for every
`s < 1/k`, `|F_0(x) - F_0(0)| ≤ O_s(C log^{1/2}(2 + |x|))` with `C` independent of `x`. -/
theorem isOsBond_sub_of_linftyIterationData {p : unitInterval}
    {F : Vertex 2 → Vertex 2 → Configuration 2 → ℝ} {A B k : ℝ}
    (hD : LinftyIterationData p F A B k) {s : ℝ} (hs : 0 < s) (hsk : s * k < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : Vertex 2,
      IsOsBond 2 p (fun ω => |F 0 x ω - F 0 0 ω|) s
        (C * Real.sqrt (Real.log (2 + ‖latticeEuclideanEmbedding x‖))) := by
  obtain ⟨C₁, hC₁, hmom⟩ := isOsBond_of_moment_le (d := 2) (p := p) (A := 1) one_pos hs hsk
  set K := 6084 * max A B with hK
  have hK0 : 0 ≤ K := by
    have := hD.hA
    have : 0 ≤ max A B := le_trans hD.hA (le_max_left _ _)
    positivity
  set K₀ := 3 / Real.log 2 with hK₀
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK₀0 : 0 < K₀ := by positivity
  refine ⟨C₁ * (K + 1) * Real.sqrt K₀, by positivity, fun x => ?_⟩
  obtain ⟨m, hm1, hx, hmL⟩ := exists_scale_le_log x
  set L := Real.log (2 + ‖latticeEuclideanEmbedding x‖) with hL
  have hL0 : 0 < L := Real.log_pos (by linarith [norm_nonneg (latticeEuclideanEmbedding x)])
  set c := (K + 1) * Real.sqrt (K₀ * L) with hc
  have hc0 : 0 < c := by positivity
  have hXm : Measurable fun ω => |F 0 x ω - F 0 0 ω| / c :=
    ((hD.meas 0 x).sub (hD.meas 0 0)).abs.div_const c
  have hX : IsOsBond 2 p (fun ω => |F 0 x ω - F 0 0 ω| / c) s C₁ := by
    refine hmom _ hXm (fun ω => by positivity) fun q hq => ?_
    have hq0 : (0 : ℝ) ≤ q := by linarith
    have hmom' := hD.mom_sub_le hm1 hx hq
    -- the moment of `X = |F_0(x) - F_0(0)| / c`
    have hpt : ∀ ω, (|F 0 x ω - F 0 0 ω| / c) ^ q = |F 0 x ω - F 0 0 ω| ^ q / c ^ q :=
      fun ω => Real.div_rpow (abs_nonneg _) hc0.le q
    have hbound : (K * q ^ k) ^ q * ((m : ℝ) + 2) ^ (q / 2) / c ^ q ≤ (1 * q ^ k) ^ q := by
      have hqk : 0 ≤ q ^ k := Real.rpow_nonneg hq0 k
      rw [div_le_iff₀ (Real.rpow_pos_of_pos hc0 q), one_mul]
      have h1 : (K * q ^ k) ^ q ≤ ((K + 1) * q ^ k) ^ q :=
        Real.rpow_le_rpow (by positivity) (by nlinarith) hq0
      have h2 : ((m : ℝ) + 2) ^ (q / 2) ≤ Real.sqrt (K₀ * L) ^ q := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity), one_div_mul_eq_div]
        exact Real.rpow_le_rpow (by positivity) hmL (by positivity)
      calc (K * q ^ k) ^ q * ((m : ℝ) + 2) ^ (q / 2) ≤ ((K + 1) * q ^ k) ^ q *
            Real.sqrt (K₀ * L) ^ q := mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = (q ^ k) ^ q * c ^ q := by
            rw [hc, Real.mul_rpow (show (0 : ℝ) ≤ K + 1 by positivity) hqk,
              Real.mul_rpow (show (0 : ℝ) ≤ K + 1 by positivity) (Real.sqrt_nonneg (K₀ * L))]
            ring
    have hlin : ∫⁻ ω, ENNReal.ofReal ((|F 0 x ω - F 0 0 ω| / c) ^ q) ∂latticeBondLaw 2 p ≤
        ENNReal.ofReal ((1 * q ^ k) ^ q) := by
      calc ∫⁻ ω, ENNReal.ofReal ((|F 0 x ω - F 0 0 ω| / c) ^ q) ∂latticeBondLaw 2 p
          = ∫⁻ ω, ENNReal.ofReal (|F 0 x ω - F 0 0 ω| ^ q) * ENNReal.ofReal (1 / c ^ q)
              ∂latticeBondLaw 2 p := by
            refine lintegral_congr fun ω => ?_
            rw [hpt, ← ENNReal.ofReal_mul (by positivity), mul_one_div]
        _ = mom p (fun ω => F 0 x ω - F 0 0 ω) q * ENNReal.ofReal (1 / c ^ q) :=
            lintegral_mul_const _ (measurable_ofReal_abs_rpow ((hD.meas 0 x).sub (hD.meas 0 0)) q)
        _ ≤ ENNReal.ofReal ((K * q ^ k) ^ q * ((m : ℝ) + 2) ^ (q / 2)) *
              ENNReal.ofReal (1 / c ^ q) := by gcongr
        _ = ENNReal.ofReal ((K * q ^ k) ^ q * ((m : ℝ) + 2) ^ (q / 2) / c ^ q) := by
            rw [← ENNReal.ofReal_mul (by positivity), mul_one_div]
        _ ≤ ENNReal.ofReal ((1 * q ^ k) ^ q) := ENNReal.ofReal_le_ofReal hbound
    have hmq : Measurable fun ω => (|F 0 x ω - F 0 0 ω| / c) ^ q := hXm.pow_const q
    have hnn : 0 ≤ᵐ[latticeBondLaw 2 p] fun ω => (|F 0 x ω - F 0 0 ω| / c) ^ q :=
      Eventually.of_forall fun ω => by positivity
    have hint : Integrable (fun ω => (|F 0 x ω - F 0 0 ω| / c) ^ q) (latticeBondLaw 2 p) := by
      refine ⟨hmq.aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal hnn]
      exact lt_of_le_of_lt hlin ENNReal.ofReal_lt_top
    refine ⟨hint, ?_⟩
    rw [integral_eq_lintegral_of_nonneg_ae hnn hmq.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hlin
  have h2 := IsOsBond.const_mul hc0 hX
  have heq : (fun ω => c * (|F 0 x ω - F 0 0 ω| / c)) = fun ω => |F 0 x ω - F 0 0 ω| := by
    funext ω
    field_simp
  have hscale : c * C₁ = C₁ * (K + 1) * Real.sqrt K₀ * Real.sqrt L := by
    rw [hc, Real.sqrt_mul hK₀0.le]
    ring
  rw [heq, hscale] at h2
  exact h2

end Rigidity.Corrector
