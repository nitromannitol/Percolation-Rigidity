import Rigidity.Proofs.Corrector.DarioLinftyIteration

/-!
# Steps 5 and 6 of the proof of Dario's Theorem 1, in dimension two

* Step 5 (`isOsBond_sub_of_linftyIterationData`): the moment bound of Steps 1–4,
  `E|F_0(x) - F_0(0)|^q ≤ (K q^k)^q (m+2)^{q/2}` with `3^m ≤ |x|_∞ < 3^{m+1}`, gives
  `|F_0(x) - F_0(0)| ≤ O_s(C log^{1/2}(2 + |x|))` for every `s < 1/k` (`isOsBond_of_moment_le`),
  since `m + 2 ≤ (3 / log 2) log(2 + |x|)`.
* Step 6 and the assembly (`darioOptimalCorrectorTwo_of_coarsened`): the coarsening error
  `|χ_p(x) - [χ_p]_𝒫(x)| 1_{x ∈ 𝒞_∞} ≤ O_s(C)` of Step 6 (5.10), taken as a hypothesis
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
theorem isOsBond_sub_of_linftyIterationData {p : unitInterval} {A B k : ℝ} (hA : 0 ≤ A)
    {s : ℝ} (hs : 0 < s) (hsk : s * k < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ F : Vertex 2 → Vertex 2 → Configuration 2 → ℝ,
      LinftyIterationData p F A B k → ∀ x : Vertex 2,
      IsOsBond 2 p (fun ω => |F 0 x ω - F 0 0 ω|) s
        (C * Real.sqrt (Real.log (2 + ‖latticeEuclideanEmbedding x‖))) := by
  obtain ⟨C₁, hC₁, hmom⟩ := isOsBond_of_moment_le (d := 2) (p := p) (A := 1) one_pos hs hsk
  set K := 6084 * max A B with hK
  have hK0 : 0 ≤ K := by
    have : 0 ≤ max A B := le_trans hA (le_max_left _ _)
    positivity
  set K₀ := 3 / Real.log 2 with hK₀
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK₀0 : 0 < K₀ := by positivity
  refine ⟨C₁ * (K + 1) * Real.sqrt K₀, by positivity, fun F hD x => ?_⟩
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


/-! ### Step 6 and the assembly -/

theorem latticeEuclideanEmbedding_sub (x y : Vertex 2) :
    latticeEuclideanEmbedding (x - y) = latticeEuclideanEmbedding x - latticeEuclideanEmbedding y := by
  refine PiLp.ext fun i => ?_
  rw [PiLp.sub_apply]
  change (((x - y) i : ℤ) : ℝ) = ((x i : ℤ) : ℝ) - ((y i : ℤ) : ℝ)
  rw [Pi.sub_apply, Int.cast_sub]

/-- The scale `0` is degenerate: `X ≤ O_s(0)` for every `X`, since `X/0 = 0`. -/
theorem isOsBond_zero_scale {p : unitInterval} (X : Configuration 2 → ℝ) {s : ℝ} (hs : 0 < s) :
    IsOsBond 2 p X s 0 := by
  have h1 : ∀ ω, Real.exp (Real.rpow (max (X ω / 0) 0) s) = 1 := by
    intro ω
    rw [div_zero, max_self]
    change Real.exp ((0 : ℝ) ^ s) = 1
    rw [Real.zero_rpow hs.ne', Real.exp_zero]
  unfold IsOsBond
  simp only [h1]
  exact ⟨integrable_const 1, by simp⟩

/-- **The coarsening error of Dario, Step 6 (5.10), for increments** (hypothesis): for
every slope `e_i` and points `x, y`, there is `E ≤ O_{s₆}(C₆)` such that for every corrected plane
`ℓ` of slope `e_i`, the corrector increment `χ(x) - χ(y)` differs from the field increment
`G i y 0 (x - y) - G i y 0 0` by at most `E`. This is (5.10) at `x` and at `y` combined by
the triangle inequality. -/
def CoarseningErrorTwo (p : unitInterval)
    (G : Fin 2 → Vertex 2 → Vertex 2 → Vertex 2 → Configuration 2 → ℝ) (s₆ C₆ : ℝ) : Prop :=
  ∀ (i : Fin 2) (x y : Vertex 2), ∃ E : Configuration 2 → ℝ, Measurable E ∧
    IsOsBond 2 p E s₆ C₆ ∧
    ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω,
      ∀ ℓ : uniqueInfiniteComponent h → ℝ,
        IsCorrectedPlane (uniqueInfiniteComponent h) (Pi.single i 1) ℓ →
      ∀ (hx : x ∈ (uniqueInfiniteComponent h).supp) (hy : y ∈ (uniqueInfiniteComponent h).supp),
        |((ℓ ⟨x, hx⟩ - ∑ j, (Pi.single i (1 : ℝ) : Fin 2 → ℝ) j * x j) -
            (ℓ ⟨y, hy⟩ - ∑ j, (Pi.single i (1 : ℝ) : Fin 2 → ℝ) j * y j)) -
          (G i y 0 (x - y) ω - G i y 0 0 ω)| ≤ E ω

/-- **The coarsened corrector of Dario, §5, in dimension two** (hypothesis): for every base point
`y` and every coordinate slope `e_i`, fields `G i y` satisfying the hypotheses of Steps 1–4
(`LinftyIterationData`; `G i y y' z` stands for `[χ_{e_i}]_{𝒫_{y + y'}}(y + z)`), and the
coarsening error of Step 6 (`CoarseningErrorTwo`). -/
def DarioCoarsenedCorrectorTwo (p : unitInterval) : Prop :=
  ∃ A B k s₆ C₆ : ℝ, 0 < s₆ ∧ 0 < C₆ ∧
    ∃ G : Fin 2 → Vertex 2 → Vertex 2 → Vertex 2 → Configuration 2 → ℝ,
      (∀ i y, LinftyIterationData p (G i y) A B k) ∧ CoarseningErrorTwo p G s₆ C₆

/-- **Dario's Theorem 1 in dimension two** (`DarioOptimalCorrectorTwo`) from the coarsened
corrector data of §5 (`DarioCoarsenedCorrectorTwo`: Theorem 2 at the box, the stationarity, the
comparison of the translated partitions and the coarsening error) and the planar qualitative
corrector input (linearity of the corrector in the slope). -/
theorem darioOptimalCorrectorTwo_of_coarsened
    (hG : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      DarioCoarsenedCorrectorTwo p)
    (hC : SupercriticalBondCorrectorInputTwo) : DarioOptimalCorrectorTwo := by
  intro p hpc hp1
  obtain ⟨A, B, k, s₆, C₆, hs₆, hC₆, G, hGD, hE⟩ := hG p hpc hp1
  have hA : 0 ≤ A := (hGD 0 0).hA
  set s₅ : ℝ := 1 / (2 * (|k| + 1)) with hs₅def
  have hs₅ : 0 < s₅ := by positivity
  have hs₅k : s₅ * k < 1 := by
    have hk : k ≤ |k| := le_abs_self k
    rw [hs₅def, div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]
    linarith [abs_nonneg k]
  obtain ⟨C₅, hC₅, h5⟩ := isOsBond_sub_of_linftyIterationData (p := p) (B := B) hA hs₅ hs₅k
  set s' := min s₆ s₅ with hs'def
  have hs' : 0 < s' := lt_min hs₆ hs₅
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set Θ : ℝ := 2 * ((C₆ * 6 ^ (1 / s') / Real.sqrt (Real.log 2) + C₅ * 6 ^ (1 / s')) *
    4 ^ (1 / s')) with hΘ
  have hΘ0 : 0 < Θ := by positivity
  refine ⟨s', Θ * 4 ^ (1 / s'), hs', by positivity, fun q x y => ?_⟩
  set L := Real.log (2 + ‖latticeEuclideanEmbedding x - latticeEuclideanEmbedding y‖) with hL
  have hL2 : Real.log 2 ≤ L :=
    Real.log_le_log (by norm_num) (by linarith [norm_nonneg (latticeEuclideanEmbedding x -
      latticeEuclideanEmbedding y)])
  have hL0 : 0 < L := lt_of_lt_of_le hl2 hL2
  have hsqL : Real.sqrt (Real.log 2) ≤ Real.sqrt L := Real.sqrt_le_sqrt hL2
  have hsl2 : 0 < Real.sqrt (Real.log 2) := Real.sqrt_pos.2 hl2
  choose E hEm hEO hEae using fun i : Fin 2 => hE i x y
  set Gd : Fin 2 → Configuration 2 → ℝ := fun i ω => |G i y 0 (x - y) ω - G i y 0 0 ω| with hGd
  have hGdm : ∀ i, Measurable (Gd i) := fun i =>
    (((hGD i y).meas 0 (x - y)).sub ((hGD i y).meas 0 0)).abs
  have hGdO : ∀ i, IsOsBond 2 p (Gd i) s₅ (C₅ * Real.sqrt L) := by
    intro i
    have := h5 (G i y) (hGD i y) (x - y)
    rwa [latticeEuclideanEmbedding_sub] at this
  set Y : Fin 2 → Configuration 2 → ℝ := fun i ω => 2 * max (E i ω) (Gd i ω) with hY
  have hYm : ∀ i, Measurable (Y i) := fun i => ((hEm i).max (hGdm i)).const_mul 2
  have hYO : ∀ i, IsOsBond 2 p (Y i) s' (Θ * Real.sqrt L) := by
    intro i
    have hE' := IsOsBond.mono_exponent hs' (min_le_left _ _) (hEm i) (hEO i)
    have hG' := IsOsBond.mono_exponent hs' (min_le_right _ _) (hGdm i) (hGdO i)
    have hmax := IsOsBond.max hs' (by positivity) (by positivity) (hEm i) (hGdm i) hE' hG'
    have h2 := IsOsBond.const_mul (two_pos) hmax
    refine IsOsBond.mono_scale hs' (by positivity) ?_ (hYm i) h2
    have hC6 : C₆ * 6 ^ (1 / s') ≤ C₆ * 6 ^ (1 / s') / Real.sqrt (Real.log 2) * Real.sqrt L := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hsl2]
      exact mul_le_mul_of_nonneg_left hsqL (by positivity)
    have hmx : max (C₆ * 6 ^ (1 / s')) (C₅ * Real.sqrt L * 6 ^ (1 / s')) ≤
        (C₆ * 6 ^ (1 / s') / Real.sqrt (Real.log 2) + C₅ * 6 ^ (1 / s')) * Real.sqrt L := by
      refine max_le ?_ ?_
      · have : 0 ≤ C₅ * 6 ^ (1 / s') * Real.sqrt L := by positivity
        nlinarith
      · have : 0 ≤ C₆ * 6 ^ (1 / s') / Real.sqrt (Real.log 2) * Real.sqrt L := by positivity
        nlinarith
    rw [hΘ]
    calc 2 * (max (C₆ * 6 ^ (1 / s')) (C₅ * Real.sqrt L * 6 ^ (1 / s')) * 4 ^ (1 / s'))
        ≤ 2 * ((C₆ * 6 ^ (1 / s') / Real.sqrt (Real.log 2) + C₅ * 6 ^ (1 / s')) * Real.sqrt L *
          4 ^ (1 / s')) := by gcongr
      _ = _ := by ring
  set Ym : Configuration 2 → ℝ := fun ω => max (Y 0 ω) (Y 1 ω) with hYmdef
  have hYmm : Measurable Ym := (hYm 0).max (hYm 1)
  have hYmO : IsOsBond 2 p Ym s' (Θ * 4 ^ (1 / s') * Real.sqrt L) := by
    have := IsOsBond.max hs' (by positivity) (by positivity) (hYm 0) (hYm 1) (hYO 0) (hYO 1)
    rw [max_self] at this
    have e : Θ * 4 ^ (1 / s') * Real.sqrt L = Θ * Real.sqrt L * 4 ^ (1 / s') := by ring
    rw [e]
    exact this
  set Q := ∑ i, |q i| with hQ
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun i _ => abs_nonneg _
  refine ⟨fun ω => Q * Ym ω, hYmm.const_mul Q, ?_, ?_⟩
  · rcases hQ0.eq_or_lt with hQz | hQp
    · rw [← hQz, mul_zero, zero_mul]
      exact isOsBond_zero_scale _ hs'
    · have := IsOsBond.const_mul hQp hYmO
      convert this using 1
      ring
  · filter_upwards [hEae 0, hEae 1, hC p hpc hp1] with ω h0 h1 hR2
    intro h ℓ hℓ hx hy
    obtain ⟨ℓ₀, ⟨hℓ₀, -⟩, -⟩ := (hR2 h).1 (Pi.single 0 1) ⟨x, hx⟩
    obtain ⟨ℓ₁, ⟨hℓ₁, -⟩, -⟩ := (hR2 h).1 (Pi.single 1 1) ⟨x, hx⟩
    have hlin := corrector_sub_eq (hR2 h).1 hℓ hℓ₀ hℓ₁ ⟨x, hx⟩ ⟨y, hy⟩
    dsimp only at hlin
    have hi : ∀ i : Fin 2, ∀ ℓi : uniqueInfiniteComponent h → ℝ,
        IsCorrectedPlane (uniqueInfiniteComponent h) (Pi.single i 1) ℓi →
        |(ℓi ⟨x, hx⟩ - ∑ j, (Pi.single i (1 : ℝ) : Fin 2 → ℝ) j * x j) -
          (ℓi ⟨y, hy⟩ - ∑ j, (Pi.single i (1 : ℝ) : Fin 2 → ℝ) j * y j)| ≤ Y i ω := by
      intro i ℓi hℓi
      have hb : |((ℓi ⟨x, hx⟩ - ∑ j, (Pi.single i (1 : ℝ) : Fin 2 → ℝ) j * x j) -
          (ℓi ⟨y, hy⟩ - ∑ j, (Pi.single i (1 : ℝ) : Fin 2 → ℝ) j * y j)) -
          (G i y 0 (x - y) ω - G i y 0 0 ω)| ≤ E i ω := by
        fin_cases i
        · exact h0 h ℓi hℓi hx hy
        · exact h1 h ℓi hℓi hx hy
      have hle : |(ℓi ⟨x, hx⟩ - ∑ j, (Pi.single i (1 : ℝ) : Fin 2 → ℝ) j * x j) -
          (ℓi ⟨y, hy⟩ - ∑ j, (Pi.single i (1 : ℝ) : Fin 2 → ℝ) j * y j)| ≤ E i ω + Gd i ω := by
        have := abs_sub_abs_le_abs_sub ((ℓi ⟨x, hx⟩ - ∑ j, (Pi.single i (1 : ℝ) : Fin 2 → ℝ) j *
          x j) - (ℓi ⟨y, hy⟩ - ∑ j, (Pi.single i (1 : ℝ) : Fin 2 → ℝ) j * y j))
          (G i y 0 (x - y) ω - G i y 0 0 ω)
        simp only [hGd]
        linarith
      calc _ ≤ E i ω + Gd i ω := hle
        _ ≤ 2 * max (E i ω) (Gd i ω) := by
            have := le_max_left (E i ω) (Gd i ω)
            have := le_max_right (E i ω) (Gd i ω)
            linarith
    have hb0 := hi 0 ℓ₀ hℓ₀
    have hb1 := hi 1 ℓ₁ hℓ₁
    change |(ℓ ⟨x, hx⟩ - ∑ i, q i * x i) - (ℓ ⟨y, hy⟩ - ∑ i, q i * y i)| ≤ Q * Ym ω
    rw [hlin]
    have hY0 : Y 0 ω ≤ Ym ω := le_max_left _ _
    have hY1 : Y 1 ω ≤ Ym ω := le_max_right _ _
    calc _ ≤ |q 0| * Y 0 ω + |q 1| * Y 1 ω := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul]
          exact add_le_add (mul_le_mul_of_nonneg_left hb0 (abs_nonneg _))
            (mul_le_mul_of_nonneg_left hb1 (abs_nonneg _))
      _ ≤ (|q 0| + |q 1|) * Ym ω := by
          nlinarith [abs_nonneg (q 0), abs_nonneg (q 1)]
      _ = Q * Ym ω := by rw [hQ, Fin.sum_univ_two]

end Rigidity.Corrector
