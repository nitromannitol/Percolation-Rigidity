import Rigidity.Steps.S3.NotLipschitz

/-!
# `step:3.2-event`, mixed-Green-scale part

`GreenScaleEventStep` (corrected draft L982-983): if the minimal scales `M_y` satisfy the
stochastic integrability `M_y ≤ O_s(c)` (that is, `E[exp((M_y / c)^s)] ≤ 2`, as in (stoch.estMdecay)
of Proposition 2.8), then with probability tending to one they are all at most `N^{1/(10d²)}` on
`Q_N`. Proof: the Markov inequality for `exp((M_y / c)^s)` gives
`P(M_y > N^{1/(10d²)}) ≤ 2 exp(-(N^{1/(10d²)} / c)^s)`, the union bound over the `(2N + 1)^d`
points of `Q_N` multiplies it by a polynomial factor, and a stretched exponential beats any
polynomial.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Topology LatticeProb LatticeProb.Percolation Rigidity.Steps.S3

namespace Rigidity.Proofs.S3

/-- `|Q_N| = (2N + 1)^d`. -/
theorem card_latticeCube (d N : ℕ) : (latticeCube d N).card = (2 * N + 1) ^ d := by
  simp only [latticeCube, Fintype.card_piFinset, Int.card_Icc, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  congr 1
  omega

/-- The Markov inequality for the exponential moment: if `X ≤ O_s(c)`, i.e.
`E[exp((X / c)^s)] ≤ 2`, then `P(X > t) ≤ 2 exp(-(t / c)^s)` for every `t ≥ 0`. -/
theorem measure_lt_le_of_expMoment {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] {s c t : ℝ} (hs : 0 < s) (hc : 0 < c) (ht : 0 ≤ t) {X : Ω → ℝ}
    (hint : Integrable (fun ω => Real.exp (Real.rpow (X ω / c) s)) μ)
    (hle : (∫ ω, Real.exp (Real.rpow (X ω / c) s) ∂μ) ≤ 2) :
    μ {ω | t < X ω} ≤ ENNReal.ofReal (2 * Real.exp (-(t / c) ^ s)) := by
  set ε := Real.exp ((t / c) ^ s)
  have hsub : {ω | t < X ω} ⊆ {ω | ε ≤ Real.exp (Real.rpow (X ω / c) s)} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    rw [Real.exp_le_exp, Real.rpow_eq_pow]
    exact Real.rpow_le_rpow (div_nonneg ht hc.le) (div_le_div_of_nonneg_right hω.le hc.le) hs.le
  have hmarkov :=
    mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall fun ω => (Real.exp_pos _).le) hint ε
  have hreal : μ.real {ω | ε ≤ Real.exp (Real.rpow (X ω / c) s)} ≤
      2 * Real.exp (-(t / c) ^ s) := by
    rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _), mul_comm]
    exact hmarkov.trans hle
  calc μ {ω | t < X ω} ≤ μ {ω | ε ≤ Real.exp (Real.rpow (X ω / c) s)} := measure_mono hsub
    _ = ENNReal.ofReal (μ.real {ω | ε ≤ Real.exp (Real.rpow (X ω / c) s)}) :=
        (ofReal_measureReal (measure_ne_top _ _)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

/-- A stretched exponential beats the polynomial size of `Q_N`: for `a, s, c > 0`,
`(2N + 1)^d · 2 exp(-(N^a / c)^s) → 0`. -/
theorem tendsto_card_mul_exp_neg (d : ℕ) {a s c : ℝ} (ha : 0 < a) (hs : 0 < s) (hc : 0 < c) :
    Tendsto (fun N : ℕ => (((2 * N + 1) ^ d : ℕ) : ℝ) * (2 * Real.exp (-((N : ℝ) ^ a / c) ^ s)))
      atTop (𝓝 0) := by
  have hb : 0 < a * s := mul_pos ha hs
  have hk : 0 < (c ^ s)⁻¹ := inv_pos.mpr (Real.rpow_pos_of_pos hc s)
  have hx : Tendsto (fun N : ℕ => (N : ℝ) ^ (a * s)) atTop atTop :=
    (tendsto_rpow_atTop hb).comp tendsto_natCast_atTop_atTop
  have hG := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((d : ℝ) / (a * s)) _ hk).comp
    hx).const_mul (2 * 3 ^ d)
  rw [mul_zero] at hG
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hG
    (Eventually.of_forall fun N => by positivity) ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have h1 : ((N : ℝ) ^ (a * s)) ^ ((d : ℝ) / (a * s)) = (N : ℝ) ^ d := by
    rw [← Real.rpow_mul hN0, mul_div_cancel₀ _ hb.ne', Real.rpow_natCast]
  have h2 : ((N : ℝ) ^ a / c) ^ s = (c ^ s)⁻¹ * (N : ℝ) ^ (a * s) := by
    rw [Real.div_rpow (Real.rpow_nonneg hN0 a) hc.le, ← Real.rpow_mul hN0, div_eq_inv_mul]
  have h3 : (((2 * N + 1) ^ d : ℕ) : ℝ) ≤ 3 ^ d * (N : ℝ) ^ d := by
    rw [← mul_pow]
    push_cast
    exact pow_le_pow_left₀ (by positivity) (by linarith) d
  simp only [Function.comp_apply, h1, h2, neg_mul]
  calc (((2 * N + 1) ^ d : ℕ) : ℝ) * (2 * Real.exp (-((c ^ s)⁻¹ * (N : ℝ) ^ (a * s))))
      ≤ 3 ^ d * (N : ℝ) ^ d * (2 * Real.exp (-((c ^ s)⁻¹ * (N : ℝ) ^ (a * s)))) := by gcongr
    _ = _ := by ring

variable (d : ℕ) [NeZero d]

/-- `step:3.2-event`, mixed-Green-scale part: if every minimal scale satisfies `M_y ≤ O_s(c)`,
then `P(∃ y ∈ Q_N, M_y > N^{1/(10d²)}) ≤ (2N + 1)^d · 2 exp(-(N^{1/(10d²)} / c)^s) → 0`. -/
theorem greenScaleEventStep (p : unitInterval) : GreenScaleEventStep d p := by
  intro s c hs hc M _ hint hle
  set μ := latticeBondLaw d p
  set a : ℝ := 1 / (10 * (d : ℝ) ^ 2)
  have ha : 0 < a := by
    have : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
    positivity
  have hbound : ∀ N : ℕ, μ {ω | ∃ y ∈ latticeCube d N, (N : ℝ) ^ a < M y ω} ≤
      ENNReal.ofReal ((((2 * N + 1) ^ d : ℕ) : ℝ) * (2 * Real.exp (-((N : ℝ) ^ a / c) ^ s))) := by
    intro N
    have hset : {ω | ∃ y ∈ latticeCube d N, (N : ℝ) ^ a < M y ω} =
        ⋃ y ∈ latticeCube d N, {ω | (N : ℝ) ^ a < M y ω} := by
      ext ω
      simp
    rw [hset, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, ← card_latticeCube,
      ← nsmul_eq_mul, ← Finset.sum_const]
    exact (measure_biUnion_finset_le _ _).trans <| Finset.sum_le_sum fun y _ =>
      measure_lt_le_of_expMoment μ hs hc (by positivity) (hint y) (hle y)
  have hlim := ENNReal.tendsto_ofReal (tendsto_card_mul_exp_neg d ha hs hc)
  rw [ENNReal.ofReal_zero] at hlim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le) hbound

end Rigidity.Proofs.S3
