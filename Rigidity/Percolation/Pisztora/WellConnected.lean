import Rigidity.Percolation.Pisztora.CubeEstimates
import Rigidity.Percolation.Blocks.SlabConnectivity
import Rigidity.Proofs.Percolation.PositiveCriticalProbability

/-!
# Well-connected cubes in dimension at least three

Above the critical point in dimension `d ≥ 3`, uniform slab connectivity (the Grimmett–Marstrand
theorem, `uniformCubeSlabConnectivity_of_criticalProbability_lt`) gives, for every cube `z + Q_M`
and `t = ⌊M^{1/d} / (4 · 100^{1/d})⌋`, a crossing component joining all open paths of `ℓ¹`-radius
larger than `8t/10`, except with probability at most a polynomial in `M` times `exp(-c t)`
(`crossing_fail_le`). Since `100 (4t)^d ≤ M`, this component is a largest cluster and the cube is
good and crossing (`isGoodSubcube_of_root_coalesce`). Hence `z + Q_M` fails to be good with
probability at most `K exp(-κ M^{1/d})` (`exists_not_goodSubcube_le`).

A union bound over the cube `x + Q_N` and the at most `(4N + 1)^d (N + 1)` cubes `z + Q_M` with
`N^{1/(10d)²}/2 ≤ M ≤ N/10` meeting it proves Proposition 2.3 of the paper in dimension
`d ≥ 3` with the exponent `s = 1/(100 d³)` (`wellConnected_of_three_le`). This is the derivation
stated with the input `Rigidity.External.WellConnectedInput`, with the box estimate of Pisztora
(1996) replaced by the slab estimate above. Together with the planar case it gives the input
(`wellConnectedInput_of_planar`).
-/

noncomputable section

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory Rigidity.External
open scoped ENNReal

variable {d : ℕ}

/-! ### Elementary bounds -/

/-- A probability is at most `K exp(-κ x)` whenever `x ≤ x₀` and `exp(κ x₀) ≤ K`. -/
theorem measure_le_ofReal_exp_of_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (s : Set Ω) {K κ x x₀ : ℝ} (hκ : 0 ≤ κ)
    (hK : Real.exp (κ * x₀) ≤ K) (hx : x ≤ x₀) :
    μ s ≤ ENNReal.ofReal (K * Real.exp (-(κ * x))) := by
  refine prob_le_one.trans ?_
  rw [← ENNReal.ofReal_one]
  refine ENNReal.ofReal_le_ofReal ?_
  have hK0 : 0 ≤ K := (Real.exp_pos _).le.trans hK
  calc (1 : ℝ) = Real.exp (κ * x₀) * Real.exp (-(κ * x₀)) := by
        rw [← Real.exp_add]; simp
    _ ≤ K * Real.exp (-(κ * x)) :=
        mul_le_mul hK (Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left hx hκ)))
          (Real.exp_nonneg _) hK0

/-- Polynomial factors are absorbed into stretched exponentials with half the rate. -/
theorem exists_pow_mul_exp_neg_rpow_le {c s : ℝ} (hc : 0 < c) (hs : 0 < s) (k : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 0 ≤ t →
      (t + 1) ^ k * Real.exp (-(c * t ^ s)) ≤ K * Real.exp (-(c / 2 * t ^ s)) := by
  obtain ⟨K, hK, hKb⟩ := exists_pow_mul_exp_neg_le hc (⌈s⁻¹⌉₊ * k)
  refine ⟨2 ^ k * K, by positivity, fun t ht => ?_⟩
  have hw0 : 0 ≤ t ^ s := Real.rpow_nonneg ht s
  have ht' : t ≤ (t ^ s + 1) ^ ⌈s⁻¹⌉₊ := by
    calc t = (t ^ s) ^ s⁻¹ := (Real.rpow_rpow_inv ht hs.ne').symm
      _ ≤ (t ^ s + 1) ^ s⁻¹ := Real.rpow_le_rpow hw0 (by linarith) (inv_nonneg.2 hs.le)
      _ ≤ (t ^ s + 1) ^ (⌈s⁻¹⌉₊ : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (Nat.le_ceil _)
      _ = (t ^ s + 1) ^ ⌈s⁻¹⌉₊ := Real.rpow_natCast _ _
  have h1 : t + 1 ≤ 2 * (t ^ s + 1) ^ ⌈s⁻¹⌉₊ := by
    have : 1 ≤ (t ^ s + 1) ^ ⌈s⁻¹⌉₊ := one_le_pow₀ (by linarith)
    linarith
  have h2 : (t + 1) ^ k ≤ 2 ^ k * (t ^ s + 1) ^ (⌈s⁻¹⌉₊ * k) := by
    rw [pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ (by linarith) h1 k
  calc (t + 1) ^ k * Real.exp (-(c * t ^ s))
      ≤ 2 ^ k * (t ^ s + 1) ^ (⌈s⁻¹⌉₊ * k) * Real.exp (-(c * t ^ s)) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_nonneg _)
    _ = 2 ^ k * ((t ^ s + 1) ^ (⌈s⁻¹⌉₊ * k) * Real.exp (-(c * t ^ s))) := by ring
    _ ≤ 2 ^ k * (K * Real.exp (-(c / 2 * t ^ s))) :=
        mul_le_mul_of_nonneg_left (hKb _ hw0) (by positivity)
    _ = _ := by ring

/-! ### Good subcubes -/

/-- In `z + Q_M` with `100 (4t)^d ≤ M`, a crossing component joining every open path that leaves
each `ℓ¹`-ball of radius `8t/10` makes the cube good and crossing. -/
theorem isGoodSubcube_of_hasCrossingComponent [NeZero d] {ω : Configuration d} {z : Vertex d}
    {M t : ℕ} (ht : 0 < t) (htM : 100 * (4 * t) ^ d ≤ M)
    (h : HasCrossingComponentConnectingPaths ω (cubeIC z M).vertices
      (fun a => ↑((cubeIC z M).lowerFace a)) (fun a => ↑((cubeIC z M).upperFace a))
      (fun n γ => ∀ y : Vertex d, ∃ a : Fin (n + 1),
        ((8 * t : ℕ) : ℤ) < 10 * ∑ k, |γ a k - y k|)) :
    IsGoodSubcube ω z M ∧ IsCrossingCube ω z M := by
  obtain ⟨root, hroot, hpaths⟩ :=
    HasCrossingComponentConnectingPaths.of_l1_radius_le t (8 * t) ht le_rfl h
  have hcast : (((2 * t : ℕ) : ℤ)) = 2 * (t : ℤ) := by push_cast; ring
  refine isGoodSubcube_of_root_coalesce (D := 2 * t) (by omega)
    (by rw [show 2 * (2 * t) = 4 * t by ring]; exact htM) hroot ?_
  rw [hcast]
  intro n γ hγ m η hη
  obtain ⟨y, -, hy₁, hy₂⟩ := hpaths n γ hγ.1 hγ.2.1 hγ.2.2
  obtain ⟨y', -, hy₁', hy₂'⟩ := hpaths m η hη.1 hη.2.1 hη.2.2
  exact hy₁.trans (hy₂.symm.trans (hy₂'.trans hy₁'.symm))

/-- **Good subcubes.** Above the critical point in dimension at least three, the cube `z + Q_M`
is good and crossing except with probability at most `K exp(-κ M^{1/d})`, uniformly in `z` and
`M`. -/
theorem exists_not_goodSubcube_le [NeZero d] (hd : 3 ≤ d) {p : unitInterval}
    (hp : criticalProbability d < (p : ℝ)) :
    ∃ K κ : ℝ, 0 < K ∧ 0 < κ ∧ ∀ (z : Vertex d) (M : ℕ),
      latticeBondLaw d p {ω | ¬ (IsGoodSubcube ω z M ∧ IsCrossingCube ω z M)} ≤
        ENNReal.ofReal (K * Real.exp (-(κ * (M : ℝ) ^ (d : ℝ)⁻¹))) := by
  have hd0 : 0 < d := by omega
  let j : Fin d := ⟨0, by omega⟩
  let i : Fin d := ⟨1, by omega⟩
  have hij : i ≠ j := by simp [i, j, Fin.ext_iff]
  have hp0 : 0 < (p : ℝ) := (criticalProbability_pos d).trans hp
  obtain ⟨width, ρ, c, hP⟩ :=
    (uniformCubeSlabConnectivity_of_criticalProbability_lt hd p hp).exists_slabParams j hp0
  have hw : 0 < width := hP.1
  have hc : 0 < c := hP.2.2.2.1
  set q : ℕ := 10 * d * width with hq
  have hq0 : 0 < q := Nat.mul_pos (Nat.mul_pos (by norm_num) hd0) hw
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq0
  set L : ℝ := 4 * (100 : ℝ) ^ (d : ℝ)⁻¹ with hL
  have hL0 : 0 < L := by rw [hL]; positivity
  set κ₁ : ℝ := 8 * c / (q * L) with hκ₁
  have hκ₁0 : 0 < κ₁ := div_pos (by linarith) (mul_pos hq' hL0)
  obtain ⟨K₁, hK₁, hK₁b⟩ := exists_pow_mul_exp_neg_le hκ₁0 (d * (2 * d + 1))
  set v₀ : ℝ := L * (q + 1) with hv₀
  set A : ℝ := ((d : ℝ) + 2) * 4 ^ (2 * d + 1) * Real.exp (c * (2 + 8 / q)) * K₁ with hA
  have hA0 : 0 < A := mul_pos (by positivity) hK₁
  refine ⟨A + Real.exp (κ₁ / 2 * v₀), κ₁ / 2, add_pos hA0 (Real.exp_pos _), half_pos hκ₁0,
    fun z M => ?_⟩
  set v : ℝ := (M : ℝ) ^ (d : ℝ)⁻¹ with hv
  have hv0 : 0 ≤ v := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hvM : v ^ d = M := Real.rpow_inv_natCast_pow (Nat.cast_nonneg M) (by omega)
  by_cases hsmall : v ≤ v₀
  · exact measure_le_ofReal_exp_of_le _ _ (half_pos hκ₁0).le
      (le_add_of_nonneg_left hA0.le) hsmall
  push Not at hsmall
  set t : ℕ := ⌊v / L⌋₊ with ht
  have htv : (t : ℝ) ≤ v / L := Nat.floor_le (div_nonneg hv0 hL0.le)
  have htv' : v / L - 1 < t := Nat.sub_one_lt_floor _
  have htq : q + 1 ≤ t := by
    apply Nat.le_floor
    rw [le_div_iff₀ hL0]
    calc ((q + 1 : ℕ) : ℝ) * L = v₀ := by rw [hv₀]; push_cast; ring
      _ ≤ v := hsmall.le
  have ht0 : 0 < t := by omega
  have h4t : ((4 * t : ℕ) : ℝ) ^ d * 100 ≤ M := by
    have h100 : (0 : ℝ) < (100 : ℝ) ^ (d : ℝ)⁻¹ := by positivity
    have h1 : ((4 * t : ℕ) : ℝ) ≤ v / (100 : ℝ) ^ (d : ℝ)⁻¹ := by
      push_cast
      calc 4 * (t : ℝ) ≤ 4 * (v / L) := by linarith
        _ = v / (100 : ℝ) ^ (d : ℝ)⁻¹ := by rw [hL]; field_simp
    have h2 := pow_le_pow_left₀ (by positivity) h1 d
    rw [div_pow, hvM, Real.rpow_inv_natCast_pow (by norm_num) (by omega)] at h2
    rwa [le_div_iff₀ (by norm_num)] at h2
  have htM : 100 * (4 * t) ^ d ≤ M := by
    have : ((100 * (4 * t) ^ d : ℕ) : ℝ) ≤ M := by
      push_cast at h4t ⊢; linarith
    exact_mod_cast this
  have h4tM : 4 * t ≤ M :=
    calc 4 * t ≤ (4 * t) ^ d := Nat.le_self_pow (by omega) _
      _ ≤ 100 * (4 * t) ^ d := Nat.le_mul_of_pos_left _ (by norm_num)
      _ ≤ M := htM
  have hradius : 10 * d * width ≤ 8 * t := by rw [← hq]; omega
  have hfit : 8 * t < 10 * d * (cubeIC z M).size := by
    have hsize : (cubeIC z M).size = 2 * M + 1 := rfl
    have hdM : 2 * M + 1 ≤ d * (2 * M + 1) := Nat.le_mul_of_pos_left _ hd0
    rw [hsize]
    calc 8 * t ≤ 2 * M := by omega
      _ < 10 * (d * (2 * M + 1)) := by omega
      _ = 10 * d * (2 * M + 1) := by ring
  refine (measure_mono ?_).trans ((crossing_fail_le hP hd0 j i hij (cubeIC z M) (8 * t)
    hradius hfit).trans (ENNReal.ofReal_le_ofReal ?_))
  · intro ω hbad hgood
    exact hbad (isGoodSubcube_of_hasCrossingComponent ht0 htM hgood)
  have hsize : ((cubeIC z M).size : ℝ) + 1 = 2 * (M + 1) := by
    show (((2 * M + 1 : ℕ) : ℝ)) + 1 = _
    push_cast; ring
  rw [hsize]
  have hMv : (M : ℝ) + 1 ≤ (v + 1) ^ d := by
    rw [← hvM]
    simpa using pow_add_pow_le (n := d) hv0 zero_le_one (by omega)
  have hpre : (2 * ((M : ℝ) + 1)) ^ (2 * d + 1) ≤
      4 ^ (2 * d + 1) * (v + 1) ^ (d * (2 * d + 1)) := by
    rw [pow_mul, ← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    have : 1 ≤ (v + 1) ^ d := one_le_pow₀ (by linarith)
    linarith
  have hexp : Real.exp (-(c * ((8 * t / q - 1 : ℕ) : ℝ))) ≤
      Real.exp (c * (2 + 8 / q)) * Real.exp (-(κ₁ * v)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have h1 := ratio_sub_one_ge (8 * t) q hq0
    have h2 : κ₁ * v - c * (8 / q) ≤ c * (((8 * t : ℕ) : ℝ) / q) := by
      have hκv : κ₁ * v = c * (8 * (v / L) / q) := by rw [hκ₁]; ring
      rw [hκv]
      have h3 : 8 * (v / L) / q - 8 / q ≤ ((8 * t : ℕ) : ℝ) / q := by
        rw [← sub_div]
        refine div_le_div_of_nonneg_right ?_ hq'.le
        push_cast
        linarith
      have h4 := mul_le_mul_of_nonneg_left h3 hc.le
      rw [mul_sub] at h4
      linarith
    have h5 := mul_le_mul_of_nonneg_left h1 hc.le
    rw [mul_sub] at h5
    have h6 : c * (2 + 8 / (q : ℝ)) = c * 2 + c * (8 / q) := by ring
    rw [h6]
    linarith
  have hKv := hK₁b v hv0
  calc ((d : ℝ) + 2) * (2 * ((M : ℝ) + 1)) ^ (2 * d + 1) *
        Real.exp (-(c * ((8 * t / q - 1 : ℕ) : ℝ)))
      ≤ ((d : ℝ) + 2) * (4 ^ (2 * d + 1) * (v + 1) ^ (d * (2 * d + 1))) *
          (Real.exp (c * (2 + 8 / q)) * Real.exp (-(κ₁ * v))) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hpre (by positivity)) hexp (Real.exp_nonneg _)
          (by positivity)
    _ = ((d : ℝ) + 2) * 4 ^ (2 * d + 1) * Real.exp (c * (2 + 8 / q)) *
          ((v + 1) ^ (d * (2 * d + 1)) * Real.exp (-(κ₁ * v))) := by ring
    _ ≤ ((d : ℝ) + 2) * 4 ^ (2 * d + 1) * Real.exp (c * (2 + 8 / q)) *
          (K₁ * Real.exp (-(κ₁ / 2 * v))) := mul_le_mul_of_nonneg_left hKv (by positivity)
    _ = A * Real.exp (-(κ₁ / 2 * v)) := by rw [hA]; ring
    _ ≤ (A + Real.exp (κ₁ / 2 * v₀)) * Real.exp (-(κ₁ / 2 * v)) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (Real.exp_nonneg _))
          (Real.exp_nonneg _)

/-! ### Well-connected cubes -/

/-- For `N ≥ 10⁴` and `a ≤ 1/2`, `N^a ≤ N / 100`. -/
theorem rpow_le_div_hundred {a : ℝ} (ha' : a ≤ 1 / 2) {N : ℕ} (hN : 10000 ≤ N) :
    (N : ℝ) ^ a ≤ N / 100 := by
  have hN' : (10000 : ℝ) ≤ N := by exact_mod_cast hN
  have h1 : (1 : ℝ) ≤ N := by linarith
  have hsqrt : (100 : ℝ) ≤ Real.sqrt N := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]
    linarith
  calc (N : ℝ) ^ a ≤ (N : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 ha'
    _ = Real.sqrt N := (Real.sqrt_eq_rpow _).symm
    _ ≤ N / 100 := by
        rw [le_div_iff₀ (by norm_num)]
        calc Real.sqrt N * 100 ≤ Real.sqrt N * Real.sqrt N :=
              mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg _)
          _ = N := Real.mul_self_sqrt (by linarith)

/-- **Well-connected cubes in dimension at least three** (Proposition 2.3 of the paper,
`Rigidity.External.WellConnectedInput`, for `d ≥ 3`). Above the critical point there are
`c, C > 0` and `s > 0` such that every cube `x + Q_N` is well-connected outside an event of
probability at most `C exp(-c N^s)`; here `s = 1/(100 d³)`. -/
theorem wellConnected_of_three_le [NeZero d] (hd : 3 ≤ d) (p : unitInterval)
    (hp : criticalProbability d < (p : ℝ)) :
    ∃ c C s : ℝ, 0 < c ∧ 0 < C ∧ 0 < s ∧ ∀ (x : Vertex d) (N : ℕ),
      latticeBondLaw d p {ω | ¬ IsWellConnected ω x N} ≤
        ENNReal.ofReal (C * Real.exp (-(c * (N : ℝ) ^ s))) := by
  obtain ⟨K, κ, hK, hκ, hgood⟩ := exists_not_goodSubcube_le hd hp
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  set a : ℝ := 1 / (10 * (d : ℝ)) ^ 2 with ha
  have ha1 : a ≤ 1 / 2 := by
    rw [ha]
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith
  have hdinv : (0 : ℝ) < (d : ℝ)⁻¹ := by positivity
  set s : ℝ := a * (d : ℝ)⁻¹ with hs
  have hs0 : 0 < s := mul_pos (by rw [ha]; positivity) hdinv
  have hsd : s ≤ (d : ℝ)⁻¹ :=
    (mul_le_mul_of_nonneg_right (by linarith : a ≤ 1) hdinv.le).trans_eq (one_mul _)
  obtain ⟨K₂, hK₂, hK₂b⟩ := exists_pow_mul_exp_neg_rpow_le (half_pos hκ) hs0 (d + 1)
  set C₀ : ℝ := 2 * 4 ^ d * K * K₂ with hC₀
  have hC₀0 : 0 < C₀ := mul_pos (mul_pos (by positivity) hK) hK₂
  refine ⟨κ / 2 / 2, C₀ + Real.exp (κ / 2 / 2 * (10000 : ℝ) ^ s), s, half_pos (half_pos hκ),
    add_pos hC₀0 (Real.exp_pos _), hs0, fun x N => ?_⟩
  by_cases hN : N < 10000
  · refine measure_le_ofReal_exp_of_le _ _ (half_pos (half_pos hκ)).le
      (le_add_of_nonneg_left hC₀0.le) ?_
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hN.le) hs0.le
  push Not at hN
  have hN1 : (1 : ℝ) ≤ N := by
    have : (10000 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hNa : (N : ℝ) ^ a ≤ N / 100 := rpow_le_div_hundred ha1 hN
  set B : Vertex d → ℕ → Set (Configuration d) :=
    fun z M => {ω | ¬ (IsGoodSubcube ω z M ∧ IsCrossingCube ω z M)} with hB
  set S : Finset (Vertex d × ℕ) := cubeFinset x (2 * N) ×ˢ Finset.range (N + 1) with hS
  set E : Vertex d × ℕ → Set (Configuration d) :=
    fun zM => {ω | (N : ℝ) ^ a / 2 ≤ zM.2 ∧ ω ∈ B zM.1 zM.2} with hE
  have hsub : {ω | ¬ IsWellConnected ω x N} ⊆ B x N ∪ ⋃ zM ∈ S, E zM := by
    intro ω hω
    by_contra hcon
    rw [Set.mem_union, not_or, Set.mem_iUnion₂] at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hgx : IsGoodSubcube ω x N ∧ IsCrossingCube ω x N := by
      by_contra h
      exact h1 h
    refine hω ⟨hNa, hgx.2, fun z M hM1 hM2 hne => ?_⟩
    have hMN : M ≤ N := by
      have : (M : ℝ) ≤ N := hM2.trans (by linarith)
      exact_mod_cast this
    have hmem : (z, M) ∈ S := by
      refine Finset.mem_product.2 ⟨mem_cubeFinset.2 (mem_cubeAt.2 fun k => ?_),
        Finset.mem_range.2 (by omega)⟩
      obtain ⟨y, hyz, hyx⟩ := hne
      obtain ⟨h1a, h1b⟩ := abs_le.1 (mem_cubeAt.1 hyz k)
      obtain ⟨h2a, h2b⟩ := abs_le.1 (mem_cubeAt.1 hyx k)
      rw [abs_le]
      push_cast
      constructor <;> omega
    by_contra hbad
    exact h2 ⟨(z, M), hmem, hM1, fun hg => hbad hg.1⟩
  set b : ℝ := K * Real.exp (-(κ / 2 * (N : ℝ) ^ s)) with hb
  have hb0 : 0 ≤ b := mul_nonneg hK.le (Real.exp_nonneg _)
  have hNs0 : 0 ≤ (N : ℝ) ^ s := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hbig : latticeBondLaw d p (B x N) ≤ ENNReal.ofReal b := by
    refine (hgood x N).trans (ENNReal.ofReal_le_ofReal ?_)
    have hkey : κ / 2 * (N : ℝ) ^ s ≤ κ * (N : ℝ) ^ (d : ℝ)⁻¹ :=
      calc κ / 2 * (N : ℝ) ^ s ≤ κ * (N : ℝ) ^ s := by nlinarith
        _ ≤ κ * (N : ℝ) ^ (d : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN1 hsd) hκ.le
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (neg_le_neg hkey)) hK.le
  have hterm : ∀ zM ∈ S, latticeBondLaw d p (E zM) ≤ ENNReal.ofReal b := by
    rintro ⟨z, M⟩ -
    by_cases hM : (N : ℝ) ^ a / 2 ≤ M
    · refine (measure_mono fun ω (hω : (N : ℝ) ^ a / 2 ≤ M ∧ ω ∈ B z M) => hω.2).trans
        ((hgood z M).trans (ENNReal.ofReal_le_ofReal ?_))
      have hNa0 : 0 ≤ (N : ℝ) ^ a / 2 := by positivity
      have h1 : ((N : ℝ) ^ a / 2) ^ (d : ℝ)⁻¹ ≤ (M : ℝ) ^ (d : ℝ)⁻¹ :=
        Real.rpow_le_rpow hNa0 hM hdinv.le
      have h2 : ((N : ℝ) ^ a / 2) ^ (d : ℝ)⁻¹ = (N : ℝ) ^ s / (2 : ℝ) ^ (d : ℝ)⁻¹ := by
        rw [Real.div_rpow (by positivity) (by norm_num), hs, Real.rpow_mul (Nat.cast_nonneg _)]
      have h3 : (2 : ℝ) ^ (d : ℝ)⁻¹ ≤ 2 := by
        calc (2 : ℝ) ^ (d : ℝ)⁻¹ ≤ (2 : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num)
                (inv_le_one_of_one_le₀ (by linarith))
          _ = 2 := Real.rpow_one 2
      have h4 : (N : ℝ) ^ s / 2 ≤ (N : ℝ) ^ s / (2 : ℝ) ^ (d : ℝ)⁻¹ :=
        div_le_div_of_nonneg_left hNs0 (by positivity) h3
      rw [← h2] at h4
      have hkey : κ / 2 * (N : ℝ) ^ s ≤ κ * (M : ℝ) ^ (d : ℝ)⁻¹ :=
        calc κ / 2 * (N : ℝ) ^ s = κ * ((N : ℝ) ^ s / 2) := by ring
          _ ≤ κ * (M : ℝ) ^ (d : ℝ)⁻¹ := mul_le_mul_of_nonneg_left (h4.trans h1) hκ.le
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (neg_le_neg hkey)) hK.le
    · have hempty : E (z, M) = ∅ := Set.eq_empty_of_forall_notMem
        fun ω (hω : (N : ℝ) ^ a / 2 ≤ M ∧ ω ∈ B z M) => hM hω.1
      rw [hempty, measure_empty]
      exact zero_le
  have hcard : (S.card : ℝ) ≤ 4 ^ d * ((N : ℝ) + 1) ^ (d + 1) := by
    rw [hS, Finset.card_product, card_cubeFinset, Finset.card_range]
    push_cast
    have h1 : (2 * (2 * (N : ℝ)) + 1) ^ d ≤ (4 * ((N : ℝ) + 1)) ^ d :=
      pow_le_pow_left₀ (by positivity) (by linarith) d
    calc (2 * (2 * (N : ℝ)) + 1) ^ d * ((N : ℝ) + 1)
        ≤ (4 * ((N : ℝ) + 1)) ^ d * ((N : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = 4 ^ d * ((N : ℝ) + 1) ^ (d + 1) := by rw [mul_pow, pow_succ]; ring
  have hpoly : 1 + (S.card : ℝ) ≤ 2 * 4 ^ d * ((N : ℝ) + 1) ^ (d + 1) := by
    have : (1 : ℝ) ≤ 4 ^ d * ((N : ℝ) + 1) ^ (d + 1) :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by linarith))
    linarith
  have hK2 := hK₂b N (Nat.cast_nonneg _)
  calc latticeBondLaw d p {ω | ¬ IsWellConnected ω x N}
      ≤ latticeBondLaw d p (B x N ∪ ⋃ zM ∈ S, E zM) := measure_mono hsub
    _ ≤ latticeBondLaw d p (B x N) + latticeBondLaw d p (⋃ zM ∈ S, E zM) :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal b + ∑ zM ∈ S, latticeBondLaw d p (E zM) :=
        add_le_add hbig (measure_biUnion_finset_le _ _)
    _ ≤ ENNReal.ofReal b + S.card • ENNReal.ofReal b :=
        add_le_add le_rfl (Finset.sum_le_card_nsmul _ _ _ hterm)
    _ = ENNReal.ofReal ((1 + S.card) * b) := by
        rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ← ENNReal.ofReal_add hb0 (mul_nonneg (Nat.cast_nonneg _) hb0)]
        congr 1
        ring
    _ ≤ ENNReal.ofReal ((C₀ + Real.exp (κ / 2 / 2 * (10000 : ℝ) ^ s)) *
          Real.exp (-(κ / 2 / 2 * (N : ℝ) ^ s))) := by
        apply ENNReal.ofReal_le_ofReal
        calc (1 + (S.card : ℝ)) * b
            ≤ (2 * 4 ^ d * ((N : ℝ) + 1) ^ (d + 1)) * b := mul_le_mul_of_nonneg_right hpoly hb0
          _ = 2 * 4 ^ d * K *
                (((N : ℝ) + 1) ^ (d + 1) * Real.exp (-(κ / 2 * (N : ℝ) ^ s))) := by
              rw [hb]; ring
          _ ≤ 2 * 4 ^ d * K * (K₂ * Real.exp (-(κ / 2 / 2 * (N : ℝ) ^ s))) :=
              mul_le_mul_of_nonneg_left hK2 (by positivity)
          _ = C₀ * Real.exp (-(κ / 2 / 2 * (N : ℝ) ^ s)) := by rw [hC₀]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (Real.exp_nonneg _))
              (Real.exp_nonneg _)

/-- **Proposition 2.3** (`Rigidity.External.WellConnectedInput`) follows from its planar case:
the dimensions `d ≥ 3` are `wellConnected_of_three_le`. -/
theorem wellConnectedInput_of_planar
    (h2 : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      ∃ c C s : ℝ, 0 < c ∧ 0 < C ∧ 0 < s ∧ ∀ (x : Vertex 2) (N : ℕ),
        latticeBondLaw 2 p {ω | ¬ IsWellConnected ω x N} ≤
          ENNReal.ofReal (C * Real.exp (-(c * (N : ℝ) ^ s)))) :
    WellConnectedInput := by
  intro d _ hd p hp hp1
  rcases Nat.lt_or_ge d 3 with h | h
  · obtain rfl : d = 2 := by omega
    exact h2 p hp hp1
  · exact wellConnected_of_three_le h p hp

end Rigidity.Percolation
