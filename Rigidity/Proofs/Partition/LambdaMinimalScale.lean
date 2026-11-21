import Rigidity.Proofs.Partition.LambdaScale
import Rigidity.Proofs.Partition.MinimalScale

/-!
# Probability of many bad cubes near a triadic cube

The two failure events of `sum_pow_scale_le_of_counts` are rare. A bad cube of scale at least `J`
near the cube of scale `m` centred at the origin occurs with probability at most
`C 3^{d m} exp(-c 3^J)`, by a union bound over the at most `25ᵈ 3^{d m}` nearby cubes of each
scale. Once `j` is so large that `e · 25ᵈ · 3^{(τ + 1)(j + 1)} · C exp(-c 3^j) ≤ e⁻¹`, at least
`3^{e_j}` bad cubes of scale `j` in a residue class occur with probability at most `exp(-3^{e_j})`.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-- The threshold scale beyond which the residue classes rarely contain many bad cubes. -/
theorem exists_large_scale_exp_le (A c : ℝ) (hA : 0 ≤ A) (hc : 0 < c) (k : ℕ) :
    ∃ j0 : ℕ, 3 ≤ j0 ∧ ∀ j, j0 ≤ j →
      A * (3 : ℝ) ^ (k * (j + 1)) * Real.exp (-c * (3 : ℝ) ^ j) ≤ Real.exp (-1) := by
  set B : ℝ := A * 3 ^ k * ((k.factorial : ℝ) / (c / 2) ^ k) with hBdef
  have hB : 0 ≤ B := by positivity
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((2 / c) * (1 + B)) (by norm_num : (1 : ℝ) < 3)
  refine ⟨max n 3, le_max_right _ _, fun j hj => ?_⟩
  set y : ℝ := (3 : ℝ) ^ j with hydef
  have hy0 : 0 ≤ y := by positivity
  have hyn : (2 / c) * (1 + B) < y :=
    hn.trans_le (pow_le_pow_right₀ (by norm_num) ((le_max_left _ _).trans hj))
  have h1 : (3 : ℝ) ^ (k * (j + 1)) = 3 ^ k * y ^ k := by
    rw [hydef, ← pow_mul, ← pow_add]
    congr 1
    ring
  have h2 := pow_mul_exp_neg_le k hc hy0
  have h3 : A * (3 : ℝ) ^ (k * (j + 1)) * Real.exp (-c * y) ≤ B * Real.exp (-(c / 2) * y) := by
    rw [h1, hBdef]
    have hA3 : 0 ≤ A * 3 ^ k := by positivity
    calc A * (3 ^ k * y ^ k) * Real.exp (-c * y) = A * 3 ^ k * (y ^ k * Real.exp (-c * y)) := by
          ring
      _ ≤ A * 3 ^ k * ((k.factorial : ℝ) / (c / 2) ^ k * Real.exp (-(c / 2) * y)) :=
          mul_le_mul_of_nonneg_left h2 hA3
      _ = _ := by ring
  have h4 : -(c / 2) * y ≤ -(1 + B) := by
    have : (c / 2) * ((2 / c) * (1 + B)) = 1 + B := by field_simp
    nlinarith
  have h5 : B * Real.exp (-(c / 2) * y) ≤ B * Real.exp (-(1 + B)) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h4) hB
  have h6 : B * Real.exp (-(1 + B)) ≤ Real.exp (-1) := by
    have hexp : Real.exp (-(1 + B)) = Real.exp (-1) * Real.exp (-B) := by
      rw [← Real.exp_add]; ring_nf
    rw [hexp]
    have hBe : B ≤ Real.exp B := by linarith [Real.add_one_le_exp B]
    have hBe' : B * Real.exp (-B) ≤ 1 := by
      rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos B)]
      exact hBe
    have he : 0 < Real.exp (-1) := Real.exp_pos _
    nlinarith
  exact h3.trans (h5.trans h6)

/-- **A large bad cube near the cube of scale `m`** occurs with probability at most
`25ᵈ 3^{d m} C exp(-c 3^J) ∑_k exp(-2c)^k`. -/
theorem measure_exists_bad_near_le (p : unitInterval) {C1 c : ℝ} (hC1 : 0 ≤ C1) (hc : 0 < c)
    (hq : ∀ T : TriadicCube d, latticeBondLaw d p {ω | T ∉ TriadicCube.goodCubes ω} ≤
      ENNReal.ofReal (C1 * Real.exp (-c * (3 : ℝ) ^ T.scale))) (m J : ℕ) :
    latticeBondLaw d p {ω | ∃ T : TriadicCube d, J ≤ T.scale ∧ T ∉ TriadicCube.goodCubes ω ∧
        ∃ x ∈ (originCube d m).vertices, ∀ i, |x i - T.center i| ≤ 11 * T.side} ≤
      ENNReal.ofReal (25 ^ d * 3 ^ (d * m) * C1) * ENNReal.ofReal (Real.exp (-c * 3 ^ J)) *
        ∑' k : ℕ, ENNReal.ofReal (Real.exp (-c * (3 - 1))) ^ k := by
  classical
  let B : ℕ → Set (Configuration d) := fun n =>
    ⋃ ι ∈ nearIndices d m n, {ω | (⟨n, ι⟩ : TriadicCube d) ∉ TriadicCube.goodCubes ω}
  have hsub : {ω | ∃ T : TriadicCube d, J ≤ T.scale ∧ T ∉ TriadicCube.goodCubes ω ∧
      ∃ x ∈ (originCube d m).vertices, ∀ i, |x i - T.center i| ≤ 11 * T.side} ⊆
      {ω | ∃ n : ℕ, J ≤ n ∧ ω ∈ B n} := by
    rintro ω ⟨T, hJ, hbad, x, hx, hnear⟩
    refine ⟨T.scale, hJ, ?_⟩
    simp only [B, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
    exact ⟨T.index, index_mem_nearIndices hx hnear, hbad⟩
  have hB : ∀ n : ℕ, latticeBondLaw d p (B n) ≤
      ENNReal.ofReal (25 ^ d * 3 ^ (d * m) * C1) *
        ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ n)) := by
    intro n
    have hcard : ((nearIndices d m n).card : ℝ) ≤ 25 ^ d * 3 ^ (d * m) := by
      rw [card_nearIndices]
      have h1 : (1 : ℝ) ≤ 3 ^ (m - n) := one_le_pow₀ (by norm_num)
      have h2 : (3 : ℝ) ^ (m - n) ≤ 3 ^ m := pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
      calc (2 * (3 : ℝ) ^ (m - n) + 23) ^ d ≤ (25 * 3 ^ m) ^ d := by gcongr; linarith
        _ = 25 ^ d * 3 ^ (d * m) := by rw [mul_pow, ← pow_mul, mul_comm m d]
    calc latticeBondLaw d p (B n)
        ≤ ∑ ι ∈ nearIndices d m n,
            latticeBondLaw d p {ω | (⟨n, ι⟩ : TriadicCube d) ∉ TriadicCube.goodCubes ω} :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ _ι ∈ nearIndices d m n, ENNReal.ofReal (C1 * Real.exp (-c * (3 : ℝ) ^ n)) :=
          Finset.sum_le_sum fun ι _ => hq _
      _ = ENNReal.ofReal ((nearIndices d m n).card * (C1 * Real.exp (-c * (3 : ℝ) ^ n))) := by
          rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      _ ≤ ENNReal.ofReal (25 ^ d * 3 ^ (d * m) * C1 * Real.exp (-c * (3 : ℝ) ^ n)) := by
          apply ENNReal.ofReal_le_ofReal
          have he : 0 ≤ C1 * Real.exp (-c * (3 : ℝ) ^ n) := by positivity
          calc ((nearIndices d m n).card : ℝ) * (C1 * Real.exp (-c * (3 : ℝ) ^ n))
              ≤ 25 ^ d * 3 ^ (d * m) * (C1 * Real.exp (-c * (3 : ℝ) ^ n)) :=
                mul_le_mul_of_nonneg_right hcard he
            _ = _ := by ring
      _ = _ := by rw [ENNReal.ofReal_mul (by positivity)]
  exact (measure_mono hsub).trans
    (measure_exists_large_index_le_stretched _ B _ 3 c (by norm_num) hc hB J)

/-- **Many bad cubes in a residue class at a large scale** occur with probability at most
`exp(-3^{e})`, `e = d (m - j) - (τ + 1)(j + 1)`. -/
theorem measure_classBadCount_ge_le (p : unitInterval) {C1 c : ℝ} (hC1 : 0 ≤ C1)
    (hq : ∀ T : TriadicCube d, latticeBondLaw d p {ω | T ∉ TriadicCube.goodCubes ω} ≤
      ENNReal.ofReal (C1 * Real.exp (-c * (3 : ℝ) ^ T.scale))) {m j τ : ℕ} (hj3 : 3 ≤ j)
    (hj : Real.exp 1 * 25 ^ d * C1 * (3 : ℝ) ^ ((τ + 1) * (j + 1)) *
      Real.exp (-c * (3 : ℝ) ^ j) ≤ Real.exp (-1))
    (hexp : (τ + 1) * (j + 1) ≤ d * (m - j)) (r : Fin d → Fin 3) :
    latticeBondLaw d p {ω | 3 ^ (d * (m - j) - (τ + 1) * (j + 1)) ≤ classBadCount ω m j r} ≤
      ENNReal.ofReal (Real.exp (-(3 : ℝ) ^ (d * (m - j) - (τ + 1) * (j + 1)))) := by
  set e := d * (m - j) - (τ + 1) * (j + 1) with hedef
  set a : ℝ := C1 * Real.exp (-c * (3 : ℝ) ^ j) with hadef
  have ha : 0 ≤ a := by positivity
  have hk : 0 < 3 ^ e := by positivity
  have h := measure_le_classBadCount_le p ha (m := m) hj3 (fun ι => hq _) r hk
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  have hde : d * (m - j) = e + (τ + 1) * (j + 1) := by omega
  have hN : (2 * (3 : ℝ) ^ (m - j) + 23) ^ d ≤ 25 ^ d * (3 ^ e * 3 ^ ((τ + 1) * (j + 1))) := by
    have h1 : (1 : ℝ) ≤ 3 ^ (m - j) := one_le_pow₀ (by norm_num)
    calc (2 * (3 : ℝ) ^ (m - j) + 23) ^ d ≤ (25 * 3 ^ (m - j)) ^ d := by gcongr; linarith
      _ = 25 ^ d * 3 ^ (d * (m - j)) := by rw [mul_pow, ← pow_mul, mul_comm (m - j) d]
      _ = _ := by rw [hde, pow_add]
  have hbase : Real.exp 1 * (2 * (3 : ℝ) ^ (m - j) + 23) ^ d * a / ((3 ^ e : ℕ) : ℝ) ≤
      Real.exp (-1) := by
    have hpos : (0 : ℝ) < ((3 ^ e : ℕ) : ℝ) := by exact_mod_cast hk
    rw [div_le_iff₀ hpos]
    have hcast : ((3 ^ e : ℕ) : ℝ) = 3 ^ e := by push_cast; ring
    rw [hcast]
    have hea : 0 ≤ Real.exp 1 * a := by positivity
    calc Real.exp 1 * (2 * (3 : ℝ) ^ (m - j) + 23) ^ d * a
        ≤ Real.exp 1 * (25 ^ d * (3 ^ e * 3 ^ ((τ + 1) * (j + 1)))) * a := by gcongr
      _ = (Real.exp 1 * 25 ^ d * C1 * (3 : ℝ) ^ ((τ + 1) * (j + 1)) *
            Real.exp (-c * (3 : ℝ) ^ j)) * 3 ^ e := by rw [hadef]; ring
      _ ≤ Real.exp (-1) * 3 ^ e := mul_le_mul_of_nonneg_right hj (by positivity)
  have hb0 : 0 ≤ Real.exp 1 * (2 * (3 : ℝ) ^ (m - j) + 23) ^ d * a / ((3 ^ e : ℕ) : ℝ) := by
    positivity
  calc (Real.exp 1 * (2 * (3 : ℝ) ^ (m - j) + 23) ^ d * a / ((3 ^ e : ℕ) : ℝ)) ^ (3 ^ e)
      ≤ Real.exp (-1) ^ (3 ^ e) := pow_le_pow_left₀ hb0 hbase _
    _ = Real.exp (-(3 : ℝ) ^ e) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring

/-- A polynomial factor in `3ᵐ` against `exp(-c 3^{⌊m / K⌋})` is at most a constant times
`exp(-c' 3^{m / K})`. -/
theorem mul_exp_neg_three_pow_div_le {K : ℕ} (hK : 0 < K) (k : ℕ) {c : ℝ} (hc : 0 < c) (m : ℕ)
    {P : ℝ} (hP : P ≤ ((3 : ℝ) ^ m) ^ k) :
    P * Real.exp (-c * 3 ^ (m / K)) ≤
      (((K * k).factorial : ℝ) / (c / 3 / 2) ^ (K * k)) *
        Real.exp (-(c / 3 / 2) * ((3 : ℝ) ^ m) ^ ((1 : ℝ) / K)) := by
  set x : ℝ := ((3 : ℝ) ^ m) ^ ((1 : ℝ) / K) with hxdef
  have hx0 : 0 ≤ x := by positivity
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hxK : x ^ K = (3 : ℝ) ^ m := by
    rw [hxdef, one_div]
    exact Real.rpow_inv_natCast_pow (by positivity) hK.ne'
  have hx : x = (3 : ℝ) ^ ((m : ℝ) / K) := by
    rw [hxdef, ← Real.rpow_natCast 3 m, ← Real.rpow_mul (by norm_num), mul_one_div]
  have hmK : (m : ℝ) / K ≤ ((m / K : ℕ) : ℝ) + 1 := by
    have h1 := Nat.div_add_mod m K
    have h2 := Nat.mod_lt m hK
    have h3 : (m : ℝ) ≤ K * (((m / K : ℕ) : ℝ) + 1) := by
      have : m ≤ K * (m / K + 1) := by
        rw [Nat.mul_add, mul_one]
        omega
      exact_mod_cast this
    rw [div_le_iff₀ hKr]
    linarith
  have hx3 : x ≤ 3 * 3 ^ (m / K) := by
    rw [hx]
    calc (3 : ℝ) ^ ((m : ℝ) / K) ≤ (3 : ℝ) ^ (((m / K : ℕ) : ℝ) + 1) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hmK
      _ = 3 * 3 ^ (m / K) := by
          rw [Real.rpow_add (by norm_num), Real.rpow_natCast, Real.rpow_one]
          ring
  have hP' : P ≤ x ^ (K * k) := by rw [pow_mul, hxK]; exact hP
  have hexp : Real.exp (-c * 3 ^ (m / K)) ≤ Real.exp (-(c / 3) * x) := by
    apply Real.exp_le_exp.2
    nlinarith
  have hpow := pow_mul_exp_neg_le (K * k) (show 0 < c / 3 by positivity) hx0
  calc P * Real.exp (-c * 3 ^ (m / K)) ≤ x ^ (K * k) * Real.exp (-(c / 3) * x) := by
        gcongr
    _ ≤ _ := hpow

/-- **Armstrong and Dario, Proposition 2.4, the first bound**, for supercritical bond percolation
on `ℤᵈ`, `d ≥ 2`, with `Λ` written through the sizes `3^{n(x)}` of the partition cubes: for every
`τ ∈ ℕ` there are `C`, `s > 0` and a measurable random scale `M` with a stretched-exponential
moment of order `s` such that, almost surely, whenever `M < 3ᵐ`,
`∑_{x ∈ Q_m} 3^{τ n(x)} ≤ C 3^{d m}`, where `Q_m` is the triadic cube of scale `m` centred at the
origin. -/
theorem exists_scale_sum_pow_partitionCube_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (τ : ℕ) :
    ∃ C s : ℝ, 0 < s ∧ ∃ M : Configuration d → ℝ≥0∞, Measurable M ∧
      (∃ θ : ℝ, 0 < θ ∧
        Integrable (fun ω => Real.exp (((M ω).toReal / θ) ^ s)) (latticeBondLaw d p) ∧
        (∫ ω, Real.exp (((M ω).toReal / θ) ^ s) ∂(latticeBondLaw d p)) ≤ 2) ∧
      ∀ᵐ ω ∂(latticeBondLaw d p), ∀ m : ℕ, M ω < 3 ^ m →
        ∑ x ∈ (originCube d m).toIntegerCube.vertices,
          (3 : ℝ) ^ (τ * (partitionCube ω x).scale) ≤ C * 3 ^ (d * m) := by
  classical
  obtain ⟨C1, c, hC1, hc, hq⟩ := exists_measure_not_mem_goodCubes_le hd hpc
  have hae := ae_partitionEvent hd hpc
  set μ := latticeBondLaw d p with hμdef
  have hd1 : 1 ≤ d := by omega
  set K : ℕ := 2 * (d + τ + 1) with hKdef
  have hK : 0 < K := by omega
  obtain ⟨j0, hj03, hj0⟩ :=
    exists_large_scale_exp_le (Real.exp 1 * 25 ^ d * C1) c (by positivity) hc (τ + 1)
  set Cfin : ℝ := (j0 : ℝ) * 575 ^ d * 3 ^ (τ * j0) + 69 ^ d with hCfin
  set f : Vertex d → Configuration d → ℝ :=
    fun x ω => TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x with hfdef
  have hfm : ∀ x, Measurable (f x) := fun x =>
    TriadicCube.measurable_stoppingSize _ TriadicCube.measurableSet_mem_goodCubes x
  set E : ℕ → Set (Configuration d) := fun m =>
    {ω | Cfin * 3 ^ (d * m) < ∑ x ∈ (originCube d m).toIntegerCube.vertices, f x ω ^ τ}
    with hEdef
  have hEm : ∀ m, MeasurableSet (E m) := fun m =>
    measurableSet_lt measurable_const (Finset.measurable_sum _ fun x _ => (hfm x).pow_const τ)
  -- on the partition event, the stopping sizes are the sides of the partition cubes
  have hsize : ∀ ω, PartitionEvent ω → ∀ m,
      ∑ x ∈ (originCube d m).toIntegerCube.vertices, f x ω ^ τ =
        ∑ x ∈ (originCube d m).toIntegerCube.vertices,
          (3 : ℝ) ^ (τ * (partitionCube ω x).scale) := by
    intro ω hP m
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hfdef]
    simp only
    rw [TriadicCube.stoppingSize_eq_of_mem (mem_partitionCube hP x) (partitionCube_spec hP x).2,
      ← pow_mul, mul_comm]
  -- the scale inequalities
  have hexpK : ∀ m j, j < m / K → (τ + 1) * (j + 1) + d * j + m / K ≤ d * m := by
    intro m j hj
    have h1 : (j + 1) * K ≤ m := (Nat.le_div_iff_mul_le hK).1 hj
    have h2 : m / K * K ≤ m := Nat.div_mul_le_self m K
    have h3 : m ≤ d * m := Nat.le_mul_of_pos_left m (by omega)
    have hKe : K = 2 * (d + τ + 1) := hKdef
    rw [hKe] at h1
    have h2' : m / K * (2 * (d + τ + 1)) ≤ m := by
      calc m / K * (2 * (d + τ + 1)) = m / K * K := by rw [← hKe]
        _ ≤ m := h2
    have ha : (τ + 1) * (j + 1) + d * j + d = (j + 1) * (d + τ + 1) := by ring
    have hb : m / K ≤ m / K * (d + τ + 1) := Nat.le_mul_of_pos_right _ (by omega)
    have hc1 : (j + 1) * (2 * (d + τ + 1)) = 2 * ((j + 1) * (d + τ + 1)) := by ring
    have hd1' : m / K * (2 * (d + τ + 1)) = 2 * (m / K * (d + τ + 1)) := by ring
    omega
  set Big : ℕ → Set (Configuration d) := fun m =>
    {ω | ∃ T : TriadicCube d, m / K ≤ T.scale ∧ T ∉ TriadicCube.goodCubes ω ∧
      ∃ x ∈ (originCube d m).vertices, ∀ i, |x i - T.center i| ≤ 11 * T.side} with hBigdef
  set Mid : ℕ → Set (Configuration d) := fun m =>
    ⋃ j ∈ Finset.Ico j0 (m / K), ⋃ r : Fin d → Fin 3,
      {ω | 3 ^ (d * (m - j) - (τ + 1) * (j + 1)) ≤ classBadCount ω m j r} with hMiddef
  have hsub : ∀ m, E m ⊆ {ω | ¬ PartitionEvent ω} ∪ (Big m ∪ Mid m) := by
    intro m ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hcon
    obtain ⟨hP, hBig, hMid⟩ := hcon
    have hfar : ∀ T : TriadicCube d, m / K ≤ T.scale → T ∉ TriadicCube.goodCubes ω →
        ∀ x ∈ (originCube d m).vertices, ¬ ∀ i, |x i - T.center i| ≤ 11 * T.side :=
      fun T hT hbad x hx hnear => hBig ⟨T, hT, hbad, x, hx, hnear⟩
    have hmid : ∀ j, j0 ≤ j → j < m / K → ∀ r,
        classBadCount ω m j r < 3 ^ (d * (m - j) - (τ + 1) * (j + 1)) := by
      intro j hj0' hjJ r
      by_contra hge
      apply hMid
      simp only [hMiddef, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop, Finset.mem_Ico]
      exact ⟨j, ⟨hj0', hjJ⟩, r, not_lt.1 hge⟩
    have hbound := sum_pow_scale_le_of_counts hP m (m / K) j0 τ (Nat.div_le_self m K)
      (fun j hj => le_trans (Nat.le_add_right _ _) (hexpK m j hj)) hfar hmid
    have hω' : Cfin * 3 ^ (d * m) <
        ∑ x ∈ (originCube d m).toIntegerCube.vertices, f x ω ^ τ := hω
    rw [hsize ω hP m] at hω'
    exact absurd hbound (not_le.2 hω')
  -- the probability of the failure events
  have hnull : μ {ω | ¬ PartitionEvent ω} = 0 := ae_iff.1 hae
  set G : ℝ≥0∞ := ∑' k : ℕ, ENNReal.ofReal (Real.exp (-c * (3 - 1))) ^ k with hGdef
  have hG : G ≠ ∞ := stretched_exp_geometric_sum_ne_top 3 c (by norm_num) hc
  set c' : ℝ := min (c / 3 / 2) (1 / 3 / 2) with hc'def
  have hc' : 0 < c' := lt_min (by positivity) (by norm_num)
  set D1 : ℝ := ((K * d).factorial : ℝ) / (c / 3 / 2) ^ (K * d) with hD1
  set D2 : ℝ := ((K * 1).factorial : ℝ) / (1 / 3 / 2) ^ (K * 1) with hD2
  set Ctot : ℝ≥0∞ := ENNReal.ofReal (25 ^ d * C1 * D1) * G + ENNReal.ofReal (3 ^ d * D2)
    with hCtot
  have hCtot_ne : Ctot ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hG, ENNReal.ofReal_ne_top⟩
  have hE : ∀ m, μ (E m) ≤
      Ctot * ENNReal.ofReal (Real.exp (-c' * ((3 : ℝ) ^ m) ^ ((1 : ℝ) / K))) := by
    intro m
    set x : ℝ := ((3 : ℝ) ^ m) ^ ((1 : ℝ) / K) with hxdef
    have hx0 : 0 ≤ x := by positivity
    have hexp1 : Real.exp (-(c / 3 / 2) * x) ≤ Real.exp (-c' * x) :=
      Real.exp_le_exp.2 (by nlinarith [min_le_left (c / 3 / 2) (1 / 3 / 2)])
    have hexp2 : Real.exp (-(1 / 3 / 2) * x) ≤ Real.exp (-c' * x) :=
      Real.exp_le_exp.2 (by nlinarith [min_le_right (c / 3 / 2) (1 / 3 / 2)])
    -- the large bad cube
    have hbig : μ (Big m) ≤ ENNReal.ofReal (25 ^ d * C1 * D1) * G *
        ENNReal.ofReal (Real.exp (-c' * x)) := by
      refine (measure_exists_bad_near_le p hC1 hc hq m (m / K)).trans ?_
      have hpoly := mul_exp_neg_three_pow_div_le hK d hc m (P := (3 : ℝ) ^ (d * m))
        (le_of_eq (by rw [← pow_mul, mul_comm d m]))
      rw [← hD1] at hpoly
      have hreal : 25 ^ d * 3 ^ (d * m) * C1 * Real.exp (-c * 3 ^ (m / K)) ≤
          25 ^ d * C1 * D1 * Real.exp (-c' * x) := by
        have h25 : (0 : ℝ) ≤ 25 ^ d * C1 := by positivity
        calc 25 ^ d * 3 ^ (d * m) * C1 * Real.exp (-c * 3 ^ (m / K))
            = 25 ^ d * C1 * ((3 : ℝ) ^ (d * m) * Real.exp (-c * 3 ^ (m / K))) := by ring
          _ ≤ 25 ^ d * C1 * (D1 * Real.exp (-(c / 3 / 2) * x)) :=
              mul_le_mul_of_nonneg_left hpoly h25
          _ ≤ 25 ^ d * C1 * (D1 * Real.exp (-c' * x)) := by
              gcongr
          _ = _ := by ring
      calc ENNReal.ofReal (25 ^ d * 3 ^ (d * m) * C1) *
            ENNReal.ofReal (Real.exp (-c * 3 ^ (m / K))) * G
          = ENNReal.ofReal (25 ^ d * 3 ^ (d * m) * C1 * Real.exp (-c * 3 ^ (m / K))) * G := by
            exact congrArg (· * G) (ENNReal.ofReal_mul (by positivity)).symm
        _ ≤ ENNReal.ofReal (25 ^ d * C1 * D1 * Real.exp (-c' * x)) * G := by
            gcongr
        _ = _ := by
            rw [ENNReal.ofReal_mul (p := 25 ^ d * C1 * D1) (by positivity)]
            ring
    -- many bad cubes in a residue class
    have hmid : μ (Mid m) ≤ ENNReal.ofReal (3 ^ d * D2) * ENNReal.ofReal (Real.exp (-c' * x)) := by
      have hterm : ∀ j ∈ Finset.Ico j0 (m / K), ∀ r : Fin d → Fin 3,
          μ {ω | 3 ^ (d * (m - j) - (τ + 1) * (j + 1)) ≤ classBadCount ω m j r} ≤
            ENNReal.ofReal (Real.exp (-(3 : ℝ) ^ (m / K))) := by
        intro j hj r
        rw [Finset.mem_Ico] at hj
        have hjm := hexpK m j hj.2
        have hjm0 : j ≤ m := le_trans hj.2.le (Nat.div_le_self m K)
        have hjm' : (τ + 1) * (j + 1) ≤ d * (m - j) := by
          have h1 : d * (m - j) + d * j = d * m := by
            rw [← Nat.mul_add, Nat.sub_add_cancel hjm0]
          linarith
        refine (measure_classBadCount_ge_le p hC1 hq (by omega) (hj0 j hj.1) hjm' r).trans ?_
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.2
        have h1 : d * (m - j) + d * j = d * m := by
          rw [← Nat.mul_add, Nat.sub_add_cancel hjm0]
        have hle : m / K ≤ d * (m - j) - (τ + 1) * (j + 1) :=
          Nat.le_sub_of_add_le (by linarith)
        have := pow_le_pow_right₀ (show (1 : ℝ) ≤ 3 by norm_num) hle
        linarith
      have hsumE : μ (Mid m) ≤ ENNReal.ofReal (((Finset.Ico j0 (m / K)).card : ℝ) * 3 ^ d *
          Real.exp (-(3 : ℝ) ^ (m / K))) := by
        calc μ (Mid m) ≤ ∑ j ∈ Finset.Ico j0 (m / K), ∑ r : Fin d → Fin 3,
              μ {ω | 3 ^ (d * (m - j) - (τ + 1) * (j + 1)) ≤ classBadCount ω m j r} :=
            (measure_biUnion_finset_le _ _).trans
              (Finset.sum_le_sum fun j _ => measure_iUnion_fintype_le _ _)
          _ ≤ ∑ j ∈ Finset.Ico j0 (m / K), ∑ _r : Fin d → Fin 3,
              ENNReal.ofReal (Real.exp (-(3 : ℝ) ^ (m / K))) :=
            Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun r _ => hterm j hj r
          _ = _ := by
            rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
              ENNReal.ofReal_natCast, ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
              nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
            ring
      have hcard : ((Finset.Ico j0 (m / K)).card : ℝ) ≤ m := by
        have h1 : (Finset.Ico j0 (m / K)).card ≤ m := by
          rw [Nat.card_Ico]
          have := Nat.div_le_self m K
          omega
        exact_mod_cast h1
      have hpoly := mul_exp_neg_three_pow_div_le hK 1 one_pos m (P := (m : ℝ)) (by
        rw [pow_one]
        exact_mod_cast (Nat.lt_pow_self (by norm_num : 1 < 3)).le)
      rw [← hD2] at hpoly
      have hreal : ((Finset.Ico j0 (m / K)).card : ℝ) * 3 ^ d * Real.exp (-(3 : ℝ) ^ (m / K)) ≤
          3 ^ d * D2 * Real.exp (-c' * x) := by
        have he : Real.exp (-(3 : ℝ) ^ (m / K)) = Real.exp (-1 * (3 : ℝ) ^ (m / K)) := by
          congr 1
          ring
        have h3d : (0 : ℝ) ≤ 3 ^ d := by positivity
        calc ((Finset.Ico j0 (m / K)).card : ℝ) * 3 ^ d * Real.exp (-(3 : ℝ) ^ (m / K))
            ≤ (m : ℝ) * 3 ^ d * Real.exp (-(3 : ℝ) ^ (m / K)) := by gcongr
          _ = 3 ^ d * ((m : ℝ) * Real.exp (-1 * (3 : ℝ) ^ (m / K))) := by rw [he]; ring
          _ ≤ 3 ^ d * (D2 * Real.exp (-(1 / 3 / 2) * x)) :=
              mul_le_mul_of_nonneg_left hpoly h3d
          _ ≤ 3 ^ d * (D2 * Real.exp (-c' * x)) := by gcongr
          _ = _ := by ring
      refine hsumE.trans ?_
      rw [← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal hreal
    calc μ (E m) ≤ μ ({ω | ¬ PartitionEvent ω} ∪ (Big m ∪ Mid m)) := measure_mono (hsub m)
      _ ≤ μ {ω | ¬ PartitionEvent ω} + (μ (Big m) + μ (Mid m)) :=
          (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
      _ ≤ 0 + (ENNReal.ofReal (25 ^ d * C1 * D1) * G * ENNReal.ofReal (Real.exp (-c' * x)) +
            ENNReal.ofReal (3 ^ d * D2) * ENNReal.ofReal (Real.exp (-c' * x))) := by
          rw [hnull]
          exact add_le_add le_rfl (add_le_add hbig hmid)
      _ = Ctot * ENNReal.ofReal (Real.exp (-c' * x)) := by
          rw [hCtot]
          ring
  obtain ⟨θ, hθ, hint, hle⟩ := exceptionalScale_exp_moment μ E hEm Ctot hCtot_ne ((1 : ℝ) / K)
    c' (by positivity) hc' hE
  refine ⟨Cfin, (1 : ℝ) / K, by positivity, exceptionalScale E, measurable_exceptionalScale E hEm,
    ⟨θ, hθ, hint, hle⟩, ?_⟩
  filter_upwards [hae] with ω hP m hm
  have hnot : ω ∉ E m := by
    intro hωE
    have h3 : (3 : ℝ≥0∞) ^ m ≤ exceptionalScale E ω := by
      unfold exceptionalScale
      exact le_iSup_of_le m (by rw [if_pos hωE])
    exact absurd hm (not_lt.2 h3)
  have h : ¬ (Cfin * 3 ^ (d * m) <
      ∑ x ∈ (originCube d m).toIntegerCube.vertices, f x ω ^ τ) := hnot
  rw [hsize ω hP m] at h
  exact not_lt.1 h

end Rigidity.Percolation
