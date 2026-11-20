import Rigidity.Proofs.Section5.CrossingFlow
import Rigidity.Proofs.Percolation.KestenCrossing
import Rigidity.Proofs.Percolation.PlanarWellConnected

/-!
# Crossing events at dyadic scales

`CrossingGood ω L w H N` collects the crossings and well-connected cubes which the flow
construction of `CrossingFlow.lean` uses inside `[-L, L]²`: open horizontal crossings of all the
rectangles `[-L, L] × [r, r + w]`, open vertical crossings of all the rectangles
`[c, c + w] × [-L, L]`, `-L ≤ r, c ≤ L`, and for every centre `z ∈ [-L, L]²` open crossings of the
rectangles `[z₀, z₀ + w] × [z₁, z₁ + H]` (vertically) and `[z₀, z₀ + H] × [z₁, z₁ + w]`
(horizontally) and well-connectedness of the cube `z + Q_N`.

Kesten's rectangle crossing estimate and planar well-connectedness bound the probability of the
complement by a union bound. With `L = 4^m`, `w = m²`, `H = 2^m (m² + 1)` and `N = m^q`, `q s ≥ 2`,
these bounds are summable in `m`, so the event holds for all large `m`, almost surely.
-/

open MeasureTheory Filter LatticeProb.Percolation Rigidity.External Rigidity.Proofs.S3
open scoped ENNReal

namespace Rigidity.Proofs.Section5

/-- A union over a finite index set of sets of measure at most `f` has measure at most `|S| f`. -/
theorem measure_biUnion_le_card_mul {α ι : Type*} [MeasurableSpace α] (μ : Measure α)
    (S : Finset ι) (A : ι → Set α) {f : ℝ} (h : ∀ i ∈ S, μ (A i) ≤ ENNReal.ofReal f) :
    μ (⋃ i ∈ S, A i) ≤ ENNReal.ofReal (S.card * f) := by
  calc μ (⋃ i ∈ S, A i) ≤ ∑ i ∈ S, μ (A i) := measure_biUnion_finset_le S A
    _ ≤ ∑ _i ∈ S, ENNReal.ofReal f := Finset.sum_le_sum h
    _ = ENNReal.ofReal (S.card * f) := by
      rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
        ENNReal.ofReal_natCast]

/-- The crossings and well-connected cubes used by the flow construction in `[-L, L]²`. -/
def CrossingGood (ω : Configuration 2) (L w H N : ℕ) : Prop :=
  (∀ r ∈ Finset.Icc (-(L : ℤ)) L, HasOpenCrossing ω ![-(L : ℤ), r] (2 * L) w 0) ∧
  (∀ c ∈ Finset.Icc (-(L : ℤ)) L, HasOpenCrossing ω ![c, -(L : ℤ)] (2 * L) w 1) ∧
  ∀ z ∈ cubeFinset (0 : Vertex 2) L, HasOpenCrossing ω ![z 0, z 1] H w 1 ∧
    HasOpenCrossing ω ![z 0, z 1] H w 0 ∧ IsWellConnected ω z N

/-- The union bound for the failure of `CrossingGood`, in terms of the constants of Kesten's
estimate and of the well-connectedness estimate. -/
noncomputable def crossingFailureBound (C c C' c' s : ℝ) (L w H N : ℕ) : ℝ :=
  2 * ((2 * L + 1) * (C * (2 * L + 1) * Real.exp (-(c * w)))) +
    (2 * L + 1) ^ 2 * (2 * (C * (H + 1) * Real.exp (-(c * w))) +
      C' * Real.exp (-(c' * (N : ℝ) ^ s)))

theorem card_Icc_neg (L : ℕ) : ((Finset.Icc (-(L : ℤ)) L).card : ℝ) = 2 * L + 1 := by
  rw [Int.card_Icc]
  have : ((L : ℤ) + 1 - -(L : ℤ)).toNat = 2 * L + 1 := by omega
  rw [this]
  push_cast
  ring

/-- **Failure probability of the crossing event.** -/
theorem measure_not_crossingGood_le {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) :
    ∃ C c C' c' s : ℝ, 0 < C ∧ 0 < c ∧ 0 < C' ∧ 0 < c' ∧ 0 < s ∧ ∀ L w H N : ℕ,
      latticeBondLaw 2 p {ω | ¬ CrossingGood ω L w H N} ≤
        ENNReal.ofReal (crossingFailureBound C c C' c' s L w H N) := by
  obtain ⟨C, c, hC, hc, hK⟩ := Rigidity.Percolation.kesten_rectangle_crossing p hpc
  obtain ⟨c', C', s, hc', hC', hs, hW⟩ := Rigidity.Percolation.wellConnected_input_two p hpc hp1
  refine ⟨C, c, C', c', s, hC, hc, hC', hc', hs, fun L w H N => ?_⟩
  set μ := latticeBondLaw 2 p
  have hsub : {ω | ¬ CrossingGood ω L w H N} ⊆
      (⋃ r ∈ Finset.Icc (-(L : ℤ)) L, {ω | ¬ HasOpenCrossing ω ![-(L : ℤ), r] (2 * L) w 0}) ∪
      (⋃ r ∈ Finset.Icc (-(L : ℤ)) L, {ω | ¬ HasOpenCrossing ω ![r, -(L : ℤ)] (2 * L) w 1}) ∪
      (⋃ z ∈ cubeFinset (0 : Vertex 2) L, ({ω | ¬ HasOpenCrossing ω ![z 0, z 1] H w 1} ∪
        {ω | ¬ HasOpenCrossing ω ![z 0, z 1] H w 0} ∪ {ω | ¬ IsWellConnected ω z N})) := by
    intro ω hω
    by_contra hcon
    apply hω
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq, not_or, not_exists,
      not_not] at hcon
    obtain ⟨⟨h1, h2⟩, h3⟩ := hcon
    exact ⟨fun r hr => h1 r hr, fun r hr => h2 r hr,
      fun z hz => ⟨(h3 z hz).1.1, (h3 z hz).1.2, (h3 z hz).2⟩⟩
  have hrow : μ (⋃ r ∈ Finset.Icc (-(L : ℤ)) L,
      {ω | ¬ HasOpenCrossing ω ![-(L : ℤ), r] (2 * L) w 0}) ≤
        ENNReal.ofReal ((2 * L + 1) * (C * (2 * L + 1) * Real.exp (-(c * w)))) := by
    have h := measure_biUnion_le_card_mul μ (Finset.Icc (-(L : ℤ)) L)
      (fun r => {ω | ¬ HasOpenCrossing ω ![-(L : ℤ), r] (2 * L) w 0})
      (f := C * (2 * L + 1) * Real.exp (-(c * w)))
      fun r _ => (hK _ _ _ _).trans (le_of_eq (by push_cast; ring_nf))
    rwa [card_Icc_neg] at h
  have hcol : μ (⋃ r ∈ Finset.Icc (-(L : ℤ)) L,
      {ω | ¬ HasOpenCrossing ω ![r, -(L : ℤ)] (2 * L) w 1}) ≤
        ENNReal.ofReal ((2 * L + 1) * (C * (2 * L + 1) * Real.exp (-(c * w)))) := by
    have h := measure_biUnion_le_card_mul μ (Finset.Icc (-(L : ℤ)) L)
      (fun r => {ω | ¬ HasOpenCrossing ω ![r, -(L : ℤ)] (2 * L) w 1})
      (f := C * (2 * L + 1) * Real.exp (-(c * w)))
      fun r _ => (hK _ _ _ _).trans (le_of_eq (by push_cast; ring_nf))
    rwa [card_Icc_neg] at h
  have hcube : μ (⋃ z ∈ cubeFinset (0 : Vertex 2) L,
      ({ω | ¬ HasOpenCrossing ω ![z 0, z 1] H w 1} ∪
        {ω | ¬ HasOpenCrossing ω ![z 0, z 1] H w 0} ∪ {ω | ¬ IsWellConnected ω z N})) ≤
        ENNReal.ofReal ((2 * L + 1) ^ 2 * (2 * (C * (H + 1) * Real.exp (-(c * w))) +
          C' * Real.exp (-(c' * (N : ℝ) ^ s)))) := by
    have hcard : ((cubeFinset (0 : Vertex 2) L).card : ℝ) = (2 * L + 1) ^ 2 := by
      rw [card_cubeFinset]
      push_cast
      ring
    rw [← hcard]
    refine measure_biUnion_le_card_mul μ _ _ fun z _ => ?_
    refine (measure_union_le _ _).trans ?_
    refine (add_le_add (measure_union_le _ _) (hW z N)).trans ?_
    refine (add_le_add (add_le_add (hK _ _ _ _) (hK _ _ _ _)) le_rfl).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  refine (measure_mono hsub).trans ?_
  refine (measure_union_le _ _).trans ?_
  refine (add_le_add (measure_union_le _ _) hcube).trans ?_
  refine (add_le_add (add_le_add hrow hcol) le_rfl).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  unfold crossingFailureBound
  congr 1
  ring

/-- Polynomially weighted geometric sequences with Gaussian decay are summable. -/
theorem summable_pow_mul_geom_mul_exp_neg_sq (k : ℕ) {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    Summable fun m : ℕ => (m : ℝ) ^ k * a ^ m * Real.exp (-(c * (m : ℝ) ^ 2)) := by
  refine Summable.of_norm_bounded_eventually_nat
    (Real.summable_pow_mul_exp_neg_nat_mul k one_pos) ?_
  obtain ⟨M, hM⟩ := exists_nat_ge ((Real.log a + 1) / c)
  filter_upwards [eventually_ge_atTop M] with m hm
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hmM : (Real.log a + 1) / c ≤ m := hM.trans (by exact_mod_cast hm)
  have hlin : Real.log a + 1 ≤ c * m := by rwa [div_le_iff₀ hc, mul_comm] at hmM
  have key : a ^ m * Real.exp (-(c * (m : ℝ) ^ 2)) ≤ Real.exp (-1 * m) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos ha, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith
  calc (m : ℝ) ^ k * a ^ m * Real.exp (-(c * (m : ℝ) ^ 2))
      = (m : ℝ) ^ k * (a ^ m * Real.exp (-(c * (m : ℝ) ^ 2))) := by ring
    _ ≤ (m : ℝ) ^ k * Real.exp (-1 * m) := mul_le_mul_of_nonneg_left key (by positivity)

/-- The exponent `q = ⌈2/s⌉ + 2` has `q s ≥ 2`. -/
theorem two_le_mul_crossExponent {s : ℝ} (hs : 0 < s) : 2 ≤ ((⌈2 / s⌉₊ + 2 : ℕ) : ℝ) * s := by
  have h := Nat.le_ceil (2 / s)
  have h2 : 2 / s * s = 2 := by field_simp
  push_cast
  nlinarith

/-- `(m^q)^s ≥ m²` when `q s ≥ 2`. -/
theorem sq_le_rpow_pow {s : ℝ} {q : ℕ} (hq : 2 ≤ (q : ℝ) * s) (m : ℕ) :
    (m : ℝ) ^ 2 ≤ ((m ^ q : ℕ) : ℝ) ^ s := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [CharP.cast_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    push_cast
    rw [← Real.rpow_natCast (m : ℝ) q, ← Real.rpow_mul (by positivity),
      ← Real.rpow_natCast (m : ℝ) 2]
    exact Real.rpow_le_rpow_of_exponent_le hm1 (by exact_mod_cast hq)

/-- **Crossing events hold at all large dyadic scales.** For `p_c(2) < p < 1` there is a
natural `q ≥ 2` such that, almost surely, `CrossingGood ω (4^m) (m²) (2^m (m² + 1)) (m^q)`
holds for all large `m`. -/
theorem ae_eventually_crossingGood {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) : ∃ q : ℕ, 2 ≤ q ∧ ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ᶠ m : ℕ in atTop,
      CrossingGood ω (4 ^ m) (m ^ 2) (2 ^ m * (m ^ 2 + 1)) (m ^ q) := by
  obtain ⟨C, c, C', c', s, hC, hc, hC', hc', hs, hbound⟩ := measure_not_crossingGood_le hpc hp1
  set q := ⌈2 / s⌉₊ + 2 with hqdef
  have hqs : 2 ≤ (q : ℝ) * s := two_le_mul_crossExponent hs
  refine ⟨q, by omega, ?_⟩
  let b : ℕ → ℝ := fun m =>
    crossingFailureBound C c C' c' s (4 ^ m) (m ^ 2) (2 ^ m * (m ^ 2 + 1)) (m ^ q)
  let g : ℕ → ℝ := fun m =>
    18 * C * ((m : ℝ) ^ 0 * 16 ^ m * Real.exp (-(c * (m : ℝ) ^ 2))) +
      18 * C * ((m : ℝ) ^ 2 * 32 ^ m * Real.exp (-(c * (m : ℝ) ^ 2))) +
      36 * C * ((m : ℝ) ^ 0 * 32 ^ m * Real.exp (-(c * (m : ℝ) ^ 2))) +
      9 * C' * ((m : ℝ) ^ 0 * 16 ^ m * Real.exp (-(c' * (m : ℝ) ^ 2)))
  have hg : Summable g := by
    refine (((((summable_pow_mul_geom_mul_exp_neg_sq 0 (by norm_num) hc).mul_left (18 * C)).add
      ((summable_pow_mul_geom_mul_exp_neg_sq 2 (by norm_num) hc).mul_left (18 * C))).add
      ((summable_pow_mul_geom_mul_exp_neg_sq 0 (by norm_num) hc).mul_left (36 * C))).add
      ((summable_pow_mul_geom_mul_exp_neg_sq 0 (by norm_num) hc').mul_left (9 * C')))
  have hb0 : ∀ m, 0 ≤ b m := fun m => by
    simp only [b, crossingFailureBound]
    positivity
  have hbg : ∀ m, b m ≤ g m := by
    intro m
    simp only [b, g, crossingFailureBound]
    have hL : (2 * ((4 ^ m : ℕ) : ℝ) + 1) ≤ 3 * 4 ^ m := by
      have : (1 : ℝ) ≤ 4 ^ m := one_le_pow₀ (by norm_num)
      push_cast
      linarith
    have hH : (((2 ^ m * (m ^ 2 + 1) : ℕ) : ℝ) + 1) ≤ 2 ^ m * ((m : ℝ) ^ 2 + 2) := by
      have : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
      push_cast
      nlinarith
    have hN : Real.exp (-(c' * (((m ^ q : ℕ) : ℝ)) ^ s)) ≤ Real.exp (-(c' * (m : ℝ) ^ 2)) := by
      apply Real.exp_le_exp.2
      have := sq_le_rpow_pow hqs m
      nlinarith
    have hw : ((m ^ 2 : ℕ) : ℝ) = (m : ℝ) ^ 2 := by push_cast; ring
    rw [hw]
    have e16 : (16 : ℝ) ^ m = 4 ^ m * 4 ^ m := by rw [← mul_pow]; norm_num
    have e32 : (32 : ℝ) ^ m = 4 ^ m * 4 ^ m * 2 ^ m := by rw [← mul_pow, ← mul_pow]; norm_num
    have hE : 0 ≤ Real.exp (-(c * (m : ℝ) ^ 2)) := (Real.exp_pos _).le
    have hE' : 0 ≤ Real.exp (-(c' * (m : ℝ) ^ 2)) := (Real.exp_pos _).le
    have h4 : (0 : ℝ) ≤ 4 ^ m := by positivity
    have h2 : (0 : ℝ) ≤ 2 ^ m := by positivity
    have hL0 : (0 : ℝ) ≤ 2 * ((4 ^ m : ℕ) : ℝ) + 1 := by positivity
    have hLsq : (2 * ((4 ^ m : ℕ) : ℝ) + 1) ^ 2 ≤ 9 * (4 ^ m * 4 ^ m) := by nlinarith
    rw [e16, e32]
    simp only [pow_zero, one_mul]
    have hT1 : 2 * ((2 * ((4 ^ m : ℕ) : ℝ) + 1) * (C * (2 * ((4 ^ m : ℕ) : ℝ) + 1) *
        Real.exp (-(c * (m : ℝ) ^ 2)))) ≤ 18 * C * (4 ^ m * 4 ^ m *
          Real.exp (-(c * (m : ℝ) ^ 2))) := by
      have : 2 * ((2 * ((4 ^ m : ℕ) : ℝ) + 1) * (C * (2 * ((4 ^ m : ℕ) : ℝ) + 1) *
          Real.exp (-(c * (m : ℝ) ^ 2)))) =
          2 * C * Real.exp (-(c * (m : ℝ) ^ 2)) * (2 * ((4 ^ m : ℕ) : ℝ) + 1) ^ 2 := by ring
      rw [this]
      have : 0 ≤ 2 * C * Real.exp (-(c * (m : ℝ) ^ 2)) := by positivity
      nlinarith
    have hT2 : (2 * ((4 ^ m : ℕ) : ℝ) + 1) ^ 2 * (2 * (C * (((2 ^ m * (m ^ 2 + 1) : ℕ) : ℝ) + 1) *
        Real.exp (-(c * (m : ℝ) ^ 2)))) ≤
        18 * C * ((m : ℝ) ^ 2 * (4 ^ m * 4 ^ m * 2 ^ m) * Real.exp (-(c * (m : ℝ) ^ 2))) +
        36 * C * (4 ^ m * 4 ^ m * 2 ^ m * Real.exp (-(c * (m : ℝ) ^ 2))) := by
      have hA : 0 ≤ 2 * C * Real.exp (-(c * (m : ℝ) ^ 2)) := by positivity
      have hHH : 0 ≤ ((2 ^ m * (m ^ 2 + 1) : ℕ) : ℝ) + 1 := by positivity
      calc (2 * ((4 ^ m : ℕ) : ℝ) + 1) ^ 2 * (2 * (C * (((2 ^ m * (m ^ 2 + 1) : ℕ) : ℝ) + 1) *
            Real.exp (-(c * (m : ℝ) ^ 2))))
          = (2 * ((4 ^ m : ℕ) : ℝ) + 1) ^ 2 * ((((2 ^ m * (m ^ 2 + 1) : ℕ) : ℝ) + 1) *
            (2 * C * Real.exp (-(c * (m : ℝ) ^ 2)))) := by ring
        _ ≤ (9 * (4 ^ m * 4 ^ m)) * ((2 ^ m * ((m : ℝ) ^ 2 + 2)) *
            (2 * C * Real.exp (-(c * (m : ℝ) ^ 2)))) := by
          apply mul_le_mul hLsq _ (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_right hH hA
        _ = _ := by ring
    have hT3 : (2 * ((4 ^ m : ℕ) : ℝ) + 1) ^ 2 * (C' * Real.exp (-(c' * (((m ^ q : ℕ) : ℝ)) ^ s)))
        ≤ 9 * C' * (4 ^ m * 4 ^ m * Real.exp (-(c' * (m : ℝ) ^ 2))) := by
      calc (2 * ((4 ^ m : ℕ) : ℝ) + 1) ^ 2 * (C' * Real.exp (-(c' * (((m ^ q : ℕ) : ℝ)) ^ s)))
          ≤ (9 * (4 ^ m * 4 ^ m)) * (C' * Real.exp (-(c' * (m : ℝ) ^ 2))) := by
            apply mul_le_mul hLsq _ (by positivity) (by positivity)
            exact mul_le_mul_of_nonneg_left hN hC'.le
        _ = _ := by ring
    calc _ = 2 * ((2 * ((4 ^ m : ℕ) : ℝ) + 1) * (C * (2 * ((4 ^ m : ℕ) : ℝ) + 1) *
            Real.exp (-(c * (m : ℝ) ^ 2)))) +
          ((2 * ((4 ^ m : ℕ) : ℝ) + 1) ^ 2 * (2 * (C * (((2 ^ m * (m ^ 2 + 1) : ℕ) : ℝ) + 1) *
            Real.exp (-(c * (m : ℝ) ^ 2)))) +
          (2 * ((4 ^ m : ℕ) : ℝ) + 1) ^ 2 *
            (C' * Real.exp (-(c' * (((m ^ q : ℕ) : ℝ)) ^ s)))) := by ring
      _ ≤ _ := by linarith
  have hsum : ∑' m, latticeBondLaw 2 p
      {ω | ¬ CrossingGood ω (4 ^ m) (m ^ 2) (2 ^ m * (m ^ 2 + 1)) (m ^ q)} ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum fun m => hbound _ _ _ _)
    rw [← ENNReal.ofReal_tsum_of_nonneg hb0 (hg.of_nonneg_of_le hb0 hbg)]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  exact hω.mono fun m hm => by simpa using hm

end Rigidity.Proofs.Section5
