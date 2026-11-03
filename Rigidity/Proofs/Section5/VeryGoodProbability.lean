import Rigidity.Proofs.Section5.RenormField

/-!
# Lemma 5.23: very good cubes have stretched exponentially high probability

Step `step:5.21-very-good` (eq. `verygoodstretchedexpclose1`, corrected draft L2207-2210), from
the literature inputs
`Rigidity.External.WellConnectedInput` (Proposition 2.3) and
`Rigidity.External.KestenRectangleCrossing` (Kesten, Theorem 11.1).

A cube `x + Q_r` fails to be very good when it is not well-connected or when one of its
`⌊(2r + 1)/w⌋` bands of width `w = ⌈√r⌉` in either direction has no open crossing. The band `j`
is the rectangle with corner `channelCorner x r w j k`, of length `2r` in the crossing direction
and `w - 1` in the other one, so Kesten's estimate bounds the probability that it is not crossed by
`C (2r + 1) exp(-c (w - 1)) ≤ C e^c (2r + 1) exp(-c √r)`. The union bound over the at most
`2r + 1` bands, with `(2r + 1)^2 exp(-c √r) ≤ K exp(-(c/2) √r)`, gives the stretched exponential
bound with exponent `min s (1/2)`.

Proposition 2.3 (`WellConnectedInput`) is stated for `p_c < p < 1`. For `p = 1` the bond law is the
Dirac mass at the configuration with every edge open (`latticeBondLaw_one`), in which every cube
`x + Q_N` with `N ≥ 1` and `N^{1/400} ≤ N/100` is well-connected (`allOpen_isWellConnected`): its
largest cluster is the whole cube. The condition `N^{1/400} ≤ N/100` holds once `N^{1/400} ≥ 2`, and
the bound `e^2 exp(-N^{1/400})` is at least `1` otherwise.
-/

open MeasureTheory LatticeProb.Percolation

namespace Rigidity.Proofs.Section5

open Rigidity.Section5

/-! ### Well-connectedness for every supercritical `p` -/

/-- The well-connectedness of Section 5 is that of Proposition 2.3 in dimension `2`. -/
theorem isWellConnected_iff_external (ω : Configuration 2) (x : Vertex 2) (N : ℕ) :
    IsWellConnected ω x N ↔ External.IsWellConnected ω x N := by
  have h : (1 / (10 * ((2 : ℕ) : ℝ)) ^ 2 : ℝ) = 1 / 400 := by norm_num
  unfold External.IsWellConnected
  rw [h]
  exact Iff.rfl

theorem mem_of_reachable_openIn {ω : Configuration 2} {B : Set (Vertex 2)} {a b : Vertex 2}
    (ha : a ∈ B) (h : (openIn ω B).Reachable a b) : b ∈ B := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact ha
  | cons hadj _ ih => exact ih hadj.2.2

theorem mem_cubeAt_two {z y : Vertex 2} {M : ℕ} :
    y ∈ cubeAt z M ↔ (z 0 - M ≤ y 0 ∧ y 0 ≤ z 0 + M) ∧ (z 1 - M ≤ y 1 ∧ y 1 ≤ z 1 + M) := by
  simp only [cubeAt, Set.mem_setOf_eq, Fin.forall_fin_two, abs_le]
  constructor <;> rintro ⟨⟨h1, h2⟩, h3, h4⟩ <;> refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

theorem allOpen_adj_openIn {B : Set (Vertex 2)} {a a' : Vertex 2} (ha : a ∈ B) (ha' : a' ∈ B)
    (h : (a 0 - a' 0).natAbs + (a 1 - a' 1).natAbs = 1) : (openIn (allOpen 2) B).Adj a a' := by
  refine ⟨?_, ha, ha'⟩
  rw [openGraph_allOpen, lattice_adj_iff_l1Dist]
  simp only [latticeL1Dist, Fin.sum_univ_two, Int.abs_eq_natAbs]
  omega

/-- With every edge open, a cube is connected. -/
theorem reachable_cubeAt_allOpen {z : Vertex 2} {M : ℕ} (n : ℕ) :
    ∀ a b : Vertex 2, (a 0 - b 0).natAbs + (a 1 - b 1).natAbs = n → a ∈ cubeAt z M →
      b ∈ cubeAt z M → (openIn (allOpen 2) (cubeAt z M)).Reachable a b := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a b hn ha hb
  have step : ∀ u v : ℤ, ![u, v] ∈ cubeAt z M → (a 0 - u).natAbs + (a 1 - v).natAbs = 1 →
      (u - b 0).natAbs + (v - b 1).natAbs < n →
        (openIn (allOpen 2) (cubeAt z M)).Reachable a b := by
    intro u v huv h1 h2
    exact (allOpen_adj_openIn ha huv (by simpa using h1)).reachable.trans
      (ih _ h2 _ _ (by simp) huv hb)
  have hmem : ∀ u v : ℤ, (z 0 - M ≤ u ∧ u ≤ z 0 + M) ∧ (z 1 - M ≤ v ∧ v ≤ z 1 + M) →
      ![u, v] ∈ cubeAt z M := fun u v h => mem_cubeAt_two.mpr (by simpa using h)
  rw [mem_cubeAt_two] at ha hb
  rcases lt_trichotomy (a 0) (b 0) with h0 | h0 | h0
  · exact step (a 0 + 1) (a 1) (hmem _ _ (by omega)) (by omega) (by omega)
  · rcases lt_trichotomy (a 1) (b 1) with h1 | h1 | h1
    · exact step (a 0) (a 1 + 1) (hmem _ _ (by omega)) (by omega) (by omega)
    · have : a = b := funext fun i => by fin_cases i <;> assumption
      subst this
      exact SimpleGraph.Reachable.refl _
    · exact step (a 0) (a 1 - 1) (hmem _ _ (by omega)) (by omega) (by omega)
  · exact step (a 0 - 1) (a 1) (hmem _ _ (by omega)) (by omega) (by omega)

/-- With every edge open, the largest cluster of a cube is the whole cube. -/
theorem isLargestClusterIn_allOpen (z : Vertex 2) (M : ℕ) :
    IsLargestClusterIn (allOpen 2) (cubeAt z M) (cubeAt z M) := by
  have hz : z ∈ cubeAt z M := fun i => by simp
  refine ⟨⟨z, hz, ?_⟩, fun x hx => Set.ncard_le_ncard
    (fun y hy => mem_of_reachable_openIn hx hy) (finite_cubeAt z M)⟩
  ext y
  exact ⟨fun hy => reachable_cubeAt_allOpen _ z y rfl hz hy,
    fun hy => mem_of_reachable_openIn hz hy⟩

theorem crossesCube_cubeAt (z : Vertex 2) (M : ℕ) : CrossesCube z M (cubeAt z M) := by
  intro i
  refine ⟨⟨Function.update z i (z i - M), fun j => ?_, by simp⟩,
    ⟨Function.update z i (z i + M), fun j => ?_, by simp⟩⟩ <;>
  · rcases eq_or_ne j i with rfl | hj
    · simp
    · simp [Function.update_of_ne hj]

/-- With every edge open, a cube `x + Q_N` with `N ≥ 1` and `N^{1/400} ≤ N/100` is
well-connected. -/
theorem allOpen_isWellConnected (x : Vertex 2) {N : ℕ} (hN : 1 ≤ N)
    (h : (N : ℝ) ^ (1 / 400 : ℝ) ≤ N / 100) : IsWellConnected (allOpen 2) x N := by
  refine ⟨h, ⟨_, isLargestClusterIn_allOpen x N, crossesCube_cubeAt x N⟩, fun z M hM _ _ => ?_⟩
  refine ⟨_, isLargestClusterIn_allOpen z M, crossesCube_cubeAt z M, fun n γ _ hγ hn => ?_⟩
  have h1 : (1 : ℝ) ≤ (N : ℝ) ^ (1 / 400 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hN) (by norm_num)
  have hM1 : (0 : ℝ) < M := by linarith
  have hn0 : 0 < n := by
    have : (0 : ℝ) < n := by linarith [div_pos hM1 (by norm_num : (0 : ℝ) < 100)]
    exact_mod_cast this
  exact ⟨γ 0, by simpa using (hγ ⟨0, hn0⟩).2.1, SimpleGraph.Reachable.refl _⟩

/-- Proposition 2.3 in dimension `2` for every `p_c < p ≤ 1`: for `p < 1` it is
`WellConnectedInput`; for `p = 1` every edge is open almost surely. -/
theorem wellConnected_bound (hW : External.WellConnectedInput) (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C c s : ℝ, 0 < C ∧ 0 < c ∧ 0 < s ∧ ∀ (x : Vertex 2) (N : ℕ),
      latticeBondLaw 2 p {ω | ¬ IsWellConnected ω x N} ≤
        ENNReal.ofReal (C * Real.exp (-(c * (N : ℝ) ^ s))) := by
  rcases lt_or_eq_of_le p.2.2 with hp1 | hp1
  · obtain ⟨c, C, s, hc, hC, hs, hb⟩ := hW 2 le_rfl p hpc hp1
    refine ⟨C, c, s, hC, hc, hs, fun x N => ?_⟩
    simpa only [isWellConnected_iff_external] using hb x N
  · have hp : p = 1 := Subtype.ext hp1
    subst hp
    refine ⟨Real.exp 2, 1, 1 / 400, Real.exp_pos _, one_pos, by norm_num, fun x N => ?_⟩
    rw [latticeBondLaw_one, Measure.dirac_apply]
    set u := (N : ℝ) ^ (1 / 400 : ℝ) with hu_def
    by_cases hu : u < 2
    · calc _ ≤ (1 : ENNReal) := by unfold Set.indicator; split_ifs <;> simp
        _ ≤ _ := by
          rw [ENNReal.one_le_ofReal, one_mul, ← Real.exp_add]
          exact Real.one_le_exp (by linarith)
    · push Not at hu
      have hu400 : u ^ (400 : ℕ) = N := by
        rw [hu_def, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
        norm_num
      have hN : 1 ≤ N := by
        rcases Nat.eq_zero_or_pos N with h | h
        · exfalso
          have : u = 0 := by rw [hu_def, h, Nat.cast_zero, Real.zero_rpow (by norm_num)]
          linarith
        · exact h
      have hcond : u ≤ (N : ℝ) / 100 := by
        rw [← hu400, le_div_iff₀ (by norm_num)]
        have h399 : (2 : ℝ) ^ 399 ≤ u ^ 399 := pow_le_pow_left₀ (by norm_num) hu 399
        have h100 : (100 : ℝ) ≤ 2 ^ 399 :=
          calc (100 : ℝ) ≤ 2 ^ 7 := by norm_num
            _ ≤ 2 ^ 399 := pow_le_pow_right₀ (by norm_num) (by norm_num)
        have : u ^ (400 : ℕ) = u * u ^ 399 := by ring
        rw [this]
        linarith [mul_le_mul_of_nonneg_left (h100.trans h399) (by linarith : (0 : ℝ) ≤ u)]
      have hwc := allOpen_isWellConnected x hN hcond
      rw [Set.indicator_of_notMem (by simpa using hwc)]
      simp

/-! ### Kesten channels -/

/-- The corner of the band `j` of width `w` of `x + Q_r` in the coordinate `k`. -/
def channelCorner (x : Vertex 2) (r w j : ℕ) (k : Fin 2) : Vertex 2 :=
  fun l => x l - r + if l = k then (j : ℤ) * w else 0

theorem fin_two_eq_or_eq {i k : Fin 2} (hik : i ≠ k) (l : Fin 2) : l = i ∨ l = k := by
  fin_cases i <;> fin_cases k <;> fin_cases l <;> simp_all

/-- The band `j` of `x + Q_r` contains the rectangle of Kesten's estimate at its corner. -/
theorem mem_band_of_mem_crossingRectangle {x : Vertex 2} {r w j : ℕ} {i k : Fin 2} (hik : i ≠ k)
    (hw : 0 < w) (hj : (j + 1) * w ≤ 2 * r + 1) {y : Vertex 2}
    (hy : y ∈ External.crossingRectangle (channelCorner x r w j k) (2 * r) (w - 1) i) :
    y ∈ band x r w j k := by
  have hj' : (j : ℤ) * w + w ≤ 2 * r + 1 := by
    have : ((j + 1) * w : ℕ) ≤ ((2 * r + 1 : ℕ) : ℤ) := by exact_mod_cast hj
    push_cast at this
    linarith
  have hyi := hy i
  have hyk := hy k
  simp only [channelCorner, if_neg hik, if_neg (Ne.symm hik), add_zero] at hyi hyk
  push_cast [Nat.cast_sub (show 1 ≤ w from hw)] at hyi hyk
  have hw0 : (0 : ℤ) ≤ (j : ℤ) * w := by positivity
  refine ⟨fun l => ?_, by linarith, by linarith⟩
  rw [abs_le]
  rcases fin_two_eq_or_eq hik l with rfl | rfl
  · constructor <;> linarith
  · constructor <;> linarith

theorem reachable_openIn_of_induce {ω : Configuration 2} {S B : Set (Vertex 2)} (hSB : S ⊆ B)
    {y z : Vertex 2} {hy : y ∈ S} {hz : z ∈ S}
    (h : ((openGraph ω).induce S).Reachable ⟨y, hy⟩ ⟨z, hz⟩) : (openIn ω B).Reachable y z := by
  let f : (openGraph ω).induce S →g openIn ω B :=
    ⟨Subtype.val, fun {a b} hab => ⟨hab, hSB a.2, hSB b.2⟩⟩
  exact h.map f

/-- Open crossings of the rectangles of all the bands give Kesten channels. -/
theorem hasKestenChannels_of_crossings {ω : Configuration 2} {x : Vertex 2} {r : ℕ} {i k : Fin 2}
    (hik : i ≠ k) (h : ∀ j < (2 * r + 1) / ⌈Real.sqrt r⌉₊,
      External.HasOpenCrossing ω (channelCorner x r ⌈Real.sqrt r⌉₊ j k) (2 * r)
        (⌈Real.sqrt r⌉₊ - 1) i) :
    HasKestenChannels ω x r i k := by
  intro j hj
  have hw : 0 < ⌈Real.sqrt r⌉₊ := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hj
  have hj' : (j + 1) * ⌈Real.sqrt r⌉₊ ≤ 2 * r + 1 := (Nat.le_div_iff_mul_le hw).mp hj
  obtain ⟨y, z, hy, hz, hyi, hzi, hr⟩ := h j hj
  refine ⟨y, z, mem_band_of_mem_crossingRectangle hik hw hj' hy,
    mem_band_of_mem_crossingRectangle hik hw hj' hz, ?_, ?_,
    reachable_openIn_of_induce (fun _ hv => mem_band_of_mem_crossingRectangle hik hw hj' hv) hr⟩
  · rw [hyi]
    simp [channelCorner, hik]
  · rw [hzi]
    simp [channelCorner, hik]
    ring

/-- `(2t² + 1)² exp(-c t) ≤ (9 + 216 (2/c)⁴) exp(-(c/2) t)` for `t ≥ 0`. -/
theorem sq_mul_exp_le {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : 0 ≤ t) :
    (2 * t ^ 2 + 1) ^ 2 * Real.exp (-(c * t)) ≤
      (9 + 216 * (2 / c) ^ 4) * Real.exp (-(c / 2 * t)) := by
  set E := Real.exp (c / 2 * t)
  set F := Real.exp (-(c / 2 * t))
  have hEF : E * F = 1 := by rw [← Real.exp_add]; simp
  have hFF : Real.exp (-(c * t)) = F * F := by rw [← Real.exp_add]; ring_nf
  have hE1 : 1 ≤ E := Real.one_le_exp (by positivity)
  have hF0 : 0 ≤ F := (Real.exp_pos _).le
  have he : (c / 2 * t) ^ 4 / 24 ≤ E := by
    simpa [Nat.factorial] using Real.pow_div_factorial_le_exp _ (by positivity : 0 ≤ c / 2 * t) 4
  have h4 : t ^ 4 ≤ 24 * (2 / c) ^ 4 * E := by
    have ht4 : t ^ 4 = (c / 2 * t) ^ 4 * (2 / c) ^ 4 := by field_simp
    rw [ht4]
    have : (c / 2 * t) ^ 4 ≤ 24 * E := by linarith
    nlinarith [pow_nonneg (div_pos two_pos hc).le 4]
  have hpoly : (2 * t ^ 2 + 1) ^ 2 ≤ (9 + 216 * (2 / c) ^ 4) * E := by
    nlinarith [sq_nonneg (t ^ 2 - 1), pow_nonneg (div_pos two_pos hc).le 4]
  calc (2 * t ^ 2 + 1) ^ 2 * Real.exp (-(c * t)) = (2 * t ^ 2 + 1) ^ 2 * F * F := by
        rw [hFF]; ring
    _ ≤ (9 + 216 * (2 / c) ^ 4) * E * F * F := by gcongr
    _ = (9 + 216 * (2 / c) ^ 4) * F := by rw [mul_assoc _ E F, hEF, mul_one]

/-- The union bound over the bands: Kesten channels in one direction fail with probability at most
`C e^c (9 + 216 (2/c)⁴) exp(-(c/2) r^{1/2})`. -/
theorem measure_not_hasKestenChannels_le {p : unitInterval} {C c : ℝ} (hC : 0 < C) (hc : 0 < c)
    (hK : ∀ (x : Vertex 2) (m n : ℕ) (i : Fin 2),
      latticeBondLaw 2 p {ω | ¬ External.HasOpenCrossing ω x m n i} ≤
        ENNReal.ofReal (C * (m + 1) * Real.exp (-(c * n))))
    {i k : Fin 2} (hik : i ≠ k) (x : Vertex 2) (r : ℕ) :
    latticeBondLaw 2 p {ω | ¬ HasKestenChannels ω x r i k} ≤
      ENNReal.ofReal (C * Real.exp c * (9 + 216 * (2 / c) ^ 4) *
        Real.exp (-(c / 2 * (r : ℝ) ^ (1 / 2 : ℝ)))) := by
  set w := ⌈Real.sqrt r⌉₊
  set J := (2 * r + 1) / w
  have hsub : {ω | ¬ HasKestenChannels ω x r i k} ⊆
      ⋃ j ∈ Finset.range J, {ω | ¬ External.HasOpenCrossing ω (channelCorner x r w j k) (2 * r)
        (w - 1) i} := by
    intro ω hω
    simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_setOf_eq, exists_prop]
    by_contra hcon
    push Not at hcon
    exact hω (hasKestenChannels_of_crossings hik hcon)
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans
    ((Finset.sum_le_sum fun j _ => hK _ _ _ i).trans ?_))
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hJ : (J : ℝ) ≤ 2 * r + 1 := by
    have : J ≤ 2 * r + 1 := Nat.div_le_self _ _
    exact_mod_cast this
  have hw : Real.sqrt r - 1 ≤ ((w - 1 : ℕ) : ℝ) := by
    have h1 : w ≤ (w - 1 : ℕ) + 1 := by omega
    have h2 : (w : ℝ) ≤ ((w - 1 : ℕ) : ℝ) + 1 := by exact_mod_cast h1
    linarith [Nat.le_ceil (Real.sqrt r)]
  have hexp : Real.exp (-(c * ((w - 1 : ℕ) : ℝ))) ≤ Real.exp c * Real.exp (-(c * Real.sqrt r)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hsq : (2 * (r : ℝ) + 1) ^ 2 * Real.exp (-(c * Real.sqrt r)) ≤
      (9 + 216 * (2 / c) ^ 4) * Real.exp (-(c / 2 * (r : ℝ) ^ (1 / 2 : ℝ))) := by
    have := sq_mul_exp_le hc (Real.sqrt_nonneg r)
    rw [Real.sq_sqrt (Nat.cast_nonneg r)] at this
    rwa [← Real.sqrt_eq_rpow]
  push_cast
  calc (J : ℝ) * (C * (2 * r + 1) * Real.exp (-(c * ((w - 1 : ℕ) : ℝ))))
      ≤ (2 * r + 1) * (C * (2 * r + 1) * (Real.exp c * Real.exp (-(c * Real.sqrt r)))) := by
        gcongr
    _ = C * Real.exp c * ((2 * (r : ℝ) + 1) ^ 2 * Real.exp (-(c * Real.sqrt r))) := by ring
    _ ≤ C * Real.exp c * ((9 + 216 * (2 / c) ^ 4) *
          Real.exp (-(c / 2 * (r : ℝ) ^ (1 / 2 : ℝ)))) := by gcongr
    _ = _ := by ring

/-! ### The step -/

theorem exp_neg_mul_rpow_le {c c' s s' : ℝ} (hc : 0 ≤ c) (hcc : c ≤ c') (hs : 0 < s)
    (hss : s ≤ s') (r : ℕ) :
    Real.exp (-(c' * (r : ℝ) ^ s')) ≤ Real.exp (-(c * (r : ℝ) ^ s)) := by
  refine Real.exp_le_exp.mpr (neg_le_neg ?_)
  have hr : (r : ℝ) ^ s ≤ (r : ℝ) ^ s' := by
    rcases Nat.eq_zero_or_pos r with h | h
    · simp [h, Real.zero_rpow hs.ne', Real.zero_rpow (hs.trans_le hss).ne']
    · exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast h) hss
  calc c * (r : ℝ) ^ s ≤ c' * (r : ℝ) ^ s := mul_le_mul_of_nonneg_right hcc (by positivity)
    _ ≤ c' * (r : ℝ) ^ s' := mul_le_mul_of_nonneg_left hr (hc.trans hcc)

/-- **Step `step:5.21-very-good`** (eq. `verygoodstretchedexpclose1`). -/
theorem veryGoodProbabilityStep : Steps.Section5.VeryGoodProbabilityStep := by
  intro hW hK p hpc
  obtain ⟨C₁, c₁, s₁, hC₁, hc₁, hs₁, hb₁⟩ := wellConnected_bound hW p hpc
  obtain ⟨C₂, c₂, hC₂, hc₂, hb₂⟩ := hK p hpc
  set K := C₂ * Real.exp c₂ * (9 + 216 * (2 / c₂) ^ 4) with hK_def
  have hK0 : 0 < K := by positivity
  set c := min c₁ (c₂ / 2)
  set s := min s₁ (1 / 2)
  have hc : 0 < c := lt_min hc₁ (by positivity)
  have hs : 0 < s := lt_min hs₁ (by norm_num)
  refine ⟨C₁ + 2 * K, c, s, by positivity, hc, hs, fun x r => ?_⟩
  have hsub : {ω | ¬ IsVeryGood ω x r} ⊆ ({ω | ¬ IsWellConnected ω x r} ∪
      {ω | ¬ HasKestenChannels ω x r 0 1}) ∪ {ω | ¬ HasKestenChannels ω x r 1 0} := by
    intro ω hω
    simp only [Set.mem_union, Set.mem_setOf_eq]
    by_contra hcon
    push Not at hcon
    exact hω ⟨hcon.1.1, hcon.1.2, hcon.2⟩
  have h01 := measure_not_hasKestenChannels_le hC₂ hc₂ hb₂ (by decide : (0 : Fin 2) ≠ 1) x r
  have h10 := measure_not_hasKestenChannels_le hC₂ hc₂ hb₂ (by decide : (1 : Fin 2) ≠ 0) x r
  rw [← hK_def] at h01 h10
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ((add_le_add
    (measure_union_le _ _) le_rfl).trans ((add_le_add (add_le_add (hb₁ x r) h01) h10).trans ?_)))
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have e1 := exp_neg_mul_rpow_le hc.le (min_le_left _ _) hs (min_le_left _ _) r
  have e2 := exp_neg_mul_rpow_le hc.le (min_le_right _ _) hs (min_le_right _ _) r
  nlinarith [mul_le_mul_of_nonneg_left e1 hC₁.le, mul_le_mul_of_nonneg_left e2 hK0.le]

end Rigidity.Proofs.Section5
