import Rigidity.Proofs.WeakPoincare.GoodBallsHolds
import PercolationClusterHomogenization.Proofs.Partition.GeneralPartition

/-!
# Very good balls and the weak Poincaré inequality of Dario–Gu in every dimension

From the good balls at a fixed centre (`ClusterGoodBalls d`, proved for `d ≥ 2` in
`clusterGoodBalls_holds`):

* `clusterVeryGoodBalls_of_goodBalls`: Barlow's Theorem 2.18 (c) with Lemma 2.19 in the Euclidean
  form `ClusterVeryGoodBalls d`. For `θ > 0` and `A ≥ 1`, the minimal scales `M(z)` of the centres
  `z` of the box of radius `⌈A 3^{m+1}⌉` around `y` are at most `3^{θm}` except on an event of
  probability at most `(9 A 3^m)^d · 2 exp(-(3^{θm}/C)^s)` (Markov's inequality and a union bound),
  which is summable against `exp((3^{m+1})^{θs/2})` (`summable_box_tail`); the minimal scale `S(y)`
  of these events (`exists_minimalScale_of_summable`) has a stretched exponential moment, and for
  `R ≥ S(y)`, with `3^m ≤ R < 3^{m+1}`, every ball `𝒞_∞ ∩ B_r(z)` with `|z - y| ≤ A R` and
  `r ≥ R^θ ≥ 3^{θm} ≥ M(z)` is good.
* `clusterPoincare_of_goodBalls`: Dario–Gu, Proposition 2.7, weak form, `ClusterPoincare d`, from
  the volume bounds at the radii `R` and `L R` and the unnormalized weak Poincaré inequality.

`clusterVeryGoodBalls_holds` and `clusterPoincare_holds` are these statements for `d ≥ 2`, in
particular for every `d ≥ 3`.
-/

open MeasureTheory Finset LatticeProb.Percolation Rigidity.External Rigidity.Percolation
open Rigidity.Proofs.Cluster Rigidity.Proofs.S2
open scoped ENNReal

namespace Rigidity.WeakPoincare

variable {d : ℕ}

/-- Markov's inequality for a nonnegative variable `X ≤ O_s(θ)`:
`P(X > t) ≤ 2 exp(-(t/θ)^s)` for `t ≥ 0`. -/
theorem measure_lt_le_of_isOsBond {p : unitInterval} {X : Configuration d → ℝ} {s θ : ℝ}
    (hX : ∀ ω, 0 ≤ X ω) (hθ : 0 < θ) (hs : 0 < s) (h : IsOsBond d p X s θ) {t : ℝ}
    (ht : 0 ≤ t) :
    latticeBondLaw d p {ω | t < X ω} ≤ ENNReal.ofReal (2 * Real.exp (-((t / θ) ^ s))) := by
  obtain ⟨hi, hb⟩ := h
  have he : (fun ω => Real.exp (Real.rpow (max (X ω / θ) 0) s)) =
      fun ω => Real.exp ((X ω / θ) ^ s) := by
    funext ω
    rw [max_eq_left (div_nonneg (hX ω) hθ.le)]
    rfl
  rw [he] at hi hb
  exact measure_lt_le_of_exp_rpow_moment _ hθ hs hi hb ht

/-- The box of radius `⌈A 3^{m+1}⌉`, `A ≥ 1`, has at most `(9 A 3^m)^d` points. -/
theorem card_box_ceil_le (c : Vertex d) {A : ℝ} (hA : 1 ≤ A) (m : ℕ) :
    ((box c ⌈A * 3 ^ (m + 1)⌉).card : ℝ) ≤ (9 * A * 3 ^ m) ^ d := by
  have hA0 : 0 < A := by linarith
  have hx : 0 < A * 3 ^ (m + 1) := by positivity
  have h0 : (0 : ℤ) ≤ ⌈A * 3 ^ (m + 1)⌉ := Int.ceil_nonneg hx.le
  have h0' : (0 : ℝ) ≤ ((⌈A * 3 ^ (m + 1)⌉ : ℤ) : ℝ) := by exact_mod_cast h0
  rw [card_box c h0]
  refine pow_le_pow_left₀ (by push_cast; linarith) ?_ d
  have h1 : ((⌈A * 3 ^ (m + 1)⌉ : ℤ) : ℝ) < A * 3 ^ (m + 1) + 1 := Int.ceil_lt_add_one _
  have h2 : (1 : ℝ) ≤ 3 ^ m := one_le_pow₀ (by norm_num)
  have h4 : A * (3 : ℝ) ^ (m + 1) = 3 * (A * 3 ^ m) := by ring
  have h5 : 1 ≤ A * (3 : ℝ) ^ m := by nlinarith
  push_cast
  linarith

/-- **The tail of the union bound over the boxes is summable**:
`Σ_m (9 A 3^m)^d · 2 exp(-(3^{θm}/C)^s) · exp((3^{m+1})^{θs/2}) < ∞`. -/
theorem summable_box_tail {A C s θ : ℝ} (hA : 1 ≤ A) (hC : 0 < C) (hs : 0 < s) (hθ : 0 < θ) :
    Summable fun m : ℕ => (9 * A * 3 ^ m) ^ d * (2 * Real.exp (-((((3 : ℝ) ^ m) ^ θ / C) ^ s))) *
      Real.exp ((1 * 3 ^ (m + 1)) ^ (θ * s / 2)) := by
  have hA0 : 0 ≤ A := by linarith
  set s₁ := θ * s / 2 with hs₁
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  set τ := s₁ * Real.log 3 with hτ
  have hτ0 : 0 < τ := by positivity
  set B := (C ^ s)⁻¹ with hB
  have hB0 : 0 < B := by positivity
  set K := (d : ℝ) * Real.log 3 / τ + 3 ^ s₁ with hK
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
    ((summable_exp_mul_sub_sq K B τ hB0 hτ0).mul_left (2 * (9 * A) ^ d))
  show (9 * A * 3 ^ m) ^ d * (2 * Real.exp (-((((3 : ℝ) ^ m) ^ θ / C) ^ s))) *
      Real.exp ((1 * 3 ^ (m + 1)) ^ s₁) ≤
    2 * (9 * A) ^ d * Real.exp (K * Real.exp (τ * m) - B * Real.exp (τ * m) ^ 2)
  obtain ⟨E, hE⟩ : ∃ E, E = Real.exp (τ * m) := ⟨_, rfl⟩
  rw [← hE]
  have hτne : τ ≠ 0 := hτ0.ne'
  have f1 : (3 : ℝ) ^ m = Real.exp (Real.log 3 * m) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
  have f2 : ((3 : ℝ) ^ m) ^ d ≤ Real.exp ((d : ℝ) * Real.log 3 / τ * E) := by
    rw [f1, ← Real.exp_nat_mul]
    refine Real.exp_le_exp.2 ?_
    have h1 : τ * m ≤ E := by
      have := Real.add_one_le_exp (τ * m)
      rw [hE]
      linarith
    have h2 : (d : ℝ) * (Real.log 3 * m) = (d : ℝ) * Real.log 3 / τ * (τ * m) := by
      rw [div_mul_eq_mul_div, eq_div_iff hτne]
      ring
    rw [h2]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have f3 : (((3 : ℝ) ^ m) ^ θ / C) ^ s = B * E ^ 2 := by
    have h3m : (0 : ℝ) ≤ (3 : ℝ) ^ m := by positivity
    rw [Real.div_rpow (Real.rpow_nonneg h3m _) hC.le, ← Real.rpow_mul h3m, f1,
      ← Real.exp_mul, hE, sq, ← Real.exp_add, hB, hτ, hs₁, div_eq_inv_mul]
    congr 2
    ring
  have f4 : ((1 : ℝ) * 3 ^ (m + 1)) ^ s₁ = 3 ^ s₁ * E := by
    rw [scale_exponent_eq (by norm_num) m, mul_one, hE, hτ]
  have f5 : Real.exp ((d : ℝ) * Real.log 3 / τ * E) * Real.exp (-(B * E ^ 2)) *
      Real.exp (3 ^ s₁ * E) = Real.exp (K * E - B * E ^ 2) := by
    rw [← Real.exp_add, ← Real.exp_add, hK]
    congr 1
    ring
  calc (9 * A * 3 ^ m) ^ d * (2 * Real.exp (-((((3 : ℝ) ^ m) ^ θ / C) ^ s))) *
        Real.exp ((1 * 3 ^ (m + 1)) ^ s₁)
      = (9 * A) ^ d * ((3 : ℝ) ^ m) ^ d * (2 * Real.exp (-(B * E ^ 2))) *
          Real.exp (3 ^ s₁ * E) := by rw [f3, f4, mul_pow (9 * A) ((3 : ℝ) ^ m) d]
    _ ≤ (9 * A) ^ d * Real.exp ((d : ℝ) * Real.log 3 / τ * E) *
          (2 * Real.exp (-(B * E ^ 2))) * Real.exp (3 ^ s₁ * E) := by gcongr
    _ = 2 * (9 * A) ^ d * (Real.exp ((d : ℝ) * Real.log 3 / τ * E) * Real.exp (-(B * E ^ 2)) *
          Real.exp (3 ^ s₁ * E)) := by ring
    _ = 2 * (9 * A) ^ d * Real.exp (K * E - B * E ^ 2) := by
        rw [f5]

/-- **Very good balls from good balls** (Barlow 2004, Theorem 2.18 (c) with Lemma 2.19). -/
theorem clusterVeryGoodBalls_of_goodBalls [NeZero d] (hG : ClusterGoodBalls d) :
    ClusterVeryGoodBalls d := by
  intro p hpc hp1
  obtain ⟨s, C, L, hs, hC, hL, hgood⟩ := hG p hpc hp1
  refine ⟨C, L, hC, hL, fun θ A hθ hA => ?_⟩
  choose M hMm hM0 hMos hMae using hgood
  have hA0 : 0 ≤ A := by linarith
  set μ := latticeBondLaw d p with hμ
  set s₁ := θ * s / 2 with hs₁
  have hs₁0 : 0 < s₁ := by positivity
  set b : ℕ → ℝ := fun m =>
    (9 * A * 3 ^ m) ^ d * (2 * Real.exp (-((((3 : ℝ) ^ m) ^ θ / C) ^ s))) with hb
  have hb0 : ∀ m, 0 ≤ b m := fun m => by positivity
  have hsumm : Summable fun m => b m * Real.exp ((1 * 3 ^ (m + 1)) ^ s₁) :=
    summable_box_tail (d := d) hA hC hs hθ
  set Bad : Vertex d → ℕ → Set (Configuration d) := fun y m =>
    ⋃ z ∈ box y ⌈A * 3 ^ (m + 1)⌉, {ω | ((3 : ℝ) ^ m) ^ θ < M z ω} with hBad
  have hBadm : ∀ y m, MeasurableSet (Bad y m) := fun y m =>
    Finset.measurableSet_biUnion _ fun z _ => measurableSet_lt measurable_const (hMm z)
  have hBadμ : ∀ y m, μ (Bad y m) ≤ ENNReal.ofReal (b m) := by
    intro y m
    calc μ (Bad y m) ≤ ∑ z ∈ box y ⌈A * 3 ^ (m + 1)⌉, μ {ω | ((3 : ℝ) ^ m) ^ θ < M z ω} :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ _z ∈ box y ⌈A * 3 ^ (m + 1)⌉,
          ENNReal.ofReal (2 * Real.exp (-((((3 : ℝ) ^ m) ^ θ / C) ^ s))) :=
          Finset.sum_le_sum fun z _ =>
            measure_lt_le_of_isOsBond (hM0 z) hC hs (hMos z) (by positivity)
      _ = ENNReal.ofReal ((box y ⌈A * 3 ^ (m + 1)⌉).card *
          (2 * Real.exp (-((((3 : ℝ) ^ m) ^ θ / C) ^ s)))) := by
          rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      _ ≤ ENNReal.ofReal (b m) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (card_box_ceil_le y hA m)
            (by positivity))
  set B₁ := Real.exp ((1 : ℝ) ^ s₁) + ∑' m, b m * Real.exp ((1 * 3 ^ (m + 1)) ^ s₁) with hB₁
  have hB₁1 : 1 ≤ B₁ := by
    have h1 := Real.one_le_exp (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 1) s₁)
    have h2 : 0 ≤ ∑' m, b m * Real.exp ((1 * 3 ^ (m + 1)) ^ s₁) :=
      tsum_nonneg fun m => mul_nonneg (hb0 m) (Real.exp_pos _).le
    linarith
  refine ⟨s₁, 1 * B₁ ^ (1 / s₁), hs₁0, by positivity, fun y => ?_⟩
  obtain ⟨S, hSm, hS0, hSint, hSle, hSae⟩ := exists_minimalScale_of_summable μ (Bad y)
    (hBadm y) one_pos b hb0 (hBadμ y) hsumm
  have he : (fun ω => Real.exp ((max (S ω / 1) 0).rpow s₁)) = fun ω => Real.exp (S ω ^ s₁) := by
    funext ω
    rw [div_one, max_eq_left (hS0 ω)]
    rfl
  refine ⟨S, hSm, hS0, ?_, ?_⟩
  · refine isOsBond_of_integral_le hs₁0 hB₁1 (by rw [he]; exact hSint) ?_
    rw [he]
    exact hSle
  have hall := ae_all_iff.2 hMae
  filter_upwards [hSae, hall] with ω hSω hallω
  intro h R hR z hz r hr
  obtain ⟨N, hSN, hN⟩ := hSω
  have hRN : (3 : ℝ) ^ N ≤ R := by
    rw [hSN, one_mul] at hR
    exact hR
  have hex : ∃ n : ℕ, R < (3 : ℝ) ^ (n + 1) := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt R (by norm_num : (1 : ℝ) < 3)
    exact ⟨n, hn.trans (pow_lt_pow_right₀ (by norm_num) (Nat.lt_succ_self n))⟩
  classical
  set m := Nat.find hex with hmdef
  have hm1 : R < (3 : ℝ) ^ (m + 1) := Nat.find_spec hex
  have hNm : N ≤ m := by
    by_contra hlt
    push Not at hlt
    have : (3 : ℝ) ^ (m + 1) ≤ 3 ^ N := pow_le_pow_right₀ (by norm_num) hlt
    linarith
  have hm0 : (3 : ℝ) ^ m ≤ R := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · rw [h0, pow_zero]
      have : (1 : ℝ) ≤ 3 ^ N := one_le_pow₀ (by norm_num)
      linarith
    · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
      have hmin := Nat.find_min hex (show k < m by omega)
      rw [not_lt] at hmin
      rw [hk]
      exact hmin
  have hzB : z ∈ box y ⌈A * 3 ^ (m + 1)⌉ := mem_box.2 fun i => by
    have h1 := abs_sub_le_latticeDist z y i
    have h2 : A * R ≤ A * 3 ^ (m + 1) := mul_le_mul_of_nonneg_left hm1.le hA0
    have h3 := Int.le_ceil (A * 3 ^ (m + 1))
    have h4 : ((|z i - y i| : ℤ) : ℝ) ≤ ((⌈A * 3 ^ (m + 1)⌉ : ℤ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h4
  have hMz : M z ω ≤ ((3 : ℝ) ^ m) ^ θ := by
    by_contra hlt
    push Not at hlt
    exact hN m hNm (Set.mem_iUnion₂.2 ⟨z, hzB, hlt⟩)
  have hrM : M z ω ≤ r :=
    hMz.trans ((Real.rpow_le_rpow (by positivity) hm0 hθ.le).trans hr)
  exact hallω z h r hrM

/-- The normalization of the weak Poincaré inequality: from `S ≤ C R² E`, `C⁻¹ R^d ≤ |B_R|`,
`|B_{LR}| ≤ C (LR)^d` and `C³ L^d ≤ K²`, `(S/|B_R|)^{1/2} ≤ K R (E/|B_{LR}|)^{1/2}`. -/
theorem sqrt_div_le_of_goodBall {S nR nL E C K L R : ℝ} (hR : 0 < R) (hC : 0 < C) (hL : 0 < L)
    (hE : 0 ≤ E) (hS : S ≤ C * R ^ 2 * E) (hnR : C⁻¹ * R ^ d ≤ nR) (hnL : nL ≤ C * (L * R) ^ d)
    (hnL0 : 0 < nL) (hK0 : 0 ≤ K) (hK : C ^ 3 * L ^ d ≤ K ^ 2) :
    Real.sqrt (S / nR) ≤ K * R * Real.sqrt (E / nL) := by
  have hRd : 0 < R ^ d := by positivity
  have hnR0 : 0 < nR := lt_of_lt_of_le (by positivity) hnR
  have hCne : C ≠ 0 := hC.ne'
  have hRC : R ^ d ≤ C * nR := by
    have h := mul_le_mul_of_nonneg_left hnR hC.le
    rwa [← mul_assoc, mul_inv_cancel₀ hCne, one_mul] at h
  have h1 : S / nR ≤ C ^ 2 * R ^ 2 * E / R ^ d := by
    rw [div_le_div_iff₀ hnR0 hRd]
    calc S * R ^ d ≤ (C * R ^ 2 * E) * R ^ d := mul_le_mul_of_nonneg_right hS hRd.le
      _ ≤ (C * R ^ 2 * E) * (C * nR) := mul_le_mul_of_nonneg_left hRC (by positivity)
      _ = C ^ 2 * R ^ 2 * E * nR := by ring
  have hCL : 0 < C * (L * R) ^ d := by positivity
  have h2 : C ^ 2 * R ^ 2 * E / R ^ d ≤ (K * R) ^ 2 * (E / nL) := by
    calc C ^ 2 * R ^ 2 * E / R ^ d = (C ^ 3 * L ^ d) * R ^ 2 * E / (C * (L * R) ^ d) := by
          rw [div_eq_div_iff hRd.ne' hCL.ne', mul_pow]
          ring
      _ ≤ K ^ 2 * R ^ 2 * E / (C * (L * R) ^ d) := by gcongr
      _ ≤ K ^ 2 * R ^ 2 * E / nL := by gcongr
      _ = (K * R) ^ 2 * (E / nL) := by ring
  calc Real.sqrt (S / nR) ≤ Real.sqrt ((K * R) ^ 2 * (E / nL)) := Real.sqrt_le_sqrt (h1.trans h2)
    _ = K * R * Real.sqrt (E / nL) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

/-- **Dario–Gu, Proposition 2.7, weak form, from good balls.** -/
theorem clusterPoincare_of_goodBalls [NeZero d] (hG : ClusterGoodBalls d) : ClusterPoincare d := by
  intro p hpc hp1
  obtain ⟨s, C, L, hs, hC, hL, hgood⟩ := hG p hpc hp1
  set K := max C (C ^ 2 * L ^ d) with hK
  have hKC : C ≤ K := le_max_left _ _
  have hK0 : 0 < K := lt_of_lt_of_le hC hKC
  have hK2 : C ^ 3 * L ^ d ≤ K ^ 2 := by
    have h1 : C ^ 2 * L ^ d ≤ K := le_max_right _ _
    calc C ^ 3 * L ^ d = C * (C ^ 2 * L ^ d) := by ring
      _ ≤ K * K := mul_le_mul hKC h1 (by positivity) hK0.le
      _ = K ^ 2 := by ring
  refine ⟨s, K, L, hs, hK0, hL, fun y => ?_⟩
  obtain ⟨M, hMm, hM0, hMos, hMae⟩ := hgood y
  refine ⟨M, hMm, hM0, IsOsBond.mono_scale hs hC hKC hMm hMos, ?_⟩
  filter_upwards [hMae] with ω hω
  intro h R hR u
  have hR0 : 0 ≤ R := (hM0 ω).trans hR
  have hL0 : 0 < L := by linarith
  rcases hR0.lt_or_eq with hRpos | hReq
  · obtain ⟨⟨hvol, hpo⟩, -⟩ := hω h R hR
    have hLR : M ω ≤ L * R := hR.trans (le_mul_of_one_le_left hR0 hL)
    obtain ⟨⟨hvolL, -⟩, hcardL⟩ := hω h (L * R) hLR
    have hnL0 : (0 : ℝ) < (clusterBall (uniqueInfiniteComponent h) y (L * R)).card :=
      lt_of_lt_of_le (by positivity) hvolL
    exact sqrt_div_le_of_goodBall hRpos hC hL0 (nbrEnergy_nonneg _ _ _) (hpo u) hvol
      hcardL hnL0 hK0.le hK2
  · subst hReq
    have hn : ∀ x, ¬ latticeDist x y < 0 := fun x => not_lt.2 (latticeDist_nonneg x y)
    have hempty : clusterBall (uniqueInfiniteComponent h) y 0 = ∅ := by
      ext x
      simp [mem_clusterBall, hn]
    rw [hempty]
    simp

/-- **Very good balls of the supercritical infinite cluster** in every dimension `d ≥ 2` (Barlow
2004, Theorem 2.18 (c) with Lemma 2.19, Euclidean balls). -/
theorem clusterVeryGoodBalls_holds [NeZero d] (hd : 2 ≤ d) : ClusterVeryGoodBalls d :=
  clusterVeryGoodBalls_of_goodBalls (clusterGoodBalls_holds hd)

/-- **The weak Poincaré inequality on balls of the supercritical infinite cluster** in every
dimension `d ≥ 2` (Dario–Gu, Proposition 2.7, weak form). -/
theorem clusterPoincare_holds [NeZero d] (hd : 2 ≤ d) : ClusterPoincare d :=
  clusterPoincare_of_goodBalls (clusterGoodBalls_holds hd)

end Rigidity.WeakPoincare
