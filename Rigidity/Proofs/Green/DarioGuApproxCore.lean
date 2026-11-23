import Rigidity.Proofs.Green.DarioGuApproxAnnuli

/-!
# The estimate of each annulus in the proof of Lemma 4.1 of Dario–Gu

`approx_term_le`: with `U_n = 𝒞 ∩ B_{2^n √τ}(y)`, `g = p(s, x, ·)`, `O_n = Σ_{U_n} |g - (g)_{U_n}|`,
`a_n = Φ_{C₀}(τ, ρ_n)` (`ρ_0 = 0`, `ρ_n = 2^{n-1} √τ`), and `s = t - τ ≥ 2τ`:

`a_n O_n (1 + |U_n|/|U_0|) ≤ K 64^n e^{-2^n/(4C₀)} (τ/t)^{1/2} Φ_{C*}(t, x - y)`,

* at the scales `4 (L 2^n √τ)² ≤ s` when `|x - y| ≤ s`: by the weak Poincaré inequality on
  `B_{2^n √τ}(y)` and the gradient bound (Theorem 3, Remark 1.3) on `B_{L 2^n √τ}(y)`, as in (4.9),
  (4.10) and (4.13) of the source;
* at the scales `4 (L 2^n √τ)² > s` when `|x - y| ≤ s`: by (eq:PhiCTrick) and (4.15), as in
  (4.14)-(4.16);
* when `|x - y| > s`: by (eq:PhiCTrick), (4.15) and `Φ_C(t, r) ≤ C t^{-1/2} Φ_{2C}(t, r)` for
  `r ≥ 2t/3` (Remark 1.3 requires `t - τ ≥ |x - y|`; the source applies Theorem 3 at every `x`).
-/

open Finset LatticeProb.Percolation Rigidity.External

namespace Rigidity.Green

/-- `φ (O V) ≤ 2 K_B K_c K_v 4^n e Φ₈` from `O ≤ 2 S`, `V ≤ K_v 4^n`, `φ S ≤ K_B e K_c Φ₈`. -/
theorem approx_real_base {φ O V S KB Kc Kv e Φ₈ : ℝ} (n : ℕ) (hφ0 : 0 ≤ φ) (hS0 : 0 ≤ S)
    (hV0 : 0 ≤ V) (hKv : 0 ≤ Kv) (hO : O ≤ 2 * S) (hV : V ≤ Kv * 4 ^ n)
    (hmid : φ * S ≤ KB * e * (Kc * Φ₈)) :
    φ * (O * V) ≤ 2 * KB * Kc * Kv * (4 ^ n * e) * Φ₈ := by
  calc φ * (O * V) ≤ φ * ((2 * S) * (Kv * 4 ^ n)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hO hV hV0 (by positivity)) hφ0
    _ = 2 * Kv * 4 ^ n * (φ * S) := by ring
    _ ≤ 2 * Kv * 4 ^ n * (KB * e * (Kc * Φ₈)) := mul_le_mul_of_nonneg_left hmid (by positivity)
    _ = _ := by ring

/-- The arithmetic of the far points (`|x - y| > s`) in the proof of Lemma 4.1. -/
theorem approx_real_B2 {KB Kc Kv τ t e Φ₈ Φ₂ Φ x C₈ : ℝ} (n : ℕ) (hKB : 0 ≤ KB) (hKc : 0 ≤ Kc)
    (hKv : 0 ≤ Kv) (he : 0 ≤ e) (hC₈ : 0 ≤ C₈) (hΦ₂ : 0 ≤ Φ₂)
    (hx : x ≤ 2 * KB * Kc * Kv * (4 ^ n * e) * Φ₈)
    (hfar : Φ₈ ≤ 9 * C₈ / 4 * (Real.sqrt t)⁻¹ * Φ₂)
    (hinv : (Real.sqrt t)⁻¹ ≤ Real.sqrt τ / Real.sqrt t) (hΦ : Φ₂ ≤ Φ) :
    x ≤ 2 * KB * Kc * Kv * (9 * C₈ / 4) * (64 ^ n * e) * (Real.sqrt τ / Real.sqrt t) * Φ := by
  have hK : 0 ≤ 2 * KB * Kc * Kv * (4 ^ n * e) := by positivity
  have hΦ0 : 0 ≤ Φ := hΦ₂.trans hΦ
  have h1 : Φ₈ ≤ 9 * C₈ / 4 * (Real.sqrt τ / Real.sqrt t) * Φ :=
    hfar.trans (mul_le_mul (mul_le_mul_of_nonneg_left hinv (by positivity)) hΦ hΦ₂
      (by have := Real.sqrt_nonneg τ; have := Real.sqrt_nonneg t; positivity))
  have h4 : (4 : ℝ) ^ n ≤ 64 ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
  have hst : 0 ≤ Real.sqrt τ / Real.sqrt t := by
    have := Real.sqrt_nonneg τ; have := Real.sqrt_nonneg t; positivity
  calc x ≤ 2 * KB * Kc * Kv * (4 ^ n * e) * (9 * C₈ / 4 * (Real.sqrt τ / Real.sqrt t) * Φ) :=
        hx.trans (mul_le_mul_of_nonneg_left h1 hK)
    _ = 2 * KB * Kc * Kv * (9 * C₈ / 4) * (4 ^ n * e) * (Real.sqrt τ / Real.sqrt t) * Φ := by ring
    _ ≤ _ := by gcongr

/-- **The term of the `n`-th annulus** in the proof of Lemma 4.1. -/
theorem approx_term_le {C₀ CP CL CG cd Kc C₈ : ℝ} (hC₀ : 0 < C₀) (hCP : 0 < CP) (hCL : 1 ≤ CL)
    (hCG : 0 < CG)
    (hcd : 0 < cd) (hKc : 0 < Kc) (hC₈ : 0 < C₈) :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧ ∀ (ω : Configuration 2) (K' : OpenComponent ω) (x y : Vertex 2)
      (s t τ : ℝ), 1 ≤ τ → 2 * τ ≤ s → s ≤ t → 2 * t ≤ 3 * s →
      (∀ R : ℝ, Real.sqrt τ ≤ R → ∀ u : Vertex 2 → ℝ,
        Real.sqrt ((∑ z ∈ clusterBall K' y R, (u z - finAvg (clusterBall K' y R) u) ^ 2) /
            (clusterBall K' y R).card) ≤
          CP * R * Real.sqrt (gradEnergy ω (clusterBall K' y (CL * R)) u /
            (clusterBall K' y (CL * R)).card)) →
      (∀ R : ℝ, Real.sqrt τ ≤ R → 4 * R ^ 2 ≤ s → latticeDist x y ≤ s →
        Real.sqrt (gradEnergy ω (clusterBall K' y R) (fun z => openHeat ω s x z) /
            (clusterBall K' y R).card) ≤
          CG * s ^ (-(3 / 2 : ℝ)) * Real.exp (-(latticeDist x y ^ 2 / (CG * s)))) →
      cd * τ ≤ (clusterBall K' y (2 ^ 0 * Real.sqrt τ)).card →
      (∀ S : Finset (Vertex 2), ∑ z ∈ S, openHeat ω s x z * dgPhi (16 * C₀) τ (latticeDist z y) ≤
        Kc * dgPhi C₈ t (latticeDist x y)) →
      ∀ n : ℕ, dgPhi C₀ τ (annulusInner τ n) *
        ((∑ z ∈ clusterBall K' y (2 ^ n * Real.sqrt τ), |openHeat ω s x z -
            finAvg (clusterBall K' y (2 ^ n * Real.sqrt τ)) (fun z => openHeat ω s x z)|) *
          (1 + ((clusterBall K' y (2 ^ n * Real.sqrt τ)).card : ℝ) /
            (clusterBall K' y (2 ^ 0 * Real.sqrt τ)).card)) ≤
        K * ((64 : ℝ) ^ n * Real.exp (-((2 : ℝ) ^ n / (4 * C₀)))) *
          (Real.sqrt τ / Real.sqrt t) * dgPhi C t (latticeDist x y) := by
  set Kv := 1 + 25 / cd with hKv
  set KB := Real.exp (1 / (16 * C₀) + 1 / (4 * C₀)) / 16 with hKB
  set Cs := max CG (2 * C₈) with hCs
  have hCs0 : 0 < Cs := lt_max_of_lt_left hCG
  set KA := 25 * C₀ * Real.exp (1 / C₀) * CP * CG * Kv * 2 * (3 / (2 * Cs)) with hKA
  set K1 := 8 * CL * KB * Kc * Kv with hK1
  have hCL0 : 0 < CL := by linarith
  set K2 := 2 * KB * Kc * Kv * (9 * C₈ / 4) with hK2
  have hKv0 : 0 < Kv := by positivity
  have hKB0 : 0 < KB := by positivity
  refine ⟨max KA (max K1 K2), Cs, lt_max_of_lt_left (by positivity), hCs0, ?_⟩
  intro ω K' x y s t τ hτ1 hτs hst h23 hP hG hvol hconv n
  have hτ0 : 0 < τ := by linarith
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  have hsτ : 1 ≤ Real.sqrt τ := by rw [Real.one_le_sqrt]; exact hτ1
  have hsτ0 : 0 < Real.sqrt τ := by linarith
  have hstt : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
  have hR1 : Real.sqrt τ ≤ 2 ^ n * Real.sqrt τ :=
    le_mul_of_one_le_left hsτ0.le (one_le_pow₀ (by norm_num))
  have hg0 : ∀ z, 0 ≤ openHeat ω s x z := fun z => openHeat_nonneg' ω hs0.le x z
  have he0 : 0 < Real.exp (-((2 : ℝ) ^ n / (4 * C₀))) := Real.exp_pos _
  have hd0 := latticeDist_nonneg x y
  have hφ0 : 0 ≤ dgPhi C₀ τ (annulusInner τ n) := dgPhi_nonneg hC₀.le hτ0.le _
  have hO0 : 0 ≤ ∑ z ∈ clusterBall K' y (2 ^ n * Real.sqrt τ), |openHeat ω s x z -
      finAvg (clusterBall K' y (2 ^ n * Real.sqrt τ)) (fun z => openHeat ω s x z)| :=
    Finset.sum_nonneg fun z _ => abs_nonneg _
  have hU0pos : (0 : ℝ) < (clusterBall K' y (2 ^ 0 * Real.sqrt τ)).card :=
    lt_of_lt_of_le (by positivity) hvol
  have hV0 : 0 ≤ 1 + ((clusterBall K' y (2 ^ n * Real.sqrt τ)).card : ℝ) /
      (clusterBall K' y (2 ^ 0 * Real.sqrt τ)).card := by positivity
  -- the volume ratio
  have hratio : 1 + ((clusterBall K' y (2 ^ n * Real.sqrt τ)).card : ℝ) /
      (clusterBall K' y (2 ^ 0 * Real.sqrt τ)).card ≤ Kv * 4 ^ n := by
    have hcardU : ((clusterBall K' y (2 ^ n * Real.sqrt τ)).card : ℝ) ≤ 25 * 4 ^ n * τ := by
      have h := card_clusterBall_le K' y (hsτ.trans hR1)
      have h4 : ((2 : ℝ) ^ n) ^ 2 = 4 ^ n := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      rw [mul_pow, h4, Real.sq_sqrt hτ0.le] at h
      linarith
    have h1 : ((clusterBall K' y (2 ^ n * Real.sqrt τ)).card : ℝ) /
        (clusterBall K' y (2 ^ 0 * Real.sqrt τ)).card ≤ 25 / cd * 4 ^ n := by
      rw [div_le_iff₀ hU0pos]
      calc ((clusterBall K' y (2 ^ n * Real.sqrt τ)).card : ℝ) ≤ 25 * 4 ^ n * τ := hcardU
        _ = 25 / cd * 4 ^ n * (cd * τ) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hvol (by positivity)
    have h4n : (1 : ℝ) ≤ 4 ^ n := one_le_pow₀ (by norm_num)
    rw [hKv]
    nlinarith
  have hsq := sqrt_div_sqrt_le (τ := τ) hs0 ht0 h23
  have hR1' : Real.sqrt τ ≤ CL * (2 ^ n * Real.sqrt τ) :=
    hR1.trans (le_mul_of_one_le_left (by positivity) hCL)
  by_cases hA : latticeDist x y ≤ s ∧ 4 * (CL * (2 ^ n * Real.sqrt τ)) ^ 2 ≤ s
  · -- Poincaré and Theorem 3
    have hO := approx_O_le hCP hCG hτ1 hs0 n (hP _ hR1 _) (hG _ hR1' hA.2 hA.1)
    have hinv := inv_mul_exp_le_dgPhi (C := CG) (C' := Cs) (r := latticeDist x y) hCG
      (le_max_left _ _) hs0 hA.1 hst h23
    have h := approx_real_A n hC₀ hCP hCG hKv0 hCs0 hτ0 hs0 ht0 he0.le (Real.exp_pos _).le hO0
      hV0 (dgPhi_annulusInner_le hC₀ hτ1 n) hO hratio hinv hsq
    refine h.trans ?_
    have : 0 ≤ (64 : ℝ) ^ n * Real.exp (-((2 : ℝ) ^ n / (4 * C₀))) *
        (Real.sqrt τ / Real.sqrt t) * dgPhi Cs t (latticeDist x y) := by
      have := dgPhi_nonneg hCs0.le ht0.le (latticeDist x y)
      positivity
    calc KA * (64 ^ n * Real.exp (-((2 : ℝ) ^ n / (4 * C₀)))) * (Real.sqrt τ / Real.sqrt t) *
          dgPhi Cs t (latticeDist x y)
        = KA * ((64 : ℝ) ^ n * Real.exp (-((2 : ℝ) ^ n / (4 * C₀))) *
          (Real.sqrt τ / Real.sqrt t) * dgPhi Cs t (latticeDist x y)) := by ring
      _ ≤ max KA (max K1 K2) * ((64 : ℝ) ^ n * Real.exp (-((2 : ℝ) ^ n / (4 * C₀))) *
          (Real.sqrt τ / Real.sqrt t) * dgPhi Cs t (latticeDist x y)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) this
      _ = _ := by ring
  · -- (eq:PhiCTrick) and (4.15)
    have hmid : dgPhi C₀ τ (annulusInner τ n) *
        ∑ z ∈ clusterBall K' y (2 ^ n * Real.sqrt τ), openHeat ω s x z ≤
        KB * Real.exp (-((2 : ℝ) ^ n / (4 * C₀))) * (Kc * dgPhi C₈ t (latticeDist x y)) := by
      rw [Finset.mul_sum]
      calc ∑ z ∈ clusterBall K' y (2 ^ n * Real.sqrt τ),
            dgPhi C₀ τ (annulusInner τ n) * openHeat ω s x z
          ≤ ∑ z ∈ clusterBall K' y (2 ^ n * Real.sqrt τ), openHeat ω s x z *
              (KB * Real.exp (-((2 : ℝ) ^ n / (4 * C₀))) * dgPhi (16 * C₀) τ (latticeDist z y)) := by
            refine Finset.sum_le_sum fun z hz => ?_
            rw [mul_comm]
            exact mul_le_mul_of_nonneg_left (dgPhi_annulusInner_le_mul_dgPhi hC₀ hτ1 n
              (latticeDist_nonneg z y) (mem_clusterBall.1 hz).2) (hg0 z)
        _ = KB * Real.exp (-((2 : ℝ) ^ n / (4 * C₀))) * ∑ z ∈ clusterBall K' y (2 ^ n * Real.sqrt τ),
              openHeat ω s x z * dgPhi (16 * C₀) τ (latticeDist z y) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun z _ => by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hconv _) (by positivity)
    have hbase := approx_real_base n hφ0 (Finset.sum_nonneg fun z _ => hg0 z) hV0 hKv0.le
      (sum_abs_sub_finAvg_le_two_mul hg0) hratio hmid
    have hΦ₈ := dgPhi_nonneg hC₈.le ht0.le (latticeDist x y)
    by_cases hnear : latticeDist x y ≤ s
    · -- the scales `4R² > s`
      have hRs : s < 4 * (CL * (2 ^ n * Real.sqrt τ)) ^ 2 := by
        by_contra h
        exact hA ⟨hnear, not_lt.1 h⟩
      have hone : 1 ≤ CL * (2 ^ (n + 1) * (Real.sqrt τ / Real.sqrt s)) := by
        have hss0 : 0 < Real.sqrt s := Real.sqrt_pos.2 hs0
        have h1 : Real.sqrt s < 2 * (CL * (2 ^ n * Real.sqrt τ)) := by
          have := Real.sqrt_lt_sqrt hs0.le hRs
          rwa [show (4 : ℝ) * (CL * (2 ^ n * Real.sqrt τ)) ^ 2 =
            (2 * (CL * (2 ^ n * Real.sqrt τ))) ^ 2 by ring, Real.sqrt_sq (by positivity)] at this
        rw [mul_div_assoc', mul_div_assoc', le_div_iff₀ hss0, one_mul, pow_succ]
        linarith
      have hΦC : dgPhi C₈ t (latticeDist x y) ≤ dgPhi Cs t (latticeDist x y) :=
        dgPhi_mono hC₈ ((by linarith : C₈ ≤ 2 * C₈).trans (le_max_right _ _)) ht0 hd0
      have h := approx_real_B1 n hCL0.le hKB0.le hKc.le hKv0.le he0.le hΦ₈ hbase hone hsq hΦC
      refine h.trans ?_
      have : 0 ≤ (64 : ℝ) ^ n * Real.exp (-((2 : ℝ) ^ n / (4 * C₀))) *
          (Real.sqrt τ / Real.sqrt t) * dgPhi Cs t (latticeDist x y) := by
        have := dgPhi_nonneg hCs0.le ht0.le (latticeDist x y)
        positivity
      calc 8 * CL * KB * Kc * Kv * (64 ^ n * Real.exp (-((2 : ℝ) ^ n / (4 * C₀)))) *
            (Real.sqrt τ / Real.sqrt t) * dgPhi Cs t (latticeDist x y)
          = K1 * ((64 : ℝ) ^ n * Real.exp (-((2 : ℝ) ^ n / (4 * C₀))) *
            (Real.sqrt τ / Real.sqrt t) * dgPhi Cs t (latticeDist x y)) := by rw [hK1]; ring
        _ ≤ max KA (max K1 K2) * ((64 : ℝ) ^ n * Real.exp (-((2 : ℝ) ^ n / (4 * C₀))) *
            (Real.sqrt τ / Real.sqrt t) * dgPhi Cs t (latticeDist x y)) :=
            mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) this
        _ = _ := by ring
    · -- far points: `|x - y| > s ≥ 2t/3`
      push Not at hnear
      have ht1 : 1 ≤ t := by linarith
      have hfar := dgPhi_le_rpow_mul_dgPhi hC₈ ht1 (show 2 * t / 3 ≤ latticeDist x y by linarith)
      have hinv : (Real.sqrt t)⁻¹ ≤ Real.sqrt τ / Real.sqrt t := by
        rw [inv_eq_one_div]
        exact div_le_div_of_nonneg_right hsτ hstt.le
      have hΦC : dgPhi (2 * C₈) t (latticeDist x y) ≤ dgPhi Cs t (latticeDist x y) :=
        dgPhi_mono (by positivity) (le_max_right _ _) ht0 hd0
      have h := approx_real_B2 n hKB0.le hKc.le hKv0.le he0.le hC₈.le
        (dgPhi_nonneg (by positivity) ht0.le _) hbase hfar hinv hΦC
      refine h.trans ?_
      have : 0 ≤ (64 : ℝ) ^ n * Real.exp (-((2 : ℝ) ^ n / (4 * C₀))) *
          (Real.sqrt τ / Real.sqrt t) * dgPhi Cs t (latticeDist x y) := by
        have := dgPhi_nonneg hCs0.le ht0.le (latticeDist x y)
        positivity
      calc 2 * KB * Kc * Kv * (9 * C₈ / 4) * (64 ^ n * Real.exp (-((2 : ℝ) ^ n / (4 * C₀)))) *
            (Real.sqrt τ / Real.sqrt t) * dgPhi Cs t (latticeDist x y)
          = K2 * ((64 : ℝ) ^ n * Real.exp (-((2 : ℝ) ^ n / (4 * C₀))) *
            (Real.sqrt τ / Real.sqrt t) * dgPhi Cs t (latticeDist x y)) := by rw [hK2]; ring
        _ ≤ max KA (max K1 K2) * ((64 : ℝ) ^ n * Real.exp (-((2 : ℝ) ^ n / (4 * C₀))) *
            (Real.sqrt τ / Real.sqrt t) * dgPhi Cs t (latticeDist x y)) :=
            mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _)) this
        _ = _ := by ring

end Rigidity.Green
