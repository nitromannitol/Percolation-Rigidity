import Rigidity.Proofs.Barlow.ExitTail

/-!
# The displacement tail of the planar heat kernel in a very good ball

`BarlowRegion ω K C_V C_P L x₀ R N ε` collects the hypotheses of Section 3 of Barlow
(*Random walks on supercritical percolation clusters*, Ann. Probab. 32 (2004)) on the ball
`B(x₀, R)`: every Euclidean ball of the component `K` with centre within `R` of `x₀` and radius
in `[N, R/18]` is good (Definition 1.7), and the heat kernel from points of `K` is at most `ε`
at distance `R/18` up to time `R` (the role of Lemma 1.1(b) of the source). Under these
hypotheses this file proves, for points of `K` near `x₀`:

* `BarlowRegion.heat_le`: `p_s(x₁, y) ≤ 2C/s` (Corollary 3.2);
* `BarlowRegion.meanDist_le_sqrt`: `M(x₁, t) ≤ K_M √t` (Proposition 3.4);
* `BarlowRegion.exitProb_le_oneBall`: `P^w(σ(w, r) ≤ n) ≤ 1/2 + a n` (Lemma 3.5);
* `BarlowRegion.tsum_far_le`: `P^x(|Y_t - x| ≥ ρ) ≤ (4/3) e^{-c ρ²/t} + e^{-t}` for the
  continuous time walk (Proposition 3.7 with the Poisson clock).
-/

open scoped Classical
open Finset LatticeProb.Percolation Rigidity.Green

namespace Rigidity.Barlow

variable {ω : Configuration 2}

/-- **Tonelli** for nonnegative double series over `ℕ × Vertex 2`. -/
theorem tsum_tsum_comm_of_nonneg {f : ℕ → Vertex 2 → ℝ} (h0 : ∀ n y, 0 ≤ f n y)
    (hrow : ∀ n, Summable (f n)) (hcol : ∀ y, Summable fun n => f n y)
    (hS : Summable fun n => ∑' y, f n y) :
    Summable (fun y => ∑' n, f n y) ∧ ∑' y, ∑' n, f n y = ∑' n, ∑' y, f n y := by
  have hL0 : ∀ y, 0 ≤ ∑' n, f n y := fun y => tsum_nonneg fun n => h0 n y
  have hR0 : ∀ n, 0 ≤ ∑' y, f n y := fun n => tsum_nonneg fun y => h0 n y
  have key : ∑' y, ENNReal.ofReal (∑' n, f n y) = ∑' n, ENNReal.ofReal (∑' y, f n y) := by
    have e1 : ∀ y, ENNReal.ofReal (∑' n, f n y) = ∑' n, ENNReal.ofReal (f n y) :=
      fun y => ENNReal.ofReal_tsum_of_nonneg (fun n => h0 n y) (hcol y)
    have e2 : ∀ n, ENNReal.ofReal (∑' y, f n y) = ∑' y, ENNReal.ofReal (f n y) :=
      fun n => ENNReal.ofReal_tsum_of_nonneg (fun y => h0 n y) (hrow n)
    simp_rw [e1, e2]
    exact ENNReal.tsum_comm
  have hfin : ∑' n, ENNReal.ofReal (∑' y, f n y) ≠ ⊤ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg hR0 hS]
    exact ENNReal.ofReal_ne_top
  have hsum : Summable fun y => ∑' n, f n y := by
    have := ENNReal.summable_toReal (f := fun y => ENNReal.ofReal (∑' n, f n y)) (by rw [key]; exact hfin)
    simpa [ENNReal.toReal_ofReal (hL0 _)] using this
  refine ⟨hsum, ?_⟩
  refine (ENNReal.ofReal_eq_ofReal_iff (tsum_nonneg hL0) (tsum_nonneg hR0)).1 ?_
  rw [ENNReal.ofReal_tsum_of_nonneg hL0 hsum, ENNReal.ofReal_tsum_of_nonneg hR0 hS]
  exact key

/-- `P^x(Y_t ≠ x) ≤ M(x, t)`. -/
theorem one_sub_openHeat_le_meanDist {t : ℝ} (ht : 0 ≤ t) (x : Vertex 2) :
    1 - openHeat ω t x x ≤ meanDist ω x t := by
  have hs := hasSum_openHeat ω ht x
  have hpt : ∀ y, openHeat ω t x y - (if y = x then openHeat ω t x x else 0) ≤
      latticeDist x y * openHeat ω t x y := by
    intro y
    by_cases hy : y = x
    · subst hy
      simp [latticeDist]
    · rw [if_neg hy, sub_zero]
      have h1 : 1 ≤ latticeDist x y := one_le_norm_edz (Ne.symm hy)
      nlinarith [openHeat_nonneg ω ht x y]
  have hite : Summable fun y => (if y = x then openHeat ω t x x else 0) :=
    summable_of_ne_finset_zero (s := {x}) fun y hy => by
      rw [Finset.mem_singleton] at hy
      rw [if_neg hy]
  have hle := Summable.tsum_le_tsum hpt (hs.summable.sub hite)
    (summable_latticeDist_mul_openHeat ht x)
  rw [hs.summable.tsum_sub hite, hs.tsum_eq, tsum_ite_eq] at hle
  exact hle

/-- `Σ_{n > ⌊8t⌋} Pois_{4t}(n) ≤ e^{-t}`. -/
theorem tsum_poissonWeight_tail_le {t : ℝ} (ht : 0 ≤ t) :
    Summable (fun n : ℕ => poissonWeight 4 t n * (if ⌊8 * t⌋₊ < n then 1 else 0)) ∧
      ∑' n : ℕ, poissonWeight 4 t n * (if ⌊8 * t⌋₊ < n then 1 else 0) ≤ Real.exp (-t) := by
  have hexp := hasSum_poissonWeight_mul_real_pow 4 t (Real.exp 1)
  have hpt : ∀ n : ℕ, poissonWeight 4 t n * (if ⌊8 * t⌋₊ < n then 1 else 0) ≤
      Real.exp (-8 * t) * (poissonWeight 4 t n * Real.exp 1 ^ n) := by
    intro n
    have hw := poissonWeight_nonneg (D := 4) ht n
    split_ifs with h
    · have hn : 8 * t ≤ n := by
        have := Nat.lt_floor_add_one (8 * t)
        have h' : ((⌊8 * t⌋₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast h
        push_cast at h'
        linarith
      have h1 : 1 ≤ Real.exp (-8 * t) * Real.exp 1 ^ n := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        exact Real.one_le_exp (by nlinarith)
      nlinarith
    · rw [mul_zero]
      positivity
  have hsumB := hexp.summable.mul_left (Real.exp (-8 * t))
  have hsum := hsumB.of_nonneg_of_le (fun n => mul_nonneg (poissonWeight_nonneg ht n)
    (by split_ifs <;> norm_num)) hpt
  refine ⟨hsum, ?_⟩
  have hle := Summable.tsum_le_tsum hpt hsum hsumB
  rw [tsum_mul_left, hexp.tsum_eq] at hle
  refine hle.trans ?_
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  have he := Real.exp_one_lt_d9
  push_cast
  nlinarith

/-- `P^x(|Y_t - x| ≥ ρ) ≤ P^x(σ(x, ρ) ≤ ⌊8t⌋) + e^{-t}`: the walk makes at most `8t` steps by time
`t` except with probability `e^{-t}`. -/
theorem tsum_far_openHeat_le {K : OpenComponent ω} {t : ℝ} (ht : 0 ≤ t) {x : Vertex 2}
    (ρ : ℝ) :
    ∑' y, (if ρ ≤ latticeDist x y then openHeat ω t x y else 0) ≤
      exitProb ω (clBall K x ρ) ⌊8 * t⌋₊ x + Real.exp (-t) := by
  have hdeg := openGraph_degree_le_four ω
  set f : ℕ → Vertex 2 → ℝ := fun n y =>
    poissonWeight 4 t n * (if ρ ≤ latticeDist x y then lazyPow (openGraph ω) 4 n x y else 0)
    with hf
  have hQ0 : ∀ n y, 0 ≤ lazyPow (openGraph ω) 4 n x y :=
    fun n y => (lazyPow_mem_Icc (by norm_num) hdeg n x y).1
  have h0 : ∀ n y, 0 ≤ f n y := fun n y => mul_nonneg (poissonWeight_nonneg ht n)
    (by split_ifs; exacts [hQ0 n y, le_rfl])
  have hite_le : ∀ n y, (if ρ ≤ latticeDist x y then lazyPow (openGraph ω) 4 n x y else 0) ≤
      lazyPow (openGraph ω) 4 n x y := fun n y => by split_ifs; exacts [le_rfl, hQ0 n y]
  have hrowS : ∀ n, Summable fun y =>
      (if ρ ≤ latticeDist x y then lazyPow (openGraph ω) 4 n x y else 0) := fun n =>
    (hasSum_lazyPow_of_degree_le (by norm_num) hdeg n x).summable.of_nonneg_of_le
      (fun y => by split_ifs; exacts [hQ0 n y, le_rfl]) (hite_le n)
  have hrow : ∀ n, Summable (f n) := fun n => (hrowS n).mul_left _
  have hcol : ∀ y, Summable fun n => f n y := fun y =>
    (summable_vsrwHeat (G := openGraph ω) (D := 4) (by norm_num) hdeg t x y).of_nonneg_of_le
      (fun n => h0 n y) (fun n => mul_le_mul_of_nonneg_left (hite_le n y)
        (poissonWeight_nonneg ht n))
  have hrowle : ∀ n, ∑' y, f n y ≤ poissonWeight 4 t n * exitProb ω (clBall K x ρ) n x := by
    intro n
    rw [tsum_mul_left]
    refine mul_le_mul_of_nonneg_left ?_ (poissonWeight_nonneg ht n)
    refine (Summable.tsum_le_tsum (fun y => ?_) (hrowS n) ?_).trans
      (tsum_notMem_lazyPow_le_exitProb (clBall K x ρ) n x)
    · by_cases hy : ρ ≤ latticeDist x y
      · rw [if_pos hy]
        have : y ∉ clBall K x ρ := fun hyA => by
          rw [mem_clBall, latticeDist_comm] at hyA
          linarith [hyA.2]
        rw [if_neg this]
      · rw [if_neg hy]
        split_ifs
        · exact le_rfl
        · exact hQ0 n y
    · exact (hasSum_lazyPow_of_degree_le (by norm_num) hdeg n x).summable.of_nonneg_of_le
        (fun y => by split_ifs; exacts [le_rfl, hQ0 n y])
        (fun y => by split_ifs; exacts [hQ0 n y, le_rfl])
  have hS : Summable fun n => ∑' y, f n y :=
    (hasSum_poissonWeight (D := 4) t).summable.of_nonneg_of_le (fun n => tsum_nonneg (h0 n))
      fun n => (hrowle n).trans (mul_le_of_le_one_right (poissonWeight_nonneg ht n)
        (exitProb_mem_Icc _ n x).2)
  obtain ⟨-, hcomm⟩ := tsum_tsum_comm_of_nonneg h0 hrow hcol hS
  have hL : ∀ y, (if ρ ≤ latticeDist x y then openHeat ω t x y else 0) = ∑' n, f n y := by
    intro y
    by_cases hy : ρ ≤ latticeDist x y
    · rw [if_pos hy, openHeat, vsrwHeat]
      exact tsum_congr fun n => by rw [hf]; simp only [if_pos hy]
    · rw [if_neg hy]
      symm
      refine (tsum_congr fun n => ?_).trans tsum_zero
      rw [hf]
      simp only [if_neg hy, mul_zero]
  rw [tsum_congr hL, hcomm]
  obtain ⟨hsT, hT⟩ := tsum_poissonWeight_tail_le ht
  set N' := ⌊8 * t⌋₊
  have hpt : ∀ n, ∑' y, f n y ≤ poissonWeight 4 t n * exitProb ω (clBall K x ρ) N' x +
      poissonWeight 4 t n * (if N' < n then 1 else 0) := by
    intro n
    refine (hrowle n).trans ?_
    rw [← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ (poissonWeight_nonneg ht n)
    split_ifs with h
    · linarith [(exitProb_mem_Icc (ω := ω) (clBall K x ρ) n x).2,
        (exitProb_mem_Icc (ω := ω) (clBall K x ρ) N' x).1]
    · rw [add_zero]
      exact exitProb_mono (not_lt.1 h) x
  have hle := Summable.tsum_le_tsum hpt hS
    (((hasSum_poissonWeight (D := 4) t).summable.mul_right _).add hsT)
  rw [((hasSum_poissonWeight (D := 4) t).summable.mul_right _).tsum_add hsT, tsum_mul_right,
    (hasSum_poissonWeight (D := 4) t).tsum_eq, one_mul] at hle
  linarith

/-! ### The hypotheses of Section 3 -/

/-- The hypotheses of Section 3 of Barlow 2004 on the ball `B(x₀, R)` of the component `K`. -/
structure BarlowRegion (ω : Configuration 2) (K : OpenComponent ω) (CV CP L : ℝ) (x0 : Vertex 2)
    (R N ε : ℝ) : Prop where
  hCV : 0 < CV
  hCP : 0 < CP
  hL : 1 ≤ L
  hN : 1 ≤ N
  hNR : N ≤ R / 18
  good : ∀ z, latticeDist z x0 ≤ R → ∀ r, N ≤ r → r ≤ R / 18 → IsGoodBall ω K CV CP L z r
  ε0 : 0 ≤ ε
  far : ∀ x ∈ K.supp, ∀ s, 0 ≤ s → s ≤ R → ∀ y, R / 18 ≤ latticeDist y x → openHeat ω s x y ≤ ε
  εN : ε * N ^ 2 * CV ^ 2 ≤ 25
  εR : 4 * ε * R ≤ 1

/-- `T₀ = C_P L² C_V N⁴`, the initial time of Proposition 3.1. -/
noncomputable def barlowT0 (CV CP L N : ℝ) : ℝ := CP * L ^ 2 * CV * N ^ 4

/-- `T₁ = max(1, 4T₀)`. -/
noncomputable def barlowT1 (CV CP L N : ℝ) : ℝ := max 1 (4 * barlowT0 CV CP L N)

/-- `T_M = max(T₁², 4C)`, from which on the mean displacement bound holds. -/
noncomputable def barlowTM (CV CP L N : ℝ) : ℝ :=
  max (barlowT1 CV CP L N ^ 2) (4 * diagConst CV CP L)

/-- The constant `K_M` of the mean displacement bound. -/
noncomputable def barlowKM (CV CP L : ℝ) : ℝ :=
  2 * (31 + Real.log (2 * diagConst CV CP L) + 2 * Real.log 4)

/-- `B₀ = (K_M/2 + 6) √2`. -/
noncomputable def barlowB0 (CV CP L : ℝ) : ℝ := (barlowKM CV CP L / 2 + 6) * Real.sqrt 2

/-- `n_* = ⌈4 T_M⌉`. -/
noncomputable def barlowNstar (CV CP L N : ℝ) : ℕ := ⌈4 * barlowTM CV CP L N⌉₊

/-- The smallest radius `r₁ = 4 B₀ √n_*` of Lemma 3.5. -/
noncomputable def barlowR1 (CV CP L N : ℝ) : ℝ :=
  4 * barlowB0 CV CP L * Real.sqrt (barlowNstar CV CP L N)

theorem barlowKM_nonneg (CV CP L : ℝ) : 0 ≤ barlowKM CV CP L := by
  unfold barlowKM
  have h1 : 0 ≤ Real.log (2 * diagConst CV CP L) :=
    Real.log_nonneg (by linarith [one_le_diagConst CV CP L])
  have h2 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  linarith

theorem barlowB0_pos (CV CP L : ℝ) : 0 < barlowB0 CV CP L := by
  unfold barlowB0
  have := barlowKM_nonneg CV CP L
  have : 0 < Real.sqrt 2 := by positivity
  positivity

theorem one_le_barlowT1 (CV CP L N : ℝ) : 1 ≤ barlowT1 CV CP L N := le_max_left _ _

theorem one_le_barlowNstar (CV CP L N : ℝ) : 1 ≤ barlowNstar CV CP L N := by
  unfold barlowNstar
  have h1 : 1 ≤ barlowTM CV CP L N :=
    (one_le_barlowT1 CV CP L N).trans ((le_self_pow₀ (one_le_barlowT1 CV CP L N)
      (by norm_num)).trans (le_max_left _ _))
  have : (1 : ℝ) ≤ ⌈4 * barlowTM CV CP L N⌉₊ :=
    (by linarith : (1 : ℝ) ≤ 4 * barlowTM CV CP L N).trans (Nat.le_ceil _)
  exact_mod_cast this

theorem four_mul_barlowB0_le_barlowR1 (CV CP L N : ℝ) :
    4 * barlowB0 CV CP L ≤ barlowR1 CV CP L N := by
  unfold barlowR1
  have h : 1 ≤ Real.sqrt (barlowNstar CV CP L N) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast one_le_barlowNstar CV CP L N)
  have := barlowB0_pos CV CP L
  nlinarith

namespace BarlowRegion

variable {K : OpenComponent ω} {CV CP L : ℝ} {x0 : Vertex 2} {R N ε : ℝ}

/-- **Corollary 3.2**: `p_s(x₁, y) ≤ 2C/s` for `4T₀ ≤ s ≤ R`, `|x₁ - x₀| ≤ 7R/9`. -/
theorem heat_le (h : BarlowRegion ω K CV CP L x0 R N ε) {x1 : Vertex 2} (hx1 : x1 ∈ K.supp)
    (hx10 : latticeDist x1 x0 ≤ 7 * R / 9) (y : Vertex 2) {s : ℝ}
    (hs : 4 * barlowT0 CV CP L N ≤ s) (hsR : s ≤ R) :
    openHeat ω s x1 y ≤ 2 * diagConst CV CP L / s := by
  have hT0 : 0 < barlowT0 CV CP L N := by
    unfold barlowT0
    have := h.hCP; have := h.hCV; have : 0 < N := by linarith [h.hN]
    have : 0 < L := by linarith [h.hL]
    positivity
  have hs0 : 0 < s := by linarith
  have hT : 2 * (CP * L ^ 2 * CV * N ^ 4) ≤ s / 2 := by
    unfold barlowT0 at hs
    linarith
  have h1 := openHeat_le_of_good h.hCV h.hCP h.hL h.hN h.hNR h.good hx1 hx10 h.ε0 h.far h.εN
    h.εR y hT (by linarith)
  have e : 2 * (s / 2) = s := by ring
  rw [e] at h1
  calc openHeat ω s x1 y ≤ diagConst CV CP L / (s / 2) := h1
    _ = 2 * diagConst CV CP L / s := by field_simp

/-- **Proposition 3.4**: `M(x₁, t) ≤ K_M √t` for `T_M ≤ t ≤ R`, `|x₁ - x₀| ≤ 7R/9`. -/
theorem meanDist_le_sqrt (h : BarlowRegion ω K CV CP L x0 R N ε) {x1 : Vertex 2}
    (hx1 : x1 ∈ K.supp) (hx10 : latticeDist x1 x0 ≤ 7 * R / 9) {t : ℝ}
    (ht : barlowTM CV CP L N ≤ t) (htR : t ≤ R) :
    meanDist ω x1 t ≤ barlowKM CV CP L * Real.sqrt t := by
  set D := diagConst CV CP L with hD
  have hD1 : 1 ≤ D := one_le_diagConst CV CP L
  have hT1 := one_le_barlowT1 CV CP L N
  have hT2 : barlowT1 CV CP L N ^ 2 ≤ t := (le_max_left _ _).trans ht
  have hT4 : 4 * barlowT0 CV CP L N ≤ barlowT1 CV CP L N := le_max_right _ _
  have hT1t : barlowT1 CV CP L N ≤ t :=
    (le_self_pow₀ hT1 (by norm_num)).trans hT2
  have ht0 : 0 < t := by linarith
  have h4D : 4 * D ≤ t := (le_max_right _ _).trans ht
  have key := meanDist_le_of_entropy (ω := ω) (x := x1) (c1 := -Real.log (2 * D)) hT1 hT2
    (fun s hs1 hs2 => by
      have hs0 : 0 < s := by linarith
      have hQ := neg_log_le_heatEntropy (ω := ω) (B := 2 * D / s) hs0 x1
        (fun y => h.heat_le hx1 hx10 y (hT4.trans hs1) (hs2.trans htR))
      rw [Real.log_div (by positivity) hs0.ne'] at hQ
      linarith)
    (by
      have h1 := one_sub_openHeat_le_meanDist (ω := ω) ht0.le x1
      have h2 := h.heat_le hx1 hx10 x1 (hT4.trans hT1t) htR
      have h3 : 2 * D / t ≤ 1 / 2 := by
        rw [div_le_iff₀ ht0]
        linarith
      linarith)
  calc meanDist ω x1 t ≤ 2 * (31 - -Real.log (2 * D) + 2 * Real.log 4) * Real.sqrt t := key
    _ = barlowKM CV CP L * Real.sqrt t := by unfold barlowKM; rw [← hD]; ring

/-- `E^z |X_k - z| ≤ (K_M/2 + 6) √k` for `4T_M ≤ k ≤ 4R`, `|z - x₀| ≤ 7R/9`. -/
theorem discMean_le_sqrt (h : BarlowRegion ω K CV CP L x0 R N ε) {z : Vertex 2}
    (hz : z ∈ K.supp) (hz0 : latticeDist z x0 ≤ 7 * R / 9) {k : ℕ}
    (hk : 4 * barlowTM CV CP L N ≤ k) (hkR : (k : ℝ) ≤ 4 * R) :
    discMean ω z k ≤ (barlowKM CV CP L / 2 + 6) * Real.sqrt k := by
  have hTM1 : 1 ≤ barlowTM CV CP L N :=
    (one_le_barlowT1 CV CP L N).trans ((le_self_pow₀ (one_le_barlowT1 CV CP L N)
      (by norm_num)).trans (le_max_left _ _))
  have hk1 : 1 ≤ k := by
    have : (1 : ℝ) ≤ k := by linarith
    exact_mod_cast this
  have h1 := discMean_le_meanDist_add (ω := ω) z hk1
  have h2 := h.meanDist_le_sqrt hz hz0 (t := (k : ℝ) / 4) (by linarith) (by linarith)
  have hsq : Real.sqrt ((k : ℝ) / 4) = Real.sqrt k / 2 := by
    rw [Real.sqrt_div (Nat.cast_nonneg _), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  rw [hsq] at h2
  linarith

/-- **Lemma 3.5**: `P^w(σ(w, r) ≤ n) ≤ 1/2 + (2B₀²/r²) n` for `n ≤ 2R`, `r₁ ≤ r ≤ R/9`,
`|w - x₀| ≤ 5R/9`. -/
theorem exitProb_le_oneBall (h : BarlowRegion ω K CV CP L x0 R N ε) (hR9 : 9 ≤ R)
    (hns : (barlowNstar CV CP L N : ℝ) ≤ 2 * R) {w : Vertex 2} (hw : w ∈ K.supp)
    (hw0 : latticeDist w x0 ≤ 5 * R / 9) {r : ℝ} (hr1 : barlowR1 CV CP L N ≤ r)
    (hrR : r ≤ R / 9) {n : ℕ} (hn : (n : ℝ) ≤ 2 * R) :
    exitProb ω (clBall K w r) n w ≤ 1 / 2 + (2 * barlowB0 CV CP L ^ 2 / r ^ 2) * n := by
  set B0 := barlowB0 CV CP L with hB0
  have hB0p : 0 < B0 := barlowB0_pos CV CP L
  have hr4 : 4 * B0 ≤ r := (four_mul_barlowB0_le_barlowR1 CV CP L N).trans hr1
  have hr0 : 0 < r := by linarith
  -- the bound `P ≤ 2 B₀ √n / r` for `n_* ≤ n ≤ 2R`
  have hbase : ∀ n : ℕ, (barlowNstar CV CP L N : ℝ) ≤ n → (n : ℝ) ≤ 2 * R →
      exitProb ω (clBall K w r) n w ≤ 2 * B0 * Real.sqrt n / r := by
    intro n hn1 hn2
    have h0 : (1 : ℝ) ≤ barlowNstar CV CP L N := by exact_mod_cast one_le_barlowNstar CV CP L N
    have hnpos : (1 : ℝ) ≤ n := h0.trans hn1
    set Mb := B0 * Real.sqrt n with hMb
    have hMbpos : 0 < Mb := by positivity
    have hMbd : ∀ z ∈ K.supp, latticeDist z w < r + 1 → ∀ k, n ≤ k → k ≤ 2 * n →
        discMean ω z k ≤ Mb := by
      intro z hz hzw k hk1 hk2
      have hz0 : latticeDist z x0 ≤ 7 * R / 9 := by
        have := latticeDist_triangle z w x0
        rw [latticeDist_comm w z] at this
        linarith
      have hk4 : 4 * barlowTM CV CP L N ≤ k := by
        have h1 : 4 * barlowTM CV CP L N ≤ barlowNstar CV CP L N := Nat.le_ceil _
        have h2 : (n : ℝ) ≤ k := by exact_mod_cast hk1
        linarith
      have hkR : (k : ℝ) ≤ 4 * R := by
        have : (k : ℝ) ≤ 2 * n := by exact_mod_cast hk2
        linarith
      refine (h.discMean_le_sqrt hz hz0 hk4 hkR).trans ?_
      rw [hMb, hB0, barlowB0, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (by linarith [barlowKM_nonneg CV CP L])
      rw [← Real.sqrt_mul (by norm_num)]
      exact Real.sqrt_le_sqrt (by
        have : (k : ℝ) ≤ 2 * n := by exact_mod_cast hk2
        linarith)
    have hP1 := (exitProb_mem_Icc (ω := ω) (clBall K w r) n w).2
    by_cases hM2 : 2 * Mb ≤ r
    · have hkey := exitProb_clBall_le hw hr0 hMbd
      have hw2 := hMbd w hw (by simp [latticeDist]; linarith) (2 * n) (by omega) le_rfl
      have hP0 := (exitProb_mem_Icc (ω := ω) (clBall K w r) n w).1
      rw [le_div_iff₀ hr0]
      nlinarith
    · have : 1 ≤ 2 * B0 * Real.sqrt n / r := by
        rw [le_div_iff₀ hr0]
        linarith
      linarith
  have ha0 : 0 ≤ 2 * B0 ^ 2 / r ^ 2 := by positivity
  by_cases hn1 : (barlowNstar CV CP L N : ℝ) ≤ n
  · have h1 := hbase n hn1 hn
    set x := 2 * B0 * Real.sqrt n / r with hx
    have hxsq : x ^ 2 / 2 = 2 * B0 ^ 2 / r ^ 2 * n := by
      rw [hx, div_pow, mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      field_simp
    nlinarith [sq_nonneg (x - 1)]
  · have hlt : barlowNstar CV CP L N ≤ n ∨ n < barlowNstar CV CP L N := le_or_gt _ _
    have hn' : n ≤ barlowNstar CV CP L N := by
      rcases hlt with h' | h'
      · exact absurd (by exact_mod_cast h' : (barlowNstar CV CP L N : ℝ) ≤ n) hn1
      · exact h'.le
    have h1 := exitProb_mono (ω := ω) (A := clBall K w r) hn' w
    have h2 := hbase (barlowNstar CV CP L N) le_rfl hns
    have h3 : 2 * B0 * Real.sqrt (barlowNstar CV CP L N) / r ≤ 1 / 2 := by
      rw [div_le_iff₀ hr0]
      have : barlowR1 CV CP L N = 4 * B0 * Real.sqrt (barlowNstar CV CP L N) := rfl
      linarith
    have h4 : 0 ≤ 2 * B0 ^ 2 / r ^ 2 * n := mul_nonneg ha0 (Nat.cast_nonneg _)
    linarith

end BarlowRegion

/-- The constant `κ = 512 B₀² / log(4/3) + 1` of Proposition 3.7. -/
noncomputable def barlowKappa (CV CP L : ℝ) : ℝ := 512 * barlowB0 CV CP L ^ 2 / Real.log (4 / 3) + 1

/-- The Gaussian constant `c₆ = log(4/3)/(4κ)` of Proposition 3.7. -/
noncomputable def barlowC6 (CV CP L : ℝ) : ℝ := Real.log (4 / 3) / (4 * barlowKappa CV CP L)

theorem one_le_barlowKappa (CV CP L : ℝ) : 1 ≤ barlowKappa CV CP L := by
  unfold barlowKappa
  have : 0 < Real.log (4 / 3) := Real.log_pos (by norm_num)
  have : 0 ≤ 512 * barlowB0 CV CP L ^ 2 / Real.log (4 / 3) := by positivity
  linarith

theorem barlowC6_pos (CV CP L : ℝ) : 0 < barlowC6 CV CP L := by
  unfold barlowC6
  have : 0 < Real.log (4 / 3) := Real.log_pos (by norm_num)
  have := one_le_barlowKappa CV CP L
  positivity

namespace BarlowRegion

variable {K : OpenComponent ω} {CV CP L : ℝ} {x0 : Vertex 2} {R N ε : ℝ}

/-- **Proposition 3.7** for the continuous time walk: `P^x(|Y_t - x| ≥ ρ) ≤ (4/3) e^{-c₆ ρ²/t} +
e^{-t}` for `κ ≤ ρ ≤ R/9`, `ρ r₁ ≤ κ t`, `1 ≤ t ≤ R/36`, `|x - x₀| ≤ R/3`. -/
theorem tsum_far_le (h : BarlowRegion ω K CV CP L x0 R N ε) (hR9 : 9 ≤ R)
    (hns : (barlowNstar CV CP L N : ℝ) ≤ 2 * R) {x : Vertex 2} (hx : x ∈ K.supp)
    (hx0 : latticeDist x x0 ≤ R / 3) {t ρ : ℝ} (ht1 : 1 ≤ t) (htR : t ≤ R / 36)
    (hκρ : barlowKappa CV CP L ≤ ρ) (hρr : ρ * barlowR1 CV CP L N ≤ barlowKappa CV CP L * t)
    (hρR : ρ ≤ R / 9) :
    ∑' y, (if ρ ≤ latticeDist x y then openHeat ω t x y else 0) ≤
      4 / 3 * Real.exp (-(barlowC6 CV CP L * ρ ^ 2 / t)) + Real.exp (-t) := by
  set κ := barlowKappa CV CP L with hκ
  set B0 := barlowB0 CV CP L with hB0
  set r1 := barlowR1 CV CP L N with hr1
  have hκ1 : 1 ≤ κ := one_le_barlowKappa CV CP L
  have hB0p : 0 < B0 := barlowB0_pos CV CP L
  have hr14 : 4 * B0 ≤ r1 := four_mul_barlowB0_le_barlowR1 CV CP L N
  have ht0 : 0 < t := by linarith
  have hρ0 : 0 < ρ := by linarith
  set r := κ * t / ρ with hr
  have hrr1 : r1 ≤ r := by
    rw [hr, le_div_iff₀ hρ0]
    linarith
  have hrt : r ≤ t := by
    rw [hr, div_le_iff₀ hρ0]
    nlinarith
  have hrR : r ≤ R / 9 := by linarith
  have hr0 : 0 < r := by positivity
  have hB01 : 1 ≤ B0 := by
    rw [hB0]
    unfold barlowB0
    have h1 : 1 ≤ Real.sqrt 2 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by norm_num)
    have := barlowKM_nonneg CV CP L
    nlinarith
  have hr1' : 1 ≤ r := by linarith
  set m := ⌊ρ / (r + 1)⌋₊ with hm
  have hmle : (m : ℝ) * (r + 1) ≤ ρ := by
    have := Nat.floor_le (by positivity : 0 ≤ ρ / (r + 1))
    rw [← hm] at this
    rwa [le_div_iff₀ (by linarith)] at this
  have hmge : ρ / (r + 1) - 1 < m := by
    have := Nat.lt_floor_add_one (ρ / (r + 1))
    rw [← hm] at this
    linarith
  set N' := ⌊8 * t⌋₊ with hN'
  have hN'le : (N' : ℝ) ≤ 8 * t := Nat.floor_le (by positivity)
  set a := 2 * B0 ^ 2 / r ^ 2 with ha
  have ha0 : 0 < a := by positivity
  have ha8 : a ≤ 1 / 8 := by
    rw [ha, div_le_iff₀ (by positivity)]
    nlinarith
  have hdisc := exitProb_clBall_le_exp (ω := ω) (K := K) (x0 := x0) (x := x) (D := 5 * R / 9)
    (r := r) (a := a) (N := N') (m := m) hr0 ha0 ha8
    (fun z hz hz0 k hk => h.exitProb_le_oneBall hR9 hns hz hz0 hrr1 hrR (n := k) (by
      have : (k : ℝ) ≤ N' := by exact_mod_cast hk
      linarith)) hx (by linarith)
  have hanti := exitProb_anti (ω := ω) (A := clBall K x ρ) (A' := clBall K x (m * (r + 1)))
    (fun w hw => ⟨hw.1, lt_of_lt_of_le hw.2 hmle⟩) N' x
  have hfar := tsum_far_openHeat_le (ω := ω) (K := K) ht0.le (x := x) ρ
  -- the exponent
  set Λ4 := Real.log (4 / 3) with hΛ4
  have hΛ0 : 0 < Λ4 := Real.log_pos (by norm_num)
  have h34 : ((3 : ℝ) / 4) ^ m = Real.exp (-(m * Λ4)) := by
    have e : (3 : ℝ) / 4 = Real.exp (-Λ4) := by
      rw [Real.exp_neg, hΛ4, Real.exp_log (by norm_num)]
      norm_num
    rw [e, ← Real.exp_nat_mul]
    ring_nf
  have hX : ρ ^ 2 / (2 * κ * t) - 1 < m := by
    have h1 : ρ ^ 2 / (2 * κ * t) ≤ ρ / (r + 1) := by
      rw [div_le_div_iff₀ (by positivity) (by linarith), hr]
      have : ρ * (κ * t / ρ + 1) ≤ ρ * (2 * (κ * t / ρ)) := by
        apply mul_le_mul_of_nonneg_left _ hρ0.le
        linarith [hr1', hr]
      have e : ρ * (2 * (κ * t / ρ)) = 2 * κ * t := by field_simp
      nlinarith
    linarith
  have h8a : 8 * a * N' ≤ 128 * B0 ^ 2 * ρ ^ 2 / (κ ^ 2 * t) := by
    have e : 128 * B0 ^ 2 * ρ ^ 2 / (κ ^ 2 * t) = 8 * a * (8 * t) := by
      rw [ha, hr]
      field_simp
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_left hN'le (by positivity)
  have hκb : 128 * B0 ^ 2 / κ ^ 2 ≤ Λ4 / (4 * κ) := by
    have hk : 512 * B0 ^ 2 ≤ Λ4 * κ := by
      have e : κ = 512 * B0 ^ 2 / Λ4 + 1 := rfl
      rw [e, mul_add, mul_div_cancel₀ _ hΛ0.ne']
      linarith
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hexp : Real.exp (8 * a * N') * ((3 : ℝ) / 4) ^ m ≤
      4 / 3 * Real.exp (-(barlowC6 CV CP L * ρ ^ 2 / t)) := by
    rw [h34, ← Real.exp_add]
    have e43 : (4 : ℝ) / 3 = Real.exp Λ4 := by rw [hΛ4, Real.exp_log (by norm_num)]
    rw [e43, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have hc6 : barlowC6 CV CP L = Λ4 / (4 * κ) := rfl
    rw [hc6]
    have h1 : -(m * Λ4) ≤ -((ρ ^ 2 / (2 * κ * t) - 1) * Λ4) := by
      apply neg_le_neg
      exact mul_le_mul_of_nonneg_right hX.le hΛ0.le
    have h2 : 128 * B0 ^ 2 * ρ ^ 2 / (κ ^ 2 * t) ≤ Λ4 / (4 * κ) * ρ ^ 2 / t := by
      have e : 128 * B0 ^ 2 * ρ ^ 2 / (κ ^ 2 * t) = 128 * B0 ^ 2 / κ ^ 2 * (ρ ^ 2 / t) := by
        field_simp
      have e' : Λ4 / (4 * κ) * ρ ^ 2 / t = Λ4 / (4 * κ) * (ρ ^ 2 / t) := by ring
      rw [e, e']
      exact mul_le_mul_of_nonneg_right hκb (by positivity)
    have e2 : (ρ ^ 2 / (2 * κ * t) - 1) * Λ4 = 2 * (Λ4 / (4 * κ) * ρ ^ 2 / t) - Λ4 := by
      field_simp
      ring
    rw [e2] at h1
    have e3 : Λ4 / (4 * κ) * ρ ^ 2 / t = Λ4 / (4 * κ) * ρ ^ 2 / t := rfl
    linarith
  calc ∑' y, (if ρ ≤ latticeDist x y then openHeat ω t x y else 0)
      ≤ exitProb ω (clBall K x ρ) N' x + Real.exp (-t) := hfar
    _ ≤ Real.exp (8 * a * N') * (3 / 4) ^ m + Real.exp (-t) := by linarith
    _ ≤ _ := by linarith

end BarlowRegion

end Rigidity.Barlow
