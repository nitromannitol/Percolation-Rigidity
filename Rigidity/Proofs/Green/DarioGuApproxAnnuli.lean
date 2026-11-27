import Rigidity.Proofs.Green.DarioGuApproxInputs
import Rigidity.Proofs.Green.DarioGuApproxPhi

/-!
# The dyadic annuli of the proof of Lemma 4.1 of Dario–Gu

Steps 2 and 3 of the proof of Lemma 4.1 (lines 2029-2148 of the source). For the balls
`U_n = 𝒞 ∩ B_{2^n √τ}(y)` and `g = p(s, x, ·)`, `s = t - τ`:

* `sum_abs_mul_abs_sub_finAvg_le`: if `|w| ≤ a_n` on `U_n \ U_{n-1}`, then
  `Σ_z |w(z)| |g(z) - (g)_{U_0}| ≤ Σ_n a_n O_n (1 + |U_n|/|U_0|)`, `O_n = Σ_{U_n} |g - (g)_{U_n}|`
  ((4.11): the average on `U_0` is replaced by the average on `U_n` at the cost of
  `|U_n| O_n / |U_0|`, the term (4.11)-b).
* `dgPhi_annulusInner_le`, `dgPhi_annulusInner_le_mul_dgPhi`: the bounds on `a_n = Φ_{C₀}(τ, ρ_n)`,
  `ρ_0 = 0`, `ρ_n = 2^{n-1} √τ`, used with Theorem 3 and with (4.12) respectively.
* `approx_O_le`: `O_n ≤ 25 C_P C_G 8^n τ^{3/2} s^{-3/2} e^{-|x - y|²/(C_G s)}` from the Poincaré
  inequality and the gradient bound ((4.9), (4.10), (4.13)); `approx_real_A`, `approx_real_B1`: the
  arithmetic of the scales.
-/

open Finset LatticeProb.Percolation Rigidity.External

namespace Rigidity.Green

/-- `|(g)_V - c| ≤ |V|^{-1} Σ_V |g - c|`. -/
theorem abs_finAvg_sub_le {V : Finset (Vertex 2)} (hV : V.Nonempty) (g : Vertex 2 → ℝ) (c : ℝ) :
    |finAvg V g - c| ≤ (∑ z ∈ V, |g z - c|) / V.card := by
  have hc : (0 : ℝ) < V.card := by exact_mod_cast hV.card_pos
  have e : finAvg V g - c = (∑ z ∈ V, (g z - c)) / V.card := by
    rw [finAvg, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    field_simp
  rw [e, abs_div, abs_of_pos hc]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hc.le

/-- **The annuli (4.11).** -/
theorem sum_abs_mul_abs_sub_finAvg_le {U : ℕ → Finset (Vertex 2)} (hmono : Monotone U)
    (hU0 : (U 0).Nonempty) (w g : Vertex 2 → ℝ) (a : ℕ → ℝ) (ha0 : ∀ n, 0 ≤ a n)
    (ha : ∀ n z, z ∈ U n → (∀ m < n, z ∉ U m) → |w z| ≤ a n) {B : ℝ}
    (hB : ∀ N, ∑ n ∈ range N, a n * ((∑ z ∈ U n, |g z - finAvg (U n) g|) *
      (1 + (U n).card / (U 0).card)) ≤ B)
    (S : Finset (Vertex 2)) (hS : ∀ z ∈ S, ∃ n, z ∈ U n) :
    ∑ z ∈ S, |w z| * |g z - finAvg (U 0) g| ≤ B := by
  classical
  set idx : Vertex 2 → ℕ := fun z => if h : ∃ n, z ∈ U n then Nat.find h else 0 with hidx
  have hspec : ∀ z ∈ S, z ∈ U (idx z) ∧ ∀ m < idx z, z ∉ U m := by
    intro z hz
    have h := hS z hz
    simp only [hidx, dif_pos h]
    exact ⟨Nat.find_spec h, fun m hm => Nat.find_min h hm⟩
  set N := S.sup idx + 1 with hN
  have hmaps : ∀ z ∈ S, idx z ∈ range N := fun z hz =>
    Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := idx) hz))
  have hc0 : (0 : ℝ) < (U 0).card := by exact_mod_cast hU0.card_pos
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine le_trans (Finset.sum_le_sum fun n _ => ?_) (hB N)
  set F := S.filter fun z => idx z = n with hF
  have hFU : F ⊆ U n := by
    intro z hz
    rw [hF, Finset.mem_filter] at hz
    rw [← hz.2]
    exact (hspec z hz.1).1
  set O := ∑ z ∈ U n, |g z - finAvg (U n) g| with hO
  have hO0 : 0 ≤ O := Finset.sum_nonneg fun z _ => abs_nonneg _
  have hcn : |finAvg (U n) g - finAvg (U 0) g| ≤ O / (U 0).card := by
    rw [abs_sub_comm]
    refine (abs_finAvg_sub_le hU0 g _).trans (div_le_div_of_nonneg_right ?_ hc0.le)
    exact Finset.sum_le_sum_of_subset_of_nonneg (hmono (Nat.zero_le n)) fun z _ _ => abs_nonneg _
  have hpt : ∀ z ∈ F, |w z| * |g z - finAvg (U 0) g| ≤
      a n * (|g z - finAvg (U n) g| + O / (U 0).card) := by
    intro z hz
    have hz' := Finset.mem_filter.1 hz
    have hw : |w z| ≤ a n := by
      have := hspec z hz'.1
      rw [hz'.2] at this
      exact ha n z this.1 this.2
    have htri : |g z - finAvg (U 0) g| ≤ |g z - finAvg (U n) g| + O / (U 0).card := by
      calc |g z - finAvg (U 0) g|
          = |(g z - finAvg (U n) g) + (finAvg (U n) g - finAvg (U 0) g)| := by ring_nf
        _ ≤ |g z - finAvg (U n) g| + |finAvg (U n) g - finAvg (U 0) g| := abs_add_le _ _
        _ ≤ _ := by linarith
    exact mul_le_mul hw htri (abs_nonneg _) (ha0 n)
  calc ∑ z ∈ F, |w z| * |g z - finAvg (U 0) g|
      ≤ ∑ z ∈ F, a n * (|g z - finAvg (U n) g| + O / (U 0).card) := Finset.sum_le_sum hpt
    _ = a n * (∑ z ∈ F, |g z - finAvg (U n) g| + F.card * (O / (U 0).card)) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    _ ≤ a n * (O + (U n).card * (O / (U 0).card)) := by
        apply mul_le_mul_of_nonneg_left _ (ha0 n)
        apply add_le_add
        · exact Finset.sum_le_sum_of_subset_of_nonneg hFU fun z _ _ => abs_nonneg _
        · apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast Finset.card_le_card hFU
    _ = a n * (O * (1 + (U n).card / (U 0).card)) := by ring

/-- The inner radius `ρ_n` of the `n`-th annulus: `ρ_0 = 0`, `ρ_n = 2^{n-1} √τ`. -/
noncomputable def annulusInner (τ : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else 2 ^ (n - 1) * Real.sqrt τ

theorem annulusInner_nonneg (τ : ℝ) (n : ℕ) : 0 ≤ annulusInner τ n := by
  unfold annulusInner
  split_ifs <;> positivity

/-- `Φ_{C₀}(τ, ρ_n) ≤ C₀ e^{1/C₀} τ^{-1} e^{-2^n/(4C₀)}`. -/
theorem dgPhi_annulusInner_le {C₀ τ : ℝ} (hC₀ : 0 < C₀) (hτ : 1 ≤ τ) (n : ℕ) :
    dgPhi C₀ τ (annulusInner τ n) ≤
      C₀ * Real.exp (1 / C₀) * τ⁻¹ * Real.exp (-((2 : ℝ) ^ n / (4 * C₀))) := by
  have hτ0 : 0 < τ := by linarith
  rw [dgPhi_eq]
  have key : Real.exp (-(dgShape τ (annulusInner τ n) / C₀)) ≤
      Real.exp (1 / C₀) * Real.exp (-((2 : ℝ) ^ n / (4 * C₀))) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    unfold annulusInner
    split_ifs with hn
    · subst hn
      have : dgShape τ 0 = 0 := by unfold dgShape; rw [if_pos hτ0.le]; simp
      rw [this]
      have : (2 : ℝ) ^ 0 / (4 * C₀) ≤ 1 / C₀ := by
        rw [pow_zero, div_le_div_iff₀ (by positivity) hC₀]
        linarith
      rw [zero_div, neg_zero]
      linarith [show (0 : ℝ) ≤ 1 / C₀ by positivity]
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      have hg := two_pow_le_dgShape hτ m
      simp only [Nat.succ_sub_one] at hg ⊢
      have e : (2 : ℝ) ^ (m + 1) / (4 * C₀) = 2 ^ m / C₀ / 2 := by
        rw [pow_succ]
        field_simp
        ring
      rw [e]
      have h1 : 2 ^ m / C₀ ≤ dgShape τ (2 ^ m * Real.sqrt τ) / C₀ :=
        div_le_div_of_nonneg_right hg hC₀.le
      have h2 : (0 : ℝ) ≤ 2 ^ m / C₀ := by positivity
      linarith [show (0 : ℝ) ≤ 1 / C₀ by positivity]
  calc C₀ * τ⁻¹ * Real.exp (-(dgShape τ (annulusInner τ n) / C₀))
      ≤ C₀ * τ⁻¹ * (Real.exp (1 / C₀) * Real.exp (-((2 : ℝ) ^ n / (4 * C₀)))) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = _ := by ring

/-- `Φ_{C₀}(τ, ρ_n) ≤ K_B e^{-2^n/(4C₀)} Φ_{16C₀}(τ, r)` for `r < 2^n √τ`,
`K_B = e^{1/(16C₀) + 1/(4C₀)}/16`. -/
theorem dgPhi_annulusInner_le_mul_dgPhi {C₀ τ r : ℝ} (hC₀ : 0 < C₀) (hτ : 1 ≤ τ) (n : ℕ)
    (hr0 : 0 ≤ r) (hr : r < 2 ^ n * Real.sqrt τ) :
    dgPhi C₀ τ (annulusInner τ n) ≤
      Real.exp (1 / (16 * C₀) + 1 / (4 * C₀)) / 16 * Real.exp (-((2 : ℝ) ^ n / (4 * C₀))) *
        dgPhi (16 * C₀) τ r := by
  have hτ0 : 0 < τ := by linarith
  have hst : 0 < Real.sqrt τ := Real.sqrt_pos.2 hτ0
  have hΦ0 := dgPhi_nonneg (by positivity : (0 : ℝ) ≤ 16 * C₀) hτ0.le r
  unfold annulusInner
  split_ifs with hn
  · subst hn
    rw [dgPhi_zero_eq hτ0, dgPhi_eq]
    have hg : dgShape τ r ≤ 1 := by
      have h1 := dgShape_le_sq hτ0 hr0
      have h2 : r ^ 2 < τ := by
        rw [pow_zero, one_mul] at hr
        have := mul_self_lt_mul_self hr0 hr
        rw [Real.mul_self_sqrt hτ0.le] at this
        nlinarith
      have : r ^ 2 / τ ≤ 1 := by rw [div_le_one hτ0]; exact h2.le
      linarith
    have he : Real.exp (-(1 / (16 * C₀))) ≤ Real.exp (-(dgShape τ r / (16 * C₀))) := by
      apply Real.exp_le_exp.2
      rw [neg_le_neg_iff]
      exact div_le_div_of_nonneg_right hg (by positivity)
    have hprod : Real.exp (1 / (16 * C₀) + 1 / (4 * C₀)) * Real.exp (-((2 : ℝ) ^ 0 / (4 * C₀))) *
        Real.exp (-(1 / (16 * C₀))) = 1 := by
      rw [← Real.exp_add, ← Real.exp_add, pow_zero]
      convert Real.exp_zero using 2
      ring
    calc C₀ * τ⁻¹ = Real.exp (1 / (16 * C₀) + 1 / (4 * C₀)) / 16 *
          Real.exp (-((2 : ℝ) ^ 0 / (4 * C₀))) * (16 * C₀ * τ⁻¹ * Real.exp (-(1 / (16 * C₀)))) := by
          have : Real.exp (1 / (16 * C₀) + 1 / (4 * C₀)) / 16 * Real.exp (-((2 : ℝ) ^ 0 / (4 * C₀))) *
              (16 * C₀ * τ⁻¹ * Real.exp (-(1 / (16 * C₀)))) =
              (Real.exp (1 / (16 * C₀) + 1 / (4 * C₀)) * Real.exp (-((2 : ℝ) ^ 0 / (4 * C₀))) *
                Real.exp (-(1 / (16 * C₀)))) * (C₀ * τ⁻¹) := by ring
          rw [this, hprod, one_mul]
      _ ≤ _ := by gcongr
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    simp only [Nat.succ_sub_one]
    have hρ : r ≤ 2 * (2 ^ m * Real.sqrt τ) := by
      rw [pow_succ] at hr
      linarith
    have h1 := dgPhi_le_mul_dgPhi hC₀ hτ0 hr0 hρ
    have hg := two_pow_le_dgShape hτ m
    have he : Real.exp (-(dgShape τ (2 ^ m * Real.sqrt τ) / (2 * C₀))) ≤
        Real.exp (1 / (16 * C₀) + 1 / (4 * C₀)) * Real.exp (-((2 : ℝ) ^ (m + 1) / (4 * C₀))) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      have e : (2 : ℝ) ^ (m + 1) / (4 * C₀) = 2 ^ m / (2 * C₀) := by
        rw [pow_succ]
        field_simp
        ring
      rw [e]
      have h2 : 2 ^ m / (2 * C₀) ≤ dgShape τ (2 ^ m * Real.sqrt τ) / (2 * C₀) :=
        div_le_div_of_nonneg_right hg (by positivity)
      have h3 : (0 : ℝ) ≤ 1 / (16 * C₀) + 1 / (4 * C₀) := by positivity
      linarith
    calc dgPhi C₀ τ (2 ^ m * Real.sqrt τ)
        ≤ Real.exp (-(dgShape τ (2 ^ m * Real.sqrt τ) / (2 * C₀))) * dgPhi (16 * C₀) τ r / 16 := h1
      _ ≤ Real.exp (1 / (16 * C₀) + 1 / (4 * C₀)) * Real.exp (-((2 : ℝ) ^ (m + 1) / (4 * C₀))) *
            dgPhi (16 * C₀) τ r / 16 := by gcongr
      _ = _ := by ring

theorem rpow_neg_three_halves {s : ℝ} (hs : 0 < s) : s ^ (-(3 / 2 : ℝ)) = (s * Real.sqrt s)⁻¹ := by
  rw [Real.rpow_neg hs.le, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hs, Real.rpow_one,
    ← Real.sqrt_eq_rpow]

theorem sqrt_div_sqrt_le {τ s t : ℝ} (hs : 0 < s) (ht : 0 < t) (h : 2 * t ≤ 3 * s) :
    Real.sqrt τ / Real.sqrt s ≤ 2 * (Real.sqrt τ / Real.sqrt t) := by
  have hss : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have h1 : Real.sqrt t ≤ 2 * Real.sqrt s := by
    have : Real.sqrt t ≤ Real.sqrt (4 * s) := Real.sqrt_le_sqrt (by linarith)
    rwa [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at this
  rw [div_le_iff₀ hss, mul_comm, ← mul_assoc, ← mul_div_assoc, le_div_iff₀ hst]
  have := Real.sqrt_nonneg τ
  nlinarith

/-- `O = Σ_U |g - (g)_U| ≤ 2 Σ_U g` for `g ≥ 0`. -/
theorem sum_abs_sub_finAvg_le_two_mul {U : Finset (Vertex 2)} {g : Vertex 2 → ℝ}
    (hg : ∀ z, 0 ≤ g z) : ∑ z ∈ U, |g z - finAvg U g| ≤ 2 * ∑ z ∈ U, g z := by
  rcases U.eq_empty_or_nonempty with rfl | hne
  · simp
  have hc : (0 : ℝ) < U.card := by exact_mod_cast hne.card_pos
  have havg : 0 ≤ finAvg U g := div_nonneg (Finset.sum_nonneg fun z _ => hg z) hc.le
  have hsum : ∑ _z ∈ U, finAvg U g = ∑ z ∈ U, g z := by
    rw [Finset.sum_const, nsmul_eq_mul, finAvg]
    field_simp
  calc ∑ z ∈ U, |g z - finAvg U g| ≤ ∑ z ∈ U, (g z + finAvg U g) := by
        refine Finset.sum_le_sum fun z _ => ?_
        rw [abs_le]
        constructor <;> linarith [hg z]
    _ = 2 * ∑ z ∈ U, g z := by rw [Finset.sum_add_distrib, hsum]; ring

/-- The arithmetic of the scales of Theorem 3 in the proof of Lemma 4.1. -/
theorem approx_real_A {C₀ CP CG Kv Cs τ s t e E φ O V Φ : ℝ} (n : ℕ) (hC₀ : 0 < C₀)
    (hCP : 0 < CP) (hCG : 0 < CG) (hKv : 0 < Kv) (hCs : 0 < Cs) (hτ : 0 < τ) (hs : 0 < s)
    (ht : 0 < t) (he : 0 ≤ e) (hE : 0 ≤ E) (hO0 : 0 ≤ O) (hV0 : 0 ≤ V)
    (hφ : φ ≤ C₀ * Real.exp (1 / C₀) * τ⁻¹ * e)
    (hO : O ≤ 25 * CP * CG * (8 ^ n * τ * Real.sqrt τ) * ((s * Real.sqrt s)⁻¹ * E))
    (hV : V ≤ Kv * 4 ^ n) (hinv : s⁻¹ * E ≤ 3 / (2 * Cs) * Φ)
    (hsq : Real.sqrt τ / Real.sqrt s ≤ 2 * (Real.sqrt τ / Real.sqrt t)) :
    φ * (O * V) ≤ 25 * C₀ * Real.exp (1 / C₀) * CP * CG * Kv * 2 * (3 / (2 * Cs)) *
      (64 ^ n * e) * (Real.sqrt τ / Real.sqrt t) * Φ := by
  have hss : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hsτ : 0 ≤ Real.sqrt τ := Real.sqrt_nonneg τ
  have hΦ : 0 ≤ Φ := by
    have : 0 ≤ s⁻¹ * E := by positivity
    have h2 : 0 < 3 / (2 * Cs) := by positivity
    nlinarith
  have hsτt : 0 ≤ Real.sqrt τ / Real.sqrt t := by positivity
  have h1 : φ * (O * V) ≤ (C₀ * Real.exp (1 / C₀) * τ⁻¹ * e) *
      ((25 * CP * CG * (8 ^ n * τ * Real.sqrt τ) * ((s * Real.sqrt s)⁻¹ * E)) * (Kv * 4 ^ n)) :=
    mul_le_mul hφ (mul_le_mul hO hV hV0 (by positivity)) (by positivity) (by positivity)
  have h2 : (C₀ * Real.exp (1 / C₀) * τ⁻¹ * e) *
      ((25 * CP * CG * (8 ^ n * τ * Real.sqrt τ) * ((s * Real.sqrt s)⁻¹ * E)) * (Kv * 4 ^ n)) =
      25 * C₀ * Real.exp (1 / C₀) * CP * CG * Kv * ((8 : ℝ) ^ n * 4 ^ n) * e *
        (Real.sqrt τ / Real.sqrt s) * (s⁻¹ * E) := by
    field_simp
  have h3 : (8 : ℝ) ^ n * 4 ^ n = 32 ^ n := by rw [← mul_pow]; norm_num
  have h4 : (32 : ℝ) ^ n ≤ 64 ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
  rw [h2, h3] at h1
  refine h1.trans ?_
  have hK : 0 ≤ 25 * C₀ * Real.exp (1 / C₀) * CP * CG * Kv := by positivity
  calc 25 * C₀ * Real.exp (1 / C₀) * CP * CG * Kv * (32 : ℝ) ^ n * e *
        (Real.sqrt τ / Real.sqrt s) * (s⁻¹ * E)
      ≤ 25 * C₀ * Real.exp (1 / C₀) * CP * CG * Kv * (64 : ℝ) ^ n * e *
        (2 * (Real.sqrt τ / Real.sqrt t)) * (3 / (2 * Cs) * Φ) := by
        gcongr
    _ = _ := by ring

/-- The arithmetic of the other scales (`4 (A R)² > s`) in the proof of Lemma 4.1. -/
theorem approx_real_B1 {A KB Kc Kv τ s t e Φ₈ Φ x : ℝ} (n : ℕ) (hA : 0 ≤ A) (hKB : 0 ≤ KB)
    (hKc : 0 ≤ Kc) (hKv : 0 ≤ Kv) (he : 0 ≤ e) (hΦ₈ : 0 ≤ Φ₈)
    (hx : x ≤ 2 * KB * Kc * Kv * (4 ^ n * e) * Φ₈)
    (hone : 1 ≤ A * (2 ^ (n + 1) * (Real.sqrt τ / Real.sqrt s)))
    (hsq : Real.sqrt τ / Real.sqrt s ≤ 2 * (Real.sqrt τ / Real.sqrt t)) (hΦ : Φ₈ ≤ Φ) :
    x ≤ 8 * A * KB * Kc * Kv * (64 ^ n * e) * (Real.sqrt τ / Real.sqrt t) * Φ := by
  have hK : 0 ≤ 2 * KB * Kc * Kv * (4 ^ n * e) := by positivity
  have hsτs : 0 ≤ Real.sqrt τ / Real.sqrt s := div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have h1 : x ≤ 2 * KB * Kc * Kv * (4 ^ n * e) * Φ₈ *
      (A * (2 ^ (n + 1) * (Real.sqrt τ / Real.sqrt s))) :=
    hx.trans (le_mul_of_one_le_right (by positivity) hone)
  have h8 : (4 : ℝ) ^ n * 2 ^ n ≤ 64 ^ n := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) n
  have hΦ0 : 0 ≤ Φ := hΦ₈.trans hΦ
  refine h1.trans ?_
  calc 2 * KB * Kc * Kv * (4 ^ n * e) * Φ₈ * (A * (2 ^ (n + 1) * (Real.sqrt τ / Real.sqrt s)))
      ≤ 2 * KB * Kc * Kv * (4 ^ n * e) * Φ *
          (A * (2 ^ (n + 1) * (2 * (Real.sqrt τ / Real.sqrt t)))) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hΦ hK)
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq (by positivity)) hA)
          (by positivity) (mul_nonneg hK hΦ0)
    _ = 8 * A * KB * Kc * Kv * ((4 : ℝ) ^ n * 2 ^ n * e) * (Real.sqrt τ / Real.sqrt t) * Φ := by
        rw [pow_succ]; ring
    _ ≤ 8 * A * KB * Kc * Kv * (64 ^ n * e) * (Real.sqrt τ / Real.sqrt t) * Φ := by
        have : 0 ≤ (Real.sqrt τ / Real.sqrt t) * Φ := by
          have := Real.sqrt_nonneg τ
          have := Real.sqrt_nonneg t
          positivity
        have h8e : (4 : ℝ) ^ n * 2 ^ n * e ≤ 64 ^ n * e := mul_le_mul_of_nonneg_right h8 he
        nlinarith [mul_le_mul_of_nonneg_left h8e (by positivity : (0 : ℝ) ≤ 8 * A * KB * Kc * Kv)]

/-- `O ≤ 25 C_P C_G 8^n τ^{3/2} s^{-3/2} e^{-|x - y|²/(C_G s)}` at the scales of Theorem 3, from
the weak Poincaré inequality on `B_R(y)`, `R = 2^n √τ`, and the gradient bound on `B_{L R}(y)`. -/
theorem approx_O_le {ω : Configuration 2} {K' : OpenComponent ω} {x y : Vertex 2}
    {s τ CP CL CG : ℝ}
    (hCP : 0 < CP) (hCG : 0 < CG) (hτ1 : 1 ≤ τ) (hs : 0 < s) (n : ℕ)
    (hP : Real.sqrt ((∑ z ∈ clusterBall K' y (2 ^ n * Real.sqrt τ),
        (openHeat ω s x z - finAvg (clusterBall K' y (2 ^ n * Real.sqrt τ))
          (fun z => openHeat ω s x z)) ^ 2) / (clusterBall K' y (2 ^ n * Real.sqrt τ)).card) ≤
      CP * (2 ^ n * Real.sqrt τ) * Real.sqrt (gradEnergy ω
        (clusterBall K' y (CL * (2 ^ n * Real.sqrt τ))) (fun z => openHeat ω s x z) /
          (clusterBall K' y (CL * (2 ^ n * Real.sqrt τ))).card))
    (hG : Real.sqrt (gradEnergy ω (clusterBall K' y (CL * (2 ^ n * Real.sqrt τ)))
        (fun z => openHeat ω s x z) / (clusterBall K' y (CL * (2 ^ n * Real.sqrt τ))).card) ≤
      CG * s ^ (-(3 / 2 : ℝ)) * Real.exp (-(latticeDist x y ^ 2 / (CG * s)))) :
    ∑ z ∈ clusterBall K' y (2 ^ n * Real.sqrt τ), |openHeat ω s x z -
        finAvg (clusterBall K' y (2 ^ n * Real.sqrt τ)) (fun z => openHeat ω s x z)| ≤
      25 * CP * CG * (8 ^ n * τ * Real.sqrt τ) *
        ((s * Real.sqrt s)⁻¹ * Real.exp (-(latticeDist x y ^ 2 / (CG * s)))) := by
  have hτ0 : 0 < τ := by linarith
  have hsτ : 1 ≤ Real.sqrt τ := by rw [Real.one_le_sqrt]; exact hτ1
  have hR1 : 1 ≤ (2 : ℝ) ^ n * Real.sqrt τ :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hsτ
  have hosc := sum_abs_sub_finAvg_le (u := fun z => openHeat ω s x z) hCP.le (by linarith) hP hG
  rw [rpow_neg_three_halves hs] at hosc
  have hcard := card_clusterBall_le K' y hR1
  have hsqτ := Real.mul_self_sqrt hτ0.le
  have h8 : ((2 : ℝ) ^ n) ^ 3 = 8 ^ n := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hs3 : Real.sqrt τ ^ 3 = τ * Real.sqrt τ := by rw [pow_succ, sq, hsqτ]
  have hR3 : (2 : ℝ) ^ n * Real.sqrt τ * (25 * ((2 : ℝ) ^ n * Real.sqrt τ) ^ 2) =
      25 * (8 ^ n * τ * Real.sqrt τ) := by
    calc (2 : ℝ) ^ n * Real.sqrt τ * (25 * ((2 : ℝ) ^ n * Real.sqrt τ) ^ 2)
        = 25 * (((2 : ℝ) ^ n) ^ 3 * Real.sqrt τ ^ 3) := by ring
      _ = 25 * (8 ^ n * τ * Real.sqrt τ) := by rw [h8, hs3]; ring
  have hE := Real.exp_pos (-(latticeDist x y ^ 2 / (CG * s)))
  have hss : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  calc _ ≤ CP * (2 ^ n * Real.sqrt τ) * (clusterBall K' y (2 ^ n * Real.sqrt τ)).card *
        (CG * (s * Real.sqrt s)⁻¹ * Real.exp (-(latticeDist x y ^ 2 / (CG * s)))) := hosc
    _ ≤ CP * (2 ^ n * Real.sqrt τ) * (25 * ((2 : ℝ) ^ n * Real.sqrt τ) ^ 2) *
        (CG * (s * Real.sqrt s)⁻¹ * Real.exp (-(latticeDist x y ^ 2 / (CG * s)))) := by
        gcongr
    _ = CP * CG * ((2 : ℝ) ^ n * Real.sqrt τ * (25 * ((2 : ℝ) ^ n * Real.sqrt τ) ^ 2)) *
        ((s * Real.sqrt s)⁻¹ * Real.exp (-(latticeDist x y ^ 2 / (CG * s)))) := by ring
    _ = _ := by rw [hR3]; ring

end Rigidity.Green
