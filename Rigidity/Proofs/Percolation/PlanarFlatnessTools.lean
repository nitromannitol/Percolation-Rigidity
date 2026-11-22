import Rigidity.Proofs.Percolation.PlanarFlatnessBound
import Rigidity.Proofs.Percolation.PlanarTauSummable

/-!
# Tools for the proof of Lemma 5.8 of Armstrong and Dario

* `sum_centers_coarsen_le`: for the minimizer `u = u(·, □, q)` of `μ` on a cube `□` of scale `m`
  and `k ≤ m`, the mean square over the subcubes `V = z + □_k` of `| |V|⁻¹ ⟨∇[u]_P⟩_V - ξ |` is at
  most three times the sum of the quantity of Lemma 5.5, of the mean over `V` of
  `| |V|⁻¹ ⟨∇[u(·, V, q)]_P⟩_V - c |²` and of `|c - ξ|²`, for every vector `c` (the
  inequality `(a + b + c)² ≤ 3 (a² + b² + c²)` in the proof of (5.32) of Armstrong and Dario);
* `lintegral_ofReal_le_of_le`: the expectation of a random variable bounded by a nonnegative
  combination of random variables with known expectations;
* elementary sums: `∑_{k ≥ n} (3^{-k/2} + exp(-c 3^k)) ≤ C 3^{-n/4}`,
  `∑_{k=a}^{m-1} 3^k ∑_{l=k}^{m-1} τ_l ≤ 3 ∑_{l<m} 3^l τ_l` and
  `∑_{k<m} 3^k 3^{-k/4} ≤ 3^{3m/4}`;
* `exists_sum_sq_planarAhomInvFinite_sub_le`: display (5.24) of Armstrong and Dario in the form
  `|(ā_{□_k}⁻¹ - ā_{□_n}⁻¹) q|² ≤ C |q|² (∑_{l=k}^{n-1} τ_l + 3^{-k/4})`.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped Classical Matrix ENNReal

namespace Rigidity.Percolation

open Rigidity.Proofs.Multiscale (cube centers subcube gradSum sum_centers card_centers
  sum_range_three_pow_le)

variable {ω : Configuration 2}

/-- `(a + b + c)² ≤ 3 (a² + b² + c²)`. -/
theorem add_add_sq_le (a b c : ℝ) : (a + b + c) ^ 2 ≤ 3 * a ^ 2 + 3 * b ^ 2 + 3 * c ^ 2 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]

theorem inv_mul_le_of_le_three {N X A B C : ℝ} (hN : 0 < N)
    (h : X ≤ 3 * A + 3 * B + 3 * (N * C)) :
    N⁻¹ * X ≤ 3 * (N⁻¹ * A) + 3 * (N⁻¹ * B) + 3 * C := by
  have h2 := mul_le_mul_of_nonneg_left h (inv_nonneg.2 hN.le)
  have e : N⁻¹ * (3 * A + 3 * B + 3 * (N * C)) =
      3 * (N⁻¹ * A) + 3 * (N⁻¹ * B) + N⁻¹ * N * (3 * C) := by ring
  rw [e, inv_mul_cancel₀ hN.ne', one_mul] at h2
  exact h2

/-- **The subcube averages of the coarsened gradient of a minimizer**, split as in the proof of
(5.32) of Armstrong and Dario. -/
theorem sum_centers_coarsen_le {m k : ℕ} (hk : k ≤ m) (z : Vertex 2) (q ξ c : Fin 2 → ℝ) :
    ((centers m z k).card : ℝ)⁻¹ * ∑ y ∈ centers m z k, ∑ j : Fin 2,
        (((9 : ℝ) ^ k)⁻¹ *
          gradSum (subcube k y) (coarsen ω ⟨m, z⟩ (planarMuMinimizer ω ⟨m, z⟩ q)) j - ξ j) ^ 2 ≤
      3 * planarMuRestrictError ω ⟨m, z⟩ k q +
      3 * (((subcubesAt (⟨m, z⟩ : TriadicCube 2) k).card : ℝ)⁻¹ *
        ∑ V ∈ subcubesAt (⟨m, z⟩ : TriadicCube 2) k, ∑ j : Fin 2,
          (planarMuGradAvg ω V q j - c j) ^ 2) +
      3 * ∑ j : Fin 2, (c j - ξ j) ^ 2 := by
  set U : TriadicCube 2 := ⟨m, z⟩ with hU
  set w := coarsen ω U (planarMuMinimizer ω U q) with hw
  have hcard := card_subcubesAt_eq hk z
  rw [← hU] at hcard
  have hc : (0 : ℝ) < (centers m z k).card := by
    rw [card_centers hk]
    positivity
  rw [sum_centers hk z (fun B => ∑ j : Fin 2, (((9 : ℝ) ^ k)⁻¹ * gradSum B w j - ξ j) ^ 2)]
  rw [planarMuRestrictError, hcard]
  rw [sum_subcubesAt_eq hk z, sum_subcubesAt_eq hk z]
  set N : ℝ := ((centers m z k).card : ℝ) with hN
  have hterm : ∀ j ∈ cube (m - k) z,
      ∑ i : Fin 2, (((9 : ℝ) ^ k)⁻¹ * gradSum (cube k j) w i - ξ i) ^ 2 ≤
        3 * ∑ i : Fin 2, ((cubeGradSum ⟨k, j⟩ w i -
          coarsePairing ω ⟨k, j⟩ (Pi.single i 1) (planarMuMinimizer ω ⟨k, j⟩ q)) /
            (⟨k, j⟩ : TriadicCube 2).volume) ^ 2 +
        3 * ∑ i : Fin 2, (planarMuGradAvg ω ⟨k, j⟩ q i - c i) ^ 2 +
        3 * ∑ i : Fin 2, (c i - ξ i) ^ 2 := by
    intro j _
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have hvol : (⟨k, j⟩ : TriadicCube 2).volume = (9 : ℝ) ^ k := rfl
    have e : ((9 : ℝ) ^ k)⁻¹ * gradSum (cube k j) w i - ξ i =
        (cubeGradSum ⟨k, j⟩ w i -
          coarsePairing ω ⟨k, j⟩ (Pi.single i 1) (planarMuMinimizer ω ⟨k, j⟩ q)) /
            (⟨k, j⟩ : TriadicCube 2).volume +
        (planarMuGradAvg ω ⟨k, j⟩ q i - c i) + (c i - ξ i) := by
      have hG : cubeGradSum ⟨k, j⟩ w i = gradSum (cube k j) w i := rfl
      rw [planarMuGradAvg, hvol, hG]
      have : (0 : ℝ) < 9 ^ k := by positivity
      field_simp
      ring
    rw [e]
    exact add_add_sq_le _ _ _
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, Finset.sum_const] at hsum
  have hcube : ((cube (m - k) z).card : ℝ) = N := by
    rw [hN, card_centers hk, Rigidity.Proofs.Multiscale.card_cube]
  rw [nsmul_eq_mul, hcube] at hsum
  exact inv_mul_le_of_le_three hc hsum

/-- **Expectation of a random variable bounded by a combination of random variables.** -/
theorem lintegral_ofReal_le_of_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X f₀ : Ω → ℝ} {f g : ℕ → Ω → ℝ} {s : Finset ℕ}
    {a₀ c₀ b₀ : ℝ} {a bf bg : ℕ → ℝ}
    (ha₀ : 0 ≤ a₀) (ha : ∀ k ∈ s, 0 ≤ a k) (hc₀ : 0 ≤ c₀)
    (hf₀ : ∀ ω, 0 ≤ f₀ ω) (hf : ∀ k ∈ s, ∀ ω, 0 ≤ f k ω) (hg : ∀ k ∈ s, ∀ ω, 0 ≤ g k ω)
    (mf₀ : AEMeasurable f₀ μ) (mf : ∀ k ∈ s, AEMeasurable (f k) μ)
    (mg : ∀ k ∈ s, AEMeasurable (g k) μ)
    (hX : ∀ ω, X ω ≤ a₀ * f₀ ω + ∑ k ∈ s, a k * (f k ω + g k ω) + c₀)
    (I₀ : ∫⁻ ω, ENNReal.ofReal (f₀ ω) ∂μ ≤ ENNReal.ofReal b₀)
    (If : ∀ k ∈ s, ∫⁻ ω, ENNReal.ofReal (f k ω) ∂μ ≤ ENNReal.ofReal (bf k))
    (Ig : ∀ k ∈ s, ∫⁻ ω, ENNReal.ofReal (g k ω) ∂μ ≤ ENNReal.ofReal (bg k))
    (hb₀ : 0 ≤ b₀) (hbf : ∀ k ∈ s, 0 ≤ bf k) (hbg : ∀ k ∈ s, 0 ≤ bg k) :
    ∫⁻ ω, ENNReal.ofReal (X ω) ∂μ ≤
      ENNReal.ofReal (a₀ * b₀ + ∑ k ∈ s, a k * (bf k + bg k) + c₀) := by
  have hpt : ∀ ω, ENNReal.ofReal (X ω) ≤ ENNReal.ofReal a₀ * ENNReal.ofReal (f₀ ω) +
      ∑ k ∈ s, (ENNReal.ofReal (a k) * ENNReal.ofReal (f k ω) +
        ENNReal.ofReal (a k) * ENNReal.ofReal (g k ω)) + ENNReal.ofReal c₀ := by
    intro ω
    refine (ENNReal.ofReal_le_ofReal (hX ω)).trans (le_of_eq ?_)
    have hs : 0 ≤ ∑ k ∈ s, a k * (f k ω + g k ω) :=
      Finset.sum_nonneg fun k hk => mul_nonneg (ha k hk) (add_nonneg (hf k hk ω) (hg k hk ω))
    rw [ENNReal.ofReal_add (add_nonneg (mul_nonneg ha₀ (hf₀ ω)) hs) hc₀,
      ENNReal.ofReal_add (mul_nonneg ha₀ (hf₀ ω)) hs, ENNReal.ofReal_mul ha₀,
      ENNReal.ofReal_sum_of_nonneg fun k hk =>
        mul_nonneg (ha k hk) (add_nonneg (hf k hk ω) (hg k hk ω))]
    congr 2
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [ENNReal.ofReal_mul (ha k hk), ENNReal.ofReal_add (hf k hk ω) (hg k hk ω), mul_add]
  have m₀ : AEMeasurable (fun ω => ENNReal.ofReal a₀ * ENNReal.ofReal (f₀ ω)) μ :=
    mf₀.ennreal_ofReal.const_mul _
  have mS : ∀ k ∈ s, AEMeasurable (fun ω => ENNReal.ofReal (a k) * ENNReal.ofReal (f k ω) +
      ENNReal.ofReal (a k) * ENNReal.ofReal (g k ω)) μ := fun k hk =>
    ((mf k hk).ennreal_ofReal.const_mul _).add ((mg k hk).ennreal_ofReal.const_mul _)
  calc ∫⁻ ω, ENNReal.ofReal (X ω) ∂μ
      ≤ ∫⁻ ω, (ENNReal.ofReal a₀ * ENNReal.ofReal (f₀ ω) +
        ∑ k ∈ s, (ENNReal.ofReal (a k) * ENNReal.ofReal (f k ω) +
          ENNReal.ofReal (a k) * ENNReal.ofReal (g k ω)) + ENNReal.ofReal c₀) ∂μ :=
        lintegral_mono hpt
    _ = ENNReal.ofReal a₀ * ∫⁻ ω, ENNReal.ofReal (f₀ ω) ∂μ +
        ∑ k ∈ s, (ENNReal.ofReal (a k) * ∫⁻ ω, ENNReal.ofReal (f k ω) ∂μ +
          ENNReal.ofReal (a k) * ∫⁻ ω, ENNReal.ofReal (g k ω) ∂μ) + ENNReal.ofReal c₀ := by
        rw [lintegral_add_right' _ aemeasurable_const, lintegral_add_left' m₀,
          lintegral_finsetSum' s mS, lintegral_const, measure_univ, mul_one,
          lintegral_const_mul'' _ mf₀.ennreal_ofReal]
        congr 2
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [lintegral_add_left' ((mf k hk).ennreal_ofReal.const_mul _),
          lintegral_const_mul'' _ (mf k hk).ennreal_ofReal,
          lintegral_const_mul'' _ (mg k hk).ennreal_ofReal]
    _ ≤ ENNReal.ofReal a₀ * ENNReal.ofReal b₀ +
        ∑ k ∈ s, (ENNReal.ofReal (a k) * ENNReal.ofReal (bf k) +
          ENNReal.ofReal (a k) * ENNReal.ofReal (bg k)) + ENNReal.ofReal c₀ := by
        gcongr with k hk
        · exact If k hk
        · exact Ig k hk
    _ = ENNReal.ofReal (a₀ * b₀ + ∑ k ∈ s, a k * (bf k + bg k) + c₀) := by
        have hs : 0 ≤ ∑ k ∈ s, a k * (bf k + bg k) :=
          Finset.sum_nonneg fun k hk => mul_nonneg (ha k hk) (add_nonneg (hbf k hk) (hbg k hk))
        rw [ENNReal.ofReal_add (add_nonneg (mul_nonneg ha₀ hb₀) hs) hc₀,
          ENNReal.ofReal_add (mul_nonneg ha₀ hb₀) hs, ENNReal.ofReal_mul ha₀,
          ENNReal.ofReal_sum_of_nonneg fun k hk =>
            mul_nonneg (ha k hk) (add_nonneg (hbf k hk) (hbg k hk))]
        congr 2
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [ENNReal.ofReal_mul (ha k hk), ENNReal.ofReal_add (hbf k hk) (hbg k hk), mul_add]

/-- **The mean of random variables with bounded expectations.** -/
theorem lintegral_ofReal_avg_le {Ω α : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {s : Finset α} (hs : s.Nonempty) {F : α → Ω → ℝ} (hF : ∀ a ∈ s, ∀ ω, 0 ≤ F a ω)
    (mF : ∀ a ∈ s, AEMeasurable (F a) μ) {b : ℝ}
    (IF : ∀ a ∈ s, ∫⁻ ω, ENNReal.ofReal (F a ω) ∂μ ≤ ENNReal.ofReal b) :
    ∫⁻ ω, ENNReal.ofReal ((s.card : ℝ)⁻¹ * ∑ a ∈ s, F a ω) ∂μ ≤ ENNReal.ofReal b := by
  have hc : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hpt : ∀ ω, ENNReal.ofReal ((s.card : ℝ)⁻¹ * ∑ a ∈ s, F a ω) =
      ENNReal.ofReal (s.card : ℝ)⁻¹ * ∑ a ∈ s, ENNReal.ofReal (F a ω) := fun ω => by
    rw [ENNReal.ofReal_mul (inv_nonneg.2 hc.le), ENNReal.ofReal_sum_of_nonneg fun a ha => hF a ha ω]
  simp_rw [hpt]
  rw [lintegral_const_mul'' _ (Finset.aemeasurable_fun_sum s fun a ha => (mF a ha).ennreal_ofReal),
    lintegral_finsetSum' s fun a ha => (mF a ha).ennreal_ofReal]
  calc ENNReal.ofReal (s.card : ℝ)⁻¹ * ∑ a ∈ s, ∫⁻ ω, ENNReal.ofReal (F a ω) ∂μ
      ≤ ENNReal.ofReal (s.card : ℝ)⁻¹ * ∑ _a ∈ s, ENNReal.ofReal b := by
        gcongr with a ha
        exact IF a ha
    _ = ENNReal.ofReal b := by
        rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (inv_nonneg.2 hc.le), inv_mul_cancel₀ hc.ne', ENNReal.ofReal_one,
          one_mul]

/-- `exp (-c x) ≤ (c x)⁻¹` for `c x > 0`. -/
theorem exp_neg_le_inv {x : ℝ} (hx : 0 < x) : Real.exp (-x) ≤ x⁻¹ := by
  rw [Real.exp_neg]
  refine inv_anti₀ hx ?_
  linarith [Real.add_one_le_exp x]

/-- `3^{-k/2} = (√3)⁻¹ ^ k`. -/
theorem one_div_sqrt_three_pow (k : ℕ) :
    1 / Real.sqrt ((3 : ℝ) ^ k) = (Real.sqrt 3)⁻¹ ^ k := by
  rw [sqrt_three_pow, one_div, inv_pow]

/-- `(√3)⁻¹ ^ k ≤ 3^{-k/4}`. -/
theorem inv_sqrt_three_pow_le (k : ℕ) :
    (Real.sqrt 3)⁻¹ ^ k ≤ (3 : ℝ) ^ (-(k : ℝ) / 4) := by
  have h1 : (Real.sqrt 3)⁻¹ ^ k = (3 : ℝ) ^ (-(k : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by norm_num), ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  rw [h1]
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

/-- **The boundary errors are summable at the rate `3^{-n/4}`.** -/
theorem exists_sum_planarError_le {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k n : ℕ,
      ∑ l ∈ Finset.Ico k n, (1 / Real.sqrt ((3 : ℝ) ^ l) + Real.exp (-c * (3 : ℝ) ^ l)) +
        (1 / Real.sqrt ((3 : ℝ) ^ k) + Real.exp (-c * (3 : ℝ) ^ k)) ≤
      C * (3 : ℝ) ^ (-(k : ℝ) / 4) := by
  set r : ℝ := (Real.sqrt 3)⁻¹ with hr
  have hr0 : 0 ≤ r := by positivity
  have hs3 : (3 / 2 : ℝ) ≤ Real.sqrt 3 := by
    calc (3 / 2 : ℝ) = Real.sqrt ((3 / 2) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 3 := Real.sqrt_le_sqrt (by norm_num)
  have hr1 : r ≤ 2 / 3 := by
    rw [hr]
    calc (Real.sqrt 3)⁻¹ ≤ (3 / 2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hs3
      _ = 2 / 3 := by norm_num
  have hε : ∀ l : ℕ, 1 / Real.sqrt ((3 : ℝ) ^ l) + Real.exp (-c * (3 : ℝ) ^ l) ≤
      (1 + c⁻¹) * r ^ l := by
    intro l
    have h3 : (0 : ℝ) < 3 ^ l := by positivity
    have he : Real.exp (-c * (3 : ℝ) ^ l) ≤ c⁻¹ * r ^ l := by
      have h1 := exp_neg_le_inv (mul_pos hc h3)
      rw [neg_mul] at *
      refine h1.trans ?_
      rw [mul_inv]
      refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hc.le)
      rw [hr, ← one_div_sqrt_three_pow, one_div]
      refine inv_anti₀ (Real.sqrt_pos.2 h3) ?_
      have hsq : Real.sqrt ((3 : ℝ) ^ l) ≤ (3 : ℝ) ^ l := by
        rw [Real.sqrt_le_left (by positivity)]
        nlinarith [one_le_pow₀ (show (1 : ℝ) ≤ 3 by norm_num) (n := l)]
      exact hsq
    rw [one_div_sqrt_three_pow, ← hr]
    nlinarith
  have hgeom : ∀ k n : ℕ, ∑ l ∈ Finset.Ico k n, r ^ l ≤ 3 * r ^ k := by
    intro k n
    rcases le_or_gt n k with hnk | hkn
    · rw [Finset.Ico_eq_empty_of_le hnk, Finset.sum_empty]
      positivity
    · rw [Finset.sum_Ico_eq_sum_range]
      simp only [pow_add, ← Finset.mul_sum]
      have h := geom_sum_mul r (n - k)
      have hs : 0 ≤ ∑ i ∈ Finset.range (n - k), r ^ i :=
        Finset.sum_nonneg fun i _ => pow_nonneg hr0 i
      have hb : ∑ i ∈ Finset.range (n - k), r ^ i ≤ 3 := by
        nlinarith [pow_nonneg hr0 (n - k)]
      calc r ^ k * ∑ i ∈ Finset.range (n - k), r ^ i ≤ r ^ k * 3 :=
            mul_le_mul_of_nonneg_left hb (pow_nonneg hr0 k)
        _ = 3 * r ^ k := by ring
  refine ⟨4 * (1 + c⁻¹), by positivity, fun k n => ?_⟩
  have h1 : ∑ l ∈ Finset.Ico k n, (1 / Real.sqrt ((3 : ℝ) ^ l) + Real.exp (-c * (3 : ℝ) ^ l)) ≤
      (1 + c⁻¹) * (3 * r ^ k) := by
    calc _ ≤ ∑ l ∈ Finset.Ico k n, (1 + c⁻¹) * r ^ l := Finset.sum_le_sum fun l _ => hε l
      _ = (1 + c⁻¹) * ∑ l ∈ Finset.Ico k n, r ^ l := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hgeom k n) (by positivity)
  have h2 := hε k
  have h3 : r ^ k ≤ (3 : ℝ) ^ (-(k : ℝ) / 4) := inv_sqrt_three_pow_le k
  have hc1 : 0 ≤ 1 + c⁻¹ := by positivity
  nlinarith

/-- `∑_{k=a}^{m-1} 3^k ∑_{l=k}^{m-1} τ_l ≤ 3 ∑_{l<m} 3^l τ_l` for nonnegative `τ`. -/
theorem sum_Ico_three_pow_mul_sum_le {τ : ℕ → ℝ} (hτ : ∀ l, 0 ≤ τ l) (a m : ℕ) :
    ∑ k ∈ Finset.Ico a m, (3 : ℝ) ^ k * ∑ l ∈ Finset.Ico k m, τ l ≤
      3 * ∑ l ∈ Finset.range m, (3 : ℝ) ^ l * τ l := by
  have hswap : ∑ k ∈ Finset.Ico a m, (3 : ℝ) ^ k * ∑ l ∈ Finset.Ico k m, τ l =
      ∑ l ∈ Finset.Ico a m, ∑ k ∈ Finset.Ico a (l + 1), (3 : ℝ) ^ k * τ l := by
    simp only [Finset.mul_sum]
    refine Finset.sum_comm' fun k l => ?_
    simp only [Finset.mem_Ico]
    omega
  rw [hswap, Finset.mul_sum]
  calc ∑ l ∈ Finset.Ico a m, ∑ k ∈ Finset.Ico a (l + 1), (3 : ℝ) ^ k * τ l
      ≤ ∑ l ∈ Finset.Ico a m, ∑ k ∈ Finset.range (l + 1), (3 : ℝ) ^ k * τ l :=
        Finset.sum_le_sum fun l _ => Finset.sum_le_sum_of_subset_of_nonneg
          (fun k hk => Finset.mem_range.2 (Finset.mem_Ico.1 hk).2)
          fun k _ _ => mul_nonneg (by positivity) (hτ l)
    _ ≤ ∑ l ∈ Finset.range m, ∑ k ∈ Finset.range (l + 1), (3 : ℝ) ^ k * τ l :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun l hl => Finset.mem_range.2 (Finset.mem_Ico.1 hl).2)
          fun l _ _ => Finset.sum_nonneg fun k _ => mul_nonneg (by positivity) (hτ l)
    _ ≤ ∑ l ∈ Finset.range m, 3 * ((3 : ℝ) ^ l * τ l) := by
        refine Finset.sum_le_sum fun l _ => ?_
        rw [← Finset.sum_mul]
        have h := sum_range_three_pow_le (l + 1)
        rw [pow_succ] at h
        nlinarith [hτ l]

/-- `∑_{k<m} 3^k 3^{-k/4} ≤ 3^{3m/4}`. -/
theorem sum_range_three_pow_mul_rpow_le (m : ℕ) :
    ∑ k ∈ Finset.range m, (3 : ℝ) ^ k * (3 : ℝ) ^ (-(k : ℝ) / 4) ≤
      (3 : ℝ) ^ (3 * (m : ℝ) / 4) := by
  set r : ℝ := (3 : ℝ) ^ ((3 : ℝ) / 4) with hr
  have hk : ∀ k : ℕ, (3 : ℝ) ^ k * (3 : ℝ) ^ (-(k : ℝ) / 4) = r ^ k := by
    intro k
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_add (by norm_num), ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  have hm : (3 : ℝ) ^ (3 * (m : ℝ) / 4) = r ^ m := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  simp_rw [hk]
  rw [hm]
  have hr2 : 2 ≤ r := by
    have h4 : r ^ 4 = 27 := by
      rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    refine le_of_not_gt fun hlt => ?_
    have h16 := pow_lt_pow_left₀ hlt (show (0 : ℝ) ≤ r by positivity) (by norm_num : 4 ≠ 0)
    norm_num [h4] at h16
  have h := geom_sum_mul r m
  have hS : 0 ≤ ∑ k ∈ Finset.range m, r ^ k :=
    Finset.sum_nonneg fun k _ => pow_nonneg (by linarith) k
  nlinarith [pow_nonneg (show (0 : ℝ) ≤ r by linarith) m]

/-- **Display (5.24) of Armstrong and Dario, squared**:
`|(ā_{□_k}⁻¹ - ā_{□_n}⁻¹) q|² ≤ C |q|² (∑_{l=k}^{n-1} τ_l + 3^{-k/4})` for `k ≤ n`. -/
theorem exists_sum_sq_planarAhomInvFinite_sub_le {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k n : ℕ), k ≤ n → ∀ q : Fin 2 → ℝ,
      ∑ j : Fin 2, ((planarAhomInvFinite p k *ᵥ q) j - (planarAhomInvFinite p n *ᵥ q) j) ^ 2 ≤
        C * (q 0 ^ 2 + q 1 ^ 2) *
          (∑ l ∈ Finset.Ico k n, planarTau p l + (3 : ℝ) ^ (-(k : ℝ) / 4)) := by
  obtain ⟨C₁, hC₁, c, hc, h24⟩ := exists_abs_planarAhomInvFinite_sub_le hpc
  obtain ⟨K, hK, hKb⟩ := exists_abs_planarAhomInvFinite_le hpc
  obtain ⟨C₂, hC₂, hE⟩ := exists_sum_planarError_le hc
  refine ⟨2 * (2 * K) * C₁ * (1 + C₂) * 4, by positivity, fun k n hkn q => ?_⟩
  set T := ∑ l ∈ Finset.Ico k n, planarTau p l with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun l _ => planarTau_nonneg p l
  set ρ := (3 : ℝ) ^ (-(k : ℝ) / 4) with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  set D := planarAhomInvFinite p n - planarAhomInvFinite p k with hD
  have hDij : ∀ i j, |D i j| ≤ C₁ * (1 + C₂) * (T + ρ) := by
    intro i j
    have h := h24 k n hkn i j
    have hμτ : ∑ l ∈ Finset.Ico k n, planarMuTau p l ≤ T :=
      Finset.sum_le_sum fun l _ => le_add_of_nonneg_right (planarNuTau_nonneg p l)
    have hE' := hE k n
    rw [← hρ] at hE'
    rw [hD, Matrix.sub_apply]
    calc _ ≤ _ := h
      _ ≤ C₁ * (T + C₂ * ρ) := mul_le_mul_of_nonneg_left (by linarith) hC₁
      _ ≤ C₁ * (1 + C₂) * (T + ρ) := by
          nlinarith [mul_nonneg hC₁ hρ0, mul_nonneg (mul_nonneg hC₁ hC₂) hT0]
  have hDK : ∀ i j, |D i j| ≤ 2 * K := by
    intro i j
    rw [hD, Matrix.sub_apply]
    calc _ ≤ |planarAhomInvFinite p n i j| + |planarAhomInvFinite p k i j| := abs_sub _ _
      _ ≤ 2 * K := by linarith [hKb n i j, hKb k i j]
  have hsq : ∀ i j, D i j ^ 2 ≤ 2 * K * (C₁ * (1 + C₂) * (T + ρ)) := by
    intro i j
    rw [← sq_abs]
    calc |D i j| ^ 2 = |D i j| * |D i j| := sq _
      _ ≤ 2 * K * (C₁ * (1 + C₂) * (T + ρ)) :=
          mul_le_mul (hDK i j) (hDij i j) (abs_nonneg _) (by positivity)
  have hrow : ∀ j : Fin 2, ((planarAhomInvFinite p k *ᵥ q) j -
      (planarAhomInvFinite p n *ᵥ q) j) ^ 2 ≤
      2 * (2 * K * (C₁ * (1 + C₂) * (T + ρ))) * (q 0 ^ 2 + q 1 ^ 2) := by
    intro j
    have e : (planarAhomInvFinite p k *ᵥ q) j - (planarAhomInvFinite p n *ᵥ q) j =
        -(D j 0 * q 0 + D j 1 * q 1) := by
      simp only [hD, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.sub_apply]
      ring
    rw [e, neg_sq]
    have h0 := hsq j 0
    have h1 := hsq j 1
    nlinarith [sq_nonneg (D j 0 * q 1 - D j 1 * q 0), sq_nonneg (D j 0 * q 0 - D j 1 * q 1),
      sq_nonneg (q 0), sq_nonneg (q 1)]
  rw [Fin.sum_univ_two]
  have := hrow 0
  have := hrow 1
  have hq : 0 ≤ q 0 ^ 2 + q 1 ^ 2 := by positivity
  nlinarith

end Rigidity.Percolation
