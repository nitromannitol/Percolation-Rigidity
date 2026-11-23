import Rigidity.Proofs.Green.DarioGuTwoScaleMomentSum

/-!
# Step 4 of the proof of Proposition 4.3 of Dario–Gu: the terms `f` and `F`

Step 4 of the proof of Proposition 4.3 of Dario–Gu (lines 2416-2446 of the source) estimates the
terms `f` and `F` of (4.26) in the weighted `L²` norm. With `P = p̄(r, · - y)` on the lattice,
the term `f = (∂_r P - (σ/2) Σ_k D_k D_k P) + Σ_k D_k ∂_r P χ_k` (`stepFourF`) and the field
`F_i = a_i (D_i D_i P - Σ_k χ_k D_i D_k P)` (`stepOneF`) are restricted to a set `S` (the cluster)
on which the corrector grows like `|χ_k(x)| ≤ B (√r + |x - y| + 2)^β` (Proposition 2.12). Then,
for `C ≥ 128σ`, `0 ≤ β ≤ 1`, `r ≥ 1` and the truncated weights `ψ = ψ_R`:

* `tsum_sq_clusterF_le`: `Σ_x (ψ 1_S f)² ≤ Q e^{4/C} (1 + B)² r^{β - 4}`;
* `tsum_sq_clusterFlux_le`: `Σ_x Σ_i (1_S F_i(x) ψ(x + e_i))² ≤ Q e^{4/C} (1 + B)² r^{β - 3}` and
  `Σ_x Σ_i (1_S F_i(x) D_i ψ(x))² ≤ Q C^{-2} e^{15/C} (1 + B)² r^{β - 4}`, with `1_S F_i` square
  summable.
-/

open scoped Classical
open LatticeProb LatticeProb.Percolation

namespace Rigidity.Green

/-- The term `f` of (4.26): `(∂_r P - (σ/2) Σ_k D_k D_k P) + Σ_k D_k ∂_r P χ_k`. -/
noncomputable def stepFourF (σ : ℝ) (χ : Fin 2 → Vertex 2 → ℝ) (r : ℝ) (y x : Vertex 2) : ℝ :=
  (latticeGaussianTimeDeriv σ r x y -
      σ / 2 * ∑ k : Fin 2, fwdDiff k (fwdDiff k fun z => latticeGaussian σ r z y) x) +
    ∑ k : Fin 2, fwdDiff k (fun z => latticeGaussianTimeDeriv σ r z y) x * χ k x

/-- `f` restricted to `S`. -/
noncomputable def clusterF (S : Set (Vertex 2)) (σ : ℝ) (χ : Fin 2 → Vertex 2 → ℝ) (r : ℝ)
    (y x : Vertex 2) : ℝ :=
  if x ∈ S then stepFourF σ χ r y x else 0

/-- `F_i` restricted to `S`. -/
noncomputable def clusterFlux (S : Set (Vertex 2)) (ω : Configuration 2) (σ : ℝ)
    (χ : Fin 2 → Vertex 2 → ℝ) (r : ℝ) (y : Vertex 2) (i : Fin 2) (x : Vertex 2) : ℝ :=
  if x ∈ S then stepOneF ω χ (fun z => latticeGaussian σ r z y) i x else 0

/-- The dominated sums against `weightGauss`. -/
theorem summable_tsum_le_of_weightGauss {σ C β r : ℝ} {y : Vertex 2} {g : Vertex 2 → ℝ}
    {M Q₀ : ℝ} (hM : 0 ≤ M) (hs : Summable fun x => weightGauss σ C β r y x)
    (hQ : ∑' x, weightGauss σ C β r y x ≤ Q₀ * r ^ (1 + β))
    (hg0 : ∀ x, 0 ≤ g x) (hg : ∀ x, g x ≤ M * weightGauss σ C β r y x) :
    Summable g ∧ ∑' x, g x ≤ M * Q₀ * r ^ (1 + β) := by
  have hsg : Summable g := Summable.of_nonneg_of_le hg0 hg (hs.mul_left M)
  refine ⟨hsg, ?_⟩
  calc ∑' x, g x ≤ ∑' x, M * weightGauss σ C β r y x :=
        Summable.tsum_le_tsum hg hsg (hs.mul_left M)
    _ = M * ∑' x, weightGauss σ C β r y x := tsum_mul_left
    _ ≤ M * (Q₀ * r ^ (1 + β)) := mul_le_mul_of_nonneg_left hQ hM
    _ = M * Q₀ * r ^ (1 + β) := by ring

/-- The factors of `weightGauss`: `e^{4d²/(Cr)} Φ² (B^β)² ≤ weightGauss`. -/
theorem le_weightGauss {σ C β r : ℝ} (hr : 0 < r) (y x : Vertex 2) :
    Real.exp (4 * latticeDist x y ^ 2 / (C * r)) *
        Real.exp (-(latticeDist x y ^ 2 / (32 * σ * r))) ^ 2 *
        ((Real.sqrt r + latticeDist x y + 2) ^ β) ^ 2 ≤ weightGauss σ C β r y x := by
  have hd := latticeDist_nonneg x y
  have hB : 0 ≤ Real.sqrt r + latticeDist x y + 2 := by positivity
  have e : ((Real.sqrt r + latticeDist x y + 2) ^ β) ^ 2 =
      (Real.sqrt r + latticeDist x y + 2) ^ (2 * β) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hB]
    congr 1
    push_cast
    ring
  have h1 : 1 ≤ 1 + latticeDist x y ^ 2 / r := by
    have : 0 ≤ latticeDist x y ^ 2 / r := by positivity
    linarith
  unfold weightGauss
  rw [e]
  have h0 : 0 ≤ Real.exp (4 * latticeDist x y ^ 2 / (C * r)) *
      Real.exp (-(latticeDist x y ^ 2 / (32 * σ * r))) ^ 2 *
      (Real.sqrt r + latticeDist x y + 2) ^ (2 * β) := by positivity
  calc Real.exp (4 * latticeDist x y ^ 2 / (C * r)) *
        Real.exp (-(latticeDist x y ^ 2 / (32 * σ * r))) ^ 2 *
        (Real.sqrt r + latticeDist x y + 2) ^ (2 * β)
      ≤ Real.exp (4 * latticeDist x y ^ 2 / (C * r)) *
          Real.exp (-(latticeDist x y ^ 2 / (32 * σ * r))) ^ 2 *
          (Real.sqrt r + latticeDist x y + 2) ^ (2 * β) * (1 + latticeDist x y ^ 2 / r) :=
        le_mul_of_one_le_right h0 h1
    _ = _ := by ring

theorem rpow_sub_nat_eq {r : ℝ} (hr : 0 < r) (β m : ℝ) (n : ℕ) (h : m = n) :
    r ^ (β - m) = r ^ β / r ^ n := by
  rw [Real.rpow_sub hr, h, Real.rpow_natCast]

/-- The pointwise bound of `f`: `|f(x)| ≤ K (1 + B) r^{-5/2} Φ(x) (√r + |x - y| + 2)^β`. -/
theorem abs_stepFourF_le {σ : ℝ} (hσ : 0 < σ) : ∃ K : ℝ, 0 < K ∧
    ∀ (r β B : ℝ) (χ : Fin 2 → Vertex 2 → ℝ) (x y : Vertex 2), 1 ≤ r → 0 ≤ β → 0 ≤ B →
      (∀ k, |χ k x| ≤ B * (Real.sqrt r + latticeDist x y + 2) ^ β) →
      |stepFourF σ χ r y x| ≤ K * (1 + B) / (r ^ 2 * Real.sqrt r) *
        Real.exp (-(latticeDist x y ^ 2 / (32 * σ * r))) *
          (Real.sqrt r + latticeDist x y + 2) ^ β := by
  obtain ⟨K₁, hK₁, h1⟩ := abs_timeDeriv_sub_secondDiff_le hσ
  obtain ⟨K₂, hK₂, h2⟩ := abs_fwdDiff_latticeGaussianTimeDeriv_le hσ
  refine ⟨K₁ + 2 * K₂, by positivity, fun r β B χ x y hr hβ hB hχ => ?_⟩
  have hr0 : 0 < r := by linarith
  set X := 1 / (r ^ 2 * Real.sqrt r) * Real.exp (-(latticeDist x y ^ 2 / (32 * σ * r)))
    with hX
  have hX0 : 0 ≤ X := by positivity
  set Bb := (Real.sqrt r + latticeDist x y + 2) ^ β with hBb
  have hBb1 : 1 ≤ Bb :=
    Real.one_le_rpow (by linarith [Real.sqrt_nonneg r, latticeDist_nonneg x y]) hβ
  have a1 : |latticeGaussianTimeDeriv σ r x y -
      σ / 2 * ∑ k : Fin 2, fwdDiff k (fwdDiff k fun z => latticeGaussian σ r z y) x| ≤ K₁ * X := by
    refine (h1 r x y hr).trans (le_of_eq ?_)
    rw [hX]
    ring
  have a2 : ∀ k : Fin 2, |fwdDiff k (fun z => latticeGaussianTimeDeriv σ r z y) x| ≤ K₂ * X := by
    intro k
    refine (h2 r x y k hr).trans (le_of_eq ?_)
    rw [hX]
    ring
  have b : ∀ k : Fin 2, |fwdDiff k (fun z => latticeGaussianTimeDeriv σ r z y) x * χ k x| ≤
      K₂ * X * (B * Bb) := by
    intro k
    rw [abs_mul]
    exact mul_le_mul (a2 k) (hχ k) (abs_nonneg _) (by positivity)
  have hsum : |∑ k : Fin 2, fwdDiff k (fun z => latticeGaussianTimeDeriv σ r z y) x * χ k x| ≤
      K₂ * X * (B * Bb) + K₂ * X * (B * Bb) := by
    rw [Fin.sum_univ_two]
    exact (abs_add_le _ _).trans (add_le_add (b 0) (b 1))
  unfold stepFourF
  have hK1X : 0 ≤ K₁ * X := by positivity
  have hK2X : 0 ≤ K₂ * X := by positivity
  calc _ ≤ K₁ * X + (K₂ * X * (B * Bb) + K₂ * X * (B * Bb)) :=
        (abs_add_le _ _).trans (add_le_add a1 hsum)
    _ ≤ K₁ * X * Bb + 2 * K₂ * X * Bb + (K₁ * X * Bb * B + 2 * K₂ * X * Bb * B) := by
        have := mul_le_mul_of_nonneg_left hBb1 hK1X
        have : 0 ≤ 2 * K₂ * X * Bb := by positivity
        have : 0 ≤ K₁ * X * Bb * B := by positivity
        nlinarith
    _ = (K₁ + 2 * K₂) * (1 + B) / (r ^ 2 * Real.sqrt r) *
          Real.exp (-(latticeDist x y ^ 2 / (32 * σ * r))) * Bb := by
        rw [hX]
        ring

/-- **Step 4 for `f`**: `Σ_x (ψ_R 1_S f)² ≤ Q e^{4/C} (1 + B)² r^{β - 4}`. -/
theorem tsum_sq_clusterF_le {σ : ℝ} (hσ : 0 < σ) : ∃ Q : ℝ, 0 < Q ∧
    ∀ (C β r R B : ℝ) (S : Set (Vertex 2)) (χ : Fin 2 → Vertex 2 → ℝ) (y : Vertex 2),
      128 * σ ≤ C → 0 ≤ β → β ≤ 1 → 1 ≤ r → 0 ≤ R → 0 ≤ B →
      (∀ x ∈ S, ∀ k, |χ k x| ≤ B * (Real.sqrt r + latticeDist x y + 2) ^ β) →
      Summable (fun x => (dgWeightTrunc C r R y x * clusterF S σ χ r y x) ^ 2) ∧
        ∑' x, (dgWeightTrunc C r R y x * clusterF S σ χ r y x) ^ 2 ≤
          Q * Real.exp (4 / C) * (1 + B) ^ 2 * r ^ (β - 4) := by
  obtain ⟨K, hK, hf⟩ := abs_stepFourF_le hσ
  obtain ⟨Q₀, hQ₀, hW⟩ := tsum_weightGauss_le hσ
  refine ⟨K ^ 2 * Q₀, by positivity, fun C β r R B S χ y hC hβ0 hβ1 hr hR hB hχ => ?_⟩
  have hr0 : 0 < r := by linarith
  have hC0 : 0 < C := by nlinarith
  obtain ⟨hs, hQ⟩ := hW C β r y hC hβ0 hβ1 hr
  set M := Real.exp (4 / C) * (K * (1 + B) / (r ^ 2 * Real.sqrt r)) ^ 2 with hM
  have hM0 : 0 ≤ M := by positivity
  have hpt : ∀ x, (dgWeightTrunc C r R y x * clusterF S σ χ r y x) ^ 2 ≤
      M * weightGauss σ C β r y x := by
    intro x
    unfold clusterF
    split_ifs with hx
    · have hψ := dgWeightTrunc_sq_le hC0 hr hR (x := x) (x' := x) (y := y)
        (by linarith [latticeDist_nonneg x y])
      have hfx := hf r β B χ x y hr hβ0 hB (hχ x hx)
      have hsq := pow_le_pow_left₀ (abs_nonneg _) hfx 2
      rw [sq_abs] at hsq
      have hle := le_weightGauss (σ := σ) (C := C) (β := β) hr0 y x
      rw [mul_pow]
      calc dgWeightTrunc C r R y x ^ 2 * stepFourF σ χ r y x ^ 2
          ≤ (Real.exp (4 / C) * Real.exp (4 * latticeDist x y ^ 2 / (C * r))) *
              (K * (1 + B) / (r ^ 2 * Real.sqrt r) *
                Real.exp (-(latticeDist x y ^ 2 / (32 * σ * r))) *
                (Real.sqrt r + latticeDist x y + 2) ^ β) ^ 2 :=
            mul_le_mul hψ hsq (sq_nonneg _) (by positivity)
        _ = M * (Real.exp (4 * latticeDist x y ^ 2 / (C * r)) *
              Real.exp (-(latticeDist x y ^ 2 / (32 * σ * r))) ^ 2 *
              ((Real.sqrt r + latticeDist x y + 2) ^ β) ^ 2) := by
            rw [hM]
            ring
        _ ≤ M * weightGauss σ C β r y x := mul_le_mul_of_nonneg_left hle hM0
    · rw [mul_zero, sq, mul_zero]
      exact mul_nonneg hM0 (weightGauss_nonneg hr0 y x)
  obtain ⟨hsg, hsum⟩ := summable_tsum_le_of_weightGauss hM0 hs hQ (fun x => sq_nonneg _) hpt
  refine ⟨hsg, hsum.trans (le_of_eq ?_)⟩
  have hsr : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr0.le
  have hsr0 : 0 < Real.sqrt r := Real.sqrt_pos.2 hr0
  rw [hM, rpow_sub_nat_eq hr0 β 4 4 (by norm_num), Real.rpow_add hr0, Real.rpow_one]
  field_simp
  rw [hsr]

/-- The pointwise bound of `F_i`: `|F_i(x)| ≤ 2K (1 + B) r^{-2} Φ(x) (√r + |x - y| + 2)^β`. -/
theorem abs_stepOneF_le {σ : ℝ} (hσ : 0 < σ) : ∃ K : ℝ, 0 < K ∧
    ∀ (ω : Configuration 2) (r β B : ℝ) (χ : Fin 2 → Vertex 2 → ℝ) (x y : Vertex 2) (i : Fin 2),
      1 ≤ r → 0 ≤ β → 0 ≤ B →
      (∀ k, |χ k x| ≤ B * (Real.sqrt r + latticeDist x y + 2) ^ β) →
      |stepOneF ω χ (fun z => latticeGaussian σ r z y) i x| ≤ K * (1 + B) / r ^ 2 *
        Real.exp (-(latticeDist x y ^ 2 / (32 * σ * r))) *
          (Real.sqrt r + latticeDist x y + 2) ^ β := by
  obtain ⟨K₁, hK₁, h1⟩ := abs_fwdDiff_fwdDiff_latticeGaussian_le hσ
  refine ⟨2 * K₁, by positivity, fun ω r β B χ x y i hr hβ hB hχ => ?_⟩
  have hr0 : 0 < r := by linarith
  set X := 1 / r ^ 2 * Real.exp (-(latticeDist x y ^ 2 / (32 * σ * r))) with hX
  have hX0 : 0 ≤ X := by positivity
  set Bb := (Real.sqrt r + latticeDist x y + 2) ^ β with hBb
  have hBb1 : 1 ≤ Bb :=
    Real.one_le_rpow (by linarith [Real.sqrt_nonneg r, latticeDist_nonneg x y]) hβ
  have a : ∀ k : Fin 2, |fwdDiff i (fwdDiff k fun z => latticeGaussian σ r z y) x| ≤ K₁ * X := by
    intro k
    refine (h1 r x y i k hr).trans (le_of_eq ?_)
    rw [hX]
    ring
  have b : ∀ k : Fin 2, |χ k x * fwdDiff i (fwdDiff k fun z => latticeGaussian σ r z y) x| ≤
      B * Bb * (K₁ * X) := by
    intro k
    rw [abs_mul]
    exact mul_le_mul (hχ k) (a k) (abs_nonneg _) (by positivity)
  have hc0 := openCond_nonneg ω i x
  have hc1 := openCond_le_one ω i x
  unfold stepOneF
  rw [abs_mul, abs_of_nonneg hc0, Fin.sum_univ_two]
  have hK1X : 0 ≤ K₁ * X := by positivity
  have hin : |fwdDiff i (fwdDiff i fun z => latticeGaussian σ r z y) x -
      (χ 0 x * fwdDiff i (fwdDiff 0 fun z => latticeGaussian σ r z y) x +
        χ 1 x * fwdDiff i (fwdDiff 1 fun z => latticeGaussian σ r z y) x)| ≤
      K₁ * X + (B * Bb * (K₁ * X) + B * Bb * (K₁ * X)) :=
    (abs_sub _ _).trans (add_le_add (a i) ((abs_add_le _ _).trans (add_le_add (b 0) (b 1))))
  calc openCond ω i x * |fwdDiff i (fwdDiff i fun z => latticeGaussian σ r z y) x -
        (χ 0 x * fwdDiff i (fwdDiff 0 fun z => latticeGaussian σ r z y) x +
          χ 1 x * fwdDiff i (fwdDiff 1 fun z => latticeGaussian σ r z y) x)|
      ≤ 1 * (K₁ * X + (B * Bb * (K₁ * X) + B * Bb * (K₁ * X))) :=
        mul_le_mul hc1 hin (abs_nonneg _) zero_le_one
    _ ≤ 2 * K₁ * X * Bb + 2 * K₁ * X * Bb * B := by
        have := mul_le_mul_of_nonneg_left hBb1 hK1X
        have : 0 ≤ K₁ * X * Bb := by positivity
        have : 0 ≤ B * Bb * (K₁ * X) := by positivity
        nlinarith
    _ = 2 * K₁ * (1 + B) / r ^ 2 * Real.exp (-(latticeDist x y ^ 2 / (32 * σ * r))) * Bb := by
        rw [hX]
        ring

/-- **Step 4 for `F`**: `1_S F_i` is square summable,
`Σ_x Σ_i (1_S F_i(x) ψ_R(x + e_i))² ≤ Q e^{4/C} (1 + B)² r^{β - 3}` and
`Σ_x Σ_i (1_S F_i(x) (ψ_R(x + e_i) - ψ_R(x)))² ≤ Q C^{-2} e^{15/C} (1 + B)² r^{β - 4}`. -/
theorem tsum_sq_clusterFlux_le {σ : ℝ} (hσ : 0 < σ) : ∃ Q : ℝ, 0 < Q ∧
    ∀ (C β r R B : ℝ) (S : Set (Vertex 2)) (ω : Configuration 2) (χ : Fin 2 → Vertex 2 → ℝ)
      (y : Vertex 2), 128 * σ ≤ C → 0 ≤ β → β ≤ 1 → 1 ≤ r → 0 ≤ R → 0 ≤ B →
      (∀ x ∈ S, ∀ k, |χ k x| ≤ B * (Real.sqrt r + latticeDist x y + 2) ^ β) →
      (∀ i, Summable fun x => clusterFlux S ω σ χ r y i x ^ 2) ∧
      (Summable (fun x => ∑ i : Fin 2,
          (clusterFlux S ω σ χ r y i x * dgWeightTrunc C r R y (x + unit i)) ^ 2) ∧
        ∑' x, ∑ i : Fin 2,
          (clusterFlux S ω σ χ r y i x * dgWeightTrunc C r R y (x + unit i)) ^ 2 ≤
          Q * Real.exp (4 / C) * (1 + B) ^ 2 * r ^ (β - 3)) ∧
      (Summable (fun x => ∑ i : Fin 2, (clusterFlux S ω σ χ r y i x *
          (dgWeightTrunc C r R y (x + unit i) - dgWeightTrunc C r R y x)) ^ 2) ∧
        ∑' x, ∑ i : Fin 2, (clusterFlux S ω σ χ r y i x *
          (dgWeightTrunc C r R y (x + unit i) - dgWeightTrunc C r R y x)) ^ 2 ≤
          Q * (18 / C ^ 2 * Real.exp (15 / C)) * (1 + B) ^ 2 * r ^ (β - 4)) := by
  obtain ⟨K, hK, hF⟩ := abs_stepOneF_le hσ
  obtain ⟨Q₀, hQ₀, hW⟩ := tsum_weightGauss_le hσ
  refine ⟨2 * K ^ 2 * Q₀, by positivity,
    fun C β r R B S ω χ y hC hβ0 hβ1 hr hR hB hχ => ?_⟩
  have hr0 : 0 < r := by linarith
  have hC0 : 0 < C := by nlinarith
  obtain ⟨hs, hQ⟩ := hW C β r y hC hβ0 hβ1 hr
  set A := K * (1 + B) / r ^ 2 with hA
  have hA0 : 0 ≤ A := by positivity
  -- the pointwise square bound of `1_S F_i`
  have hsqF : ∀ i x, clusterFlux S ω σ χ r y i x ^ 2 ≤
      A ^ 2 * (Real.exp (-(latticeDist x y ^ 2 / (32 * σ * r))) ^ 2 *
        ((Real.sqrt r + latticeDist x y + 2) ^ β) ^ 2) := by
    intro i x
    unfold clusterFlux
    split_ifs with hx
    · have hFx := hF ω r β B χ x y i hr hβ0 hB (hχ x hx)
      have hsq := pow_le_pow_left₀ (abs_nonneg _) hFx 2
      rw [sq_abs] at hsq
      refine hsq.trans (le_of_eq ?_)
      rw [hA]
      ring
    · rw [sq, mul_zero]
      positivity
  have hE1 : ∀ x : Vertex 2, 1 ≤ Real.exp (4 * latticeDist x y ^ 2 / (C * r)) := fun x =>
    Real.one_le_exp (by have := latticeDist_nonneg x y; positivity)
  have hfac : ∀ x : Vertex 2, 0 ≤ Real.exp (-(latticeDist x y ^ 2 / (32 * σ * r))) ^ 2 *
      ((Real.sqrt r + latticeDist x y + 2) ^ β) ^ 2 := fun x => by positivity
  have hle : ∀ x, Real.exp (4 * latticeDist x y ^ 2 / (C * r)) *
      (Real.exp (-(latticeDist x y ^ 2 / (32 * σ * r))) ^ 2 *
        ((Real.sqrt r + latticeDist x y + 2) ^ β) ^ 2) ≤ weightGauss σ C β r y x := fun x =>
    (le_of_eq (by ring)).trans (le_weightGauss (σ := σ) (C := C) (β := β) hr0 y x)
  refine ⟨fun i => ?_, ?_, ?_⟩
  · -- square summability
    refine (summable_tsum_le_of_weightGauss (sq_nonneg A) hs hQ (fun x => sq_nonneg _)
      (fun x => (hsqF i x).trans ?_)).1
    refine mul_le_mul_of_nonneg_left ((le_mul_of_one_le_left (hfac x) (hE1 x)).trans
      (hle x)) (sq_nonneg A)
  · -- the first sum
    set M := 2 * (Real.exp (4 / C) * A ^ 2) with hM
    have hM0 : 0 ≤ M := by positivity
    have hpt : ∀ x, ∑ i : Fin 2,
        (clusterFlux S ω σ χ r y i x * dgWeightTrunc C r R y (x + unit i)) ^ 2 ≤
        M * weightGauss σ C β r y x := by
      intro x
      have hi : ∀ i : Fin 2, (clusterFlux S ω σ χ r y i x * dgWeightTrunc C r R y (x + unit i)) ^ 2
          ≤ Real.exp (4 / C) * A ^ 2 * weightGauss σ C β r y x := by
        intro i
        have hψ := dgWeightTrunc_sq_le hC0 hr hR (x := x) (x' := x + unit i) (y := y)
          (by linarith [(abs_le.1 (abs_latticeDist_add_unit_sub_le x y i)).2])
        rw [mul_pow]
        calc clusterFlux S ω σ χ r y i x ^ 2 * dgWeightTrunc C r R y (x + unit i) ^ 2
            ≤ (A ^ 2 * (Real.exp (-(latticeDist x y ^ 2 / (32 * σ * r))) ^ 2 *
                ((Real.sqrt r + latticeDist x y + 2) ^ β) ^ 2)) *
              (Real.exp (4 / C) * Real.exp (4 * latticeDist x y ^ 2 / (C * r))) :=
              mul_le_mul (hsqF i x) hψ (sq_nonneg _) (by positivity)
          _ = Real.exp (4 / C) * A ^ 2 * (Real.exp (4 * latticeDist x y ^ 2 / (C * r)) *
                (Real.exp (-(latticeDist x y ^ 2 / (32 * σ * r))) ^ 2 *
                  ((Real.sqrt r + latticeDist x y + 2) ^ β) ^ 2)) := by ring
          _ ≤ Real.exp (4 / C) * A ^ 2 * weightGauss σ C β r y x :=
              mul_le_mul_of_nonneg_left (hle x) (by positivity)
      rw [Fin.sum_univ_two, hM]
      linarith [hi 0, hi 1]
    obtain ⟨hsg, hsum⟩ := summable_tsum_le_of_weightGauss hM0 hs hQ
      (fun x => Finset.sum_nonneg fun i _ => sq_nonneg _) hpt
    refine ⟨hsg, hsum.trans (le_of_eq ?_)⟩
    rw [hM, hA, rpow_sub_nat_eq hr0 β 3 3 (by norm_num), Real.rpow_add hr0, Real.rpow_one]
    field_simp
  · -- the second sum
    set M := 2 * (A ^ 2 * (18 / C ^ 2 * Real.exp (15 / C) / r)) with hM
    have hM0 : 0 ≤ M := by positivity
    have hpt : ∀ x, ∑ i : Fin 2, (clusterFlux S ω σ χ r y i x *
        (dgWeightTrunc C r R y (x + unit i) - dgWeightTrunc C r R y x)) ^ 2 ≤
        M * weightGauss σ C β r y x := by
      intro x
      have hi : ∀ i : Fin 2, (clusterFlux S ω σ χ r y i x *
          (dgWeightTrunc C r R y (x + unit i) - dgWeightTrunc C r R y x)) ^ 2 ≤
          A ^ 2 * (18 / C ^ 2 * Real.exp (15 / C) / r) * weightGauss σ C β r y x := by
        intro i
        have hD := sq_dgWeightTrunc_sub_le hC0 hr hR x y i
        rw [mul_pow]
        calc clusterFlux S ω σ χ r y i x ^ 2 *
              (dgWeightTrunc C r R y (x + unit i) - dgWeightTrunc C r R y x) ^ 2
            ≤ (A ^ 2 * (Real.exp (-(latticeDist x y ^ 2 / (32 * σ * r))) ^ 2 *
                ((Real.sqrt r + latticeDist x y + 2) ^ β) ^ 2)) *
              (18 / C ^ 2 * Real.exp (15 / C) / r * (1 + latticeDist x y ^ 2 / r) *
                Real.exp (4 * latticeDist x y ^ 2 / (C * r))) :=
              mul_le_mul (hsqF i x) hD (sq_nonneg _) (by positivity)
          _ = A ^ 2 * (18 / C ^ 2 * Real.exp (15 / C) / r) * weightGauss σ C β r y x := by
              unfold weightGauss
              have hB0 : 0 ≤ Real.sqrt r + latticeDist x y + 2 := by
                have := latticeDist_nonneg x y
                positivity
              have e : ((Real.sqrt r + latticeDist x y + 2) ^ β) ^ 2 =
                  (Real.sqrt r + latticeDist x y + 2) ^ (2 * β) := by
                rw [← Real.rpow_natCast, ← Real.rpow_mul hB0]
                congr 1
                push_cast
                ring
              rw [e]
              ring
      rw [Fin.sum_univ_two, hM]
      linarith [hi 0, hi 1]
    obtain ⟨hsg, hsum⟩ := summable_tsum_le_of_weightGauss hM0 hs hQ
      (fun x => Finset.sum_nonneg fun i _ => sq_nonneg _) hpt
    refine ⟨hsg, hsum.trans (le_of_eq ?_)⟩
    rw [hM, hA, rpow_sub_nat_eq hr0 β 4 4 (by norm_num), Real.rpow_add hr0, Real.rpow_one]
    field_simp

end Rigidity.Green
