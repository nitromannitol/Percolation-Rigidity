import Rigidity.Proofs.Green.DarioGuTwoScaleFluxSum
import Rigidity.Proofs.Green.DarioGuTwoScaleFluxCoeff

/-!
# The pieces of the dyadic decomposition in Step 3 of Proposition 4.3 of Dario–Gu

The coefficient of the `m`-th piece in Step 3 of the proof of Proposition 4.3 of Dario–Gu is
`A_m = (η_m - η_{m-1}) D_i D_k p̄ ψ`. It vanishes outside the annulus `A_m`, where the Gaussian
factor is at most `dyDecay σ m = e^{1/(64σ)} exp(-4^{m-1}/(512σ))` (the bound
`‖D² p̄ ψ‖_{L^∞(A_m)} ≤ C t^{-d/2-1} exp(-2^{2m}/(8σ))` of the source, line 2408):

* `abs_dyCoeff_le`: `|A_m| ≤ K r^{-2} dyDecay σ m`;
* `abs_dyCoeff_sub_le`: `|A_m(x + e_j) - A_m(x)| ≤ K r^{-5/2} dyDecay σ m`;
* `dyCoeff_support`: `A_m(x) u(x) ≠ 0` with `u` vanishing off the cluster forces `x` to lie in
  the interior `int_a(𝒞 ∩ B_{2^{m+2} √r}(y))`.
-/

open scoped Classical
open LatticeProb LatticeProb.Percolation

namespace Rigidity.Green

/-- The decay factor of the scale `m`. -/
noncomputable def dyDecay (σ : ℝ) : ℕ → ℝ
  | 0 => 1
  | m + 1 => Real.exp (1 / (64 * σ)) * Real.exp (-((4 : ℝ) ^ m / (512 * σ)))

theorem dyDecay_nonneg (σ : ℝ) (m : ℕ) : 0 ≤ dyDecay σ m := by
  cases m with
  | zero => exact zero_le_one
  | succ m => exact (mul_pos (Real.exp_pos _) (Real.exp_pos _)).le

/-- The coefficient `A_m = dyPiece r y m · D_i D_k p̄ · ψ_R`. -/
noncomputable def dyCoeff (σ C r R : ℝ) (y : Vertex 2) (i k : Fin 2) (m : ℕ) (x : Vertex 2) : ℝ :=
  dyPiece r y m x * (fwdDiff i (fwdDiff k fun z => latticeGaussian σ r z y) x *
    dgWeightTrunc C r R y x)

theorem sq_two_pow_mul_sqrt {r : ℝ} (hr : 0 ≤ r) (m : ℕ) :
    ((2 : ℝ) ^ m * Real.sqrt r) ^ 2 = 4 ^ m * r := by
  rw [mul_pow, Real.sq_sqrt hr, ← pow_mul, mul_comm m 2, pow_mul]
  norm_num

theorem one_le_two_pow_mul_sqrt {r : ℝ} (hr : 1 ≤ r) (m : ℕ) : 1 ≤ (2 : ℝ) ^ m * Real.sqrt r := by
  have h1 : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
  have h2 : 1 ≤ Real.sqrt r := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hr
  nlinarith

/-- On the support of the piece `m + 1`, and at distance at most `1` from it,
`|x - y|² ≥ 4^m r/2 - 1`. -/
theorem sq_latticeDist_ge_of_dyPiece_ne {r : ℝ} (hr : 1 ≤ r) {x x' y : Vertex 2} {m : ℕ}
    (hx : dyPiece r y (m + 1) x ≠ 0) (hxx' : latticeDist x y - 1 ≤ latticeDist x' y) :
    4 ^ m * r / 2 - 1 ≤ latticeDist x' y ^ 2 := by
  have hr0 : 0 < r := by linarith
  have hd : 2 ^ m * Real.sqrt r < latticeDist x y := by
    by_contra h
    exact hx (dyPiece_succ_eq_zero_of_le hr0 (not_lt.1 h))
  have ha := one_le_two_pow_mul_sqrt hr m
  have hsq := sq_two_pow_mul_sqrt hr0.le m
  set a := (2 : ℝ) ^ m * Real.sqrt r
  have h1 : a - 1 ≤ latticeDist x' y := by linarith
  have h2 : (a - 1) ^ 2 ≤ latticeDist x' y ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
  nlinarith [sq_nonneg (a - 2)]

/-- The Gaussian factor on the annulus of the scale `m + 1`. -/
theorem exp_neg_le_dyDecay {σ c r d : ℝ} {m : ℕ} (hσ : 0 < σ) (hc1 : 64 * σ ≤ c)
    (hc2 : c ≤ 256 * σ) (hr : 1 ≤ r) (hd : 4 ^ m * r / 2 - 1 ≤ d ^ 2) :
    Real.exp (-(d ^ 2 / (c * r))) ≤ dyDecay σ (m + 1) := by
  have hr0 : 0 < r := by linarith
  have hc : 0 < c := by linarith
  simp only [dyDecay]
  rw [← Real.exp_add, Real.exp_le_exp]
  have h1 : (4 ^ m * r / 2 - 1) / (c * r) ≤ d ^ 2 / (c * r) :=
    div_le_div_of_nonneg_right hd (by positivity)
  have e : (4 ^ m * r / 2 - 1) / (c * r) = (4 : ℝ) ^ m / (2 * c) - 1 / (c * r) := by
    field_simp
  have h2 : 1 / (c * r) ≤ 1 / (64 * σ) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
  have h3 : (4 : ℝ) ^ m / (512 * σ) ≤ (4 : ℝ) ^ m / (2 * c) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  linarith

theorem exp_neg_sq_le_one (a : ℝ) {c : ℝ} (hc : 0 ≤ c) : Real.exp (-(a ^ 2 / c)) ≤ 1 :=
  Real.exp_le_one_iff.2 (neg_nonpos.2 (div_nonneg (sq_nonneg _) hc))

/-- **The bounds of the coefficients of the pieces.** -/
theorem dyCoeff_bounds {σ C : ℝ} (hσ : 0 < σ) (hC : 128 * σ ≤ C) : ∃ Ka Kb : ℝ, 0 < Ka ∧ 0 < Kb ∧
    ∀ (r R : ℝ) (y : Vertex 2) (i k : Fin 2) (m : ℕ), 1 ≤ r → 0 ≤ R →
      (∀ x, |dyCoeff σ C r R y i k m x| ≤ Ka / r ^ 2 * dyDecay σ m) ∧
      (∀ x j, |dyCoeff σ C r R y i k m (x + unit j) - dyCoeff σ C r R y i k m x| ≤
        Kb / (r ^ 2 * Real.sqrt r) * dyDecay σ m) := by
  obtain ⟨K₂, hK₂, h2⟩ := abs_secondDiff_mul_weight_le hσ
  obtain ⟨K₃, hK₃, h3⟩ := abs_secondDiff_mul_weight_sub_le hσ hC
  refine ⟨K₂, 4 * K₂ + K₃, hK₂, by positivity, fun r R y i k m hr hR => ⟨fun x => ?_,
    fun x j => ?_⟩⟩
  · have hr0 : 0 < r := by linarith
    have hP := h2 C r R x y i k (by linarith) hr hR
    have hp0 := dyPiece_nonneg hr0 y m x
    have hp1 := dyPiece_le_one (r := r) y m x
    unfold dyCoeff
    rw [abs_mul, abs_of_nonneg hp0]
    cases m with
    | zero =>
      simp only [dyDecay, mul_one]
      calc dyPiece r y 0 x * |fwdDiff i (fwdDiff k fun z => latticeGaussian σ r z y) x *
            dgWeightTrunc C r R y x|
          ≤ 1 * (K₂ / r ^ 2 * 1) :=
            mul_le_mul hp1 (hP.trans (mul_le_mul_of_nonneg_left
              (exp_neg_sq_le_one _ (by positivity)) (by positivity))) (abs_nonneg _) zero_le_one
        _ = K₂ / r ^ 2 := by ring
    | succ m =>
      by_cases hpx : dyPiece r y (m + 1) x = 0
      · rw [hpx, zero_mul]
        exact mul_nonneg (by positivity) (dyDecay_nonneg σ _)
      · have hs := sq_latticeDist_ge_of_dyPiece_ne hr hpx (x' := x) (by linarith)
        have hdec := exp_neg_le_dyDecay hσ le_rfl (by linarith) hr hs
        calc dyPiece r y (m + 1) x * |fwdDiff i (fwdDiff k fun z => latticeGaussian σ r z y) x *
              dgWeightTrunc C r R y x|
            ≤ 1 * (K₂ / r ^ 2 * dyDecay σ (m + 1)) :=
              mul_le_mul hp1 (hP.trans (mul_le_mul_of_nonneg_left hdec (by positivity)))
                (abs_nonneg _) zero_le_one
          _ = K₂ / r ^ 2 * dyDecay σ (m + 1) := one_mul _
  · have hr0 : 0 < r := by linarith
    have hsr : 0 < Real.sqrt r := Real.sqrt_pos.2 hr0
    set Q := fun z => fwdDiff i (fwdDiff k fun z => latticeGaussian σ r z y) z *
      dgWeightTrunc C r R y z with hQ
    set p := dyPiece r y m with hp
    have hP1 := h2 C r R (x + unit j) y i k (by linarith) hr hR
    have hP2 := h3 r R x y i k j hr hR
    have hpd : |p (x + unit j) - p x| ≤ 4 / Real.sqrt r := by
      refine (abs_dyPiece_sub_le hr0 y x (x + unit j) m).trans ?_
      have hΔ := abs_latticeDist_add_unit_sub_le x y j
      have h2m : Real.sqrt r ≤ 2 ^ m * Real.sqrt r := by
        have : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
        nlinarith
      calc 4 * |latticeDist (x + unit j) y - latticeDist x y| / (2 ^ m * Real.sqrt r)
          ≤ 4 * 1 / (2 ^ m * Real.sqrt r) :=
            div_le_div_of_nonneg_right (by linarith) (by positivity)
        _ ≤ 4 / Real.sqrt r := by
            rw [mul_one]
            exact div_le_div_of_nonneg_left (by norm_num) hsr h2m
    have hpx0 : 0 ≤ p x := dyPiece_nonneg hr0 y m x
    have hpx1 : p x ≤ 1 := dyPiece_le_one (r := r) y m x
    have e : dyCoeff σ C r R y i k m (x + unit j) - dyCoeff σ C r R y i k m x =
        (p (x + unit j) - p x) * Q (x + unit j) + p x * (Q (x + unit j) - Q x) := by
      simp only [dyCoeff, hQ, hp]
      ring
    rw [e]
    -- the two Gaussian factors, bounded by the decay factor of the scale
    have key : ∀ δ : ℝ, (p x ≠ 0 ∨ p (x + unit j) ≠ 0 →
        Real.exp (-(latticeDist (x + unit j) y ^ 2 / (64 * σ * r))) ≤ δ ∧
          Real.exp (-(latticeDist x y ^ 2 / (256 * σ * r))) ≤ δ) → 0 ≤ δ →
        |(p (x + unit j) - p x) * Q (x + unit j) + p x * (Q (x + unit j) - Q x)| ≤
          (4 * K₂ + K₃) / (r ^ 2 * Real.sqrt r) * δ := by
      intro δ hδ hδ0
      by_cases h0 : p x = 0 ∧ p (x + unit j) = 0
      · rw [h0.1, h0.2]
        simp only [sub_self, zero_mul, add_zero, abs_zero]
        positivity
      · have hor : p x ≠ 0 ∨ p (x + unit j) ≠ 0 := by
          by_contra hc
          push Not at hc
          exact h0 hc
        obtain ⟨hd1, hd2⟩ := hδ hor
        refine (abs_add_le _ _).trans ?_
        have t1 : |(p (x + unit j) - p x) * Q (x + unit j)| ≤
            4 / Real.sqrt r * (K₂ / r ^ 2 * δ) := by
          rw [abs_mul]
          exact mul_le_mul hpd (hP1.trans (mul_le_mul_of_nonneg_left hd1 (by positivity)))
            (abs_nonneg _) (by positivity)
        have t2 : |p x * (Q (x + unit j) - Q x)| ≤ 1 * (K₃ / (r ^ 2 * Real.sqrt r) * δ) := by
          rw [abs_mul, abs_of_nonneg hpx0]
          exact mul_le_mul hpx1 (hP2.trans (mul_le_mul_of_nonneg_left hd2 (by positivity)))
            (abs_nonneg _) zero_le_one
        have e2 : (4 * K₂ + K₃) / (r ^ 2 * Real.sqrt r) * δ =
            4 / Real.sqrt r * (K₂ / r ^ 2 * δ) + 1 * (K₃ / (r ^ 2 * Real.sqrt r) * δ) := by
          field_simp
        rw [e2]
        linarith
    cases m with
    | zero =>
      exact key 1 (fun _ => ⟨exp_neg_sq_le_one _ (by positivity),
        exp_neg_sq_le_one _ (by positivity)⟩) zero_le_one
    | succ m =>
      refine key _ (fun hor => ?_) (dyDecay_nonneg σ _)
      have hΔ := abs_le.1 (abs_latticeDist_add_unit_sub_le x y j)
      have hs : 4 ^ m * r / 2 - 1 ≤ latticeDist (x + unit j) y ^ 2 ∧
          4 ^ m * r / 2 - 1 ≤ latticeDist x y ^ 2 := by
        rcases hor with h | h
        · exact ⟨sq_latticeDist_ge_of_dyPiece_ne hr h (by linarith),
            sq_latticeDist_ge_of_dyPiece_ne hr h (by linarith)⟩
        · exact ⟨sq_latticeDist_ge_of_dyPiece_ne hr h (by linarith),
            sq_latticeDist_ge_of_dyPiece_ne hr h (by linarith)⟩
      exact ⟨exp_neg_le_dyDecay hσ le_rfl (by linarith) hr hs.1,
        exp_neg_le_dyDecay hσ (by linarith) le_rfl hr hs.2⟩

/-- An open neighbour is at distance at most `1`. -/
theorem latticeDist_le_of_adj {ω : Configuration 2} {x z : Vertex 2} (h : (openGraph ω).Adj x z)
    (y : Vertex 2) : latticeDist z y ≤ latticeDist x y + 1 := by
  have := norm_edz_le_length (SimpleGraph.Walk.cons h (SimpleGraph.Walk.nil :
    (openGraph ω).Walk z z))
  have h1 : ‖edz x z‖ ≤ 1 := by simpa using this
  have h1' : latticeDist x z ≤ 1 := h1
  have := latticeDist_triangle z x y
  have := latticeDist_comm x z
  linarith

/-- **The support of the pieces**: `A_m u ≠ 0` with `u` vanishing off the cluster forces
`x ∈ int_a(𝒞 ∩ B_{2^{m+2} √r}(y))`. -/
theorem dyCoeff_support {ω : Configuration 2} (K : OpenComponent ω) {σ C r R : ℝ} (hr : 1 ≤ r)
    {y : Vertex 2} {i k : Fin 2} {m : ℕ} {u : Vertex 2 → ℝ} (hu : ∀ x, x ∉ K.supp → u x = 0)
    (x : Vertex 2) (hx : dyCoeff σ C r R y i k m x * u x ≠ 0) :
    x ∈ clusterBall K y (2 ^ (m + 2) * Real.sqrt r) ∧
      x ∈ openInterior ω (clusterBall K y (2 ^ (m + 2) * Real.sqrt r)) := by
  have hr0 : 0 < r := by linarith
  have hxK : x ∈ K.supp := by
    by_contra h
    exact hx (by rw [hu x h, mul_zero])
  have hp : dyPiece r y m x ≠ 0 := by
    intro h
    apply hx
    unfold dyCoeff
    rw [h, zero_mul, zero_mul]
  have hd : latticeDist x y < 2 ^ (m + 1) * Real.sqrt r := by
    by_contra h
    exact hp (dyPiece_eq_zero_of_le hr0 (not_lt.1 h))
  have h1 := one_le_two_pow_mul_sqrt hr (m + 1)
  have h2 : 2 ^ (m + 2) * Real.sqrt r = 2 * (2 ^ (m + 1) * Real.sqrt r) := by ring
  have hmem : x ∈ clusterBall K y (2 ^ (m + 2) * Real.sqrt r) :=
    (mem_clusterBall K y x _).2 ⟨hxK, by linarith⟩
  refine ⟨hmem, hmem, fun z hz => (mem_clusterBall K y z _).2
    ⟨K.mem_supp_of_adj_mem_supp hxK hz, ?_⟩⟩
  have := latticeDist_le_of_adj hz y
  linarith

end Rigidity.Green
