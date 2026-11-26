import Rigidity.Proofs.Green.GeneralTwoScaleFluxScale
import Rigidity.Proofs.Green.DarioGuTwoScaleFluxBound
import Rigidity.Proofs.WeakPoincare.Balls

/-!
# The multiscale estimate of Step 3 of Proposition 4.3 of Dario–Gu on `ℤ^d`

This file proves the estimate (4.33) of Step 3 of the proof of Proposition 4.3 of Dario–Gu (lines
2333-2412 of the source) for one component `(k, i)` of the centered flux on `ℤ^d`, `d ≥ 2`, with
the weight `ψ = 1`: if the weak norm of `g̃_{k,i}` on `𝒞 ∩ B_ρ(y)` is at most `C_f ρ^α` for the
radii `ρ = 2^{m+2} √r` (Proposition 2.13), then

`-Σ_x g̃_{k,i} (D_i D_k p̄) u ≤ L C_f r^{α/2} r^{-d/4} (r^{-3/2} ‖u‖₂ + r^{-1} E(u)^{1/2})`

(`neg_tsum_flux_leD`), the bound `C Ξ₁ ‖∇w‖ + C Ξ₂ ‖w‖` of (4.33) with (4.35). The coefficient of
the `m`-th piece is `A_m = (η_m - η_{m-1}) D_i D_k p̄` (`dyCoeffD`), bounded by
`K r^{-d/2-1}` and `K r^{-d/2-3/2}` times the decay factor `dyDecay σ m` of the annulus
(`abs_dyCoeffD_le`, `abs_dyCoeffD_sub_le`); it vanishes outside `int_a(𝒞 ∩ B_{2^{m+2}√r}(y))`
(`dyCoeffD_support`); `|𝒞 ∩ B_ρ(y)| ≤ (5ρ)^d`; and the scales are summed with
`sum_dyDecayD_le`: `Σ_m 2^{(m+2)(d+1)} dyDecay σ m` is bounded.
-/

open scoped Classical
open LatticeProb LatticeProb.Percolation

namespace Rigidity.Green.GeneralDim

variable {d : ℕ}

/-! ### Distances of neighbours -/

theorem norm_edzD_add_single_le (x : Vertex d) (j : Fin d) :
    ‖edzD (x + Pi.single j 1) x‖ ≤ 1 := by
  have h : ‖edzD (x + Pi.single j 1) x‖ ^ 2 = 1 := by
    rw [sq_norm_edzD]
    simp only [cast_add_single_apply, add_sub_cancel_left]
    simp
  nlinarith [norm_nonneg (edzD (x + Pi.single j 1) x)]

theorem abs_norm_edzD_add_single_sub_le (x y : Vertex d) (j : Fin d) :
    |‖edzD (x + Pi.single j 1) y‖ - ‖edzD x y‖| ≤ 1 := by
  have e : edzD (x + Pi.single j 1) y - edzD x y = edzD (x + Pi.single j 1) x := by
    simp only [edzD]
    abel
  calc |‖edzD (x + Pi.single j 1) y‖ - ‖edzD x y‖|
      ≤ ‖edzD (x + Pi.single j 1) y - edzD x y‖ := abs_norm_sub_norm_le _ _
    _ = ‖edzD (x + Pi.single j 1) x‖ := by rw [e]
    _ ≤ 1 := norm_edzD_add_single_le x j

/-- An open neighbour is at distance at most `1`. -/
theorem norm_edzD_le_of_adj {ω : Configuration d} {x z : Vertex d} (h : (openGraph ω).Adj x z)
    (y : Vertex d) : ‖edzD z y‖ ≤ ‖edzD x y‖ + 1 := by
  obtain ⟨i, hi | hi⟩ := LatticeProb.Graph.Zd.adj_iff.mp (openGraph_le ω h)
  · simp only [LatticeProb.unit] at hi
    subst hi
    have := abs_norm_edzD_add_single_sub_le x y i
    rw [abs_le] at this
    linarith
  · simp only [LatticeProb.unit] at hi
    subst hi
    have h1 : edzD (x - Pi.single i 1) y = edzD (x - Pi.single i 1) x + edzD x y := by
      simp only [edzD]
      abel
    have h2 : ‖edzD (x - Pi.single i 1) x‖ ≤ 1 := by
      have := norm_edzD_add_single_le (x - Pi.single i 1) i
      rw [sub_add_cancel] at this
      rw [norm_sub_rev]
      exact this
    rw [h1]
    refine (norm_add_le _ _).trans ?_
    linarith

/-! ### The pieces -/

/-- The coefficient `A_m = dyPieceD r y m · D_i D_k p̄` of the `m`-th piece. -/
noncomputable def dyCoeffD (σ r : ℝ) (y : Vertex d) (i k : Fin d) (m : ℕ) (x : Vertex d) : ℝ :=
  dyPieceD r y m x * fwdDiffD i (fwdDiffD k fun z => latticeGaussianD σ r z y) x

/-- On the support of the piece `m + 1`, and at distance at most `1` from it,
`|x - y|² ≥ 4^m r/2 - 1`. -/
theorem sq_norm_ge_of_dyPieceD_ne {r : ℝ} (hr : 1 ≤ r) {x x' y : Vertex d} {m : ℕ}
    (hx : dyPieceD r y (m + 1) x ≠ 0) (hxx' : ‖edzD x y‖ - 1 ≤ ‖edzD x' y‖) :
    4 ^ m * r / 2 - 1 ≤ ‖edzD x' y‖ ^ 2 := by
  have hr0 : 0 < r := by linarith
  have hd : 2 ^ m * Real.sqrt r < ‖edzD x y‖ := by
    by_contra h
    exact hx (dyPieceD_succ_eq_zero_of_le hr0 (not_lt.1 h))
  have ha := one_le_two_pow_mul_sqrt hr m
  have hsq := sq_two_pow_mul_sqrt hr0.le m
  set a := (2 : ℝ) ^ m * Real.sqrt r
  have h1 : a - 1 ≤ ‖edzD x' y‖ := by linarith
  have h2 : (a - 1) ^ 2 ≤ ‖edzD x' y‖ ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
  nlinarith [sq_nonneg (a - 2)]

/-- The Gaussian factor on the support of the piece `m`. -/
theorem exp_neg_le_of_dyPieceD {σ r : ℝ} (hσ : 0 < σ) (hr : 1 ≤ r) {x x' y : Vertex d}
    {m : ℕ} (hp : dyPieceD r y m x ≠ 0) (hxx' : ‖edzD x y‖ - 1 ≤ ‖edzD x' y‖) :
    Real.exp (-(‖edzD x' y‖ ^ 2 / (32 * σ * r))) ≤ dyDecay σ m := by
  have hr0 : 0 < r := by linarith
  have hmono : Real.exp (-(‖edzD x' y‖ ^ 2 / (32 * σ * r))) ≤
      Real.exp (-(‖edzD x' y‖ ^ 2 / (64 * σ * r))) := by
    rw [Real.exp_le_exp, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by nlinarith)
  cases m with
  | zero =>
    simp only [dyDecay]
    exact Real.exp_le_one_iff.2 (neg_nonpos.2 (by positivity))
  | succ m =>
    exact hmono.trans (exp_neg_le_dyDecay hσ le_rfl (by linarith) hr
      (sq_norm_ge_of_dyPieceD_ne hr hp hxx'))

/-- **The bound of the coefficients of the pieces.** -/
theorem abs_dyCoeffD_le {σ r : ℝ} (hσ : 0 < σ) (hr : 1 ≤ r) (y : Vertex d) (i k : Fin d) (m : ℕ)
    (x : Vertex d) :
    |dyCoeffD σ r y i k m x| ≤ gaussConstD d σ 2 * r ^ (-((d : ℝ) / 2)) / r * dyDecay σ m := by
  have hr0 : 0 < r := by linarith
  have hg := gaussConstD_pos (d := d) hσ 2
  have hp0 := dyPieceD_nonneg hr0 y m x
  have hp1 := dyPieceD_le_one (r := r) y m x
  unfold dyCoeffD
  rw [abs_mul, abs_of_nonneg hp0]
  by_cases hpx : dyPieceD r y m x = 0
  · rw [hpx, zero_mul]
    exact mul_nonneg (by positivity) (dyDecay_nonneg σ m)
  · have hQ := abs_fwdDiffD_fwdDiffD_latticeGaussianD_le hσ hr i k x y
    have hdec := exp_neg_le_of_dyPieceD hσ hr hpx (x' := x) (by linarith)
    calc dyPieceD r y m x * |fwdDiffD i (fwdDiffD k fun z => latticeGaussianD σ r z y) x|
        ≤ 1 * (gaussConstD d σ 2 * r ^ (-((d : ℝ) / 2)) / r * dyDecay σ m) :=
          mul_le_mul hp1 (hQ.trans (mul_le_mul_of_nonneg_left hdec (by positivity)))
            (abs_nonneg _) zero_le_one
      _ = _ := one_mul _

/-- **The bound of the differences of the coefficients of the pieces.** -/
theorem abs_dyCoeffD_sub_le {σ r : ℝ} (hσ : 0 < σ) (hr : 1 ≤ r) (y : Vertex d) (i k : Fin d)
    (m : ℕ) (x : Vertex d) (j : Fin d) :
    |dyCoeffD σ r y i k m (x + Pi.single j 1) - dyCoeffD σ r y i k m x| ≤
      (4 * gaussConstD d σ 2 + gaussConstD d σ 3) * r ^ (-((d : ℝ) / 2)) / (r * Real.sqrt r) *
        dyDecay σ m := by
  have hr0 : 0 < r := by linarith
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.2 hr0
  have hg2 := gaussConstD_pos (d := d) hσ 2
  have hg3 := gaussConstD_pos (d := d) hσ 3
  have hR : 0 < r ^ (-((d : ℝ) / 2)) := by positivity
  have hδ0 := dyDecay_nonneg σ m
  set Q := fwdDiffD i (fwdDiffD k fun z => latticeGaussianD σ r z y) with hQ
  set p := dyPieceD r y m with hp
  have hΔ := abs_le.1 (abs_norm_edzD_add_single_sub_le x y j)
  have hpd : |p (x + Pi.single j 1) - p x| ≤ 4 / Real.sqrt r := by
    refine (abs_dyPieceD_sub_le hr0 y x (x + Pi.single j 1) m).trans ?_
    have h2m : Real.sqrt r ≤ 2 ^ m * Real.sqrt r := by
      have : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
      nlinarith
    calc 4 * |‖edzD (x + Pi.single j 1) y‖ - ‖edzD x y‖| / (2 ^ m * Real.sqrt r)
        ≤ 4 * 1 / (2 ^ m * Real.sqrt r) :=
          div_le_div_of_nonneg_right (by linarith [abs_norm_edzD_add_single_sub_le x y j])
            (by positivity)
      _ ≤ 4 / Real.sqrt r := by
          rw [mul_one]
          exact div_le_div_of_nonneg_left (by norm_num) hsr h2m
  have hpx0 : 0 ≤ p x := dyPieceD_nonneg hr0 y m x
  have hpx1 : p x ≤ 1 := dyPieceD_le_one (r := r) y m x
  have e : dyCoeffD σ r y i k m (x + Pi.single j 1) - dyCoeffD σ r y i k m x =
      (p (x + Pi.single j 1) - p x) * Q (x + Pi.single j 1) +
        p x * (Q (x + Pi.single j 1) - Q x) := by
    simp only [dyCoeffD, hQ, hp]
    ring
  rw [e]
  by_cases h0 : p x = 0 ∧ p (x + Pi.single j 1) = 0
  · rw [h0.1, h0.2]
    simp only [sub_self, zero_mul, add_zero, abs_zero]
    positivity
  · have hor : p x ≠ 0 ∨ p (x + Pi.single j 1) ≠ 0 := by
      by_contra hc
      push Not at hc
      exact h0 hc
    have hd1 : Real.exp (-(‖edzD (x + Pi.single j 1) y‖ ^ 2 / (32 * σ * r))) ≤ dyDecay σ m := by
      rcases hor with h | h
      · exact exp_neg_le_of_dyPieceD hσ hr h (by linarith)
      · exact exp_neg_le_of_dyPieceD hσ hr h (by linarith)
    have hd2 : Real.exp (-(‖edzD x y‖ ^ 2 / (32 * σ * r))) ≤ dyDecay σ m := by
      rcases hor with h | h
      · exact exp_neg_le_of_dyPieceD hσ hr h (by linarith)
      · exact exp_neg_le_of_dyPieceD hσ hr h (by linarith)
    have hP1 := abs_fwdDiffD_fwdDiffD_latticeGaussianD_le hσ hr i k (x + Pi.single j 1) y
    have hP2 := abs_fwdDiffD3_latticeGaussianD_le hσ hr j i k x y
    refine (abs_add_le _ _).trans ?_
    have t1 : |(p (x + Pi.single j 1) - p x) * Q (x + Pi.single j 1)| ≤
        4 / Real.sqrt r * (gaussConstD d σ 2 * r ^ (-((d : ℝ) / 2)) / r * dyDecay σ m) := by
      rw [abs_mul]
      exact mul_le_mul hpd (hP1.trans (mul_le_mul_of_nonneg_left hd1 (by positivity)))
        (abs_nonneg _) (by positivity)
    have t2 : |p x * (Q (x + Pi.single j 1) - Q x)| ≤
        1 * (gaussConstD d σ 3 * r ^ (-((d : ℝ) / 2)) / (r * Real.sqrt r) * dyDecay σ m) := by
      rw [abs_mul, abs_of_nonneg hpx0]
      exact mul_le_mul hpx1 (hP2.trans (mul_le_mul_of_nonneg_left hd2 (by positivity)))
        (abs_nonneg _) zero_le_one
    have e2 : (4 * gaussConstD d σ 2 + gaussConstD d σ 3) * r ^ (-((d : ℝ) / 2)) /
        (r * Real.sqrt r) * dyDecay σ m =
        4 / Real.sqrt r * (gaussConstD d σ 2 * r ^ (-((d : ℝ) / 2)) / r * dyDecay σ m) +
          1 * (gaussConstD d σ 3 * r ^ (-((d : ℝ) / 2)) / (r * Real.sqrt r) * dyDecay σ m) := by
      field_simp
    rw [e2]
    linarith

/-- **The support of the pieces**: `A_m u ≠ 0` with `u` vanishing off the cluster forces
`x ∈ int_a(𝒞 ∩ B_{2^{m+2} √r}(y))`. -/
theorem dyCoeffD_support {ω : Configuration d} (K : OpenComponent ω) {σ r : ℝ} (hr : 1 ≤ r)
    {y : Vertex d} {i k : Fin d} {m : ℕ} {u : Vertex d → ℝ} (hu : ∀ x, x ∉ K.supp → u x = 0)
    (x : Vertex d) (hx : dyCoeffD σ r y i k m x * u x ≠ 0) :
    x ∈ dgClusterBallD K y (2 ^ (m + 2) * Real.sqrt r) ∧
      x ∈ openInteriorD ω (dgClusterBallD K y (2 ^ (m + 2) * Real.sqrt r)) := by
  have hr0 : 0 < r := by linarith
  have hxK : x ∈ K.supp := by
    by_contra h
    exact hx (by rw [hu x h, mul_zero])
  have hp : dyPieceD r y m x ≠ 0 := by
    intro h
    apply hx
    unfold dyCoeffD
    rw [h, zero_mul, zero_mul]
  have hd : ‖edzD x y‖ < 2 ^ (m + 1) * Real.sqrt r := by
    by_contra h
    exact hp (dyPieceD_eq_zero_of_le hr0 (not_lt.1 h))
  have h1 := one_le_two_pow_mul_sqrt hr (m + 1)
  have h2 : 2 ^ (m + 2) * Real.sqrt r = 2 * (2 ^ (m + 1) * Real.sqrt r) := by ring
  have hmem : x ∈ dgClusterBallD K y (2 ^ (m + 2) * Real.sqrt r) :=
    (mem_dgClusterBallD K y x _).2 ⟨hxK, by rw [dist_eq_norm]; linarith⟩
  refine ⟨hmem, hmem, fun z hz => (mem_dgClusterBallD K y z _).2
    ⟨K.mem_supp_of_adj_mem_supp hxK hz, ?_⟩⟩
  have := norm_edzD_le_of_adj hz y
  rw [dist_eq_norm]
  linarith

theorem dgClusterBallD_eq_clusterBall {ω : Configuration d} (K : OpenComponent ω) (y : Vertex d)
    (ρ : ℝ) : dgClusterBallD K y ρ = Rigidity.WeakPoincare.clusterBall K y ρ := by
  ext x
  rw [mem_dgClusterBallD, Rigidity.WeakPoincare.mem_clusterBall, dist_eq_norm]
  rfl

/-- `|𝒞 ∩ B_ρ(y)| ≤ (5ρ)^d` for `ρ ≥ 1`. -/
theorem card_dgClusterBallD_le {ω : Configuration d} (K : OpenComponent ω) (y : Vertex d)
    {ρ : ℝ} (hρ : 1 ≤ ρ) : ((dgClusterBallD K y ρ).card : ℝ) ≤ (5 * ρ) ^ d := by
  rw [dgClusterBallD_eq_clusterBall]
  exact Rigidity.WeakPoincare.card_clusterBall_le K y hρ

/-! ### The powers of the radii -/

theorem radius_rpow_le {r : ℝ} (hr : 1 ≤ r) (m : ℕ) :
    (5 * (2 ^ (m + 2) * Real.sqrt r)) ^ ((d : ℝ) / 2) ≤
      5 ^ d * 2 ^ ((m + 2) * d) * r ^ ((d : ℝ) / 4) := by
  have hr0 : 0 < r := by linarith
  have hb : (1 : ℝ) ≤ 5 * 2 ^ (m + 2) := by
    have : (1 : ℝ) ≤ 2 ^ (m + 2) := one_le_pow₀ (by norm_num)
    linarith
  rw [show 5 * (2 ^ (m + 2) * Real.sqrt r) = (5 * 2 ^ (m + 2)) * Real.sqrt r by ring,
    Real.mul_rpow (by positivity) (Real.sqrt_nonneg r)]
  have h1 : ((5 : ℝ) * 2 ^ (m + 2)) ^ ((d : ℝ) / 2) ≤ 5 ^ d * 2 ^ ((m + 2) * d) := by
    calc ((5 : ℝ) * 2 ^ (m + 2)) ^ ((d : ℝ) / 2) ≤ ((5 : ℝ) * 2 ^ (m + 2)) ^ (d : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hb (by
            have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
            linarith)
      _ = 5 ^ d * 2 ^ ((m + 2) * d) := by
          rw [Real.rpow_natCast, mul_pow, pow_mul]
  have h2 : Real.sqrt r ^ ((d : ℝ) / 2) = r ^ ((d : ℝ) / 4) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hr0.le]
    ring_nf
  rw [h2]
  exact mul_le_mul_of_nonneg_right h1 (by positivity)

theorem radius_pow_bounds (hd : 2 ≤ d) {r : ℝ} (hr : 1 ≤ r) (m : ℕ) :
    ((5 * (2 ^ (m + 2) * Real.sqrt r)) ^ d) ^ ((1 : ℝ) / 2 - 1 / d) ≤
        5 ^ d * 2 ^ ((m + 2) * d) * r ^ ((d : ℝ) / 4) / Real.sqrt r ∧
      Real.sqrt ((5 * (2 ^ (m + 2) * Real.sqrt r)) ^ d) ≤
        5 ^ d * 2 ^ ((m + 2) * d) * r ^ ((d : ℝ) / 4) := by
  have hr0 : 0 < r := by linarith
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.2 hr0
  set R := 5 * (2 ^ (m + 2) * Real.sqrt r) with hRdef
  have hR0 : 0 < R := by positivity
  have hRr : Real.sqrt r ≤ R := by
    have : (1 : ℝ) ≤ 2 ^ (m + 2) := one_le_pow₀ (by norm_num)
    rw [hRdef]
    nlinarith
  have hd0 : (d : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hmain := radius_rpow_le (d := d) hr m
  rw [← hRdef] at hmain
  constructor
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hR0.le,
      show (d : ℝ) * (1 / 2 - 1 / d) = (d : ℝ) / 2 - 1 by field_simp, Real.rpow_sub_one hR0.ne']
    exact div_le_div₀ (by positivity) hmain hsr hRr
  · rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hR0.le,
      show (d : ℝ) * (1 / 2) = (d : ℝ) / 2 by ring]
    exact hmain

/-! ### The sum over the scales -/

/-- The bound of the weighted sum of the decay factors of the scales. -/
noncomputable def dyDecaySumD (d : ℕ) (σ : ℝ) : ℝ :=
  2 ^ (2 * (d + 1)) + 2 * (Real.exp (1 / (64 * σ)) * 2 ^ (3 * (d + 1)) * (d + 2).factorial *
    (512 * σ) ^ (d + 2))

theorem dyDecay_succ_le {σ : ℝ} (hσ : 0 < σ) (m : ℕ) :
    (2 : ℝ) ^ ((m + 1 + 2) * (d + 1)) * dyDecay σ (m + 1) ≤
      Real.exp (1 / (64 * σ)) * 2 ^ (3 * (d + 1)) * (d + 2).factorial * (512 * σ) ^ (d + 2) *
        (1 / 2) ^ m := by
  set t : ℝ := 2 ^ m with ht
  have ht1 : 1 ≤ t := one_le_pow₀ (by norm_num)
  have ht0 : 0 < t := by linarith
  set x : ℝ := (4 : ℝ) ^ m / (512 * σ) with hx
  have h4 : (4 : ℝ) ^ m = t ^ 2 := by rw [ht, ← pow_mul, mul_comm, pow_mul]; norm_num
  have hx0 : 0 < x := by positivity
  have hexp : Real.exp (-x) ≤ (d + 2).factorial / x ^ (d + 2) := by
    have h := Real.pow_div_factorial_le_exp x hx0.le (d + 2)
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity), inv_div]
    exact h
  have e2 : (2 : ℝ) ^ ((m + 1 + 2) * (d + 1)) = 2 ^ (3 * (d + 1)) * t ^ (d + 1) := by
    rw [ht, ← pow_mul, ← pow_add]
    congr 1
    ring
  simp only [dyDecay]
  rw [e2]
  have hfac : (0 : ℝ) < (d + 2).factorial := by exact_mod_cast Nat.factorial_pos _
  have key : t ^ (d + 1) * ((d + 2).factorial / x ^ (d + 2)) ≤
      (d + 2).factorial * (512 * σ) ^ (d + 2) * (1 / 2) ^ m := by
    have hxe : x ^ (d + 2) = t ^ (2 * (d + 2)) / (512 * σ) ^ (d + 2) := by
      rw [hx, h4, div_pow, ← pow_mul]
    rw [hxe]
    have hpow : t ^ (d + 1) * (1 / t ^ (2 * (d + 2))) ≤ 1 / t := by
      have e3 : t ^ (2 * (d + 2)) = t ^ (d + 1) * t ^ (d + 3) := by
        rw [← pow_add]
        congr 1
        ring
      rw [e3, one_div, mul_inv, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul, one_div]
      exact inv_anti₀ ht0 (le_self_pow₀ ht1 (by omega))
    have e4 : (1 / 2 : ℝ) ^ m = 1 / t := by rw [ht, one_div_pow]
    rw [e4]
    have e5 : t ^ (d + 1) * ((d + 2).factorial / (t ^ (2 * (d + 2)) / (512 * σ) ^ (d + 2))) =
        (d + 2).factorial * (512 * σ) ^ (d + 2) * (t ^ (d + 1) * (1 / t ^ (2 * (d + 2)))) := by
      field_simp
    rw [e5]
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  have hE := Real.exp_pos (1 / (64 * σ))
  calc 2 ^ (3 * (d + 1)) * t ^ (d + 1) * (Real.exp (1 / (64 * σ)) * Real.exp (-x))
      ≤ 2 ^ (3 * (d + 1)) * t ^ (d + 1) *
          (Real.exp (1 / (64 * σ)) * ((d + 2).factorial / x ^ (d + 2))) := by
        gcongr
    _ = Real.exp (1 / (64 * σ)) * 2 ^ (3 * (d + 1)) *
          (t ^ (d + 1) * ((d + 2).factorial / x ^ (d + 2))) := by ring
    _ ≤ Real.exp (1 / (64 * σ)) * 2 ^ (3 * (d + 1)) *
          ((d + 2).factorial * (512 * σ) ^ (d + 2) * (1 / 2) ^ m) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = _ := by ring

/-- **The sum of the scales**: `Σ_{m ≤ M} 2^{(m+2)(d+1)} dyDecay σ m ≤ dyDecaySumD d σ`. -/
theorem sum_dyDecayD_le {σ : ℝ} (hσ : 0 < σ) (M : ℕ) :
    ∑ m ∈ Finset.range (M + 1), (2 : ℝ) ^ ((m + 2) * (d + 1)) * dyDecay σ m ≤
      dyDecaySumD d σ := by
  set A := Real.exp (1 / (64 * σ)) * 2 ^ (3 * (d + 1)) * (d + 2).factorial * (512 * σ) ^ (d + 2)
    with hA
  have hA0 : 0 ≤ A := by positivity
  rw [Finset.sum_range_succ']
  have hs : ∑ m ∈ Finset.range M, (2 : ℝ) ^ ((m + 1 + 2) * (d + 1)) * dyDecay σ (m + 1) ≤
      2 * A := by
    calc ∑ m ∈ Finset.range M, (2 : ℝ) ^ ((m + 1 + 2) * (d + 1)) * dyDecay σ (m + 1)
        ≤ ∑ m ∈ Finset.range M, A * (1 / 2 : ℝ) ^ m :=
          Finset.sum_le_sum fun m _ => dyDecay_succ_le hσ m
      _ = A * ∑ m ∈ Finset.range M, (1 / 2 : ℝ) ^ m := by rw [Finset.mul_sum]
      _ ≤ A * 2 := by
          refine mul_le_mul_of_nonneg_left ?_ hA0
          rw [Finset.range_eq_Ico]
          refine (geom_sum_Ico_le_of_lt_one (by norm_num) (by norm_num)).trans ?_
          norm_num
      _ = 2 * A := mul_comm _ _
  have h0 : (2 : ℝ) ^ ((0 + 2) * (d + 1)) * dyDecay σ 0 = 2 ^ (2 * (d + 1)) := by
    simp [dyDecay]
  rw [h0]
  unfold dyDecaySumD
  rw [← hA]
  linarith

/-! ### Step 3 for one component of the flux -/

/-- **Step 3 for one component of the flux** on `ℤ^d` ((4.33) with (4.35)). -/
theorem neg_tsum_flux_leD (hd : 2 ≤ d) {σ : ℝ} (hσ : 0 < σ) : ∃ L : ℝ, 0 < L ∧
    ∀ (ω : Configuration d) (K : OpenComponent ω) (y : Vertex d) (χ : Fin d → Vertex d → ℝ)
      (k i : Fin d) (Cf α r : ℝ) (u : Vertex d → ℝ),
      0 ≤ Cf → 0 < α → α ≤ 1 → 1 ≤ r → Summable (fun x => u x ^ 2) →
      (∀ x, x ∉ K.supp → u x = 0) →
      (∀ m : ℕ, WeakNormLeD ω (dgClusterBallD K y (2 ^ (m + 2) * Real.sqrt r))
        (centeredFluxD ω σ χ k i) (Cf * (2 ^ (m + 2) * Real.sqrt r) ^ α)) →
      Summable (fun x => |centeredFluxD ω σ χ k i x *
        (fwdDiffD i (fwdDiffD k fun z => latticeGaussianD σ r z y) x * u x)|) →
      -(∑' x, centeredFluxD ω σ χ k i x *
        (fwdDiffD i (fwdDiffD k fun z => latticeGaussianD σ r z y) x * u x)) ≤
        L * Cf * r ^ (α / 2) * r ^ (-((d : ℝ) / 4)) *
          (Real.sqrt (∑' x, u x ^ 2) / (r * Real.sqrt r) +
            Real.sqrt (openEnergyD ω u) / r) := by
  set Ka := gaussConstD d σ 2 with hKa
  set Kb := 4 * gaussConstD d σ 2 + gaussConstD d σ 3 with hKb
  have hKa0 : 0 < Ka := gaussConstD_pos hσ 2
  have hKb0 : 0 < Kb := by have := gaussConstD_pos (d := d) hσ 3; positivity
  set S₀ := dyDecaySumD d σ with hS₀
  have hS₀0 : 0 < S₀ := by
    rw [hS₀]
    unfold dyDecaySumD
    have : (0 : ℝ) < (d + 2).factorial := by exact_mod_cast Nat.factorial_pos _
    positivity
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  set Kt := Ka + 3 * d * Kb + 3 * Real.sqrt d * Ka with hKt
  have hKt0 : 0 < Kt := by positivity
  refine ⟨5 ^ d * Kt * S₀, by positivity,
    fun ω K y χ k i Cf α r u hCf hα hα1 hr hu huK hW hGW => ?_⟩
  have hr0 : 0 < r := by linarith
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.2 hr0
  set U := Real.sqrt (∑' x, u x ^ 2) with hU
  set E := Real.sqrt (openEnergyD ω u) with hE
  have hU0 : 0 ≤ U := Real.sqrt_nonneg _
  have hE0 : 0 ≤ E := Real.sqrt_nonneg _
  set q := r ^ (-((d : ℝ) / 2)) with hq
  have hq0 : 0 < q := by positivity
  set W : Vertex d → ℝ := fun x => fwdDiffD i (fwdDiffD k fun z => latticeGaussianD σ r z y) x *
    u x with hWdef
  set ρ : ℕ → ℝ := fun m => (2 : ℝ) ^ (m + 2) * Real.sqrt r with hρ
  have hρ1 : ∀ m, 1 ≤ ρ m := fun m => one_le_two_pow_mul_sqrt hr (m + 2)
  set T := Ka * U / (r * Real.sqrt r) + 3 * Real.sqrt d * Ka * E / r +
    3 * d * Kb * U / (r * Real.sqrt r) with hT
  have hT0 : 0 ≤ T := by positivity
  set c : ℕ → ℝ := fun m => Cf * ρ m ^ α *
    (((5 * ρ m) ^ d) ^ ((1 : ℝ) / 2 - 1 / d) * ((Ka * q / r * dyDecay σ m) * U) +
      Real.sqrt ((5 * ρ m) ^ d) * (3 * Real.sqrt d * (Ka * q / r * dyDecay σ m) * E +
        3 * d * (Kb * q / (r * Real.sqrt r) * dyDecay σ m) * U)) with hc
  have hpieceEq : ∀ m x, centeredFluxD ω σ χ k i x * (dyPieceD r y m x * W x) =
      centeredFluxD ω σ χ k i x * (dyCoeffD σ r y i k m x * u x) := by
    intro m x
    simp only [hWdef, dyCoeffD]
    ring
  have hpiece : ∀ m, Summable fun x => centeredFluxD ω σ χ k i x * (dyPieceD r y m x * W x) := by
    intro m
    refine summable_of_ne_finset_zero (s := dgClusterBallD K y (ρ m)) fun x hx => ?_
    rw [hpieceEq]
    by_contra h0
    have h1 : dyCoeffD σ r y i k m x * u x ≠ 0 := fun h => h0 (by rw [h, mul_zero])
    exact hx (dyCoeffD_support K hr huK x h1).1
  have hcm : ∀ m, -(∑' x, centeredFluxD ω σ χ k i x * (dyPieceD r y m x * W x)) ≤ c m := by
    intro m
    rw [tsum_congr (hpieceEq m)]
    exact neg_tsum_le_of_weakNormLe_coeffD hd (hW m) (by have := hρ1 m; positivity)
      (card_dgClusterBallD_le K y (hρ1 m)) hu (fun x => abs_dyCoeffD_le hσ hr y i k m x)
      (fun x j => abs_dyCoeffD_sub_le hσ hr y i k m x j) (dyCoeffD_support K hr huK)
  have hcle : ∀ m, c m ≤ Cf * r ^ (α / 2) * r ^ (-((d : ℝ) / 4)) * T * 5 ^ d *
      ((2 : ℝ) ^ ((m + 2) * (d + 1)) * dyDecay σ m) := by
    intro m
    have hδ := dyDecay_nonneg σ m
    have hρα := rpow_two_pow_mul_sqrt_le hr0.le hα1 m
    obtain ⟨hΛ1, hΛ2⟩ := radius_pow_bounds hd hr m
    set P := (5 : ℝ) ^ d * 2 ^ ((m + 2) * d) with hP
    have hP0 : 0 ≤ P := by positivity
    set X := ((5 * ρ m) ^ d) ^ ((1 : ℝ) / 2 - 1 / d) * ((Ka * q / r * dyDecay σ m) * U) +
      Real.sqrt ((5 * ρ m) ^ d) * (3 * Real.sqrt d * (Ka * q / r * dyDecay σ m) * E +
        3 * d * (Kb * q / (r * Real.sqrt r) * dyDecay σ m) * U) with hX
    have hX0 : 0 ≤ X := by
      have : 0 ≤ ((5 * ρ m) ^ d) ^ ((1 : ℝ) / 2 - 1 / d) :=
        Real.rpow_nonneg (by have := hρ1 m; positivity) _
      positivity
    have hrq : r ^ ((d : ℝ) / 4) * q = r ^ (-((d : ℝ) / 4)) := by
      rw [hq, ← Real.rpow_add hr0]
      ring_nf
    have hXle : X ≤ P * r ^ (-((d : ℝ) / 4)) * dyDecay σ m * T := by
      have a1 : ((5 * ρ m) ^ d) ^ ((1 : ℝ) / 2 - 1 / d) * ((Ka * q / r * dyDecay σ m) * U) ≤
          P * r ^ ((d : ℝ) / 4) / Real.sqrt r * ((Ka * q / r * dyDecay σ m) * U) :=
        mul_le_mul_of_nonneg_right hΛ1 (by positivity)
      have a2 : Real.sqrt ((5 * ρ m) ^ d) * (3 * Real.sqrt d * (Ka * q / r * dyDecay σ m) * E +
          3 * d * (Kb * q / (r * Real.sqrt r) * dyDecay σ m) * U) ≤
          P * r ^ ((d : ℝ) / 4) * (3 * Real.sqrt d * (Ka * q / r * dyDecay σ m) * E +
            3 * d * (Kb * q / (r * Real.sqrt r) * dyDecay σ m) * U) :=
        mul_le_mul_of_nonneg_right hΛ2 (by positivity)
      have e : P * r ^ ((d : ℝ) / 4) / Real.sqrt r * ((Ka * q / r * dyDecay σ m) * U) +
          P * r ^ ((d : ℝ) / 4) * (3 * Real.sqrt d * (Ka * q / r * dyDecay σ m) * E +
            3 * d * (Kb * q / (r * Real.sqrt r) * dyDecay σ m) * U) =
          P * (r ^ ((d : ℝ) / 4) * q) * dyDecay σ m * T := by
        rw [hT]
        field_simp
        ring
      rw [hrq] at e
      rw [hX]
      linarith
    have h2 : (2 : ℝ) ^ ((m + 2) * (d + 1)) = 2 ^ (m + 2) * 2 ^ ((m + 2) * d) := by
      rw [← pow_add]
      congr 1
      ring
    calc c m = Cf * ρ m ^ α * X := rfl
      _ ≤ Cf * (2 ^ (m + 2) * r ^ (α / 2)) * (P * r ^ (-((d : ℝ) / 4)) * dyDecay σ m * T) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hρα hCf) hXle hX0
          exact mul_nonneg hCf (by positivity)
      _ = Cf * r ^ (α / 2) * r ^ (-((d : ℝ) / 4)) * T * 5 ^ d *
          ((2 : ℝ) ^ ((m + 2) * (d + 1)) * dyDecay σ m) := by
          rw [h2, hP]
          ring
  have hS : ∀ M, ∑ m ∈ Finset.range (M + 1), c m ≤
      Cf * r ^ (α / 2) * r ^ (-((d : ℝ) / 4)) * T * 5 ^ d * S₀ := by
    intro M
    calc ∑ m ∈ Finset.range (M + 1), c m
        ≤ ∑ m ∈ Finset.range (M + 1), Cf * r ^ (α / 2) * r ^ (-((d : ℝ) / 4)) * T * 5 ^ d *
            ((2 : ℝ) ^ ((m + 2) * (d + 1)) * dyDecay σ m) := Finset.sum_le_sum fun m _ => hcle m
      _ = Cf * r ^ (α / 2) * r ^ (-((d : ℝ) / 4)) * T * 5 ^ d *
            ∑ m ∈ Finset.range (M + 1), (2 : ℝ) ^ ((m + 2) * (d + 1)) * dyDecay σ m := by
          rw [Finset.mul_sum]
      _ ≤ Cf * r ^ (α / 2) * r ^ (-((d : ℝ) / 4)) * T * 5 ^ d * S₀ :=
          mul_le_mul_of_nonneg_left (sum_dyDecayD_le hσ M) (by positivity)
  have hmain := neg_tsum_le_of_piecesD hr0 hGW hpiece hcm hS
  refine hmain.trans ?_
  have hTle : T ≤ Kt * (U / (r * Real.sqrt r) + E / r) := by
    rw [hT, hKt]
    have a1 : 0 ≤ Ka * U / (r * Real.sqrt r) := by positivity
    have a2 : 0 ≤ 3 * Real.sqrt d * Ka * U / (r * Real.sqrt r) := by positivity
    have a3 : 0 ≤ (Ka + 3 * d * Kb) * E / r := by positivity
    have e : Kt * (U / (r * Real.sqrt r) + E / r) =
        Ka * U / (r * Real.sqrt r) + 3 * Real.sqrt d * Ka * E / r +
          3 * d * Kb * U / (r * Real.sqrt r) +
            (3 * Real.sqrt d * Ka * U / (r * Real.sqrt r) + (Ka + 3 * d * Kb) * E / r) := by
      rw [hKt]
      ring
    rw [← hKt, e]
    linarith
  have hpos : 0 ≤ Cf * r ^ (α / 2) * r ^ (-((d : ℝ) / 4)) := by positivity
  calc Cf * r ^ (α / 2) * r ^ (-((d : ℝ) / 4)) * T * 5 ^ d * S₀
      ≤ Cf * r ^ (α / 2) * r ^ (-((d : ℝ) / 4)) * (Kt * (U / (r * Real.sqrt r) + E / r)) *
          5 ^ d * S₀ := by gcongr
    _ = 5 ^ d * Kt * S₀ * Cf * r ^ (α / 2) * r ^ (-((d : ℝ) / 4)) *
          (U / (r * Real.sqrt r) + E / r) := by ring

end Rigidity.Green.GeneralDim
