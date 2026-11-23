import Rigidity.Proofs.Green.DarioGuGaussian

/-!
# Elementary estimates of the induction of §4.3 of Dario–Gu

* `far_bound`: for `|x - z| ≥ t ≥ 1`, the Carne–Varopoulos bound of `p` (Proposition 2.15) and the
  Gaussian bound of `p̄` give `|p - θ^{-1} p̄| ≤ c t^{-k} Φ_c(t, x - z)` for every `k ∈ [0, 1]`
  (lines 2577-2578 of the source: "otherwise we necessarily have `|x - z| ≥ t` and the inequality
  (4.45) is satisfied by Proposition 2.15 and Remark 2.16").
* `exists_lattice_near_midpoint`: a lattice point within distance `1` of `(x + z)/2`.
* the exponent inequalities (4.42) for `α = δ/2`, `κ = δ/4` (`d = 2`).
-/

open Finset LatticeProb.Percolation

namespace Rigidity.Green

theorem exp_neg_le_two_div_sq {u : ℝ} (hu : 0 < u) : Real.exp (-u) ≤ 2 / u ^ 2 := by
  have h := Real.pow_div_factorial_le_exp u hu.le 2
  norm_num [Nat.factorial] at h
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos u) (by positivity), inv_div]
  exact h

theorem rpow_neg_le_of_le {t a b : ℝ} (ht : 1 ≤ t) (hab : a ≤ b) : t ^ (-b) ≤ t ^ (-a) :=
  Real.rpow_le_rpow_of_exponent_le ht (by linarith)

/-- The far region (Dario–Gu, lines 2577-2578). -/
theorem far_bound {θ σ Ccv : ℝ} (hθ : 0 < θ) (hσ : 0 < σ) (hCcv : 0 < Ccv) :
    ∃ c : ℝ, 0 < c ∧ ∀ t r k a : ℝ, 1 ≤ t → t ≤ r → 0 ≤ k → k ≤ 1 → 0 ≤ a →
      a ≤ Ccv * Real.exp (-(r / Ccv * (1 + Real.log (r / t)))) →
      |a - θ⁻¹ * ((2 * Real.pi * σ * t)⁻¹ * Real.exp (-(r ^ 2 / (2 * σ * t))))| ≤
        c * t ^ (-k) * dgPhi c t r := by
  set c₀ := max (2 * Ccv) (4 * σ) with hc₀
  have hc₀0 : 0 < c₀ := lt_max_of_lt_left (by positivity)
  set Kc := 8 * Ccv ^ 3 + θ⁻¹ * c₀ ^ 2 / (Real.pi * σ)
  refine ⟨max c₀ (Kc / c₀), lt_max_of_lt_left hc₀0, fun t r k a ht htr hk0 hk1 ha0 ha => ?_⟩
  have ht0 : 0 < t := by linarith
  have hr0 : 0 < r := by linarith
  set g := dgShape t r with hg
  have hgdef : g = r * (1 + Real.log (r / t)) := dgShape_of_le ht0 htr
  have hgr : t ≤ g := by
    have hm := min_le_dgShape ht0 hr0.le
    have : min (r ^ 2 / t) r = r := by
      apply min_eq_right
      rw [le_div_iff₀ ht0]; nlinarith
    rw [this] at hm
    linarith
  have hgsq : g ≤ r ^ 2 / t := dgShape_le_sq ht0 hr0.le
  have hg0 : 0 ≤ g := by linarith
  set E := Real.exp (-(g / c₀))
  have htk : t ^ (-(2 : ℝ)) ≤ t ^ (-k) * t⁻¹ := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add ht0]
    exact Real.rpow_le_rpow_of_exponent_le ht (by linarith)
  have htk' : t ^ (-(2 : ℝ)) ≤ t ^ (-k) := rpow_neg_le_of_le ht (by linarith)
  have ht2 : t ^ (-(2 : ℝ)) = 1 / t ^ 2 := by
    rw [Real.rpow_neg ht0.le, one_div]; norm_cast
  -- the heat kernel term
  have hA : a ≤ 8 * Ccv ^ 3 * (t ^ (-k) * t⁻¹) * E := by
    have h1 : Real.exp (-(r / Ccv * (1 + Real.log (r / t)))) ≤
        E * Real.exp (-(t / (2 * Ccv))) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      have hcc : g / c₀ ≤ g / (2 * Ccv) := div_le_div_of_nonneg_left hg0 (by positivity)
        (le_max_left _ _)
      have h2 : r / Ccv * (1 + Real.log (r / t)) = g / (2 * Ccv) + g / (2 * Ccv) := by
        rw [hgdef]; field_simp; ring
      have h3 : t / (2 * Ccv) ≤ g / (2 * Ccv) := div_le_div_of_nonneg_right hgr (by positivity)
      linarith
    have h2 : Real.exp (-(t / (2 * Ccv))) ≤ 8 * Ccv ^ 2 * t ^ (-(2 : ℝ)) := by
      have := exp_neg_le_two_div_sq (u := t / (2 * Ccv)) (by positivity)
      rw [ht2]
      calc Real.exp (-(t / (2 * Ccv))) ≤ 2 / (t / (2 * Ccv)) ^ 2 := this
        _ = 8 * Ccv ^ 2 * (1 / t ^ 2) := by field_simp; ring
    calc a ≤ Ccv * Real.exp (-(r / Ccv * (1 + Real.log (r / t)))) := ha
      _ ≤ Ccv * (E * (8 * Ccv ^ 2 * t ^ (-(2 : ℝ)))) := by
          gcongr
          exact h1.trans (mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le)
      _ ≤ Ccv * (E * (8 * Ccv ^ 2 * (t ^ (-k) * t⁻¹))) := by gcongr
      _ = 8 * Ccv ^ 3 * (t ^ (-k) * t⁻¹) * E := by ring
  -- the Gaussian term
  set b := θ⁻¹ * ((2 * Real.pi * σ * t)⁻¹ * Real.exp (-(r ^ 2 / (2 * σ * t))))
  have hb0 : 0 ≤ b := by positivity
  have hB : b ≤ θ⁻¹ * c₀ ^ 2 / (Real.pi * σ) * (t ^ (-k) * t⁻¹) * E := by
    have h1 : Real.exp (-(r ^ 2 / (2 * σ * t))) ≤ E * Real.exp (-(t / c₀)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      have h4 : 2 * g / c₀ ≤ r ^ 2 / (2 * σ * t) := by
        calc 2 * g / c₀ ≤ 2 * (r ^ 2 / t) / c₀ :=
              div_le_div_of_nonneg_right (by linarith) hc₀0.le
          _ ≤ r ^ 2 / (2 * σ * t) := by
              rw [div_le_div_iff₀ hc₀0 (by positivity)]
              have : 4 * σ ≤ c₀ := le_max_right _ _
              have hr2 : 0 ≤ r ^ 2 / t := by positivity
              have : 2 * (r ^ 2 / t) * (2 * σ * t) = 4 * σ * r ^ 2 := by field_simp; ring
              nlinarith [sq_nonneg r]
      have h5 : t / c₀ ≤ g / c₀ := div_le_div_of_nonneg_right hgr hc₀0.le
      have h6 : 2 * g / c₀ = g / c₀ + g / c₀ := by ring
      linarith
    have h2 : Real.exp (-(t / c₀)) ≤ 2 * c₀ ^ 2 * t ^ (-k) := by
      have := exp_neg_le_two_div_sq (u := t / c₀) (by positivity)
      calc Real.exp (-(t / c₀)) ≤ 2 / (t / c₀) ^ 2 := this
        _ = 2 * c₀ ^ 2 * t ^ (-(2 : ℝ)) := by rw [ht2]; field_simp
        _ ≤ 2 * c₀ ^ 2 * t ^ (-k) := by gcongr
    calc b = θ⁻¹ * ((2 * Real.pi * σ * t)⁻¹ * Real.exp (-(r ^ 2 / (2 * σ * t)))) := rfl
      _ ≤ θ⁻¹ * ((2 * Real.pi * σ * t)⁻¹ * (E * (2 * c₀ ^ 2 * t ^ (-k)))) := by
          gcongr
          exact h1.trans (mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le)
      _ = θ⁻¹ * c₀ ^ 2 / (Real.pi * σ) * (t ^ (-k) * t⁻¹) * E := by
          field_simp
  have hphi : dgPhi c₀ t r = c₀ * t⁻¹ * E := dgPhi_eq c₀ t r
  have htkpos : 0 < t ^ (-k) := Real.rpow_pos_of_pos ht0 _
  calc |a - b| ≤ a + b := by
        rw [abs_le]; constructor <;> linarith
    _ ≤ Kc * (t ^ (-k) * t⁻¹) * E := by
        have : Kc * (t ^ (-k) * t⁻¹) * E = 8 * Ccv ^ 3 * (t ^ (-k) * t⁻¹) * E +
            θ⁻¹ * c₀ ^ 2 / (Real.pi * σ) * (t ^ (-k) * t⁻¹) * E := by simp only [Kc]; ring
        linarith
    _ = Kc / c₀ * t ^ (-k) * dgPhi c₀ t r := by rw [hphi]; field_simp
    _ ≤ max c₀ (Kc / c₀) * t ^ (-k) * dgPhi (max c₀ (Kc / c₀)) t r := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right (le_max_right _ _) htkpos.le)
          (dgPhi_mono hc₀0 (le_max_left _ _) ht0 hr0.le) (dgPhi_nonneg hc₀0.le ht0.le _)
          (by positivity)

/-- A lattice point within distance `1` of the midpoint `(x + z)/2`, at distance at most
`|x - z|/2 + 1` of `z`. -/
theorem exists_lattice_near_midpoint (x z : Vertex 2) : ∃ w : Vertex 2,
    ‖(1 / 2 : ℝ) • (latticeEuclideanEmbedding x + latticeEuclideanEmbedding z) -
      latticeEuclideanEmbedding w‖ ≤ 1 ∧ latticeDist w z ≤ latticeDist x z / 2 + 1 := by
  set w : Vertex 2 := fun i => (x i + z i) / 2 with hw
  have hc : ∀ i : Fin 2,
      |(1 / 2 : ℝ) * ((x i : ℝ) + z i) - (((x i + z i) / 2 : ℤ) : ℝ)| ≤ 1 / 2 := by
    intro i
    have h1 : x i + z i = 2 * ((x i + z i) / 2) + (x i + z i) % 2 := by omega
    have h2 : 0 ≤ (x i + z i) % 2 := by omega
    have h4 : ((x i : ℝ) + z i) =
        (((x i + z i) % 2 : ℤ) : ℝ) + 2 * (((x i + z i) / 2 : ℤ) : ℝ) := by
      have := congrArg (fun n : ℤ => (n : ℝ)) h1
      push_cast at this ⊢
      linarith
    have h2' : (0 : ℝ) ≤ (((x i + z i) % 2 : ℤ) : ℝ) := by exact_mod_cast h2
    have h3' : (((x i + z i) % 2 : ℤ) : ℝ) ≤ 1 := by
      have : (x i + z i) % 2 ≤ 1 := by omega
      exact_mod_cast this
    rw [h4, abs_le]
    constructor <;> nlinarith
  have hnorm : ‖(1 / 2 : ℝ) • (latticeEuclideanEmbedding x + latticeEuclideanEmbedding z) -
      latticeEuclideanEmbedding w‖ ≤ 1 := by
    rw [EuclideanSpace.norm_eq]
    refine (Real.sqrt_le_sqrt ?_).trans_eq Real.sqrt_one
    rw [Fin.sum_univ_two]
    simp only [PiLp.sub_apply, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul, Real.norm_eq_abs]
    have e0 := pow_le_pow_left₀ (abs_nonneg _) (hc 0) 2
    have e1 := pow_le_pow_left₀ (abs_nonneg _) (hc 1) 2
    change |(1 / 2 : ℝ) * ((x 0 : ℝ) + z 0) - (((x 0 + z 0) / 2 : ℤ) : ℝ)| ^ 2 +
      |(1 / 2 : ℝ) * ((x 1 : ℝ) + z 1) - (((x 1 + z 1) / 2 : ℤ) : ℝ)| ^ 2 ≤ 1
    linarith
  refine ⟨w, hnorm, ?_⟩
  unfold latticeDist
  set ex := latticeEuclideanEmbedding x
  set ez := latticeEuclideanEmbedding z
  set ew := latticeEuclideanEmbedding w
  have hm : (1 / 2 : ℝ) • (ex + ez) - ez = (1 / 2 : ℝ) • (ex - ez) := by module
  calc ‖ew - ez‖ = ‖(ew - (1 / 2 : ℝ) • (ex + ez)) + ((1 / 2 : ℝ) • (ex + ez) - ez)‖ := by
        congr 1; abel
    _ ≤ ‖ew - (1 / 2 : ℝ) • (ex + ez)‖ + ‖(1 / 2 : ℝ) • (ex + ez) - ez‖ := norm_add_le _ _
    _ = ‖(1 / 2 : ℝ) • (ex + ez) - ew‖ + ‖(1 / 2 : ℝ) • (ex - ez)‖ := by rw [norm_sub_rev, hm]
    _ ≤ 1 + ‖ex - ez‖ / 2 := by
        have hs : ‖(1 / 2 : ℝ) • (ex - ez)‖ = ‖ex - ez‖ / 2 := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]; ring
        rw [hs]; linarith [hnorm]
    _ = ‖ex - ez‖ / 2 + 1 := by ring

/-! ### The exponents of §4.3 (`d = 2`, `α = δ/2`, `κ = δ/4`, (4.42)) -/

theorem rpow_le_rpow_neg {s a b : ℝ} (hs : 1 ≤ s) (hab : a ≤ b) : s ^ (-b) ≤ s ^ (-a) :=
  Real.rpow_le_rpow_of_exponent_le hs (by linarith)

/-- The five error terms of the weighted `L²` estimate at time `s` with `τ = s^{1-κ}` are at most
`s^{-1/2-k'}`, `k' = min((1-κ)k + κ/2, 1/2 - δ)` (the improvement of (4.49) over `k`). -/
theorem step_exponents {δ k s : ℝ} (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4) (hs : 1 ≤ s) :
    (s ^ (1 - δ / 4)) ^ (-k) * (s ^ (1 - δ / 4) / s) ^ (1 / 2 : ℝ) * s ^ (-(1 / 2 : ℝ)) ≤
        s ^ (-(1 / 2 : ℝ) - min ((1 - δ / 4) * k + δ / 4 / 2) (1 / 2 - δ)) ∧
      (s ^ (1 - δ / 4)) ^ (-(1 / 2 : ℝ) + δ / 2) * s ^ (-(1 / 2 : ℝ)) ≤
        s ^ (-(1 / 2 : ℝ) - min ((1 - δ / 4) * k + δ / 4 / 2) (1 / 2 - δ)) ∧
      (s ^ (1 - δ / 4)) ^ (-(1 / 2 : ℝ) + δ / 2 / 2) * s ^ (-(1 / 2 : ℝ)) ≤
        s ^ (-(1 / 2 : ℝ) - min ((1 - δ / 4) * k + δ / 4 / 2) (1 / 2 - δ)) ∧
      (s / s ^ (1 - δ / 4)) ^ (1 / 2 : ℝ) * (s ^ (1 - δ / 4)) ^ (-(1 : ℝ) + δ / 2 / 2) ≤
        s ^ (-(1 / 2 : ℝ) - min ((1 - δ / 4) * k + δ / 4 / 2) (1 / 2 - δ)) ∧
      s ^ (-(1 : ℝ) + δ / 2) ≤
        s ^ (-(1 / 2 : ℝ) - min ((1 - δ / 4) * k + δ / 4 / 2) (1 / 2 - δ)) := by
  have hs0 : 0 < s := by linarith
  set k' := min ((1 - δ / 4) * k + δ / 4 / 2) (1 / 2 - δ) with hk'
  have hk1 : k' ≤ (1 - δ / 4) * k + δ / 4 / 2 := min_le_left _ _
  have hk2 : k' ≤ 1 / 2 - δ := min_le_right _ _
  have e1 : ∀ a : ℝ, (s ^ (1 - δ / 4)) ^ a = s ^ ((1 - δ / 4) * a) :=
    fun a => (Real.rpow_mul hs0.le _ _).symm
  have e2 : s ^ (1 - δ / 4) / s = s ^ (-(δ / 4)) := by
    rw [← Real.rpow_sub_one hs0.ne', show 1 - δ / 4 - 1 = -(δ / 4) by ring]
  have e3 : s / s ^ (1 - δ / 4) = s ^ (δ / 4) := by
    rw [div_eq_iff (Real.rpow_pos_of_pos hs0 _).ne', ← Real.rpow_add hs0,
      show δ / 4 + (1 - δ / 4) = 1 by ring, Real.rpow_one]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [e1, e2, ← Real.rpow_mul hs0.le, ← Real.rpow_add hs0, ← Real.rpow_add hs0]
    apply Real.rpow_le_rpow_of_exponent_le hs
    nlinarith
  · rw [e1, ← Real.rpow_add hs0]
    apply Real.rpow_le_rpow_of_exponent_le hs
    nlinarith
  · rw [e1, ← Real.rpow_add hs0]
    apply Real.rpow_le_rpow_of_exponent_le hs
    nlinarith
  · rw [e1, e3, ← Real.rpow_mul hs0.le, ← Real.rpow_add hs0]
    apply Real.rpow_le_rpow_of_exponent_le hs
    nlinarith
  · apply Real.rpow_le_rpow_of_exponent_le hs
    linarith


end Rigidity.Green
