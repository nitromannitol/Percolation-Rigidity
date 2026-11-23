import Rigidity.Proofs.Green.DarioGuWeightedL2

/-!
# The Gaussian kernel `p̄` in the proof of Theorem 1 of Dario–Gu

* `const_mul_latticeGaussian_le_dgPhi`: `c p̄(t, x - y) ≤ Φ_C(t, x - y)` for `C ≥ max(2σ, c/(2πσ))`.
* `gaussianHeat_mul_gaussianHeat`: the identity
  `p̄(s, u) p̄(s, v) = p̄(2s, u + v) p̄(s/2, (v - u)/2)` (Dario–Gu, line 2599, from the parallelogram
  law), with `u = x - y`, `v = y - z`, `(v - u)/2 = y - (x + z)/2`.
* `abs_sum_gaussian_sub_le`: `Σ_y |p̄(τ, y - m) - p̄(τ, y - m')| ≤ M τ^{-1/2}` for `|m - m'| ≤ 1`
  and `τ ≥ 1`; with it Proposition A.7, printed for lattice centres, applies at the centre
  `(x + z)/2` of (4.48)-b.
-/

open Finset LatticeProb.Percolation

namespace Rigidity.Green

theorem gaussianHeat_pos {σ t : ℝ} (hσ : 0 < σ) (ht : 0 < t) (u : EuclideanSpace ℝ (Fin 2)) :
    0 < gaussianHeat σ t u := by
  unfold gaussianHeat
  positivity

theorem latticeGaussian_pos {σ t : ℝ} (hσ : 0 < σ) (ht : 0 < t) (x y : Vertex 2) :
    0 < latticeGaussian σ t x y :=
  gaussianHeat_pos hσ ht _

theorem latticeGaussian_symm (σ t : ℝ) (x y : Vertex 2) :
    latticeGaussian σ t x y = latticeGaussian σ t y x := by
  unfold latticeGaussian gaussianHeat
  rw [norm_sub_rev]

theorem latticeGaussian_eq (σ t : ℝ) (x y : Vertex 2) :
    latticeGaussian σ t x y =
      (2 * Real.pi * σ * t)⁻¹ * Real.exp (-(latticeDist x y ^ 2 / (2 * σ * t))) := rfl

theorem const_mul_latticeGaussian_le_dgPhi {σ t c C : ℝ} (hσ : 0 < σ) (ht : 0 < t)
    (hC1 : 2 * σ ≤ C) (hC2 : c / (2 * Real.pi * σ) ≤ C) (x y : Vertex 2) :
    c * latticeGaussian σ t x y ≤ dgPhi C t (latticeDist x y) := by
  rw [dgPhi_eq, latticeGaussian_eq]
  have hC : 0 < C := by linarith
  have hr := latticeDist_nonneg x y
  have h1 : c * (2 * Real.pi * σ * t)⁻¹ ≤ C * t⁻¹ := by
    calc c * (2 * Real.pi * σ * t)⁻¹ = c / (2 * Real.pi * σ) * t⁻¹ := by
          field_simp
      _ ≤ C * t⁻¹ := mul_le_mul_of_nonneg_right hC2 (inv_nonneg.2 ht.le)
  have h2 : Real.exp (-(latticeDist x y ^ 2 / (2 * σ * t))) ≤
      Real.exp (-(dgShape t (latticeDist x y) / C)) := by
    apply Real.exp_le_exp.2
    rw [neg_le_neg_iff]
    calc dgShape t (latticeDist x y) / C ≤ latticeDist x y ^ 2 / t / C :=
          div_le_div_of_nonneg_right (dgShape_le_sq ht hr) hC.le
      _ ≤ latticeDist x y ^ 2 / (2 * σ * t) := by
          rw [div_div]
          exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by nlinarith)
  calc c * ((2 * Real.pi * σ * t)⁻¹ * Real.exp (-(latticeDist x y ^ 2 / (2 * σ * t))))
      = c * (2 * Real.pi * σ * t)⁻¹ * Real.exp (-(latticeDist x y ^ 2 / (2 * σ * t))) := by ring
    _ ≤ C * t⁻¹ * Real.exp (-(dgShape t (latticeDist x y) / C)) :=
        mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)

/-- **Dario–Gu, line 2599**: `p̄(s, u) p̄(s, v) = p̄(2s, u + v) p̄(s/2, (v - u)/2)`. -/
theorem gaussianHeat_mul_gaussianHeat {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s)
    (u v : EuclideanSpace ℝ (Fin 2)) :
    gaussianHeat σ s u * gaussianHeat σ s v =
      gaussianHeat σ (2 * s) (u + v) * gaussianHeat σ (s / 2) ((1 / 2 : ℝ) • (v - u)) := by
  unfold gaussianHeat
  have hp := parallelogram_law_with_norm ℝ u v
  have hd : ‖(1 / 2 : ℝ) • (v - u)‖ = ‖u - v‖ / 2 := by
    rw [norm_smul, norm_sub_rev]
    norm_num
    ring
  rw [hd]
  have he : -(‖u‖ ^ 2 / (2 * σ * s)) + -(‖v‖ ^ 2 / (2 * σ * s)) =
      -(‖u + v‖ ^ 2 / (2 * σ * (2 * s))) + -((‖u - v‖ / 2) ^ 2 / (2 * σ * (s / 2))) := by
    linear_combination (1 / (4 * σ * s)) * hp
  calc (2 * Real.pi * σ * s)⁻¹ * Real.exp (-(‖u‖ ^ 2 / (2 * σ * s))) *
        ((2 * Real.pi * σ * s)⁻¹ * Real.exp (-(‖v‖ ^ 2 / (2 * σ * s))))
      = (2 * Real.pi * σ * s)⁻¹ * (2 * Real.pi * σ * s)⁻¹ *
          Real.exp (-(‖u‖ ^ 2 / (2 * σ * s)) + -(‖v‖ ^ 2 / (2 * σ * s))) := by
        rw [Real.exp_add]
        ring
    _ = (2 * Real.pi * σ * (2 * s))⁻¹ * (2 * Real.pi * σ * (s / 2))⁻¹ *
          Real.exp (-(‖u + v‖ ^ 2 / (2 * σ * (2 * s))) +
            -((‖u - v‖ / 2) ^ 2 / (2 * σ * (s / 2)))) := by
        rw [he]
        congr 1
        field_simp
    _ = _ := by
        rw [Real.exp_add]
        ring

/-- `|e^{-a} - e^{-b}| ≤ |a - b| e^{-min(a, b)}`. -/
theorem abs_exp_neg_sub_exp_neg_le (a b : ℝ) :
    |Real.exp (-a) - Real.exp (-b)| ≤ |a - b| * Real.exp (-min a b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, abs_sub_comm a b, abs_of_nonneg (by linarith : 0 ≤ b - a),
      abs_of_nonneg (by linarith [Real.exp_le_exp.2 (neg_le_neg h)] :
        0 ≤ Real.exp (-a) - Real.exp (-b))]
    have h1 : Real.exp (-b) = Real.exp (-a) * Real.exp (-(b - a)) := by
      rw [← Real.exp_add]; ring_nf
    have h2 : 1 - (b - a) ≤ Real.exp (-(b - a)) := by
      have := Real.add_one_le_exp (-(b - a)); linarith
    rw [h1]
    nlinarith [Real.exp_pos (-a)]
  · rw [min_eq_right h, abs_of_nonneg (by linarith : 0 ≤ a - b), abs_sub_comm,
      abs_of_nonneg (by linarith [Real.exp_le_exp.2 (neg_le_neg h)] :
        0 ≤ Real.exp (-b) - Real.exp (-a))]
    have h1 : Real.exp (-a) = Real.exp (-b) * Real.exp (-(a - b)) := by
      rw [← Real.exp_add]; ring_nf
    have h2 : 1 - (a - b) ≤ Real.exp (-(a - b)) := by
      have := Real.add_one_le_exp (-(a - b)); linarith
    rw [h1]
    nlinarith [Real.exp_pos (-b)]

theorem mul_exp_neg_sq_le {r c : ℝ} (hc : 0 < c) (hr : 0 ≤ r) :
    r * Real.exp (-(r ^ 2 / c)) ≤ Real.sqrt c * Real.exp (-(r ^ 2 / (2 * c))) := by
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  set u := r / Real.sqrt c with hu
  have hr' : r = Real.sqrt c * u := by rw [hu]; field_simp
  have hu2 : r ^ 2 / c = u ^ 2 := by
    rw [hr', mul_pow, Real.sq_sqrt hc.le]; field_simp
  have hu0 : 0 ≤ u := div_nonneg hr hsc.le
  have key : u * Real.exp (-(u ^ 2 / 2)) ≤ 1 := by
    have := Real.add_one_le_exp (u ^ 2 / 2)
    have h2 : u ≤ 1 + u ^ 2 / 2 := by nlinarith [sq_nonneg (u - 1)]
    have hexp : Real.exp (-(u ^ 2 / 2)) * Real.exp (u ^ 2 / 2) = 1 := by
      rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-(u ^ 2 / 2))]
  have hsplit : Real.exp (-(r ^ 2 / c)) = Real.exp (-(u ^ 2 / 2)) * Real.exp (-(r ^ 2 / (2 * c))) := by
    rw [← Real.exp_add]
    congr 1
    have : r ^ 2 / (2 * c) = u ^ 2 / 2 := by rw [← hu2]; ring
    rw [this, hu2]
    ring
  rw [hsplit, hr']
  calc Real.sqrt c * u * (Real.exp (-(u ^ 2 / 2)) * Real.exp (-((Real.sqrt c * u) ^ 2 / (2 * c))))
      = Real.sqrt c * (u * Real.exp (-(u ^ 2 / 2))) *
          Real.exp (-((Real.sqrt c * u) ^ 2 / (2 * c))) := by ring
    _ ≤ Real.sqrt c * 1 * Real.exp (-((Real.sqrt c * u) ^ 2 / (2 * c))) := by
        gcongr
    _ = _ := by ring

theorem rpow_neg_half_eq {t : ℝ} (ht : 0 < t) : t ^ (-(1 / 2 : ℝ)) = (Real.sqrt t)⁻¹ := by
  rw [Real.rpow_neg ht.le, Real.sqrt_eq_rpow]

/-- `Σ_y |p̄(τ, y - m) - p̄(τ, y - w)| ≤ M τ^{-1/2}` for `|m - w| ≤ 1` and `τ ≥ 1`. -/
theorem sum_abs_gaussianHeat_sub_le {σ : ℝ} (hσ : 0 < σ) : ∃ M : ℝ, 0 < M ∧ ∀ τ : ℝ, 1 ≤ τ →
    ∀ (m : EuclideanSpace ℝ (Fin 2)) (w : Vertex 2), ‖m - latticeEuclideanEmbedding w‖ ≤ 1 →
      ∀ S : Finset (Vertex 2), ∑ y ∈ S, |gaussianHeat σ τ (latticeEuclideanEmbedding y - m) -
        gaussianHeat σ τ (latticeEuclideanEmbedding y - latticeEuclideanEmbedding w)| ≤
          M * τ ^ (-(1 / 2 : ℝ)) := by
  set K := Real.exp (1 / (2 * σ)) * (4 * Real.sqrt σ + 1) / (4 * Real.pi * σ ^ 2) with hK
  set L₀ := 4 * Real.exp (1 / (8 * σ) / 2) * (1 + 1 / (1 / (8 * σ))) ^ 2 with hL₀
  refine ⟨K * L₀, by positivity, fun τ hτ m w hmw S => ?_⟩
  have hτ0 : 0 < τ := by linarith
  have hsτ : 1 ≤ Real.sqrt τ := by rw [Real.one_le_sqrt]; exact hτ
  have hpt : ∀ y : Vertex 2, |gaussianHeat σ τ (latticeEuclideanEmbedding y - m) -
      gaussianHeat σ τ (latticeEuclideanEmbedding y - latticeEuclideanEmbedding w)| ≤
      K * ((τ⁻¹) ^ 2 * Real.sqrt τ) *
        Real.exp (-(1 / (8 * σ) * latticeDist y w ^ 2 / τ)) := by
    intro y
    set u := latticeEuclideanEmbedding y - m
    set r := latticeDist y w with hr
    have hr0 : 0 ≤ r := latticeDist_nonneg y w
    have hu0 : 0 ≤ ‖u‖ := norm_nonneg _
    have hdu : |‖u‖ - r| ≤ 1 := by
      have := abs_norm_sub_norm_le u (latticeEuclideanEmbedding y - latticeEuclideanEmbedding w)
      have h2 : u - (latticeEuclideanEmbedding y - latticeEuclideanEmbedding w) =
          latticeEuclideanEmbedding w - m := by simp only [u]; abel
      rw [h2] at this
      exact this.trans (by rw [norm_sub_rev]; exact hmw)
    have hu1 : ‖u‖ ≤ r + 1 := by linarith [(abs_le.1 hdu).2]
    have hu2 : r - 1 ≤ ‖u‖ := by linarith [(abs_le.1 hdu).1]
    set a := ‖u‖ ^ 2 / (2 * σ * τ)
    set b := r ^ 2 / (2 * σ * τ)
    have hab : |a - b| ≤ (2 * r + 1) / (2 * σ * τ) := by
      have : a - b = (‖u‖ - r) * (‖u‖ + r) / (2 * σ * τ) := by simp only [a, b]; ring
      rw [this, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * σ * τ),
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ ‖u‖ + r)]
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [abs_nonneg (‖u‖ - r)]
    have hmin : (r ^ 2 / 2 - 1) / (2 * σ * τ) ≤ min a b := by
      apply le_min
      · apply div_le_div_of_nonneg_right _ (by positivity)
        rcases le_total 1 r with h1 | h1
        · nlinarith [sq_nonneg (r - 2)]
        · nlinarith
      · apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith
    have hexp : Real.exp (-min a b) ≤ Real.exp (1 / (2 * σ)) * Real.exp (-(r ^ 2 / (4 * σ * τ))) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      have h1 : 1 / (2 * σ * τ) ≤ 1 / (2 * σ) :=
        one_div_le_one_div_of_le (by positivity) (by nlinarith)
      have h2 : (r ^ 2 / 2 - 1) / (2 * σ * τ) = r ^ 2 / (4 * σ * τ) - 1 / (2 * σ * τ) := by
        field_simp; ring
      linarith
    have hpoly : (2 * r + 1) * Real.exp (-(r ^ 2 / (4 * σ * τ))) ≤
        (4 * Real.sqrt σ + 1) * Real.sqrt τ * Real.exp (-(1 / (8 * σ) * r ^ 2 / τ)) := by
      have h1 := mul_exp_neg_sq_le (c := 4 * σ * τ) (by positivity) hr0
      have h8 : r ^ 2 / (2 * (4 * σ * τ)) = 1 / (8 * σ) * r ^ 2 / τ := by field_simp; ring
      rw [h8, Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
        show Real.sqrt 4 = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        at h1
      have h2 : Real.exp (-(r ^ 2 / (4 * σ * τ))) ≤ Real.exp (-(1 / (8 * σ) * r ^ 2 / τ)) := by
        apply Real.exp_le_exp.2
        rw [neg_le_neg_iff]
        rw [show 1 / (8 * σ) * r ^ 2 / τ = r ^ 2 / (8 * σ * τ) by field_simp]
        exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by nlinarith)
      have hE := Real.exp_pos (-(1 / (8 * σ) * r ^ 2 / τ))
      have hss : 0 ≤ Real.sqrt σ := Real.sqrt_nonneg _
      calc (2 * r + 1) * Real.exp (-(r ^ 2 / (4 * σ * τ)))
          = 2 * (r * Real.exp (-(r ^ 2 / (4 * σ * τ)))) + Real.exp (-(r ^ 2 / (4 * σ * τ))) := by
            ring
        _ ≤ 2 * (2 * Real.sqrt σ * Real.sqrt τ * Real.exp (-(1 / (8 * σ) * r ^ 2 / τ))) +
            Real.exp (-(1 / (8 * σ) * r ^ 2 / τ)) := by linarith
        _ ≤ (4 * Real.sqrt σ + 1) * Real.sqrt τ * Real.exp (-(1 / (8 * σ) * r ^ 2 / τ)) := by
            nlinarith [mul_le_mul_of_nonneg_right hsτ hE.le]
    have hdiff : gaussianHeat σ τ u -
        gaussianHeat σ τ (latticeEuclideanEmbedding y - latticeEuclideanEmbedding w) =
        (2 * Real.pi * σ * τ)⁻¹ * (Real.exp (-a) - Real.exp (-b)) := by
      simp only [gaussianHeat, a, b, r, latticeDist]
      ring
    rw [hdiff, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 * Real.pi * σ * τ)⁻¹)]
    have hmain := abs_exp_neg_sub_exp_neg_le a b
    calc (2 * Real.pi * σ * τ)⁻¹ * |Real.exp (-a) - Real.exp (-b)|
        ≤ (2 * Real.pi * σ * τ)⁻¹ * ((2 * r + 1) / (2 * σ * τ) *
            (Real.exp (1 / (2 * σ)) * Real.exp (-(r ^ 2 / (4 * σ * τ))))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact hmain.trans (mul_le_mul hab hexp (Real.exp_pos _).le (by positivity))
      _ = (2 * Real.pi * σ * τ)⁻¹ * (2 * σ * τ)⁻¹ * Real.exp (1 / (2 * σ)) *
            ((2 * r + 1) * Real.exp (-(r ^ 2 / (4 * σ * τ)))) := by ring
      _ ≤ (2 * Real.pi * σ * τ)⁻¹ * (2 * σ * τ)⁻¹ * Real.exp (1 / (2 * σ)) *
            ((4 * Real.sqrt σ + 1) * Real.sqrt τ * Real.exp (-(1 / (8 * σ) * r ^ 2 / τ))) :=
          mul_le_mul_of_nonneg_left hpoly (by positivity)
      _ = K * ((τ⁻¹) ^ 2 * Real.sqrt τ) * Real.exp (-(1 / (8 * σ) * r ^ 2 / τ)) := by
          rw [hK]
          field_simp
          ring
  calc ∑ y ∈ S, |gaussianHeat σ τ (latticeEuclideanEmbedding y - m) -
        gaussianHeat σ τ (latticeEuclideanEmbedding y - latticeEuclideanEmbedding w)|
      ≤ ∑ y ∈ S, K * ((τ⁻¹) ^ 2 * Real.sqrt τ) *
          Real.exp (-(1 / (8 * σ) * latticeDist y w ^ 2 / τ)) := Finset.sum_le_sum fun y _ => hpt y
    _ = K * ((τ⁻¹) ^ 2 * Real.sqrt τ) *
          ∑ y ∈ S, Real.exp (-(1 / (8 * σ) * latticeDist y w ^ 2 / τ)) := by rw [Finset.mul_sum]
    _ ≤ K * ((τ⁻¹) ^ 2 * Real.sqrt τ) * (L₀ * τ) :=
        mul_le_mul_of_nonneg_left (sum_exp_neg_sq_div_le (by positivity) hτ w S) (by positivity)
    _ = K * L₀ * τ ^ (-(1 / 2 : ℝ)) := by
        rw [rpow_neg_half_eq hτ0]
        have hs := Real.mul_self_sqrt hτ0.le
        have hs0 : 0 < Real.sqrt τ := Real.sqrt_pos.2 hτ0
        have h1 : (τ⁻¹) ^ 2 * Real.sqrt τ * τ = (Real.sqrt τ)⁻¹ := by
          calc (τ⁻¹) ^ 2 * Real.sqrt τ * τ = Real.sqrt τ / τ := by field_simp
            _ = Real.sqrt τ / (Real.sqrt τ * Real.sqrt τ) := by rw [hs]
            _ = (Real.sqrt τ)⁻¹ := by field_simp
        calc K * ((τ⁻¹) ^ 2 * Real.sqrt τ) * (L₀ * τ) = K * L₀ * ((τ⁻¹) ^ 2 * Real.sqrt τ * τ) := by
              ring
          _ = K * L₀ * (Real.sqrt τ)⁻¹ := by rw [h1]

end Rigidity.Green
