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

end Rigidity.Green
