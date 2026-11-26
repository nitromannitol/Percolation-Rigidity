import Rigidity.Proofs.Green.DarioGuGaussianLatticeThird
import Rigidity.Proofs.Green.NormalizedGaussianD

/-!
# The Gaussian kernel on `ℤ^d` and its lattice differences

The proof of Proposition 4.3 of Dario–Gu (Steps 1, 3 and 4) uses the bounds
`|D^n p̄(r, x - y)| ≤ C r^{-d/2 - |n|/2} exp(-|x - y|²/(C r))` for the lattice differences of order
`|n| ≤ 3`, and the same bounds for `∂_r p̄`, `D_k ∂_r p̄` and `∂_r p̄ - (σ/2) Σ_k D_k D_k p̄`. On `ℤ^d`
the Gaussian is a product `p̄(r, x - y) = (2πσr)^{-d/2} Π_m g(x_m - y_m)` of one-dimensional
Gaussians `g = gauss1 (2σr)`, a forward difference `D_k` acts on the `k`-th factor only, and the
bounds follow from the one-dimensional ones of `DarioGuGaussianDiff` and `DarioGuGaussianLatticeDiff`.

* `prodFactor φ x y = Π_m φ_m(x_m - y_m)`, `fwdDiffD_prodFactor`: `D_k` replaces the `k`-th factor
  by its forward difference;
* `diffProd φ n`: the factors `Δ^{n_m} φ`, so that `D^n` of `Π_m φ(x_m - y_m)` is `diffProd φ n`
  (`fwdDiffD_diffProd`);
* `abs_prodFactor_le`: the product of factors of orders `e_m` is bounded by
  `(80 e^{9/(8c)})^d c^{-Σ e_m / 2} exp(-|x - y|²/(16 c))`;
* `latticeGaussianTimeDerivD`, `hasDerivAt_latticeGaussianD`, `latticeGaussianTimeDerivD_eq`: the
  heat equation `∂_r p̄ = (σ/2) Σ_j ∂_j² p̄` in product form;
* `abs_gaussDiff_le` and its corollaries: the bounds for `r ≥ 1`.
-/

open LatticeProb LatticeProb.Percolation

namespace Rigidity.Green.GeneralDim

variable {d : ℕ}

/-- The forward difference `D_k u(x) = u(x + e_k) - u(x)` on `ℤ^d`. -/
noncomputable def fwdDiffD (k : Fin d) (u : Vertex d → ℝ) (x : Vertex d) : ℝ :=
  u (x + Pi.single k 1) - u x

/-- The one-dimensional forward difference `Δφ(u) = φ(u + 1) - φ(u)`. -/
noncomputable def fwd1 (φ : ℝ → ℝ) (u : ℝ) : ℝ := φ (u + 1) - φ u

/-- `Π_m φ_m(x_m - y_m)`. -/
noncomputable def prodFactor (φ : Fin d → ℝ → ℝ) (x y : Vertex d) : ℝ :=
  ∏ m, φ m ((x m : ℝ) - y m)

/-- The factors `Δ^{n_m} φ`: `D^n` of `Π_m φ(x_m - y_m)`. -/
noncomputable def diffProd (φ : ℝ → ℝ) (n : Fin d → ℕ) (x y : Vertex d) : ℝ :=
  prodFactor (fun m => (fwd1^[n m]) φ) x y

theorem prodFactor_eq_mul (φ : Fin d → ℝ → ℝ) (k : Fin d) (x y : Vertex d) :
    prodFactor φ x y = φ k ((x k : ℝ) - y k) * ∏ m ∈ {k}ᶜ, φ m ((x m : ℝ) - y m) := by
  unfold prodFactor
  rw [Fintype.prod_eq_mul_prod_compl k]

theorem prodFactor_update (φ : Fin d → ℝ → ℝ) (k : Fin d) (a : ℝ → ℝ) (x y : Vertex d) :
    prodFactor (Function.update φ k a) x y =
      a ((x k : ℝ) - y k) * ∏ m ∈ {k}ᶜ, φ m ((x m : ℝ) - y m) := by
  rw [prodFactor_eq_mul _ k, Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun m hm => ?_
  rw [Finset.mem_compl, Finset.mem_singleton] at hm
  rw [Function.update_of_ne hm]

theorem prodFactor_add_single (φ : Fin d → ℝ → ℝ) (k : Fin d) (x y : Vertex d) :
    prodFactor φ (x + Pi.single k 1) y =
      φ k ((x k : ℝ) - y k + 1) * ∏ m ∈ {k}ᶜ, φ m ((x m : ℝ) - y m) := by
  rw [prodFactor_eq_mul _ k]
  congr 1
  · congr 1
    simp only [Pi.add_apply, Pi.single_eq_same, Int.cast_add, Int.cast_one]
    ring
  · refine Finset.prod_congr rfl fun m hm => ?_
    rw [Finset.mem_compl, Finset.mem_singleton] at hm
    simp only [Pi.add_apply, Pi.single_eq_of_ne hm, add_zero]

/-- `D_k` replaces the `k`-th factor by its forward difference. -/
theorem fwdDiffD_prodFactor (φ : Fin d → ℝ → ℝ) (k : Fin d) (y x : Vertex d) :
    fwdDiffD k (fun z => prodFactor φ z y) x =
      prodFactor (Function.update φ k (fwd1 (φ k))) x y := by
  show prodFactor φ (x + Pi.single k 1) y - prodFactor φ x y = _
  rw [prodFactor_add_single, prodFactor_eq_mul φ k x y, prodFactor_update, fwd1]
  ring

theorem prodFactor_update_sub (φ : Fin d → ℝ → ℝ) (k : Fin d) (a b : ℝ → ℝ) (x y : Vertex d) :
    prodFactor (Function.update φ k a) x y - prodFactor (Function.update φ k b) x y =
      prodFactor (Function.update φ k (fun u => a u - b u)) x y := by
  rw [prodFactor_update, prodFactor_update, prodFactor_update]
  ring

/-- `D_k` of `a Π_m Δ^{n_m} φ(x_m - y_m)` is `a Π_m Δ^{n_m + δ_{mk}} φ(x_m - y_m)`. -/
theorem fwdDiffD_diffProd (φ : ℝ → ℝ) (n : Fin d → ℕ) (k : Fin d) (y : Vertex d) (a : ℝ) :
    fwdDiffD k (fun z => a * diffProd φ n z y) =
      fun z => a * diffProd φ (n + Pi.single k (1 : ℕ)) z y := by
  funext x
  have e : Function.update (fun m => (fwd1^[n m]) φ) k (fwd1 ((fwd1^[n k]) φ)) =
      fun m => (fwd1^[(n + Pi.single k (1 : ℕ) : Fin d → ℕ) m]) φ := by
    funext m
    by_cases hm : m = k
    · subst hm
      rw [Function.update_self, Pi.add_apply, Pi.single_eq_same, Function.iterate_succ_apply']
    · rw [Function.update_of_ne hm, Pi.add_apply, Pi.single_eq_of_ne hm, add_zero]
  have h := fwdDiffD_prodFactor (fun m => (fwd1^[n m]) φ) k y x
  have e' : prodFactor (Function.update (fun m => (fwd1^[n m]) φ) k (fwd1 ((fwd1^[n k]) φ))) x y =
      prodFactor (fun m => (fwd1^[(n + Pi.single k (1 : ℕ) : Fin d → ℕ) m]) φ) x y := by rw [e]
  show a * diffProd φ n (x + Pi.single k 1) y - a * diffProd φ n x y = _
  rw [← mul_sub]
  exact congrArg (a * ·) (h.trans e')

/-! ### The one-dimensional factors -/

/-- A factor of order `e`: `|φ(u)| ≤ 80 e^{9/(8c)} c^{-e/2} g_{16c}(u)`. -/
def FactorLe (c : ℝ) (e : ℕ) (φ : ℝ → ℝ) : Prop :=
  ∀ u, |φ u| ≤ 80 * Real.exp (9 / (8 * c)) / Real.sqrt c ^ e * gauss1 (16 * c) u

theorem one_le_exp_nine {c : ℝ} (hc : 0 < c) : 1 ≤ Real.exp (9 / (8 * c)) :=
  Real.one_le_exp (by positivity)

theorem exp_half_le_exp_nine {c : ℝ} (hc : 0 < c) :
    Real.exp (1 / (2 * c)) ≤ Real.exp (9 / (8 * c)) := by
  rw [Real.exp_le_exp, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

theorem factorLe_of_le {c : ℝ} (hc : 0 < c) {e : ℕ} {φ : ℝ → ℝ} {K : ℝ} (hK : K ≤ 80)
    (h : ∀ u, |φ u| ≤ K / Real.sqrt c ^ e * (Real.exp (9 / (8 * c)) * gauss1 (16 * c) u)) :
    FactorLe c e φ := by
  intro u
  refine (h u).trans ?_
  have hs : 0 < Real.sqrt c ^ e := pow_pos (Real.sqrt_pos.2 hc) e
  have hg := mul_pos (Real.exp_pos (9 / (8 * c))) (gauss1_pos (16 * c) u)
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hs]
  nlinarith

theorem iterate_fwd1_one (φ : ℝ → ℝ) (u : ℝ) : (fwd1^[1]) φ u = φ (u + 1) - φ u := rfl

theorem iterate_fwd1_two {c : ℝ} (u : ℝ) : (fwd1^[2]) (gauss1 c) u = secondDiff c u := by
  show fwd1 (fwd1 (gauss1 c)) u = _
  unfold fwd1 secondDiff
  rw [show u + 1 + 1 = u + 2 by ring]
  ring

theorem iterate_fwd1_three {c : ℝ} (u : ℝ) :
    (fwd1^[3]) (gauss1 c) u = secondDiff c (u + 1) - secondDiff c u := by
  show fwd1 (fwd1 (fwd1 (gauss1 c))) u = _
  unfold fwd1 secondDiff
  rw [show u + 1 + 1 + 1 = u + 1 + 2 by ring, show u + 1 + 1 = u + 2 by ring]
  ring

theorem factorLe_iterate {c : ℝ} (hc : 0 < c) {n : ℕ} (hn : n ≤ 3) :
    FactorLe c n ((fwd1^[n]) (gauss1 c)) := by
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hcs : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc.le
  interval_cases n
  · refine factorLe_of_le hc (K := 1) (by norm_num) fun u => ?_
    rw [Function.iterate_zero_apply, abs_of_pos (gauss1_pos c u), pow_zero, div_one, one_mul]
    exact (gauss1_mono hc (by linarith) u).trans
      (le_mul_of_one_le_left (gauss1_pos _ u).le (one_le_exp_nine hc))
  · refine factorLe_of_le hc (K := 2) (by norm_num) fun u => ?_
    rw [iterate_fwd1_one, pow_one]
    refine (abs_gauss1_sub_le hc u).trans ?_
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (exp_half_le_exp_nine hc)
      (gauss1_pos _ u).le) (by positivity)
  · refine factorLe_of_le hc (K := 8) (by norm_num) fun u => ?_
    rw [iterate_fwd1_two, hcs]
    refine (abs_secondDiff_le hc u).trans ?_
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (exp_half_le_exp_nine hc)
      (gauss1_pos _ u).le) (by positivity)
  · refine factorLe_of_le hc (K := 40) (by norm_num) fun u => ?_
    rw [iterate_fwd1_three, show Real.sqrt c ^ 3 = c * Real.sqrt c by rw [pow_succ, hcs]]
    exact abs_secondDiff_sub_le hc u

theorem factorLe_gauss1'' {c : ℝ} (hc : 0 < c) : FactorLe c 2 (gauss1'' c) := by
  have hcs : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc.le
  refine factorLe_of_le hc (K := 8) (by norm_num) fun u => ?_
  rw [hcs]
  refine (abs_gauss1''_le_sixteen hc u).trans ?_
  exact mul_le_mul_of_nonneg_left
    (le_mul_of_one_le_left (gauss1_pos _ u).le (one_le_exp_nine hc)) (by positivity)

theorem factorLe_fwd1_gauss1'' {c : ℝ} (hc : 0 < c) : FactorLe c 3 (fwd1 (gauss1'' c)) := by
  have hcs : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc.le
  refine factorLe_of_le hc (K := 40) (by norm_num) fun u => ?_
  rw [show Real.sqrt c ^ 3 = c * Real.sqrt c by rw [pow_succ, hcs]]
  refine (abs_gauss1''_sub_le hc u).trans ?_
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (exp_half_le_exp_nine hc)
    (gauss1_pos _ u).le) (by positivity)

/-- `|g''(u) - D²g(u)| ≤ 80 c^{-3/2} e^{1/(2c)} g_{16c}(u)`. -/
theorem abs_gauss1''_sub_secondDiff_le {c : ℝ} (hc : 0 < c) (n : ℝ) :
    |gauss1'' c n - secondDiff c n| ≤
      80 / (c * Real.sqrt c) * (Real.exp (1 / (2 * c)) * gauss1 (16 * c) n) := by
  obtain ⟨ξ, ζ, hξ0, hξ2, hζ, he⟩ := exists_secondDiff_sub_eq hc.ne' n
  have e : gauss1'' c n - secondDiff c n = -((ξ - n) * gauss1''' c ζ) := by
    rw [← he, secondDiff]
    ring
  rw [e, abs_neg, abs_mul, abs_of_pos hξ0]
  have h3 := abs_gauss1'''_le hc ζ
  have hs := gauss1_shift_le hc (show |ζ - n| ≤ 2 by
    rw [abs_le]; constructor <;> linarith [hζ.1, hζ.2])
  calc (ξ - n) * |gauss1''' c ζ| ≤ 2 * (40 / (c * Real.sqrt c) * gauss1 (8 * c) ζ) :=
        mul_le_mul hξ2.le h3 (abs_nonneg _) (by norm_num)
    _ ≤ 2 * (40 / (c * Real.sqrt c) * (Real.exp (1 / (2 * c)) * gauss1 (16 * c) n)) := by
        gcongr
    _ = 80 / (c * Real.sqrt c) * (Real.exp (1 / (2 * c)) * gauss1 (16 * c) n) := by ring

theorem factorLe_gauss1''_sub {c : ℝ} (hc : 0 < c) :
    FactorLe c 3 (fun u => gauss1'' c u - (fwd1^[2]) (gauss1 c) u) := by
  have hcs : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc.le
  refine factorLe_of_le hc (K := 80) le_rfl fun u => ?_
  rw [iterate_fwd1_two, show Real.sqrt c ^ 3 = c * Real.sqrt c by rw [pow_succ, hcs]]
  refine (abs_gauss1''_sub_secondDiff_le hc u).trans ?_
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (exp_half_le_exp_nine hc)
    (gauss1_pos _ u).le) (by positivity)

/-! ### Products -/

/-- **The bound of a product of factors.** -/
theorem abs_prodFactor_le {c : ℝ} {φ : Fin d → ℝ → ℝ} {e : Fin d → ℕ}
    (h : ∀ m, FactorLe c (e m) (φ m)) (x y : Vertex d) :
    |prodFactor φ x y| ≤ (80 * Real.exp (9 / (8 * c))) ^ d / Real.sqrt c ^ (∑ m, e m) *
      Real.exp (-(‖edzD x y‖ ^ 2 / (16 * c))) := by
  unfold prodFactor
  rw [Finset.abs_prod]
  calc ∏ m, |φ m ((x m : ℝ) - y m)| ≤ ∏ m, (80 * Real.exp (9 / (8 * c)) /
        Real.sqrt c ^ e m * gauss1 (16 * c) ((x m : ℝ) - y m)) :=
      Finset.prod_le_prod (fun m _ => abs_nonneg _) (fun m _ => h m _)
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, Finset.prod_pow_eq_pow_sum]
      congr 1
      unfold gauss1
      rw [← Real.exp_sum, sq_norm_edzD, Finset.sum_div, Finset.sum_neg_distrib]

theorem abs_diffProd_le {c : ℝ} (hc : 0 < c) {n : Fin d → ℕ} (hn : ∀ m, n m ≤ 3)
    (x y : Vertex d) :
    |diffProd (gauss1 c) n x y| ≤ (80 * Real.exp (9 / (8 * c))) ^ d /
      Real.sqrt c ^ (∑ m, n m) * Real.exp (-(‖edzD x y‖ ^ 2 / (16 * c))) :=
  abs_prodFactor_le (fun m => factorLe_iterate hc (hn m)) x y

/-! ### The Gaussian on the lattice -/

/-- `p̄(r, x - y)` at the lattice points of `ℤ^d`. -/
noncomputable def latticeGaussianD (σ r : ℝ) (x y : Vertex d) : ℝ :=
  gaussianHeatD d σ r (edzD x y)

/-- **The product structure of the Gaussian on `ℤ^d`.** -/
theorem latticeGaussianD_eq (σ r : ℝ) (x y : Vertex d) :
    latticeGaussianD σ r x y = (2 * Real.pi * σ * r) ^ (-((d : ℝ) / 2)) *
      diffProd (gauss1 (2 * σ * r)) 0 x y := by
  simp only [latticeGaussianD, gaussianHeatD, diffProd, prodFactor, Pi.zero_apply,
    Function.iterate_zero_apply, gauss1]
  congr 1
  rw [← Real.exp_sum, sq_norm_edzD, Finset.sum_div, Finset.sum_neg_distrib]

theorem latticeGaussianD_eq_diffProd (σ r : ℝ) (y : Vertex d) :
    (fun x => latticeGaussianD σ r x y) = fun x => (2 * Real.pi * σ * r) ^ (-((d : ℝ) / 2)) *
      diffProd (gauss1 (2 * σ * r)) 0 x y :=
  funext fun x => latticeGaussianD_eq σ r x y

/-- `∂_r p̄(r, x - y) = p̄(r, x - y) (|x - y|²/(2σr²) - d/(2r))`. -/
noncomputable def latticeGaussianTimeDerivD (σ r : ℝ) (x y : Vertex d) : ℝ :=
  latticeGaussianD σ r x y * (‖edzD x y‖ ^ 2 / (2 * σ * r ^ 2) - d / (2 * r))

theorem hasDerivAt_latticeGaussianD {σ r : ℝ} (hσ : 0 < σ) (hr : 0 < r) (x y : Vertex d) :
    HasDerivAt (fun s => latticeGaussianD σ s x y) (latticeGaussianTimeDerivD σ r x y) r := by
  have hc : (2 * Real.pi * σ * r) ≠ 0 := by positivity
  have hd : (2 * σ * r) ≠ 0 := by positivity
  have h1 : HasDerivAt (fun s => (2 * Real.pi * σ * s) ^ (-((d : ℝ) / 2)))
      (2 * Real.pi * σ * 1 * (-((d : ℝ) / 2)) * (2 * Real.pi * σ * r) ^ (-((d : ℝ) / 2) - 1)) r :=
    ((hasDerivAt_id' r).const_mul (2 * Real.pi * σ)).rpow_const (Or.inl hc)
  have h2 : HasDerivAt (fun s => -(‖edzD x y‖ ^ 2 / (2 * σ * s)))
      (-((0 * (2 * σ * r) - ‖edzD x y‖ ^ 2 * (2 * σ * 1)) / (2 * σ * r) ^ 2)) r :=
    ((hasDerivAt_const r (‖edzD x y‖ ^ 2)).div ((hasDerivAt_id' r).const_mul (2 * σ)) hd).neg
  have h := h1.mul h2.exp
  unfold latticeGaussianTimeDerivD latticeGaussianD gaussianHeatD
  refine h.congr_deriv ?_
  rw [Real.rpow_sub_one hc]
  field_simp
  ring

/-- **The heat equation** `∂_r p̄ = (σ/2) Σ_j ∂_j² p̄` in product form. -/
theorem latticeGaussianTimeDerivD_eq (σ r : ℝ) (hσ : 0 < σ) (hr : 0 < r) (x y : Vertex d) :
    latticeGaussianTimeDerivD σ r x y = σ / 2 * (2 * Real.pi * σ * r) ^ (-((d : ℝ) / 2)) *
      ∑ j, prodFactor (Function.update (fun _ => gauss1 (2 * σ * r)) j
        (gauss1'' (2 * σ * r))) x y := by
  have key : ∀ j, prodFactor (Function.update (fun _ => gauss1 (2 * σ * r)) j
      (gauss1'' (2 * σ * r))) x y = (4 * ((x j : ℝ) - y j) ^ 2 / (2 * σ * r) ^ 2 -
        2 / (2 * σ * r)) * diffProd (gauss1 (2 * σ * r)) 0 x y := by
    intro j
    rw [prodFactor_update]
    unfold diffProd
    rw [prodFactor_eq_mul _ j]
    simp only [Pi.zero_apply, Function.iterate_zero_apply]
    unfold gauss1''
    ring
  have hsum : ∑ j, (4 * ((x j : ℝ) - y j) ^ 2 / (2 * σ * r) ^ 2 - 2 / (2 * σ * r)) =
      4 * ‖edzD x y‖ ^ 2 / (2 * σ * r) ^ 2 - 2 * d / (2 * σ * r) := by
    rw [Finset.sum_sub_distrib, sq_norm_edzD, Finset.mul_sum, Finset.sum_div]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  unfold latticeGaussianTimeDerivD
  rw [latticeGaussianD_eq]
  simp only [key]
  rw [← Finset.sum_mul, hsum]
  field_simp
  ring

/-! ### The bounds for `r ≥ 1` -/

/-- The constant of the bounds of the lattice differences of order `j`. -/
noncomputable def gaussConstD (d : ℕ) (σ : ℝ) (j : ℕ) : ℝ :=
  (2 * Real.pi * σ) ^ (-((d : ℝ) / 2)) * (80 * Real.exp (9 / (16 * σ))) ^ d /
    Real.sqrt (2 * σ) ^ j

theorem gaussConstD_pos {σ : ℝ} (hσ : 0 < σ) (j : ℕ) : 0 < gaussConstD d σ j := by
  unfold gaussConstD
  positivity

theorem gaussScale_le {σ r : ℝ} (hσ : 0 < σ) (hr : 1 ≤ r) (j : ℕ) :
    (2 * Real.pi * σ * r) ^ (-((d : ℝ) / 2)) *
        ((80 * Real.exp (9 / (8 * (2 * σ * r)))) ^ d / Real.sqrt (2 * σ * r) ^ j) ≤
      gaussConstD d σ j * r ^ (-((d : ℝ) / 2)) / Real.sqrt r ^ j := by
  have hr0 : 0 < r := by linarith
  have h2σ : 0 < 2 * σ := by positivity
  have hE : Real.exp (9 / (8 * (2 * σ * r))) ≤ Real.exp (9 / (16 * σ)) := by
    rw [Real.exp_le_exp]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hsplit : (2 * Real.pi * σ * r) ^ (-((d : ℝ) / 2)) =
      (2 * Real.pi * σ) ^ (-((d : ℝ) / 2)) * r ^ (-((d : ℝ) / 2)) :=
    Real.mul_rpow (by positivity) hr0.le
  have hsq : Real.sqrt (2 * σ * r) ^ j = Real.sqrt (2 * σ) ^ j * Real.sqrt r ^ j := by
    rw [Real.sqrt_mul h2σ.le, mul_pow]
  rw [hsplit, hsq]
  unfold gaussConstD
  have hs1 : 0 < Real.sqrt (2 * σ) ^ j := pow_pos (Real.sqrt_pos.2 h2σ) j
  have hs2 : 0 < Real.sqrt r ^ j := pow_pos (Real.sqrt_pos.2 hr0) j
  have hA : 0 < (2 * Real.pi * σ) ^ (-((d : ℝ) / 2)) := by positivity
  have hR : 0 < r ^ (-((d : ℝ) / 2)) := by positivity
  have hP : (80 * Real.exp (9 / (8 * (2 * σ * r)))) ^ d ≤ (80 * Real.exp (9 / (16 * σ))) ^ d := by
    gcongr
  calc (2 * Real.pi * σ) ^ (-((d : ℝ) / 2)) * r ^ (-((d : ℝ) / 2)) *
        ((80 * Real.exp (9 / (8 * (2 * σ * r)))) ^ d /
          (Real.sqrt (2 * σ) ^ j * Real.sqrt r ^ j))
      ≤ (2 * Real.pi * σ) ^ (-((d : ℝ) / 2)) * r ^ (-((d : ℝ) / 2)) *
        ((80 * Real.exp (9 / (16 * σ))) ^ d / (Real.sqrt (2 * σ) ^ j * Real.sqrt r ^ j)) := by
        gcongr
    _ = _ := by ring

theorem exp_sixteen_eq (σ r : ℝ) (z : EuclideanSpace ℝ (Fin d)) :
    Real.exp (-(‖z‖ ^ 2 / (16 * (2 * σ * r)))) = Real.exp (-(‖z‖ ^ 2 / (32 * σ * r))) := by
  rw [show 16 * (2 * σ * r) = 32 * σ * r by ring]

/-- **The lattice differences of the Gaussian**: for `r ≥ 1` and a multi-index `n` with
`n_m ≤ 3`, `|D^n p̄(r, x - y)| ≤ K r^{-d/2} r^{-|n|/2} exp(-|x - y|²/(32σr))`. -/
theorem abs_gaussDiff_le {σ r : ℝ} (hσ : 0 < σ) (hr : 1 ≤ r) {n : Fin d → ℕ} (hn : ∀ m, n m ≤ 3)
    (x y : Vertex d) :
    |(2 * Real.pi * σ * r) ^ (-((d : ℝ) / 2)) * diffProd (gauss1 (2 * σ * r)) n x y| ≤
      gaussConstD d σ (∑ m, n m) * r ^ (-((d : ℝ) / 2)) / Real.sqrt r ^ (∑ m, n m) *
        Real.exp (-(‖edzD x y‖ ^ 2 / (32 * σ * r))) := by
  have hr0 : 0 < r := by linarith
  have hc : 0 < 2 * σ * r := by positivity
  have hA : 0 ≤ (2 * Real.pi * σ * r) ^ (-((d : ℝ) / 2)) := by positivity
  rw [abs_mul, abs_of_nonneg hA, ← exp_sixteen_eq]
  calc (2 * Real.pi * σ * r) ^ (-((d : ℝ) / 2)) * |diffProd (gauss1 (2 * σ * r)) n x y|
      ≤ (2 * Real.pi * σ * r) ^ (-((d : ℝ) / 2)) * ((80 * Real.exp (9 / (8 * (2 * σ * r)))) ^ d /
          Real.sqrt (2 * σ * r) ^ (∑ m, n m) *
            Real.exp (-(‖edzD x y‖ ^ 2 / (16 * (2 * σ * r))))) :=
        mul_le_mul_of_nonneg_left (abs_diffProd_le hc hn x y) hA
    _ = (2 * Real.pi * σ * r) ^ (-((d : ℝ) / 2)) * ((80 * Real.exp (9 / (8 * (2 * σ * r)))) ^ d /
          Real.sqrt (2 * σ * r) ^ (∑ m, n m)) *
            Real.exp (-(‖edzD x y‖ ^ 2 / (16 * (2 * σ * r)))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (gaussScale_le hσ hr _) (Real.exp_pos _).le

/-- The bound of a product of factors at the scale `c = 2σr`, `r ≥ 1`. -/
theorem abs_gaussProd_le {σ r : ℝ} (hσ : 0 < σ) (hr : 1 ≤ r) {φ : Fin d → ℝ → ℝ}
    {e : Fin d → ℕ} (h : ∀ m, FactorLe (2 * σ * r) (e m) (φ m)) (x y : Vertex d) :
    |(2 * Real.pi * σ * r) ^ (-((d : ℝ) / 2)) * prodFactor φ x y| ≤
      gaussConstD d σ (∑ m, e m) * r ^ (-((d : ℝ) / 2)) / Real.sqrt r ^ (∑ m, e m) *
        Real.exp (-(‖edzD x y‖ ^ 2 / (32 * σ * r))) := by
  have hr0 : 0 < r := by linarith
  have hc : 0 < 2 * σ * r := by positivity
  have hA : 0 ≤ (2 * Real.pi * σ * r) ^ (-((d : ℝ) / 2)) := by positivity
  rw [abs_mul, abs_of_nonneg hA, ← exp_sixteen_eq]
  calc (2 * Real.pi * σ * r) ^ (-((d : ℝ) / 2)) * |prodFactor φ x y|
      ≤ (2 * Real.pi * σ * r) ^ (-((d : ℝ) / 2)) * ((80 * Real.exp (9 / (8 * (2 * σ * r)))) ^ d /
          Real.sqrt (2 * σ * r) ^ (∑ m, e m) *
            Real.exp (-(‖edzD x y‖ ^ 2 / (16 * (2 * σ * r))))) :=
        mul_le_mul_of_nonneg_left (abs_prodFactor_le h x y) hA
    _ = (2 * Real.pi * σ * r) ^ (-((d : ℝ) / 2)) * ((80 * Real.exp (9 / (8 * (2 * σ * r)))) ^ d /
          Real.sqrt (2 * σ * r) ^ (∑ m, e m)) *
            Real.exp (-(‖edzD x y‖ ^ 2 / (16 * (2 * σ * r)))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (gaussScale_le hσ hr _) (Real.exp_pos _).le

theorem sum_single_eq (k : Fin d) : ∑ m, (Pi.single k 1 : Fin d → ℕ) m = 1 := by
  rw [Finset.sum_pi_single']
  simp

theorem fwdDiffD_latticeGaussianD (σ r : ℝ) (k : Fin d) (y : Vertex d) :
    fwdDiffD k (fun z => latticeGaussianD σ r z y) = fun z =>
      (2 * Real.pi * σ * r) ^ (-((d : ℝ) / 2)) *
        diffProd (gauss1 (2 * σ * r)) ((0 : Fin d → ℕ) + Pi.single k 1) z y := by
  rw [latticeGaussianD_eq_diffProd, fwdDiffD_diffProd]

theorem fwdDiffD_fwdDiffD_latticeGaussianD (σ r : ℝ) (i k : Fin d) (y : Vertex d) :
    fwdDiffD i (fwdDiffD k fun z => latticeGaussianD σ r z y) = fun z =>
      (2 * Real.pi * σ * r) ^ (-((d : ℝ) / 2)) *
        diffProd (gauss1 (2 * σ * r)) ((0 : Fin d → ℕ) + Pi.single k 1 + Pi.single i 1) z y := by
  rw [fwdDiffD_latticeGaussianD, fwdDiffD_diffProd]

theorem fwdDiffD3_latticeGaussianD (σ r : ℝ) (j i k : Fin d) (y : Vertex d) :
    fwdDiffD j (fwdDiffD i (fwdDiffD k fun z => latticeGaussianD σ r z y)) = fun z =>
      (2 * Real.pi * σ * r) ^ (-((d : ℝ) / 2)) *
        diffProd (gauss1 (2 * σ * r)) ((0 : Fin d → ℕ) + Pi.single k 1 + Pi.single i 1 + Pi.single j 1) z y := by
  rw [fwdDiffD_fwdDiffD_latticeGaussianD, fwdDiffD_diffProd]

theorem single_le_one (k : Fin d) (m : Fin d) : (Pi.single k 1 : Fin d → ℕ) m ≤ 1 := by
  by_cases h : m = k
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

/-- `|p̄(r, x - y)| ≤ K r^{-d/2} exp(-|x - y|²/(32σr))` for `r ≥ 1`. -/
theorem abs_latticeGaussianD_le {σ r : ℝ} (hσ : 0 < σ) (hr : 1 ≤ r) (x y : Vertex d) :
    |latticeGaussianD σ r x y| ≤
      gaussConstD d σ 0 * r ^ (-((d : ℝ) / 2)) * Real.exp (-(‖edzD x y‖ ^ 2 / (32 * σ * r))) := by
  have h := abs_gaussDiff_le hσ hr (n := 0) (fun m => by simp) x y
  rw [latticeGaussianD_eq]
  simpa using h

/-- `|D_k p̄(r, · - y)(x)| ≤ K r^{-d/2 - 1/2} exp(-|x - y|²/(32σr))` for `r ≥ 1`. -/
theorem abs_fwdDiffD_latticeGaussianD_le {σ r : ℝ} (hσ : 0 < σ) (hr : 1 ≤ r) (k : Fin d)
    (x y : Vertex d) :
    |fwdDiffD k (fun z => latticeGaussianD σ r z y) x| ≤
      gaussConstD d σ 1 * r ^ (-((d : ℝ) / 2)) / Real.sqrt r *
        Real.exp (-(‖edzD x y‖ ^ 2 / (32 * σ * r))) := by
  rw [fwdDiffD_latticeGaussianD]
  have h := abs_gaussDiff_le hσ hr (n := (0 : Fin d → ℕ) + Pi.single k 1)
    (fun m => by simp only [Pi.add_apply, Pi.zero_apply, zero_add]; linarith [single_le_one k m])
    x y
  simpa only [zero_add, sum_single_eq, pow_one] using h

theorem sum_two_singles (k i : Fin d) :
    ∑ m, ((0 : Fin d → ℕ) + Pi.single k 1 + Pi.single i 1 : Fin d → ℕ) m = 2 := by
  simp only [Pi.add_apply, zero_add, Finset.sum_add_distrib, sum_single_eq]

theorem sum_three_singles (k i j : Fin d) :
    ∑ m, ((0 : Fin d → ℕ) + Pi.single k 1 + Pi.single i 1 + Pi.single j 1 : Fin d → ℕ) m = 3 := by
  simp only [Pi.add_apply, zero_add, Finset.sum_add_distrib, sum_single_eq]

/-- `|D_i D_k p̄(r, · - y)(x)| ≤ K r^{-d/2 - 1} exp(-|x - y|²/(32σr))` for `r ≥ 1`. -/
theorem abs_fwdDiffD_fwdDiffD_latticeGaussianD_le {σ r : ℝ} (hσ : 0 < σ) (hr : 1 ≤ r)
    (i k : Fin d) (x y : Vertex d) :
    |fwdDiffD i (fwdDiffD k fun z => latticeGaussianD σ r z y) x| ≤
      gaussConstD d σ 2 * r ^ (-((d : ℝ) / 2)) / r *
        Real.exp (-(‖edzD x y‖ ^ 2 / (32 * σ * r))) := by
  have hr0 : 0 ≤ r := by linarith
  rw [fwdDiffD_fwdDiffD_latticeGaussianD]
  have h := abs_gaussDiff_le hσ hr (n := (0 : Fin d → ℕ) + Pi.single k 1 + Pi.single i 1)
    (fun m => by
      simp only [Pi.add_apply, zero_add]
      linarith [single_le_one k m, single_le_one i m]) x y
  rwa [sum_two_singles, Real.sq_sqrt hr0] at h

/-- `|D_j D_i D_k p̄(r, · - y)(x)| ≤ K r^{-d/2 - 3/2} exp(-|x - y|²/(32σr))` for `r ≥ 1`. -/
theorem abs_fwdDiffD3_latticeGaussianD_le {σ r : ℝ} (hσ : 0 < σ) (hr : 1 ≤ r)
    (j i k : Fin d) (x y : Vertex d) :
    |fwdDiffD j (fwdDiffD i (fwdDiffD k fun z => latticeGaussianD σ r z y)) x| ≤
      gaussConstD d σ 3 * r ^ (-((d : ℝ) / 2)) / (r * Real.sqrt r) *
        Real.exp (-(‖edzD x y‖ ^ 2 / (32 * σ * r))) := by
  have hr0 : 0 ≤ r := by linarith
  rw [fwdDiffD3_latticeGaussianD]
  have h := abs_gaussDiff_le hσ hr (n := (0 : Fin d → ℕ) + Pi.single k 1 + Pi.single i 1 + Pi.single j 1)
    (fun m => by
      simp only [Pi.add_apply, zero_add]
      linarith [single_le_one k m, single_le_one i m, single_le_one j m]) x y
  rwa [sum_three_singles, pow_succ (Real.sqrt r) 2, Real.sq_sqrt hr0] at h

/-! ### The time derivative -/

theorem factorLe_update_gauss1'' {c : ℝ} (hc : 0 < c) (j : Fin d) :
    ∀ m, FactorLe c (if m = j then 2 else 0)
      (Function.update (fun _ => gauss1 c) j (gauss1'' c) m) := by
  intro m
  by_cases hm : m = j
  · subst hm
    rw [if_pos rfl, Function.update_self]
    exact factorLe_gauss1'' hc
  · rw [if_neg hm, Function.update_of_ne hm]
    exact factorLe_iterate hc (n := 0) (by norm_num)

theorem sum_ite_eq_const (j : Fin d) (a : ℕ) : ∑ m : Fin d, (if m = j then a else 0) = a := by
  simp

/-- `|∂_r p̄(r, x - y)| ≤ K r^{-d/2 - 1} exp(-|x - y|²/(32σr))` for `r ≥ 1`. -/
theorem abs_latticeGaussianTimeDerivD_le {σ r : ℝ} (hσ : 0 < σ) (hr : 1 ≤ r) (x y : Vertex d) :
    |latticeGaussianTimeDerivD σ r x y| ≤
      σ / 2 * d * gaussConstD d σ 2 * r ^ (-((d : ℝ) / 2)) / r *
        Real.exp (-(‖edzD x y‖ ^ 2 / (32 * σ * r))) := by
  have hr0 : 0 < r := by linarith
  have hc : 0 < 2 * σ * r := by positivity
  rw [latticeGaussianTimeDerivD_eq σ r hσ hr0, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ j : Fin d, |σ / 2 * ((2 * Real.pi * σ * r) ^ (-((d : ℝ) / 2)) *
      prodFactor (Function.update (fun _ => gauss1 (2 * σ * r)) j (gauss1'' (2 * σ * r))) x y)| ≤
      σ / 2 * (gaussConstD d σ 2 * r ^ (-((d : ℝ) / 2)) / r *
        Real.exp (-(‖edzD x y‖ ^ 2 / (32 * σ * r)))) := by
    intro j
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < σ / 2)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h := abs_gaussProd_le hσ hr (factorLe_update_gauss1'' hc j) x y
    rwa [sum_ite_eq_const, Real.sq_sqrt hr0.le] at h
  calc ∑ j : Fin d, |σ / 2 * (2 * Real.pi * σ * r) ^ (-((d : ℝ) / 2)) *
        prodFactor (Function.update (fun _ => gauss1 (2 * σ * r)) j (gauss1'' (2 * σ * r))) x y|
      ≤ ∑ _j : Fin d, σ / 2 * (gaussConstD d σ 2 * r ^ (-((d : ℝ) / 2)) / r *
          Real.exp (-(‖edzD x y‖ ^ 2 / (32 * σ * r)))) :=
        Finset.sum_le_sum fun j _ => by rw [mul_assoc]; exact hterm j
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

theorem fwdDiffD_latticeGaussianTimeDerivD {σ r : ℝ} (hσ : 0 < σ) (hr : 0 < r) (k : Fin d)
    (x y : Vertex d) :
    fwdDiffD k (fun z => latticeGaussianTimeDerivD σ r z y) x =
      σ / 2 * (2 * Real.pi * σ * r) ^ (-((d : ℝ) / 2)) *
        ∑ j, prodFactor (Function.update
          (Function.update (fun _ => gauss1 (2 * σ * r)) j (gauss1'' (2 * σ * r))) k
          (fwd1 (Function.update (fun _ => gauss1 (2 * σ * r)) j (gauss1'' (2 * σ * r)) k))) x y := by
  show latticeGaussianTimeDerivD σ r (x + Pi.single k 1) y - latticeGaussianTimeDerivD σ r x y = _
  rw [latticeGaussianTimeDerivD_eq σ r hσ hr, latticeGaussianTimeDerivD_eq σ r hσ hr, ← mul_sub,
    ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  exact fwdDiffD_prodFactor _ k y x

theorem factorLe_update_fwd1 {c : ℝ} (hc : 0 < c) (j k : Fin d) :
    ∀ m, FactorLe c ((if m = j then 2 else 0) + (if m = k then 1 else 0))
      (Function.update (Function.update (fun _ => gauss1 c) j (gauss1'' c)) k
        (fwd1 (Function.update (fun _ => gauss1 c) j (gauss1'' c) k)) m) := by
  intro m
  by_cases hmk : m = k
  · subst hmk
    rw [Function.update_self, if_pos rfl]
    by_cases hmj : m = j
    · subst hmj
      rw [Function.update_self, if_pos rfl]
      exact factorLe_fwd1_gauss1'' hc
    · rw [Function.update_of_ne hmj, if_neg hmj, zero_add]
      exact factorLe_iterate hc (n := 1) (by norm_num)
  · rw [Function.update_of_ne hmk, if_neg hmk, add_zero]
    exact factorLe_update_gauss1'' hc j m

/-- `|D_k ∂_r p̄(r, · - y)(x)| ≤ K r^{-d/2 - 3/2} exp(-|x - y|²/(32σr))` for `r ≥ 1`. -/
theorem abs_fwdDiffD_latticeGaussianTimeDerivD_le {σ r : ℝ} (hσ : 0 < σ) (hr : 1 ≤ r)
    (k : Fin d) (x y : Vertex d) :
    |fwdDiffD k (fun z => latticeGaussianTimeDerivD σ r z y) x| ≤
      σ / 2 * d * gaussConstD d σ 3 * r ^ (-((d : ℝ) / 2)) / (r * Real.sqrt r) *
        Real.exp (-(‖edzD x y‖ ^ 2 / (32 * σ * r))) := by
  have hr0 : 0 < r := by linarith
  have hc : 0 < 2 * σ * r := by positivity
  rw [fwdDiffD_latticeGaussianTimeDerivD hσ hr0, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ j : Fin d, |σ / 2 * (2 * Real.pi * σ * r) ^ (-((d : ℝ) / 2)) *
      prodFactor (Function.update
          (Function.update (fun _ => gauss1 (2 * σ * r)) j (gauss1'' (2 * σ * r))) k
          (fwd1 (Function.update (fun _ => gauss1 (2 * σ * r)) j (gauss1'' (2 * σ * r)) k)))
        x y| ≤
      σ / 2 * (gaussConstD d σ 3 * r ^ (-((d : ℝ) / 2)) / (r * Real.sqrt r) *
        Real.exp (-(‖edzD x y‖ ^ 2 / (32 * σ * r)))) := by
    intro j
    rw [mul_assoc, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < σ / 2)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h := abs_gaussProd_le hσ hr (factorLe_update_fwd1 hc j k) x y
    rwa [Finset.sum_add_distrib, sum_ite_eq_const, sum_ite_eq_const, pow_succ (Real.sqrt r) 2,
      Real.sq_sqrt hr0.le] at h
  calc _ ≤ ∑ _j : Fin d, σ / 2 * (gaussConstD d σ 3 * r ^ (-((d : ℝ) / 2)) / (r * Real.sqrt r) *
          Real.exp (-(‖edzD x y‖ ^ 2 / (32 * σ * r)))) := Finset.sum_le_sum fun j _ => hterm j
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

theorem fwdDiffD_fwdDiffD_self_latticeGaussianD (σ r : ℝ) (k : Fin d) (y x : Vertex d) :
    fwdDiffD k (fwdDiffD k fun z => latticeGaussianD σ r z y) x =
      (2 * Real.pi * σ * r) ^ (-((d : ℝ) / 2)) *
        prodFactor (Function.update (fun _ => gauss1 (2 * σ * r)) k
          ((fwd1^[2]) (gauss1 (2 * σ * r)))) x y := by
  rw [fwdDiffD_fwdDiffD_latticeGaussianD]
  beta_reduce
  congr 1
  unfold diffProd
  congr 1
  funext m u
  by_cases hm : m = k
  · subst hm
    simp only [Pi.add_apply, Pi.single_eq_same, Function.update_self, zero_add]
  · simp only [Pi.add_apply, Pi.zero_apply, Pi.single_eq_of_ne hm, Function.update_of_ne hm,
      add_zero, Function.iterate_zero_apply]

/-- `|∂_r p̄ - (σ/2) Σ_k D_k D_k p̄| ≤ K r^{-d/2 - 3/2} exp(-|x - y|²/(32σr))` for `r ≥ 1`. -/
theorem abs_timeDeriv_sub_secondDiffD_le {σ r : ℝ} (hσ : 0 < σ) (hr : 1 ≤ r) (x y : Vertex d) :
    |latticeGaussianTimeDerivD σ r x y -
        σ / 2 * ∑ k, fwdDiffD k (fwdDiffD k fun z => latticeGaussianD σ r z y) x| ≤
      σ / 2 * d * gaussConstD d σ 3 * r ^ (-((d : ℝ) / 2)) / (r * Real.sqrt r) *
        Real.exp (-(‖edzD x y‖ ^ 2 / (32 * σ * r))) := by
  have hr0 : 0 < r := by linarith
  have hc : 0 < 2 * σ * r := by positivity
  have e : latticeGaussianTimeDerivD σ r x y -
      σ / 2 * ∑ k, fwdDiffD k (fwdDiffD k fun z => latticeGaussianD σ r z y) x =
      ∑ k, σ / 2 * ((2 * Real.pi * σ * r) ^ (-((d : ℝ) / 2)) *
        prodFactor (Function.update (fun _ => gauss1 (2 * σ * r)) k
          (fun u => gauss1'' (2 * σ * r) u - (fwd1^[2]) (gauss1 (2 * σ * r)) u)) x y) := by
    rw [latticeGaussianTimeDerivD_eq σ r hσ hr0]
    simp only [fwdDiffD_fwdDiffD_self_latticeGaussianD]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← prodFactor_update_sub]
    ring
  rw [e]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ k : Fin d, |σ / 2 * ((2 * Real.pi * σ * r) ^ (-((d : ℝ) / 2)) *
      prodFactor (Function.update (fun _ => gauss1 (2 * σ * r)) k
        (fun u => gauss1'' (2 * σ * r) u - (fwd1^[2]) (gauss1 (2 * σ * r)) u)) x y)| ≤
      σ / 2 * (gaussConstD d σ 3 * r ^ (-((d : ℝ) / 2)) / (r * Real.sqrt r) *
        Real.exp (-(‖edzD x y‖ ^ 2 / (32 * σ * r)))) := by
    intro k
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < σ / 2)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hf : ∀ m, FactorLe (2 * σ * r) (if m = k then 3 else 0)
        (Function.update (fun _ => gauss1 (2 * σ * r)) k
          (fun u => gauss1'' (2 * σ * r) u - (fwd1^[2]) (gauss1 (2 * σ * r)) u) m) := by
      intro m
      by_cases hm : m = k
      · subst hm
        rw [if_pos rfl, Function.update_self]
        exact factorLe_gauss1''_sub hc
      · rw [if_neg hm, Function.update_of_ne hm]
        exact factorLe_iterate hc (n := 0) (by norm_num)
    have h := abs_gaussProd_le hσ hr hf x y
    rwa [sum_ite_eq_const, pow_succ (Real.sqrt r) 2, Real.sq_sqrt hr0.le] at h
  calc _ ≤ ∑ _k : Fin d, σ / 2 * (gaussConstD d σ 3 * r ^ (-((d : ℝ) / 2)) / (r * Real.sqrt r) *
          Real.exp (-(‖edzD x y‖ ^ 2 / (32 * σ * r)))) := Finset.sum_le_sum fun k _ => hterm k
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end Rigidity.Green.GeneralDim
