import Rigidity.Proofs.Green.GreenTimeIntegralThree
import Rigidity.Proofs.Green.DarioGuGaussianMass

/-!
# The Gaussian kernel on `ℤ^d`

For `p̄(t, z) = (2πσt)^{-d/2} exp(-|z|²/(2σt))` (`gaussianHeatD`):

* `hasSum_gaussianHeatD`: by the Poisson summation formula in each coordinate,
  `Σ_{x ∈ ℤ^d} p̄(t, x - y) = Θ_t^d` with `Θ_t = Σ_{n ∈ ℤ} exp(-2π²σt n²)`;
* `tsum_gaussianHeatD_le`: for `t ≥ 1` this is at most `M_σ = (1 + Θ_1)^d`;
* `gaussianHeatD_le_of_le_norm` and `tsum_gaussianHeatD_far_le`: the mass of `p̄(t, · - y)` at
  distance at least `L` from `y` is at most `2^{d/2} M_σ exp(-L²/(4σt))` for `t ≥ 1`.
-/

open Finset LatticeProb.Percolation

namespace Rigidity.Green

/-- `(Fin (d + 1) → ℤ) ≃ ℤ × (Fin d → ℤ)` by the first coordinate. -/
def finSuccIntEquiv (d : ℕ) : ℤ × (Fin d → ℤ) ≃ (Fin (d + 1) → ℤ) where
  toFun p := Fin.cons p.1 p.2
  invFun z := (z 0, Fin.tail z)
  left_inv p := by simp
  right_inv z := Fin.cons_self_tail z

theorem hasSum_mul_prod_pi {g : ℤ → ℝ} (hg0 : ∀ n, 0 ≤ g n) (hg : Summable g) {d : ℕ} {S : ℝ}
    (ih : HasSum (fun z : Fin d → ℤ => ∏ i, g (z i)) S) :
    HasSum (fun p : ℤ × (Fin d → ℤ) => g p.1 * ∏ i, g (p.2 i)) ((∑' n, g n) * S) := by
  have hn1 : Summable fun n => ‖g n‖ :=
    hg.congr fun n => by rw [Real.norm_eq_abs, abs_of_nonneg (hg0 n)]
  have hn2 : Summable fun z : Fin d → ℤ => ‖∏ i, g (z i)‖ := ih.summable.congr fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg fun i _ => hg0 _)]
  have h := HasSum.mul (f := g) (g := fun z : Fin d → ℤ => ∏ i, g (z i)) hg.hasSum ih
    (summable_mul_of_summable_norm (f := g) (g := fun z : Fin d → ℤ => ∏ i, g (z i)) hn1 hn2)
  exact h

theorem prod_finSuccIntEquiv (g : ℤ → ℝ) {d : ℕ} (p : ℤ × (Fin d → ℤ)) :
    ∏ i, g (finSuccIntEquiv d p i) = g p.1 * ∏ i, g (p.2 i) := by
  rw [Fin.prod_univ_succ]
  rfl

theorem hasSum_prod_pi_succ {g : ℤ → ℝ} (hg0 : ∀ n, 0 ≤ g n) (hg : Summable g) {d : ℕ} {S : ℝ}
    (ih : HasSum (fun z : Fin d → ℤ => ∏ i, g (z i)) S) :
    HasSum (fun z : Fin (d + 1) → ℤ => ∏ i, g (z i)) ((∑' n, g n) * S) := by
  have hP := hasSum_mul_prod_pi hg0 hg ih
  have hF : HasSum (fun p => ∏ i, g (finSuccIntEquiv d p i)) ((∑' n, g n) * S) :=
    hP.congr_fun fun p => prod_finSuccIntEquiv g p
  exact (finSuccIntEquiv d).hasSum_iff.1 hF

/-- `Σ_{z : Fin d → ℤ} Π_i g(z_i) = (Σ_n g(n))^d` for summable `g ≥ 0`. -/
theorem hasSum_prod_pi {g : ℤ → ℝ} (hg0 : ∀ n, 0 ≤ g n) (hg : Summable g) (d : ℕ) :
    HasSum (fun z : Fin d → ℤ => ∏ i, g (z i)) ((∑' n, g n) ^ d) := by
  induction d with
  | zero =>
    have h := hasSum_single (f := fun z : Fin 0 → ℤ => ∏ i, g (z i)) (default : Fin 0 → ℤ)
      (fun b hb => (hb (Subsingleton.elim _ _)).elim)
    simp only [Finset.univ_eq_empty, Finset.prod_empty, pow_zero] at h ⊢
    exact h
  | succ d ih =>
    rw [pow_succ']
    exact hasSum_prod_pi_succ hg0 hg ih

variable {d : ℕ}

theorem sq_norm_edzD (z y : Vertex d) : ‖edzD z y‖ ^ 2 = ∑ i, ((z i : ℝ) - y i) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp only [PiLp.sub_apply, Real.norm_eq_abs, sq_abs]
  rfl

theorem gaussianHeatD_nonneg' (σ t : ℝ) (hσt : 0 ≤ 2 * Real.pi * σ * t)
    (z : EuclideanSpace ℝ (Fin d)) : 0 ≤ gaussianHeatD d σ t z := by
  unfold gaussianHeatD
  exact mul_nonneg (Real.rpow_nonneg hσt _) (Real.exp_pos _).le

theorem gaussianHeatD_add_left_eq {σ t : ℝ} (hσ : 0 < σ) (ht : 0 < t) (z y : Vertex d) :
    gaussianHeatD d σ t (edzD (z + y) y) = (2 * Real.pi * σ * t) ^ (-((d : ℝ) / 2)) *
      ∏ i, Real.exp (-Real.pi * (2 * Real.pi * σ * t)⁻¹ * ((z i : ℤ) : ℝ) ^ 2) := by
  unfold gaussianHeatD
  rw [sq_norm_edzD, ← Real.exp_sum, Finset.sum_div, ← Finset.sum_neg_distrib]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply, Int.cast_add, add_sub_cancel_right]
  have := Real.pi_pos
  field_simp

/-- **Poisson summation on `ℤ^d`**: `Σ_{x ∈ ℤ^d} p̄(t, x - y) = (Σ_{n ∈ ℤ} exp(-2π²σt n²))^d`. -/
theorem hasSum_gaussianHeatD {σ t : ℝ} (hσ : 0 < σ) (ht : 0 < t) (y : Vertex d) :
    HasSum (fun x => gaussianHeatD d σ t (edzD x y))
      ((∑' n : ℤ, Real.exp (-(2 * Real.pi ^ 2 * σ * t) * (n : ℝ) ^ 2)) ^ d) := by
  set c : ℝ := 2 * Real.pi * σ * t with hc
  have hc0 : 0 < c := by positivity
  set a : ℝ := c⁻¹ with ha
  have ha0 : 0 < a := by positivity
  set g : ℤ → ℝ := fun n => Real.exp (-Real.pi * a * (n : ℝ) ^ 2) with hg
  have hgs : Summable g :=
    (summable_exp_neg_mul_int_sq (b := Real.pi * a) (by positivity)).congr fun n => by
      simp only [hg]
      ring_nf
  have hP : ∑' n, g n = c ^ (1 / 2 : ℝ) *
      ∑' n : ℤ, Real.exp (-(2 * Real.pi ^ 2 * σ * t) * (n : ℝ) ^ 2) := by
    have hpa : -Real.pi / a = -(2 * Real.pi ^ 2 * σ * t) := by
      rw [ha, hc]
      field_simp
    have h := Real.tsum_exp_neg_mul_int_sq ha0
    rw [hpa] at h
    rw [h, ha, Real.inv_rpow hc0.le, one_div, inv_inv]
  set Θ := ∑' n : ℤ, Real.exp (-(2 * Real.pi ^ 2 * σ * t) * (n : ℝ) ^ 2)
  have hprod := hasSum_prod_pi (g := g) (fun n => (Real.exp_pos _).le) hgs d
  have h1 : HasSum (fun z : Vertex d => gaussianHeatD d σ t (edzD (z + y) y))
      (c ^ (-((d : ℝ) / 2)) * (∑' n, g n) ^ d) := by
    have := hprod.mul_left (c ^ (-((d : ℝ) / 2)))
    refine this.congr_fun fun z => ?_
    rw [gaussianHeatD_add_left_eq hσ ht]
  have h2 : c ^ (-((d : ℝ) / 2)) * (∑' n, g n) ^ d = Θ ^ d := by
    rw [hP, mul_pow, ← mul_assoc, ← Real.rpow_natCast (c ^ (1 / 2 : ℝ)), ← Real.rpow_mul hc0.le,
      ← Real.rpow_add hc0]
    have : -((d : ℝ) / 2) + 1 / 2 * d = 0 := by ring
    rw [this, Real.rpow_zero, one_mul]
  rw [h2] at h1
  exact (Equiv.addRight y).hasSum_iff.1 (h1.congr_fun fun z => rfl) |>.congr_fun fun x => rfl

/-- The mass bound `M_σ = (1 + Σ_n exp(-2π²σ n²))^d`. -/
noncomputable def gaussMassBoundD (d : ℕ) (σ : ℝ) : ℝ :=
  (1 + ∑' n : ℤ, Real.exp (-(2 * Real.pi ^ 2 * σ) * (n : ℝ) ^ 2)) ^ d

theorem one_le_gaussMassBoundD {σ : ℝ} (hσ : 0 < σ) : 1 ≤ gaussMassBoundD d σ := by
  unfold gaussMassBoundD
  have := one_le_tsum_exp_neg_mul_int_sq (b := 2 * Real.pi ^ 2 * σ) (by positivity)
  exact one_le_pow₀ (by linarith)

theorem summable_gaussianHeatD {σ t : ℝ} (hσ : 0 < σ) (ht : 0 < t) (y : Vertex d) :
    Summable fun x => gaussianHeatD d σ t (edzD x y) :=
  (hasSum_gaussianHeatD hσ ht y).summable

/-- `Σ_{x ∈ ℤ^d} p̄(t, x - y) ≤ M_σ` for `t ≥ 1`. -/
theorem tsum_gaussianHeatD_le {σ t : ℝ} (hσ : 0 < σ) (ht : 1 ≤ t) (y : Vertex d) :
    ∑' x, gaussianHeatD d σ t (edzD x y) ≤ gaussMassBoundD d σ := by
  rw [(hasSum_gaussianHeatD hσ (by linarith) y).tsum_eq, gaussMassBoundD]
  have hb₀ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  have h := tsum_exp_neg_mul_int_sq_le (b := 2 * Real.pi ^ 2 * σ * t) hb₀
    (le_mul_of_one_le_right hb₀.le ht)
  have hΘ1 := one_le_tsum_exp_neg_mul_int_sq (b := 2 * Real.pi ^ 2 * σ * t) (by positivity)
  have hΘ₀ : 0 ≤ ∑' n : ℤ, Real.exp (-(2 * Real.pi ^ 2 * σ) * (n : ℝ) ^ 2) :=
    tsum_nonneg fun n => (Real.exp_pos _).le
  have hE : Real.exp (-(2 * Real.pi ^ 2 * σ * t - 2 * Real.pi ^ 2 * σ)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith
  refine pow_le_pow_left₀ (by linarith) (h.trans ?_) d
  have := mul_le_of_le_one_left hΘ₀ hE
  linarith

/-- `p̄(t, z) ≤ 2^{d/2} exp(-L²/(4σt)) p̄(2t, z)` for `|z| ≥ L ≥ 0`. -/
theorem gaussianHeatD_le_of_le_norm {σ t L : ℝ} (hσ : 0 < σ) (ht : 0 < t) (hL : 0 ≤ L)
    {z : EuclideanSpace ℝ (Fin d)} (hz : L ≤ ‖z‖) :
    gaussianHeatD d σ t z ≤
      2 ^ ((d : ℝ) / 2) * Real.exp (-(L ^ 2 / (4 * σ * t))) * gaussianHeatD d σ (2 * t) z := by
  unfold gaussianHeatD
  have hc : (2 * Real.pi * σ * t) ^ (-((d : ℝ) / 2)) =
      2 ^ ((d : ℝ) / 2) * (2 * Real.pi * σ * (2 * t)) ^ (-((d : ℝ) / 2)) := by
    rw [show 2 * Real.pi * σ * (2 * t) = 2 * (2 * Real.pi * σ * t) by ring,
      Real.mul_rpow (x := 2) (y := 2 * Real.pi * σ * t) (by norm_num) (by positivity),
      ← mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    simp
  rw [hc]
  have hE : Real.exp (-(‖z‖ ^ 2 / (2 * σ * t))) ≤
      Real.exp (-(L ^ 2 / (4 * σ * t))) * Real.exp (-(‖z‖ ^ 2 / (2 * σ * (2 * t)))) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have hL2 : L ^ 2 ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ hL hz 2
    have h4 : 0 < 4 * σ * t := by positivity
    have e1 : ‖z‖ ^ 2 / (2 * σ * t) = 2 * (‖z‖ ^ 2 / (4 * σ * t)) := by
      field_simp
      ring
    have e2 : ‖z‖ ^ 2 / (2 * σ * (2 * t)) = ‖z‖ ^ 2 / (4 * σ * t) := by
      rw [show 2 * σ * (2 * t) = 4 * σ * t by ring]
    have e3 : L ^ 2 / (4 * σ * t) ≤ ‖z‖ ^ 2 / (4 * σ * t) := div_le_div_of_nonneg_right hL2 h4.le
    rw [e1, e2]
    linarith
  have h0 : 0 ≤ 2 ^ ((d : ℝ) / 2) * (2 * Real.pi * σ * (2 * t)) ^ (-((d : ℝ) / 2)) := by
    positivity
  calc 2 ^ ((d : ℝ) / 2) * (2 * Real.pi * σ * (2 * t)) ^ (-((d : ℝ) / 2)) *
        Real.exp (-(‖z‖ ^ 2 / (2 * σ * t)))
      ≤ 2 ^ ((d : ℝ) / 2) * (2 * Real.pi * σ * (2 * t)) ^ (-((d : ℝ) / 2)) *
        (Real.exp (-(L ^ 2 / (4 * σ * t))) * Real.exp (-(‖z‖ ^ 2 / (2 * σ * (2 * t))))) :=
        mul_le_mul_of_nonneg_left hE h0
    _ = _ := by ring

/-- **The Gaussian tail**: the mass of `p̄(t, · - y)` at distance at least `L` from `y` is at most
`2^{d/2} M_σ exp(-L²/(4σt))` for `t ≥ 1`. -/
theorem tsum_gaussianHeatD_far_le {σ t L : ℝ} (hσ : 0 < σ) (ht : 1 ≤ t) (hL : 0 ≤ L)
    (y : Vertex d) :
    ∑' x, (if L ≤ ‖edzD x y‖ then gaussianHeatD d σ t (edzD x y) else 0) ≤
      2 ^ ((d : ℝ) / 2) * gaussMassBoundD d σ * Real.exp (-(L ^ 2 / (4 * σ * t))) := by
  have ht0 : 0 < t := by linarith
  have hs2 := summable_gaussianHeatD (d := d) hσ (by linarith : (0 : ℝ) < 2 * t) y
  have hle : ∀ x, (if L ≤ ‖edzD x y‖ then gaussianHeatD d σ t (edzD x y) else 0) ≤
      2 ^ ((d : ℝ) / 2) * Real.exp (-(L ^ 2 / (4 * σ * t))) *
        gaussianHeatD d σ (2 * t) (edzD x y) := by
    intro x
    split_ifs with h
    · exact gaussianHeatD_le_of_le_norm hσ ht0 hL h
    · exact mul_nonneg (by positivity) (gaussianHeatD_nonneg' σ (2 * t) (by positivity) _)
  have hs : Summable fun x =>
      (if L ≤ ‖edzD x y‖ then gaussianHeatD d σ t (edzD x y) else 0) :=
    (hs2.mul_left (2 ^ ((d : ℝ) / 2) * Real.exp (-(L ^ 2 / (4 * σ * t))))).of_nonneg_of_le
      (fun x => by
        split_ifs
        · exact gaussianHeatD_nonneg' σ t (by positivity) _
        · exact le_rfl) hle
  calc _ ≤ ∑' x, 2 ^ ((d : ℝ) / 2) * Real.exp (-(L ^ 2 / (4 * σ * t))) *
        gaussianHeatD d σ (2 * t) (edzD x y) :=
        hs.tsum_le_tsum hle (hs2.mul_left _)
    _ = 2 ^ ((d : ℝ) / 2) * Real.exp (-(L ^ 2 / (4 * σ * t))) *
        ∑' x, gaussianHeatD d σ (2 * t) (edzD x y) := tsum_mul_left
    _ ≤ 2 ^ ((d : ℝ) / 2) * Real.exp (-(L ^ 2 / (4 * σ * t))) * gaussMassBoundD d σ :=
        mul_le_mul_of_nonneg_left (tsum_gaussianHeatD_le hσ (by linarith) y) (by positivity)
    _ = _ := by ring

end Rigidity.Green
