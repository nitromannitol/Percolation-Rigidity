import Rigidity.Proofs.Percolation.BondShellSummation

/-!
# Exponential summation over bond shells

The `n`-th bond shell around a lattice cube of radius `R` in `ℤ^d` has at most
`2d 3^d (R+1)^d (n+1)^d` bonds. A bond function with exponential decay in the shell index is
therefore summable, with sum at the volume scale `(R+1)^d`; the shell kernel
`∑ (n+1)^d e^{-cn}` is at most a constant times `1 + c^{-(d+2)}`, so at rate `c/r` it grows at
most like `r^{d+2}`.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation

/-- The bond-count factor of the `n`-th shell around a cube of radius `R`. -/
theorem shell_card_factor_le (d R n : ℕ) :
    ((2 * d * (2 * (R + n + 1) + 1) ^ d : ℕ) : ℝ) ≤
      2 * d * 3 ^ d * ((R : ℝ) + 1) ^ d * ((n : ℝ) + 1) ^ d := by
  have hR : 0 ≤ (R : ℝ) := Nat.cast_nonneg _
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have h : 2 * ((R : ℝ) + n + 1) + 1 ≤ 3 * ((R : ℝ) + 1) * ((n : ℝ) + 1) := by
    nlinarith [mul_nonneg hR hn]
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * ((R : ℝ) + n + 1) + 1) h d
  push_cast
  calc
    2 * (d : ℝ) * (2 * ((R : ℝ) + n + 1) + 1) ^ d ≤
        2 * d * (3 * ((R : ℝ) + 1) * ((n : ℝ) + 1)) ^ d :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by rw [mul_pow, mul_pow]; ring

/-- A pointwise bound for the exponential shell kernel. -/
theorem shift_pow_mul_exp_le (d : ℕ) {c : ℝ} (hc : 0 < c) (n : ℕ) (hn : 1 ≤ n) :
    ((n : ℝ) + 1) ^ d * Real.exp (-c * n) ≤
      (4 * 2 ^ d * ((d + 2).factorial : ℝ)) / c ^ (d + 2) * (1 / ((n : ℝ) + 1) ^ 2) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hfac := Real.pow_div_factorial_le_exp (x := c * n) (by positivity) (d + 2)
  have hf : (0 : ℝ) < ((d + 2).factorial : ℝ) := by positivity
  have h1 : (c * n) ^ (d + 2) ≤ ((d + 2).factorial : ℝ) * Real.exp (c * n) := by
    rw [div_le_iff₀ hf] at hfac
    linarith
  have h2 : ((n : ℝ) + 1) ^ (d + 2) ≤ 2 ^ (d + 2) * (n : ℝ) ^ (d + 2) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) _
  have hexp : Real.exp (c * n) * Real.exp (-c * n) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [mul_one_div, div_div, le_div_iff₀ (by positivity)]
  calc
    ((n : ℝ) + 1) ^ d * Real.exp (-c * n) * (c ^ (d + 2) * ((n : ℝ) + 1) ^ 2)
        = ((n : ℝ) + 1) ^ (d + 2) * (c ^ (d + 2) * Real.exp (-c * n)) := by ring
    _ ≤ (2 ^ (d + 2) * (n : ℝ) ^ (d + 2)) * (c ^ (d + 2) * Real.exp (-c * n)) :=
      mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = 2 ^ (d + 2) * ((c * n) ^ (d + 2) * Real.exp (-c * n)) := by ring
    _ ≤ 2 ^ (d + 2) * ((((d + 2).factorial : ℝ) * Real.exp (c * n)) * Real.exp (-c * n)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le)
        (by positivity)
    _ = 4 * 2 ^ d * ((d + 2).factorial : ℝ) := by
      rw [mul_assoc (((d + 2).factorial : ℝ)), hexp]
      ring

/-- The exponential shell kernel has total mass at most a constant times `1 + c^{-(d+2)}`. -/
theorem exp_shell_kernel_sum_le (d : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ c : ℝ, 0 < c →
      Summable (fun n : ℕ => ((n : ℝ) + 1) ^ d * Real.exp (-c * n)) ∧
      (∑' n : ℕ, ((n : ℝ) + 1) ^ d * Real.exp (-c * n)) ≤ D * (1 + (1 / c) ^ (d + 2)) := by
  let w : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) ^ 2
  let J : ℝ := ∑' n, w n
  let A : ℝ := 4 * 2 ^ d * ((d + 2).factorial : ℝ)
  let D : ℝ := (1 + A) * (1 + J)
  have hw : Summable w := by
    have h := (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).comp_injective
      Nat.succ_injective
    simpa only [w, Function.comp_def, Nat.cast_succ] using h
  have hw0 (n : ℕ) : 0 ≤ w n := by dsimp [w]; positivity
  have hJ : 0 ≤ J := tsum_nonneg hw0
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D, hD, fun c hc => ?_⟩
  let q : ℕ → ℝ := fun n => ((n : ℝ) + 1) ^ d * Real.exp (-c * n)
  let K : ℝ := 1 + A / c ^ (d + 2)
  have hAc : 0 ≤ A / c ^ (d + 2) := div_nonneg hA (pow_nonneg hc.le _)
  have hq0 (n : ℕ) : 0 ≤ q n := by dsimp [q]; positivity
  have hpoint (n : ℕ) : q n ≤ K * w n := by
    by_cases hn : n = 0
    · subst n
      have hq : q 0 = 1 := by simp [q]
      have hw1 : w 0 = 1 := by simp [w]
      rw [hq, hw1]
      dsimp only [K]
      linarith
    · have h := shift_pow_mul_exp_le d hc n (Nat.pos_of_ne_zero hn)
      calc
        q n ≤ A / c ^ (d + 2) * w n := h
        _ ≤ K * w n := mul_le_mul_of_nonneg_right (by dsimp only [K]; linarith) (hw0 n)
  have hqs : Summable q := Summable.of_nonneg_of_le hq0 hpoint (hw.mul_left K)
  have hsum : (∑' n, q n) ≤ K * J := by
    calc
      _ ≤ ∑' n, K * w n := hqs.tsum_le_tsum hpoint (hw.mul_left K)
      _ = _ := tsum_mul_left
  have hinv : 0 ≤ (1 / c) ^ (d + 2) := by positivity
  have hcoeff : K ≤ (1 + A) * (1 + (1 / c) ^ (d + 2)) := by
    dsimp only [K]
    rw [one_div, inv_pow, div_eq_mul_inv]
    have hinv' : 0 ≤ (c ^ (d + 2))⁻¹ := inv_nonneg.mpr (pow_nonneg hc.le _)
    nlinarith [mul_nonneg hA hinv']
  refine ⟨hqs, hsum.trans ?_⟩
  calc
    K * J ≤ ((1 + A) * (1 + (1 / c) ^ (d + 2))) * (1 + J) :=
      mul_le_mul hcoeff (by linarith) hJ (by positivity)
    _ = D * (1 + (1 / c) ^ (d + 2)) := by dsimp only [D]; ring

/-- The exponential shell kernel at rate `c/r` grows at most like `r^{d+2}`. -/
theorem exp_shell_kernel_order_growth (d : ℕ) {c : ℝ} (hc : 0 < c) :
    ∃ D : ℝ, 0 < D ∧ ∀ r : ℕ, 1 ≤ r →
      Summable (fun n : ℕ => ((n : ℝ) + 1) ^ d *
        Real.exp (-(c * (1 / (r : ℝ))) * n)) ∧
      1 + (∑' n : ℕ, ((n : ℝ) + 1) ^ d *
        Real.exp (-(c * (1 / (r : ℝ))) * n)) ≤ D * (r : ℝ) ^ (d + 2) := by
  obtain ⟨E, hE, hkernel⟩ := exp_shell_kernel_sum_le d
  let D : ℝ := 1 + E * (1 + (1 / c) ^ (d + 2))
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D, hD, fun r hr => ?_⟩
  have hu1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hu : 0 < (r : ℝ) := zero_lt_one.trans_le hu1
  have hrate : 0 < c * (1 / (r : ℝ)) := by positivity
  obtain ⟨hs, hsum⟩ := hkernel (c * (1 / (r : ℝ))) hrate
  have hinv : 1 / (c * (1 / (r : ℝ))) = (1 / c) * (r : ℝ) := by field_simp
  rw [hinv, mul_pow] at hsum
  have hp : (1 : ℝ) ≤ (r : ℝ) ^ (d + 2) := one_le_pow₀ hu1
  refine ⟨hs, ?_⟩
  calc
    _ ≤ 1 + E * (1 + (1 / c) ^ (d + 2) * (r : ℝ) ^ (d + 2)) := add_le_add le_rfl hsum
    _ ≤ (r : ℝ) ^ (d + 2) + E * ((r : ℝ) ^ (d + 2) + (1 / c) ^ (d + 2) * (r : ℝ) ^ (d + 2)) :=
      add_le_add hp (mul_le_mul_of_nonneg_left (add_le_add hp le_rfl) hE.le)
    _ = D * (r : ℝ) ^ (d + 2) := by dsimp [D]; ring

/-- A bond function with exponential decay in the shell index is summable at volume scale. -/
theorem summable_bond_shells_exp {d : ℕ} (z : Vertex d) (R : ℕ) (f : Bond d → ℝ)
    (K c : ℝ) (hK : 0 ≤ K) (hc : 0 < c) (hf : ∀ e, 0 ≤ f e)
    (hglobal : ∀ e, f e ≤ K)
    (hdecay : ∀ n, 1 ≤ n → ∀ e ∈ bondShell d z R n, f e ≤ K * Real.exp (-c * n)) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ d * Real.exp (-c * n)) ∧
    Summable f ∧
      (∑' e, f e) ≤ 2 * d * 3 ^ d * ((R : ℝ) + 1) ^ d * K *
        (1 + ∑' n : ℕ, ((n : ℝ) + 1) ^ d * Real.exp (-c * n)) := by
  classical
  let q : ℕ → ℝ := fun n => ((n : ℝ) + 1) ^ d * Real.exp (-c * n)
  let g : ℕ → ℝ := fun n => K * Real.exp (-c * n)
  let H : ℕ → ℝ := fun n =>
    ((2 * d * (2 * (R + n + 1) + 1) ^ d : ℕ) : ℝ) * g n
  let C : ℝ := 2 * d * 3 ^ d * ((R : ℝ) + 1) ^ d * K
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hq (n : ℕ) : 0 ≤ q n := by dsimp [q]; positivity
  obtain ⟨E, -, hkernel⟩ := exp_shell_kernel_sum_le d
  have hqsum : Summable q := (hkernel c hc).1
  have hH (n : ℕ) : 0 ≤ H n := by dsimp [H, g]; positivity
  have hHbound (n : ℕ) : H n ≤ C * q n := by
    have h := shell_card_factor_le d R n
    dsimp only [H, g, C, q]
    calc
      _ ≤ (2 * d * 3 ^ d * ((R : ℝ) + 1) ^ d * ((n : ℝ) + 1) ^ d) *
          (K * Real.exp (-c * n)) :=
        mul_le_mul_of_nonneg_right h (mul_nonneg hK (Real.exp_pos _).le)
      _ = _ := by ring
  have hHsum : Summable H := Summable.of_nonneg_of_le hH hHbound (hqsum.mul_left C)
  have hbound : ∀ n e, e ∈ bondShell d z R n → f e ≤ g n := by
    intro n e he
    by_cases hn : n = 0
    · subst n
      simpa [g] using hglobal e
    · exact hdecay n (Nat.pos_of_ne_zero hn) e he
  have ⟨hfs, hsum⟩ := summable_of_bondShell_bound d z R f g hf
    (fun n => mul_nonneg hK (Real.exp_pos _).le) hHsum hbound
  have hbase : (∑ e ∈ bondBox d z R, f e) ≤ C := by
    have hcard := card_bondsIncidentTo_le d (Rigidity.Proofs.S3.cubeFinset z R)
    have hvolume : ((bondBox d z R).card : ℝ) ≤ 2 * d * 3 ^ d * ((R : ℝ) + 1) ^ d := by
      have h := shell_card_factor_le d R 0
      have h' : ((bondBox d z R).card : ℝ) ≤
          ((2 * d * (2 * (R + 0 + 1) + 1) ^ d : ℕ) : ℝ) := by
        have hn : (bondBox d z R).card ≤ 2 * d * (2 * (R + 0 + 1) + 1) ^ d := by
          change (bondsIncidentTo d (Rigidity.Proofs.S3.cubeFinset z R)).card ≤ _
          rw [Rigidity.Proofs.S3.card_cubeFinset] at hcard
          exact hcard.trans (by gcongr; omega)
        exact_mod_cast hn
      exact h'.trans (by simpa using h)
    calc
      _ ≤ ∑ _e ∈ bondBox d z R, K := Finset.sum_le_sum fun e _ => hglobal e
      _ = ((bondBox d z R).card : ℝ) * K := by simp
      _ ≤ C := mul_le_mul_of_nonneg_right hvolume hK
  have hsumH : (∑' n, H n) ≤ C * ∑' n, q n := by
    calc
      _ ≤ ∑' n, C * q n := hHsum.tsum_le_tsum hHbound (hqsum.mul_left C)
      _ = _ := tsum_mul_left
  refine ⟨hqsum, hfs, hsum.trans ?_⟩
  calc
    _ ≤ C + C * ∑' n, q n := add_le_add hbase hsumH
    _ = _ := by dsimp only [C, q]; ring

/-- Positive powers of an exponentially localized bond function are summable at volume scale,
with the rate multiplied by the power. -/
theorem summable_bond_shells_exp_rpow {d : ℕ} (z : Vertex d) (R : ℕ) (f : Bond d → ℝ)
    (K c t : ℝ) (hK : 0 ≤ K) (hc : 0 < c) (ht : 0 < t) (hf : ∀ e, 0 ≤ f e)
    (hglobal : ∀ e, f e ≤ K)
    (hdecay : ∀ n, 1 ≤ n → ∀ e ∈ bondShell d z R n, f e ≤ K * Real.exp (-c * n)) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ d * Real.exp (-(c * t) * n)) ∧
    Summable (fun e => (f e) ^ t) ∧
      (∑' e, (f e) ^ t) ≤ 2 * d * 3 ^ d * ((R : ℝ) + 1) ^ d * K ^ t *
        (1 + ∑' n : ℕ, ((n : ℝ) + 1) ^ d * Real.exp (-(c * t) * n)) := by
  have hglobal' (e : Bond d) : (f e) ^ t ≤ K ^ t :=
    Real.rpow_le_rpow (hf e) (hglobal e) ht.le
  have hdecay' (n : ℕ) (hn : 1 ≤ n) (e : Bond d) (he : e ∈ bondShell d z R n) :
      (f e) ^ t ≤ K ^ t * Real.exp (-(c * t) * n) := by
    have h := Real.rpow_le_rpow (hf e) (hdecay n hn e he) ht.le
    rw [Real.mul_rpow hK (Real.exp_pos _).le, ← Real.exp_mul] at h
    convert h using 1; congr 2; ring
  exact summable_bond_shells_exp z R (fun e => (f e) ^ t) (K ^ t) (c * t)
    (Real.rpow_nonneg hK _) (mul_pos hc ht) (fun e => Real.rpow_nonneg (hf e) _)
    hglobal' hdecay'

end Rigidity.Percolation
