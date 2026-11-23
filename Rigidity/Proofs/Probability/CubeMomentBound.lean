import Rigidity.Proofs.Probability.CubeMoments

/-!
# Moments of functions on the Bernoulli cube from their vertical derivatives

The moment inequality used by Armstrong and Lin in the proof of their Proposition 2.2 (the
concentration inequality of Dario, Proposition 2.17), for the product Bernoulli law on a finite
cube: for `q ≥ 2` and `c = min(p, 1 - p)`,

  `E[|F - E F|^q] ≤ 2 (3 q / c)^{q/2} E[𝕍[F]^{q/2}]`,  `𝕍[F] = Σ_i (F - coordAvg p i F)²`.

Armstrong and Lin cite it from Boucheron, Lugosi and Massart; Boucheron, Bousquet, Lugosi and
Massart (Ann. Probab. 33 (2005), Theorem 2) prove it with the resampled quantity `V⁺`. Here it
follows from their recursion (`cubeExp_posPart_rpow_le`) as in their proof of Theorem 2: Hölder's
inequality turns it into `a_q^q ≤ a_{q-1}^q + (q/c) a_q^{q-2} v_q` for the norms
`a_q = E[Y₊^q]^{1/q}` and `v_q = E[𝕍^{q/2}]^{2/q}`, and an induction on `⌈q⌉`, started by the
Efron-Stein inequality, gives `a_q² ≤ (3/c) q v_q` (`moment_bound_of_recursion`, with the
elementary bound `((q-1)/q)^{q/2} ≤ 2/3`).

* `cubeExp_mul_le`: Hölder's inequality; `cubeExp_rpow_le_rpow`: Lyapunov's inequality;
* `sq_le_of_rpow_recursion`, `moment_bound_of_recursion`: the induction on the moments;
* `cubeExp_posPart_rpow_le_of_mean_zero`: `E[Y₊^q] ≤ (3q/c)^{q/2} E[𝕍[Y]^{q/2}]` for `E Y = 0`;
* `cubeExp_abs_sub_rpow_le`: the two-sided moment inequality above.
-/

namespace Rigidity.Probability

open Finset

/-- `((q - 1)/q)^{q/2} ≤ 2/3` for `q ≥ 2`, from Bernoulli's inequality. -/
theorem rpow_div_le_two_thirds {q : ℝ} (hq : 2 ≤ q) : ((q - 1) / q) ^ (q / 2) ≤ 2 / 3 := by
  have hq1 : 0 < q - 1 := by linarith
  have hs : 1 ≤ q / 2 := by linarith
  have hu : 0 ≤ 1 / (q - 1) := by positivity
  have hb := one_add_mul_self_le_rpow_one_add (s := 1 / (q - 1)) (by linarith) hs
  have e : 1 + 1 / (q - 1) = q / (q - 1) := by field_simp; ring
  rw [e] at hb
  have h32 : 3 / 2 ≤ 1 + q / 2 * (1 / (q - 1)) := by
    have : 1 / 2 ≤ q / 2 * (1 / (q - 1)) := by
      rw [mul_one_div, le_div_iff₀ hq1]; linarith
    linarith
  have hge : 3 / 2 ≤ (q / (q - 1)) ^ (q / 2) := le_trans h32 hb
  have e2 : (q - 1) / q = (q / (q - 1))⁻¹ := (inv_div q (q - 1)).symm
  rw [e2, Real.inv_rpow (by positivity)]
  calc ((q / (q - 1)) ^ (q / 2))⁻¹ ≤ (3 / 2)⁻¹ := inv_anti₀ (by norm_num) hge
    _ = 2 / 3 := by norm_num

/-- **One step of the induction on the moments**: if `a^q ≤ A^q + (q/c) a^{q-2} v` and
`A² ≤ (3/c)(q - 1) v`, then `a² ≤ (3/c) q v`. -/
theorem sq_le_of_rpow_recursion {q c v a A : ℝ} (hq : 2 ≤ q) (hc : 0 < c) (hv : 0 ≤ v)
    (ha : 0 ≤ a) (hA : 0 ≤ A) (hAv : A ^ 2 ≤ 3 / c * (q - 1) * v)
    (hrec : a ^ q ≤ A ^ q + q / c * a ^ (q - 2) * v) : a ^ 2 ≤ 3 / c * q * v := by
  set s := q / 2 with hs_def
  have hs : 1 ≤ s := by rw [hs_def]; linarith
  have hsq : ∀ z : ℝ, 0 ≤ z → z ^ q = (z ^ 2) ^ s := by
    intro z hz
    rw [← Real.rpow_natCast z 2, ← Real.rpow_mul hz, hs_def]
    congr 1
    push_cast
    ring
  have hsq2 : ∀ z : ℝ, 0 ≤ z → z ^ (q - 2) = (z ^ 2) ^ (s - 1) := by
    intro z hz
    rw [← Real.rpow_natCast z 2, ← Real.rpow_mul hz, hs_def]
    congr 1
    push_cast
    ring
  rw [hsq a ha, hsq A hA, hsq2 a ha] at hrec
  have hT0 : 0 ≤ a ^ 2 := sq_nonneg a
  have hU0 : 0 ≤ A ^ 2 := sq_nonneg A
  by_contra hcon
  rw [not_le] at hcon
  rcases hv.eq_or_lt with hv0 | hvpos
  · subst hv0
    have hU : A ^ 2 = 0 := le_antisymm (by simpa using hAv) hU0
    rw [hU, Real.zero_rpow (by linarith : s ≠ 0)] at hrec
    simp only [mul_zero, add_zero] at hrec
    have hTpos : 0 < a ^ 2 := by simpa using hcon
    have := Real.rpow_pos_of_pos hTpos s
    linarith
  · set B := 3 / c * q * v with hB_def
    have hB : 0 < B := by rw [hB_def]; have : 0 < q := by linarith
                          positivity
    set x := a ^ 2 / B with hx_def
    have hx : 1 < x := by rw [hx_def, one_lt_div hB]; exact hcon
    have hTx : a ^ 2 = x * B := by rw [hx_def]; field_simp
    have hUB : A ^ 2 ≤ (q - 1) / q * B := by
      calc A ^ 2 ≤ 3 / c * (q - 1) * v := hAv
        _ = (q - 1) / q * B := by rw [hB_def]; field_simp
    have hUs : (A ^ 2) ^ s ≤ ((q - 1) / q) ^ s * B ^ s := by
      have hq1 : 0 ≤ (q - 1) / q := div_nonneg (by linarith) (by linarith)
      rw [← Real.mul_rpow hq1 hB.le]
      exact Real.rpow_le_rpow hU0 hUB (by linarith)
    have hqv : q / c * v = B / 3 := by rw [hB_def]; field_simp
    have hTs : (a ^ 2) ^ s = x ^ s * B ^ s := by
      rw [hTx, Real.mul_rpow (by linarith) hB.le]
    have hTs1 : (a ^ 2) ^ (s - 1) = x ^ (s - 1) * B ^ (s - 1) := by
      rw [hTx, Real.mul_rpow (by linarith) hB.le]
    have hBs : B ^ s = B * B ^ (s - 1) := by
      rw [Real.rpow_sub_one hB.ne']; field_simp
    have hxs : x ^ s = x * x ^ (s - 1) := by
      rw [Real.rpow_sub_one (by linarith : x ≠ 0)]; field_simp
    have hy : 1 ≤ x ^ (s - 1) := Real.one_le_rpow hx.le (by linarith)
    have hZ : 0 < B * B ^ (s - 1) := mul_pos hB (Real.rpow_pos_of_pos hB _)
    have hκ : ((q - 1) / q) ^ s ≤ 2 / 3 := rpow_div_le_two_thirds hq
    have e1 : (a ^ 2) ^ s = x * x ^ (s - 1) * (B * B ^ (s - 1)) := by
      rw [hTs, hxs, hBs]
    have e2 : q / c * (a ^ 2) ^ (s - 1) * v = x ^ (s - 1) / 3 * (B * B ^ (s - 1)) := by
      rw [hTs1]
      calc q / c * (x ^ (s - 1) * B ^ (s - 1)) * v
          = (q / c * v) * (x ^ (s - 1) * B ^ (s - 1)) := by ring
        _ = B / 3 * (x ^ (s - 1) * B ^ (s - 1)) := by rw [hqv]
        _ = _ := by ring
    have e3 : (A ^ 2) ^ s ≤ ((q - 1) / q) ^ s * (B * B ^ (s - 1)) := by
      rw [← hBs]; exact hUs
    have h1 : x * x ^ (s - 1) * (B * B ^ (s - 1)) ≤
        (((q - 1) / q) ^ s + x ^ (s - 1) / 3) * (B * B ^ (s - 1)) := by
      rw [← e1]
      have := hrec
      rw [e2] at this
      nlinarith
    have hxy := le_of_mul_le_mul_right h1 hZ
    nlinarith [mul_nonneg (sub_nonneg.2 hx.le) (sub_nonneg.2 hy)]

/-- **The induction on the moments** (Boucheron, Bousquet, Lugosi and Massart, proof of
Theorem 2): from the recursion `a_t^t ≤ a_{t-1}^t + (t/c) a_t^{t-2} v_t` for `t ≥ 2`, the bound
`a_s² ≤ v_2` for `1 ≤ s ≤ 2` and the monotonicity of `v`, `a_t² ≤ (3/c) t v_t` for `t ≥ 2`. -/
theorem moment_bound_of_recursion {a v : ℝ → ℝ} {c : ℝ} (hc : 0 < c) (hc2 : c ≤ 1 / 2)
    (ha0 : ∀ t, 0 ≤ a t) (hv0 : ∀ t, 0 ≤ v t) (hbase : ∀ s, 1 ≤ s → s ≤ 2 → a s ^ 2 ≤ v 2)
    (hmono : ∀ t t', 2 ≤ t → t ≤ t' → v t ≤ v t')
    (hrec : ∀ t, 2 ≤ t → a t ^ t ≤ a (t - 1) ^ t + t / c * a t ^ (t - 2) * v t) :
    ∀ t, 2 ≤ t → a t ^ 2 ≤ 3 / c * t * v t := by
  have h6 : 6 ≤ 3 / c := by rw [le_div_iff₀ hc]; linarith
  have hlow : ∀ t, 2 ≤ t → t < 3 → a (t - 1) ^ 2 ≤ 3 / c * (t - 1) * v t := by
    intro t ht ht3
    have h1 : a (t - 1) ^ 2 ≤ v 2 := hbase (t - 1) (by linarith) (by linarith)
    have h2 : v 2 ≤ v t := hmono 2 t le_rfl ht
    have h3 : v t ≤ 3 / c * (t - 1) * v t := by
      have : 1 ≤ 3 / c * (t - 1) := by nlinarith
      nlinarith [hv0 t]
    linarith
  have key : ∀ n : ℕ, ∀ t : ℝ, 2 ≤ t → t ≤ n + 2 → a t ^ 2 ≤ 3 / c * t * v t := by
    intro n
    induction n with
    | zero =>
      intro t ht ht'
      exact sq_le_of_rpow_recursion ht hc (hv0 t) (ha0 t) (ha0 (t - 1))
        (hlow t ht (by push_cast at ht'; linarith)) (hrec t ht)
    | succ n ih =>
      intro t ht ht'
      by_cases h3 : t < 3
      · exact sq_le_of_rpow_recursion ht hc (hv0 t) (ha0 t) (ha0 (t - 1)) (hlow t ht h3)
          (hrec t ht)
      · rw [not_lt] at h3
        have hprev := ih (t - 1) (by linarith) (by push_cast at ht' ⊢; linarith)
        have hAv : a (t - 1) ^ 2 ≤ 3 / c * (t - 1) * v t := by
          have hm := hmono (t - 1) t (by linarith) (by linarith)
          have : 0 ≤ 3 / c * (t - 1) := by nlinarith
          calc a (t - 1) ^ 2 ≤ 3 / c * (t - 1) * v (t - 1) := hprev
            _ ≤ 3 / c * (t - 1) * v t := mul_le_mul_of_nonneg_left hm this
        exact sq_le_of_rpow_recursion ht hc (hv0 t) (ha0 t) (ha0 (t - 1)) hAv (hrec t ht)
  intro t ht
  exact key ⌈t⌉₊ t ht (by have := Nat.le_ceil t; linarith)

end Rigidity.Probability
