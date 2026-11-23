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

section Cube

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Hölder's inequality** for the product Bernoulli law. -/
theorem cubeExp_mul_le {p a b : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hab : a.HolderConjugate b)
    {f g : (ι → Bool) → ℝ} (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) :
    cubeExp p (fun x => f x * g x) ≤
      cubeExp p (fun x => f x ^ a) ^ (1 / a) * cubeExp p (fun x => g x ^ b) ^ (1 / b) := by
  have ha : 0 < a := hab.pos
  have hb : 0 < b := hab.symm.pos
  have hsum : 1 / a + 1 / b = 1 := by simpa using hab.one_div_add_one_div
  have hw : ∀ x : ι → Bool, 0 ≤ cubeWeight p x := cubeWeight_nonneg hp0 hp1
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg (s := (Finset.univ : Finset (ι → Bool)))
    (f := fun x => cubeWeight p x ^ (1 / a) * f x) (g := fun x => cubeWeight p x ^ (1 / b) * g x)
    hab (fun x _ => mul_nonneg (Real.rpow_nonneg (hw x) _) (hf x))
    (fun x _ => mul_nonneg (Real.rpow_nonneg (hw x) _) (hg x))
  have e1 : ∀ x, cubeWeight p x ^ (1 / a) * f x * (cubeWeight p x ^ (1 / b) * g x) =
      cubeWeight p x * (f x * g x) := by
    intro x
    have hww : cubeWeight p x ^ (1 / a) * cubeWeight p x ^ (1 / b) = cubeWeight p x := by
      rw [← Real.rpow_add' (hw x) (by rw [hsum]; norm_num), hsum, Real.rpow_one]
    calc cubeWeight p x ^ (1 / a) * f x * (cubeWeight p x ^ (1 / b) * g x)
        = (cubeWeight p x ^ (1 / a) * cubeWeight p x ^ (1 / b)) * (f x * g x) := by ring
      _ = cubeWeight p x * (f x * g x) := by rw [hww]
  have e2 : ∀ {c : ℝ}, 0 < c → ∀ {h : (ι → Bool) → ℝ}, (∀ x, 0 ≤ h x) → ∀ x,
      (cubeWeight p x ^ (1 / c) * h x) ^ c = cubeWeight p x * h x ^ c := by
    intro c hc h hh x
    rw [Real.mul_rpow (Real.rpow_nonneg (hw x) _) (hh x), ← Real.rpow_mul (hw x),
      one_div_mul_cancel hc.ne', Real.rpow_one]
  simp only [e1, e2 ha hf, e2 hb hg] at h
  exact h

/-- **Lyapunov's inequality** for the product Bernoulli law: `E[g^s] ≤ E[g^t]^{s/t}` for
`0 < s ≤ t` and `g ≥ 0`. -/
theorem cubeExp_rpow_le_rpow {p s t : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hs : 0 < s) (hst : s ≤ t)
    {g : (ι → Bool) → ℝ} (hg : ∀ x, 0 ≤ g x) :
    cubeExp p (fun x => g x ^ s) ≤ cubeExp p (fun x => g x ^ t) ^ (s / t) := by
  rcases hst.eq_or_lt with rfl | hlt
  · rw [div_self hs.ne', Real.rpow_one]
  · have ha : 1 < t / s := by rw [one_lt_div hs]; exact hlt
    have hab := Real.HolderConjugate.conjExponent ha
    have h := cubeExp_mul_le hp0 hp1 hab (f := fun x => g x ^ s) (g := fun _ => 1)
      (fun x => Real.rpow_nonneg (hg x) _) (fun _ => zero_le_one)
    have e1 : ∀ x, (g x ^ s) ^ (t / s) = g x ^ t := by
      intro x; rw [← Real.rpow_mul (hg x), mul_div_cancel₀ _ hs.ne']
    simp only [mul_one, e1, Real.one_rpow, cubeExp_const] at h
    rwa [one_div_div] at h

/-- **The moments of the positive part** of a function of mean zero:
`E[Y₊^q] ≤ (3q/c)^{q/2} E[𝕍[Y]^{q/2}]` for `q ≥ 2` and `c = min(p, 1 - p)`. -/
theorem cubeExp_posPart_rpow_le_of_mean_zero {p q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hq : 2 ≤ q)
    (Y : (ι → Bool) → ℝ) (hY : cubeExp p Y = 0) :
    cubeExp p (fun x => max (Y x) 0 ^ q) ≤
      (3 / min p (1 - p) * q) ^ (q / 2) * cubeExp p (fun x => vertVar p Y x ^ (q / 2)) := by
  set c := min p (1 - p) with hc_def
  have hc : 0 < c := lt_min hp0 (by linarith)
  have hc2 : c ≤ 1 / 2 := by
    have h1 : c ≤ p := min_le_left _ _
    have h2 : c ≤ 1 - p := min_le_right _ _
    linarith
  set mom : ℝ → ℝ := fun t => cubeExp p (fun x => max (Y x) 0 ^ t) with hmom
  set N : ℝ → ℝ := fun t => cubeExp p (fun x => vertVar p Y x ^ (t / 2)) with hN
  have hmom0 : ∀ t, 0 ≤ mom t := fun t =>
    cubeExp_nonneg hp0.le hp1.le fun x => Real.rpow_nonneg (le_max_right _ _) _
  have hN0 : ∀ t, 0 ≤ N t := fun t =>
    cubeExp_nonneg hp0.le hp1.le fun x => Real.rpow_nonneg (vertVar_nonneg p Y x) _
  set a : ℝ → ℝ := fun t => mom t ^ (1 / t) with ha_def
  set v : ℝ → ℝ := fun t => N t ^ (2 / t) with hv_def
  have ha0 : ∀ t, 0 ≤ a t := fun t => Real.rpow_nonneg (hmom0 t) _
  have hv0 : ∀ t, 0 ≤ v t := fun t => Real.rpow_nonneg (hN0 t) _
  have ha_pow : ∀ t u : ℝ, 0 < t → a t ^ u = mom t ^ (u / t) := by
    intro t u ht
    rw [ha_def, ← Real.rpow_mul (hmom0 t)]
    congr 1
    field_simp
  have hN2 : N 2 = cubeExp p (vertVar p Y) := by
    simp only [hN]
    congr 1
    funext x
    norm_num
  have hv2 : v 2 = N 2 := by rw [hv_def]; norm_num
  have hmom2 : mom 2 ≤ N 2 := by
    have hES := cubeExp_sq_sub_le_vertVar hp0.le hp1.le Y
    rw [hY] at hES
    simp only [sub_zero] at hES
    rw [hN2]
    refine le_trans (cubeExp_mono hp0.le hp1.le fun x => ?_) hES
    rw [Real.rpow_two]
    rcases le_total 0 (Y x) with h | h
    · rw [max_eq_left h]
    · rw [max_eq_right h]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      positivity
  have hbase : ∀ s, 1 ≤ s → s ≤ 2 → a s ^ 2 ≤ v 2 := by
    intro s hs1 hs2
    have h1 : mom s ≤ mom 2 ^ (s / 2) :=
      cubeExp_rpow_le_rpow hp0.le hp1.le (by linarith) hs2 (fun x => le_max_right _ _)
    have h2 : a s ≤ mom 2 ^ (1 / 2 : ℝ) := by
      calc a s = mom s ^ (1 / s) := rfl
        _ ≤ (mom 2 ^ (s / 2)) ^ (1 / s) :=
          Real.rpow_le_rpow (hmom0 s) h1 (by positivity)
        _ = mom 2 ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_mul (hmom0 2)]
          congr 1
          field_simp
    have h3 : a s ^ 2 ≤ (mom 2 ^ (1 / 2 : ℝ)) ^ 2 := pow_le_pow_left₀ (ha0 s) h2 2
    have h4 : (mom 2 ^ (1 / 2 : ℝ)) ^ 2 = mom 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (hmom0 2)]
      norm_num
    linarith
  have hmono : ∀ t t', 2 ≤ t → t ≤ t' → v t ≤ v t' := by
    intro t t' ht htt'
    have h1 : N t ≤ N t' ^ ((t / 2) / (t' / 2)) :=
      cubeExp_rpow_le_rpow hp0.le hp1.le (by linarith) (by linarith)
        (fun x => vertVar_nonneg p Y x)
    calc v t = N t ^ (2 / t) := rfl
      _ ≤ (N t' ^ ((t / 2) / (t' / 2))) ^ (2 / t) :=
        Real.rpow_le_rpow (hN0 t) h1 (by positivity)
      _ = v t' := by
        rw [← Real.rpow_mul (hN0 t')]
        congr 1
        have : t ≠ 0 := by linarith
        have : t' ≠ 0 := by linarith
        field_simp
  have hholder : ∀ t, 2 ≤ t → cubeExp p (fun x => max (Y x) 0 ^ (t - 2) * vertVar p Y x) ≤
      mom t ^ ((t - 2) / t) * N t ^ (2 / t) := by
    intro t ht
    rcases ht.eq_or_lt with rfl | hlt
    · simp only [sub_self, Real.rpow_zero, one_mul, zero_div]
      rw [← hN2]
      norm_num
    · have hab : (t / (t - 2)).HolderConjugate (t / 2) := by
        refine ⟨?_, by apply div_pos <;> linarith, by linarith⟩
        rw [inv_div, inv_div, inv_one]
        field_simp
        ring
      have h := cubeExp_mul_le hp0.le hp1.le hab
        (f := fun x => max (Y x) 0 ^ (t - 2)) (g := fun x => vertVar p Y x)
        (fun x => Real.rpow_nonneg (le_max_right _ _) _) (fun x => vertVar_nonneg p Y x)
      have e1 : ∀ x, (max (Y x) 0 ^ (t - 2)) ^ (t / (t - 2)) = max (Y x) 0 ^ t := by
        intro x
        rw [← Real.rpow_mul (le_max_right _ _), mul_div_cancel₀ _ (by linarith)]
      simp only [e1, one_div_div] at h
      convert h using 2
  have hrec : ∀ t, 2 ≤ t → a t ^ t ≤ a (t - 1) ^ t + t / c * a t ^ (t - 2) * v t := by
    intro t ht
    have h1 := cubeExp_posPart_rpow_le hp0 hp1 ht Y
    have ht0 : 0 < t := by linarith
    have ht1 : 0 < t - 1 := by linarith
    rw [ha_pow t t ht0, ha_pow (t - 1) t ht1, ha_pow t (t - 2) ht0, div_self ht0.ne',
      Real.rpow_one]
    have h2 := mul_le_mul_of_nonneg_left (hholder t ht) (div_nonneg ht0.le hc.le)
    calc mom t ≤ mom (t - 1) ^ (t / (t - 1)) +
          t / c * cubeExp p (fun x => max (Y x) 0 ^ (t - 2) * vertVar p Y x) := h1
      _ ≤ mom (t - 1) ^ (t / (t - 1)) + t / c * (mom t ^ ((t - 2) / t) * N t ^ (2 / t)) := by
        linarith
      _ = mom (t - 1) ^ (t / (t - 1)) + t / c * mom t ^ ((t - 2) / t) * v t := by
        rw [hv_def]; ring
  have hfin := moment_bound_of_recursion hc hc2 ha0 hv0 hbase hmono hrec q hq
  have hq0 : 0 < q := by linarith
  have hmomq : mom q = (a q ^ 2) ^ (q / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (ha0 q), ha_pow q _ hq0]
    have : ((2 : ℕ) : ℝ) * (q / 2) / q = 1 := by push_cast; field_simp
    rw [this, Real.rpow_one]
  have hvq : v q ^ (q / 2) = N q := by
    rw [hv_def, ← Real.rpow_mul (hN0 q)]
    have : 2 / q * (q / 2) = 1 := by field_simp
    rw [this, Real.rpow_one]
  calc cubeExp p (fun x => max (Y x) 0 ^ q) = mom q := rfl
    _ = (a q ^ 2) ^ (q / 2) := hmomq
    _ ≤ (3 / c * q * v q) ^ (q / 2) := Real.rpow_le_rpow (sq_nonneg _) hfin (by linarith)
    _ = (3 / c * q) ^ (q / 2) * v q ^ (q / 2) :=
      Real.mul_rpow (by positivity) (hv0 q)
    _ = (3 / c * q) ^ (q / 2) * N q := by rw [hvq]

/-- **The moment inequality on the Bernoulli cube**: for `q ≥ 2` and `c = min(p, 1 - p)`,
`E[|F - E F|^q] ≤ 2 (3q/c)^{q/2} E[𝕍[F]^{q/2}]`. -/
theorem cubeExp_abs_sub_rpow_le {p q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hq : 2 ≤ q)
    (F : (ι → Bool) → ℝ) :
    cubeExp p (fun x => |F x - cubeExp p F| ^ q) ≤
      2 * (3 / min p (1 - p) * q) ^ (q / 2) * cubeExp p (fun x => vertVar p F x ^ (q / 2)) := by
  set Y : (ι → Bool) → ℝ := fun x => F x - cubeExp p F with hY_def
  have hY : cubeExp p Y = 0 := by
    rw [hY_def, cubeExp_sub, cubeExp_const]
    ring
  have hYn : cubeExp p (fun x => -Y x) = 0 := by
    rw [show (fun x => -Y x) = fun x => (-1) * Y x by funext x; ring, cubeExp_const_mul, hY]
    ring
  have hVY : ∀ x, vertVar p Y x = vertVar p F x := fun x => vertVar_sub_const p F _ x
  have hVYn : ∀ x, vertVar p (fun x => -Y x) x = vertVar p F x := fun x => by
    rw [vertVar_neg, hVY]
  have h1 := cubeExp_posPart_rpow_le_of_mean_zero hp0 hp1 hq Y hY
  have h2 := cubeExp_posPart_rpow_le_of_mean_zero hp0 hp1 hq (fun x => -Y x) hYn
  simp only [hVY, hVYn] at h1 h2
  have hq0 : q ≠ 0 := by linarith
  have hsplit : ∀ x, |Y x| ^ q = max (Y x) 0 ^ q + max (-Y x) 0 ^ q := by
    intro x
    rcases le_total 0 (Y x) with h | h
    · rw [abs_of_nonneg h, max_eq_left h, max_eq_right (by linarith), Real.zero_rpow hq0,
        add_zero]
    · rw [abs_of_nonpos h, max_eq_right h, max_eq_left (by linarith), Real.zero_rpow hq0,
        zero_add]
  calc cubeExp p (fun x => |Y x| ^ q)
      = cubeExp p (fun x => max (Y x) 0 ^ q + max (-Y x) 0 ^ q) := by
        congr 1; funext x; exact hsplit x
    _ = cubeExp p (fun x => max (Y x) 0 ^ q) + cubeExp p (fun x => max (-Y x) 0 ^ q) :=
        cubeExp_add _ _ _
    _ ≤ _ := by linarith

end Cube

end Rigidity.Probability
