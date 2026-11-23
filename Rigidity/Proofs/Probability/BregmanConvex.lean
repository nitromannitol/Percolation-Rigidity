import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.MeanInequalities

/-!
# Joint convexity of the Bregman divergence of `x ↦ x ^ r` for `1 ≤ r ≤ 2`

The tensorization of the `φ`-entropy `H_φ(Z) = E[φ(Z)] - φ(E[Z])` for `φ(x) = x^r`,
`1 ≤ r ≤ 2` (Latała and Oleszkiewicz; Boucheron, Bousquet, Lugosi and Massart, *Moment
inequalities for functions of independent random variables*, Ann. Probab. 33 (2005), §3.1)
rests on the convexity of `H_φ`. For a two-point law it is the convexity of the Jensen gap
`J_λ(u, v) = λ u^r + (1 - λ) v^r - (λ u + (1 - λ) v)^r` on `[0, ∞)²`. Writing
`J_λ(u, v) = λ D(u, m) + (1 - λ) D(v, m)` with `m = λ u + (1 - λ) v`, this follows from the joint
convexity of the Bregman divergence `D(x, y) = x^r - y^r - r y^{r-1} (x - y)`, whose Hessian is
`r (r - 1)` times the quadratic form with coefficients `x^{r-2}`, `-y^{r-2}`,
`y^{r-3} ((r - 1) y + (2 - r) x)`; its determinant is nonnegative by the weighted
arithmetic-geometric mean inequality `y^{r-1} x^{2-r} ≤ (r - 1) y + (2 - r) x`.

* `bregmanRpow r x y`: the divergence `D(x, y)`;
* `bregmanRpow_nonneg`: `D ≥ 0` on `[0, ∞)²` for `r ≥ 1` (the tangent line inequality);
* `bregmanRpow_convex`: `D(μ P₁ + (1 - μ) P₀) ≤ μ D(P₁) + (1 - μ) D(P₀)` on `[0, ∞)²`, proved on
  the open quadrant from the second derivative along the segment and extended by continuity;
* `jensenGap r λ u v` and `jensenGap_convex`: the convexity of the two-point Jensen gap.
-/

namespace Rigidity.Probability

open Set Filter Topology

/-- The Bregman divergence `D(x, y) = x^r - y^r - r y^{r-1} (x - y)` of `x ↦ x^r`. -/
noncomputable def bregmanRpow (r x y : ℝ) : ℝ :=
  x ^ r - y ^ r - r * y ^ (r - 1) * (x - y)

/-- The tangent line inequality `y^r + r y^{r-1} (x - y) ≤ x^r` for `x, y ≥ 0` and `r ≥ 1`. -/
theorem bregmanRpow_nonneg {r x y : ℝ} (hr : 1 ≤ r) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ bregmanRpow r x y := by
  unfold bregmanRpow
  rcases hy.eq_or_lt with rfl | hy
  · rcases hr.eq_or_lt with rfl | hr
    · simp
    · rw [Real.zero_rpow (by linarith), Real.zero_rpow (by linarith)]
      simp only [sub_zero, mul_zero, zero_mul]
      exact Real.rpow_nonneg hx r
  · have hb := one_add_mul_self_le_rpow_one_add (s := x / y - 1)
      (by have : 0 ≤ x / y := div_nonneg hx hy.le; linarith) hr
    rw [show 1 + (x / y - 1) = x / y by ring, Real.div_rpow hx hy.le] at hb
    have hyr : 0 < y ^ r := Real.rpow_pos_of_pos hy r
    have hyr1 : y ^ r = y ^ (r - 1) * y := by
      rw [← Real.rpow_add_one hy.ne']; ring_nf
    have h2 : y ^ r * (1 + r * (x / y - 1)) ≤ x ^ r := by
      have := mul_le_mul_of_nonneg_left hb hyr.le
      rwa [mul_div_cancel₀ _ hyr.ne'] at this
    have hxy : y * (x / y) = x := mul_div_cancel₀ x hy.ne'
    have h3 : y ^ r * (1 + r * (x / y - 1)) = y ^ r + r * y ^ (r - 1) * (x - y) := by
      calc y ^ r * (1 + r * (x / y - 1))
          = y ^ (r - 1) * y + r * y ^ (r - 1) * (y * (x / y) - y) := by rw [hyr1]; ring
        _ = y ^ r + r * y ^ (r - 1) * (x - y) := by rw [hxy, hyr1]
    linarith

/-- A quadratic form with a positive leading coefficient and a nonpositive discriminant is
nonnegative. -/
theorem quadratic_nonneg_of_discrim {A B C a b : ℝ} (hA : 0 < A) (h : B ^ 2 ≤ A * C) :
    0 ≤ A * a ^ 2 - 2 * (B * a * b) + C * b ^ 2 := by
  have key : 0 ≤ A * (A * a ^ 2 - 2 * (B * a * b) + C * b ^ 2) := by
    have e : A * (A * a ^ 2 - 2 * (B * a * b) + C * b ^ 2) =
        (A * a - B * b) ^ 2 + (A * C - B ^ 2) * b ^ 2 := by ring
    rw [e]
    have : 0 ≤ A * C - B ^ 2 := by linarith
    positivity
  exact (mul_nonneg_iff_of_pos_left hA).1 key

/-- The Hessian of `D` along a direction `(a, b)` at `(x, y)` with `x, y > 0`, divided by
`r (r - 1)`, is nonnegative for `1 ≤ r ≤ 2`. -/
theorem bregmanRpow_hessian_nonneg {r x y : ℝ} (hr1 : 1 ≤ r) (hr2 : r ≤ 2) (hx : 0 < x)
    (hy : 0 < y) (a b : ℝ) :
    0 ≤ x ^ (r - 2) * a ^ 2 - 2 * (y ^ (r - 2) * a * b) +
      (y ^ (r - 2) - (r - 2) * y ^ (r - 3) * (x - y)) * b ^ 2 := by
  have hy3 : y ^ (r - 2) = y ^ (r - 3) * y := by
    rw [← Real.rpow_add_one hy.ne']; ring_nf
  have hC : y ^ (r - 2) - (r - 2) * y ^ (r - 3) * (x - y) =
      y ^ (r - 3) * ((r - 1) * y + (2 - r) * x) := by
    rw [hy3]; ring
  have hamgm : y ^ (r - 1) * x ^ (2 - r) ≤ (r - 1) * y + (2 - r) * x :=
    Real.geom_mean_le_arith_mean2_weighted (by linarith) (by linarith) hy.le hx.le (by ring)
  have e1 : x ^ (r - 2) * x ^ (2 - r) = 1 := by
    rw [← Real.rpow_add hx]; simp
  have e2 : y ^ (r - 3) * y ^ (r - 1) = y ^ (r - 2) * y ^ (r - 2) := by
    rw [← Real.rpow_add hy, ← Real.rpow_add hy]; ring_nf
  have hBB : (y ^ (r - 2)) ^ 2 ≤ x ^ (r - 2) * (y ^ (r - 3) * ((r - 1) * y + (2 - r) * x)) := by
    have h1 : (y ^ (r - 2)) ^ 2 = x ^ (r - 2) * y ^ (r - 3) * (y ^ (r - 1) * x ^ (2 - r)) := by
      calc (y ^ (r - 2)) ^ 2 = y ^ (r - 2) * y ^ (r - 2) := by ring
        _ = (y ^ (r - 3) * y ^ (r - 1)) * (x ^ (r - 2) * x ^ (2 - r)) := by rw [e1, e2, mul_one]
        _ = _ := by ring
    have hpos : 0 ≤ x ^ (r - 2) * y ^ (r - 3) := by positivity
    calc (y ^ (r - 2)) ^ 2 = x ^ (r - 2) * y ^ (r - 3) * (y ^ (r - 1) * x ^ (2 - r)) := h1
      _ ≤ x ^ (r - 2) * y ^ (r - 3) * ((r - 1) * y + (2 - r) * x) :=
        mul_le_mul_of_nonneg_left hamgm hpos
      _ = _ := by ring
  rw [hC]
  exact quadratic_nonneg_of_discrim (Real.rpow_pos_of_pos hx _) hBB

/-- A point of the segment between two positive numbers is positive. -/
theorem segment_pos {x₀ x₁ t : ℝ} (h₀ : 0 < x₀) (h₁ : 0 < x₁) (ht : t ∈ Icc (0 : ℝ) 1) :
    0 < x₀ + t * (x₁ - x₀) := by
  obtain ⟨ht0, ht1⟩ := ht
  rcases le_total x₀ x₁ with h | h
  · nlinarith
  · nlinarith

section Segment

variable {r x₀ y₀ a b : ℝ}

/-- The first derivative of `t ↦ D(x₀ + t a, y₀ + t b)`. -/
theorem hasDerivAt_bregmanRpow_segment {t : ℝ} (hX : 0 < x₀ + t * a) (hY : 0 < y₀ + t * b) :
    HasDerivAt (fun t => bregmanRpow r (x₀ + t * a) (y₀ + t * b))
      (r * a * (x₀ + t * a) ^ (r - 1) - r * a * (y₀ + t * b) ^ (r - 1) -
        r * (r - 1) * b * ((y₀ + t * b) ^ (r - 2) * ((x₀ + t * a) - (y₀ + t * b)))) t := by
  have hx : HasDerivAt (fun t => x₀ + t * a) a t := by
    simpa using ((hasDerivAt_id t).mul_const a).const_add x₀
  have hy : HasDerivAt (fun t => y₀ + t * b) b t := by
    simpa using ((hasDerivAt_id t).mul_const b).const_add y₀
  have hxr := hx.rpow_const (p := r) (Or.inl hX.ne')
  have hyr := hy.rpow_const (p := r) (Or.inl hY.ne')
  have hyr1 := hy.rpow_const (p := r - 1) (Or.inl hY.ne')
  have h := (hxr.sub hyr).sub ((hyr1.const_mul r).mul (hx.sub hy))
  refine h.congr_deriv ?_
  rw [show r - 1 - 1 = r - 2 by ring]
  simp only [Pi.sub_apply]
  ring

/-- The second derivative of `t ↦ D(x₀ + t a, y₀ + t b)`. -/
theorem hasDerivAt_bregmanRpow_segment_deriv {t : ℝ} (hX : 0 < x₀ + t * a)
    (hY : 0 < y₀ + t * b) :
    HasDerivAt (fun t => r * a * (x₀ + t * a) ^ (r - 1) - r * a * (y₀ + t * b) ^ (r - 1) -
        r * (r - 1) * b * ((y₀ + t * b) ^ (r - 2) * ((x₀ + t * a) - (y₀ + t * b))))
      (r * (r - 1) * ((x₀ + t * a) ^ (r - 2) * a ^ 2 - 2 * ((y₀ + t * b) ^ (r - 2) * a * b) +
        ((y₀ + t * b) ^ (r - 2) - (r - 2) * (y₀ + t * b) ^ (r - 3) *
          ((x₀ + t * a) - (y₀ + t * b))) * b ^ 2)) t := by
  have hx : HasDerivAt (fun t => x₀ + t * a) a t := by
    simpa using ((hasDerivAt_id t).mul_const a).const_add x₀
  have hy : HasDerivAt (fun t => y₀ + t * b) b t := by
    simpa using ((hasDerivAt_id t).mul_const b).const_add y₀
  have hxr1 := hx.rpow_const (p := r - 1) (Or.inl hX.ne')
  have hyr1 := hy.rpow_const (p := r - 1) (Or.inl hY.ne')
  have hyr2 := hy.rpow_const (p := r - 2) (Or.inl hY.ne')
  have h := ((hxr1.const_mul (r * a)).sub (hyr1.const_mul (r * a))).sub
    ((hyr2.mul (hx.sub hy)).const_mul (r * (r - 1) * b))
  refine h.congr_deriv ?_
  rw [show r - 1 - 1 = r - 2 by ring, show r - 2 - 1 = r - 3 by ring]
  simp only [Pi.sub_apply]
  ring

end Segment

/-- `D` is continuous on `ℝ²` for `r ≥ 1`. -/
theorem continuous_bregmanRpow {r : ℝ} (hr : 1 ≤ r) :
    Continuous fun q : ℝ × ℝ => bregmanRpow r q.1 q.2 := by
  unfold bregmanRpow
  have h1 := Real.continuous_rpow_const (q := r) (by linarith)
  have h2 := Real.continuous_rpow_const (q := r - 1) (by linarith)
  fun_prop

/-- The convexity inequality for `D` between two points of the open quadrant. -/
theorem bregmanRpow_convex_of_pos {r : ℝ} (hr1 : 1 ≤ r) (hr2 : r ≤ 2) {x₀ y₀ x₁ y₁ μ : ℝ}
    (hx₀ : 0 < x₀) (hy₀ : 0 < y₀) (hx₁ : 0 < x₁) (hy₁ : 0 < y₁) (hμ₀ : 0 ≤ μ) (hμ₁ : μ ≤ 1) :
    bregmanRpow r (μ * x₁ + (1 - μ) * x₀) (μ * y₁ + (1 - μ) * y₀) ≤
      μ * bregmanRpow r x₁ y₁ + (1 - μ) * bregmanRpow r x₀ y₀ := by
  set a := x₁ - x₀
  set b := y₁ - y₀
  set g : ℝ → ℝ := fun t => bregmanRpow r (x₀ + t * a) (y₀ + t * b) with hg
  have hpos : ∀ t ∈ Icc (0 : ℝ) 1, 0 < x₀ + t * a ∧ 0 < y₀ + t * b := fun t ht =>
    ⟨segment_pos hx₀ hx₁ ht, segment_pos hy₀ hy₁ ht⟩
  have hint : interior (Icc (0 : ℝ) 1) = Ioo 0 1 := interior_Icc
  have hconv : ConvexOn ℝ (Icc (0 : ℝ) 1) g := by
    refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 1)
      (f' := fun t => r * a * (x₀ + t * a) ^ (r - 1) - r * a * (y₀ + t * b) ^ (r - 1) -
        r * (r - 1) * b * ((y₀ + t * b) ^ (r - 2) * ((x₀ + t * a) - (y₀ + t * b))))
      (f'' := fun t => r * (r - 1) * ((x₀ + t * a) ^ (r - 2) * a ^ 2 -
        2 * ((y₀ + t * b) ^ (r - 2) * a * b) +
        ((y₀ + t * b) ^ (r - 2) - (r - 2) * (y₀ + t * b) ^ (r - 3) *
          ((x₀ + t * a) - (y₀ + t * b))) * b ^ 2)) ?_ ?_ ?_ ?_
    · intro t ht
      exact (hasDerivAt_bregmanRpow_segment (hpos t ht).1 (hpos t ht).2).continuousAt
        |>.continuousWithinAt
    · intro t ht
      rw [hint] at ht
      have ht' : t ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht
      exact (hasDerivAt_bregmanRpow_segment (hpos t ht').1 (hpos t ht').2).hasDerivWithinAt
    · intro t ht
      rw [hint] at ht
      have ht' : t ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht
      exact (hasDerivAt_bregmanRpow_segment_deriv (hpos t ht').1
        (hpos t ht').2).hasDerivWithinAt
    · intro t ht
      rw [hint] at ht
      have ht' : t ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht
      have := bregmanRpow_hessian_nonneg hr1 hr2 (hpos t ht').1 (hpos t ht').2 a b
      have hrr : 0 ≤ r * (r - 1) := mul_nonneg (by linarith) (by linarith)
      exact mul_nonneg hrr this
  have h : g ((1 - μ) • (0 : ℝ) + μ • (1 : ℝ)) ≤ (1 - μ) • g 0 + μ • g 1 :=
    hconv.2 (by simp) (by simp) (by linarith) hμ₀ (by ring)
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add, hg, one_mul, zero_mul, add_zero] at h
  have e1 : x₀ + μ * a = μ * x₁ + (1 - μ) * x₀ := by simp only [a]; ring
  have e2 : y₀ + μ * b = μ * y₁ + (1 - μ) * y₀ := by simp only [b]; ring
  have e3 : x₀ + a = x₁ := by simp only [a]; ring
  have e4 : y₀ + b = y₁ := by simp only [b]; ring
  rw [e1, e2, e3, e4] at h
  linarith

/-- **Joint convexity of `D` on `[0, ∞)²`** for `1 ≤ r ≤ 2`: for nonnegative `x₀, y₀, x₁, y₁`
and `μ ∈ [0, 1]`, `D(μ P₁ + (1 - μ) P₀) ≤ μ D(P₁) + (1 - μ) D(P₀)`. -/
theorem bregmanRpow_convex {r : ℝ} (hr1 : 1 ≤ r) (hr2 : r ≤ 2) {x₀ y₀ x₁ y₁ μ : ℝ}
    (hx₀ : 0 ≤ x₀) (hy₀ : 0 ≤ y₀) (hx₁ : 0 ≤ x₁) (hy₁ : 0 ≤ y₁) (hμ₀ : 0 ≤ μ) (hμ₁ : μ ≤ 1) :
    bregmanRpow r (μ * x₁ + (1 - μ) * x₀) (μ * y₁ + (1 - μ) * y₀) ≤
      μ * bregmanRpow r x₁ y₁ + (1 - μ) * bregmanRpow r x₀ y₀ := by
  have hc := continuous_bregmanRpow hr1
  set F : ℝ → ℝ := fun ε => bregmanRpow r (μ * (x₁ + ε) + (1 - μ) * (x₀ + ε))
    (μ * (y₁ + ε) + (1 - μ) * (y₀ + ε))
  set G : ℝ → ℝ := fun ε => μ * bregmanRpow r (x₁ + ε) (y₁ + ε) +
    (1 - μ) * bregmanRpow r (x₀ + ε) (y₀ + ε)
  have hF : Continuous F := by
    have : Continuous fun ε : ℝ => ((μ * (x₁ + ε) + (1 - μ) * (x₀ + ε)),
        (μ * (y₁ + ε) + (1 - μ) * (y₀ + ε))) := by fun_prop
    exact hc.comp this
  have hG : Continuous G := by
    have h1 : Continuous fun ε : ℝ => bregmanRpow r (x₁ + ε) (y₁ + ε) :=
      hc.comp (by fun_prop : Continuous fun ε : ℝ => (x₁ + ε, y₁ + ε))
    have h0 : Continuous fun ε : ℝ => bregmanRpow r (x₀ + ε) (y₀ + ε) :=
      hc.comp (by fun_prop : Continuous fun ε : ℝ => (x₀ + ε, y₀ + ε))
    exact (continuous_const.mul h1).add (continuous_const.mul h0)
  have hle : ∀ ε > (0 : ℝ), F ε ≤ G ε := fun ε hε =>
    bregmanRpow_convex_of_pos hr1 hr2 (by linarith) (by linarith) (by linarith) (by linarith)
      hμ₀ hμ₁
  have hlim := le_of_tendsto_of_tendsto (hF.continuousWithinAt (s := Ioi 0) (x := 0)).tendsto
    (hG.continuousWithinAt (s := Ioi 0) (x := 0)).tendsto
    (eventually_nhdsWithin_of_forall fun ε hε => hle ε hε)
  simpa [F, G] using hlim

/-- The two-point Jensen gap `J_λ(u, v) = λ u^r + (1 - λ) v^r - (λ u + (1 - λ) v)^r`. -/
noncomputable def jensenGap (r l u v : ℝ) : ℝ :=
  l * u ^ r + (1 - l) * v ^ r - (l * u + (1 - l) * v) ^ r

theorem jensenGap_eq_bregmanRpow (r l u v : ℝ) :
    jensenGap r l u v = l * bregmanRpow r u (l * u + (1 - l) * v) +
      (1 - l) * bregmanRpow r v (l * u + (1 - l) * v) := by
  unfold jensenGap bregmanRpow
  ring

/-- **Convexity of the two-point Jensen gap** on `[0, ∞)²` for `1 ≤ r ≤ 2` and `λ ∈ [0, 1]`. -/
theorem jensenGap_convex {r l : ℝ} (hr1 : 1 ≤ r) (hr2 : r ≤ 2) (hl₀ : 0 ≤ l) (hl₁ : l ≤ 1)
    {u₀ v₀ u₁ v₁ μ : ℝ} (hu₀ : 0 ≤ u₀) (hv₀ : 0 ≤ v₀) (hu₁ : 0 ≤ u₁) (hv₁ : 0 ≤ v₁)
    (hμ₀ : 0 ≤ μ) (hμ₁ : μ ≤ 1) :
    jensenGap r l (μ * u₁ + (1 - μ) * u₀) (μ * v₁ + (1 - μ) * v₀) ≤
      μ * jensenGap r l u₁ v₁ + (1 - μ) * jensenGap r l u₀ v₀ := by
  simp only [jensenGap_eq_bregmanRpow]
  have hm₀ : 0 ≤ l * u₀ + (1 - l) * v₀ := by
    have : 0 ≤ 1 - l := by linarith
    positivity
  have hm₁ : 0 ≤ l * u₁ + (1 - l) * v₁ := by
    have : 0 ≤ 1 - l := by linarith
    positivity
  have em : l * (μ * u₁ + (1 - μ) * u₀) + (1 - l) * (μ * v₁ + (1 - μ) * v₀) =
      μ * (l * u₁ + (1 - l) * v₁) + (1 - μ) * (l * u₀ + (1 - l) * v₀) := by ring
  rw [em]
  have hu := bregmanRpow_convex hr1 hr2 hu₀ hm₀ hu₁ hm₁ hμ₀ hμ₁
  have hv := bregmanRpow_convex hr1 hr2 hv₀ hm₀ hv₁ hm₁ hμ₀ hμ₁
  have hl' : 0 ≤ 1 - l := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hu hl₀, mul_le_mul_of_nonneg_left hv hl']

end Rigidity.Probability
