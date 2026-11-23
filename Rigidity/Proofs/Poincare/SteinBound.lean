import Rigidity.Proofs.Poincare.SteinWeighted

/-!
# The weighted square function bound: assembly

The maximal function `M` of the lattice form of Armstrong, Kuusi and Mourrat, Proposition D.2,
Step 2 ((D.9), with the weights of Remark D.6), and the conclusion of the step:

* `heatF_le_boxMax`: `ω(y)^{1/p} heatF f (y) ≤ C boxMax (ω^{1/p} f) (y)` for `s ∈ [0, T]`;
* `exists_steinWeighted`: for `f ≥ 0` supported in `S`,
  `Σ_x ω Γ^{p/2} ≤ (2/(p(p-1)))^{p/2} K_M^{(2-p)/2} K_I^{p/2} Σ ω f^p`.
-/

open scoped Classical
open LatticeProb LatticeProb.Percolation Rigidity.Green MeasureTheory

namespace Rigidity.Poincare

variable {S : Finset (Vertex 2)} {f : Vertex 2 → ℝ}

/-- `ω^{1/p} f`. -/
noncomputable def wf (a p : ℝ) (f : Vertex 2 → ℝ) (y : Vertex 2) : ℝ := coshW a y ^ (1 / p) * f y

theorem wf_nonneg (hf : ∀ y, 0 ≤ f y) (a p : ℝ) (y : Vertex 2) : 0 ≤ wf a p f y :=
  mul_nonneg (Real.rpow_nonneg (coshW_pos a y).le _) (hf y)

theorem wf_eq_zero (hfS : ∀ y ∉ S, f y = 0) (a p : ℝ) {y : Vertex 2} (hy : y ∉ S) :
    wf a p f y = 0 := by
  rw [wf, hfS y hy, mul_zero]

theorem summable_wf (hfS : ∀ y ∉ S, f y = 0) (a p : ℝ) : Summable (wf a p f) :=
  summable_of_ne_finset_zero fun _ hy => wf_eq_zero hfS a p hy

/-- **The heat flow is dominated by the maximal function of `ω^{1/p} f`**. -/
theorem heatF_le_boxMax {C₃ : ℝ}
    (hmax : ∀ T a : ℝ, 0 ≤ T → 0 ≤ a → a ≤ 1 / 6 → a * max (Real.sqrt T) 1 ≤ 1 →
      ∀ s : ℝ, 0 ≤ s → s ≤ T → ∀ G : Vertex 2 → ℝ, (∀ z, 0 ≤ G z) → Summable G →
        ∀ x : Vertex 2, ∑' y, ENNReal.ofReal (openHeat (allOpen 2) s x y *
          Real.exp (a * (|(((y - x) 0 : ℤ) : ℝ)| + |(((y - x) 1 : ℤ) : ℝ)|)) * G y) ≤
            ENNReal.ofReal (C₃ * boxMax G x))
    (hC₃ : 0 < C₃) (hf : ∀ y, 0 ≤ f y) (hfS : ∀ y ∉ S, f y = 0) {p : ℝ} (hp : 1 ≤ p)
    {a T : ℝ} (hT : 0 ≤ T) (ha0 : 0 ≤ a) (ha6 : a ≤ 1 / 6) (haT : a * max (Real.sqrt T) 1 ≤ 1)
    {s : ℝ} (hs : 0 ≤ s) (hsT : s ≤ T) (y : Vertex 2) :
    coshW a y ^ (1 / p) * heatF S f s y ≤ C₃ * boxMax (wf a p f) y := by
  set E : Vertex 2 → ℝ := fun z =>
    Real.exp (a * (|(((z - y) 0 : ℤ) : ℝ)| + |(((z - y) 1 : ℤ) : ℝ)|)) with hE
  have hE1 : ∀ z, 1 ≤ E z := fun z => Real.one_le_exp (by positivity)
  have hp0 : 0 < p := by linarith
  have hw : ∀ z, coshW a y ^ (1 / p) ≤ coshW a z ^ (1 / p) * E z := by
    intro z
    have h := coshW_le_mul_exp ha0 y z
    calc coshW a y ^ (1 / p) ≤ (coshW a z * E z) ^ (1 / p) :=
          Real.rpow_le_rpow (coshW_pos a y).le h (by positivity)
      _ = coshW a z ^ (1 / p) * E z ^ (1 / p) :=
          Real.mul_rpow (coshW_pos a z).le (by linarith [hE1 z])
      _ ≤ coshW a z ^ (1 / p) * E z := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (coshW_pos a z).le _)
          exact Real.rpow_le_self_of_one_le (hE1 z) (by rw [div_le_one hp0]; exact hp)
  have hle : coshW a y ^ (1 / p) * heatF S f s y ≤
      ∑ z ∈ S, openHeat (allOpen 2) s y z * E z * wf a p f z := by
    unfold heatF
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun z _ => ?_
    have h0 := openHeat_nonneg (allOpen 2) hs y z
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hw z) (hf z)) h0
    simp only [wf]
    nlinarith
  have heq : ∑' z, ENNReal.ofReal (openHeat (allOpen 2) s y z * E z * wf a p f z) =
      ∑ z ∈ S, ENNReal.ofReal (openHeat (allOpen 2) s y z * E z * wf a p f z) :=
    tsum_eq_sum fun z hz => by rw [wf_eq_zero hfS a p hz, mul_zero, ENNReal.ofReal_zero]
  have hsum : ENNReal.ofReal (∑ z ∈ S, openHeat (allOpen 2) s y z * E z * wf a p f z) ≤
      ENNReal.ofReal (C₃ * boxMax (wf a p f) y) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun z _ => mul_nonneg (mul_nonneg
      (openHeat_nonneg _ hs y z) (by linarith [hE1 z])) (wf_nonneg hf a p z), ← heq]
    exact hmax T a hT ha0 ha6 haT s hs hsT (wf a p f) (wf_nonneg hf a p) (summable_wf hfS a p) y
  have hM0 : 0 ≤ C₃ * boxMax (wf a p f) y :=
    mul_nonneg hC₃.le (boxMax_nonneg (wf_nonneg hf a p) (summable_wf hfS a p) y)
  exact hle.trans ((ENNReal.ofReal_le_ofReal_iff hM0).1 hsum)

theorem coshW_add_unit_le (a : ℝ) (ha : 0 ≤ a) (x : Vertex 2) (i : Fin 2) :
    coshW a x ≤ coshW a (x + unit i) * Real.exp a := by
  have h := coshW_le_mul_exp ha x (x + unit i)
  have e : x + unit i - x = unit i := by abel
  rw [e, abs_unit_sum, mul_one] at h
  exact h

theorem rpow_neg_coshW_add_unit_le {a p : ℝ} (ha : 0 ≤ a) (hp : 1 ≤ p) (x : Vertex 2)
    (i : Fin 2) :
    coshW a (x + unit i) ^ (-(1 / p)) ≤ Real.exp a * coshW a x ^ (-(1 / p)) := by
  have hp0 : 0 < p := by linarith
  have h1 : coshW a x * Real.exp (-a) ≤ coshW a (x + unit i) := by
    have := coshW_add_unit_le a ha x i
    have he : Real.exp a * Real.exp (-a) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-a), coshW_pos a (x + unit i)]
  have hpos : 0 < coshW a x * Real.exp (-a) := mul_pos (coshW_pos a x) (Real.exp_pos _)
  calc coshW a (x + unit i) ^ (-(1 / p)) ≤ (coshW a x * Real.exp (-a)) ^ (-(1 / p)) :=
        Real.rpow_le_rpow_of_nonpos hpos h1 (by
          have : 0 ≤ 1 / p := by positivity
          linarith)
    _ = coshW a x ^ (-(1 / p)) * Real.exp (-a * -(1 / p)) := by
        rw [Real.mul_rpow (coshW_pos a x).le (Real.exp_pos _).le, ← Real.exp_mul]
    _ ≤ coshW a x ^ (-(1 / p)) * Real.exp a := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_)
          (Real.rpow_nonneg (coshW_pos a x).le _)
        have : 1 / p ≤ 1 := by rw [div_le_one hp0]; exact hp
        nlinarith
    _ = Real.exp a * coshW a x ^ (-(1 / p)) := mul_comm _ _

theorem rpow_add_three_le {b₀ b₁ b₂ p : ℝ} (h₀ : 0 ≤ b₀) (h₁ : 0 ≤ b₁) (h₂ : 0 ≤ b₂)
    (hp : 0 ≤ p) : (b₀ + b₁ + b₂) ^ p ≤ 3 ^ p * (b₀ ^ p + b₁ ^ p + b₂ ^ p) := by
  set m := max b₀ (max b₁ b₂) with hm
  have hm0 : 0 ≤ m := le_max_of_le_left h₀
  have hsum : b₀ + b₁ + b₂ ≤ 3 * m := by
    have := le_max_left b₀ (max b₁ b₂)
    have := le_max_left b₁ b₂
    have := le_max_right b₁ b₂
    have := le_max_right b₀ (max b₁ b₂)
    linarith
  have hmp : m ^ p ≤ b₀ ^ p + b₁ ^ p + b₂ ^ p := by
    have p0 := Real.rpow_nonneg h₀ p
    have p1 := Real.rpow_nonneg h₁ p
    have p2 := Real.rpow_nonneg h₂ p
    rcases max_choice b₀ (max b₁ b₂) with h | h <;> rw [hm, h]
    · linarith
    · rcases max_choice b₁ b₂ with h' | h' <;> rw [h'] <;> linarith
  calc (b₀ + b₁ + b₂) ^ p ≤ (3 * m) ^ p :=
        Real.rpow_le_rpow (by positivity) hsum hp
    _ = 3 ^ p * m ^ p := Real.mul_rpow (by norm_num) hm0
    _ ≤ 3 ^ p * (b₀ ^ p + b₁ ^ p + b₂ ^ p) :=
        mul_le_mul_of_nonneg_left hmp (Real.rpow_nonneg (by norm_num) _)

/-- The maximal majorant
`M(x) = C e^a ω(x)^{-1/p} (M(ω^{1/p}f)(x) + Σ_i M(ω^{1/p}f)(x + e_i))`. -/
noncomputable def steinMajorant (C a p : ℝ) (f : Vertex 2 → ℝ) (x : Vertex 2) : ℝ :=
  C * Real.exp a * coshW a x ^ (-(1 / p)) *
    (boxMax (wf a p f) x + boxMax (wf a p f) (x + unit 0) + boxMax (wf a p f) (x + unit 1))

theorem steinMajorant_nonneg (hf : ∀ y, 0 ≤ f y) (hfS : ∀ y ∉ S, f y = 0) {C : ℝ} (hC : 0 ≤ C)
    (a p : ℝ) (x : Vertex 2) : 0 ≤ steinMajorant C a p f x := by
  have h := fun z => boxMax_nonneg (wf_nonneg hf a p) (summable_wf hfS a p) z
  have := h x; have := h (x + unit 0); have := h (x + unit 1)
  have hr := Real.rpow_nonneg (coshW_pos a x).le (-(1 / p))
  unfold steinMajorant
  exact mul_nonneg (mul_nonneg (mul_nonneg hC (Real.exp_pos a).le) hr) (by linarith)

theorem tsum_ofReal_boxMax_add_rpow (F : Vertex 2 → ℝ) (e : Vertex 2) (p : ℝ) :
    ∑' x, ENNReal.ofReal (boxMax F (x + e) ^ p) = ∑' x, ENNReal.ofReal (boxMax F x ^ p) :=
  (Equiv.addRight e).tsum_eq fun x => ENNReal.ofReal (boxMax F x ^ p)

theorem tsum_ofReal_wf_rpow (hf : ∀ y, 0 ≤ f y) (hfS : ∀ y ∉ S, f y = 0) {a p : ℝ}
    (hp : 1 ≤ p) :
    ∑' x, ENNReal.ofReal (wf a p f x ^ p) = ENNReal.ofReal (∑ y ∈ S, coshW a y * f y ^ p) := by
  have hp0 : 0 < p := by linarith
  have e : ∀ x, wf a p f x ^ p = coshW a x * f x ^ p := by
    intro x
    rw [wf, Real.mul_rpow (Real.rpow_nonneg (coshW_pos a x).le _) (hf x), ← Real.rpow_mul
      (coshW_pos a x).le, one_div_mul_cancel hp0.ne', Real.rpow_one]
  simp only [e]
  rw [ENNReal.ofReal_sum_of_nonneg fun y _ => mul_nonneg (coshW_pos a y).le
      (Real.rpow_nonneg (hf y) _)]
  exact tsum_eq_sum fun x hx => by rw [hfS x hx, Real.zero_rpow hp0.ne', mul_zero,
    ENNReal.ofReal_zero]

/-- **The weighted maximal bound**: `Σ_x ω M^p ≤ 3 (3 C e^a)^p C_HL(p) Σ ω f^p`. -/
theorem tsum_ofReal_coshW_mul_steinMajorant_le (hf : ∀ y, 0 ≤ f y) (hfS : ∀ y ∉ S, f y = 0)
    {C : ℝ} (hC : 0 ≤ C) {a p : ℝ} (hp : 1 < p) :
    ∑' x, ENNReal.ofReal (coshW a x * steinMajorant C a p f x ^ p) ≤
      ENNReal.ofReal (3 * (3 * C * Real.exp a) ^ p * (18 * 2 ^ (p - 1) * p / (p - 1)) *
        ∑ y ∈ S, coshW a y * f y ^ p) := by
  have hp0 : 0 < p := by linarith
  set F := wf a p f with hF
  have hF0 := wf_nonneg hf a p
  have hFs := summable_wf hfS a p
  have hb := fun z => boxMax_nonneg hF0 hFs z
  set W := ∑ y ∈ S, coshW a y * f y ^ p with hW
  set K := (3 * C * Real.exp a) ^ p with hK
  have hpt : ∀ x, coshW a x * steinMajorant C a p f x ^ p ≤
      K * (boxMax F x ^ p + boxMax F (x + unit 0) ^ p + boxMax F (x + unit 1) ^ p) := by
    intro x
    have hω := coshW_pos a x
    have e1 : coshW a x * (coshW a x ^ (-(1 / p))) ^ p = 1 := by
      rw [← Real.rpow_mul hω.le, show -(1 / p) * p = -1 by field_simp, Real.rpow_neg_one,
        mul_inv_cancel₀ hω.ne']
    have hB := rpow_add_three_le (hb x) (hb (x + unit 0)) (hb (x + unit 1)) hp0.le
    unfold steinMajorant
    have hfirst : 0 ≤ C * Real.exp a * coshW a x ^ (-(1 / p)) :=
      mul_nonneg (mul_nonneg hC (Real.exp_pos a).le) (Real.rpow_nonneg hω.le _)
    have hsumb : 0 ≤ boxMax F x + boxMax F (x + unit 0) + boxMax F (x + unit 1) :=
      add_nonneg (add_nonneg (hb x) (hb _)) (hb _)
    rw [Real.mul_rpow hfirst hsumb,
      Real.mul_rpow (mul_nonneg hC (Real.exp_pos a).le) (Real.rpow_nonneg hω.le _)]
    have e2 : coshW a x * ((C * Real.exp a) ^ p * (coshW a x ^ (-(1 / p))) ^ p *
        (boxMax F x + boxMax F (x + unit 0) + boxMax F (x + unit 1)) ^ p) =
        (C * Real.exp a) ^ p * (boxMax F x + boxMax F (x + unit 0) + boxMax F (x + unit 1)) ^ p
          * (coshW a x * (coshW a x ^ (-(1 / p))) ^ p) := by ring
    have hCe0 : 0 ≤ C * Real.exp a := mul_nonneg hC (Real.exp_pos a).le
    have hK' : K = 3 ^ p * (C * Real.exp a) ^ p := by
      rw [hK, mul_assoc, Real.mul_rpow (by norm_num) hCe0]
    rw [e2, e1, mul_one, hK']
    have hCe : 0 ≤ (C * Real.exp a) ^ p := Real.rpow_nonneg hCe0 _
    calc (C * Real.exp a) ^ p *
          (boxMax F x + boxMax F (x + unit 0) + boxMax F (x + unit 1)) ^ p
        ≤ (C * Real.exp a) ^ p * (3 ^ p *
          (boxMax F x ^ p + boxMax F (x + unit 0) ^ p + boxMax F (x + unit 1) ^ p)) :=
          mul_le_mul_of_nonneg_left hB hCe
      _ = 3 ^ p * (C * Real.exp a) ^ p *
          (boxMax F x ^ p + boxMax F (x + unit 0) ^ p + boxMax F (x + unit 1) ^ p) := by ring
  have hHL := tsum_boxMax_rpow_le hF0 hFs hp
  rw [tsum_ofReal_wf_rpow hf hfS hp.le] at hHL
  have hbp := fun z => Real.rpow_nonneg (hb z) p
  calc ∑' x, ENNReal.ofReal (coshW a x * steinMajorant C a p f x ^ p)
      ≤ ∑' x, (ENNReal.ofReal K * (ENNReal.ofReal (boxMax F x ^ p) +
          ENNReal.ofReal (boxMax F (x + unit 0) ^ p) +
          ENNReal.ofReal (boxMax F (x + unit 1) ^ p))) := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        rw [← ENNReal.ofReal_add (hbp _) (hbp _),
          ← ENNReal.ofReal_add (add_nonneg (hbp _) (hbp _)) (hbp _),
          ← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)]
        exact ENNReal.ofReal_le_ofReal (hpt x)
    _ = ENNReal.ofReal K * (3 * ∑' x, ENNReal.ofReal (boxMax F x ^ p)) := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_add, ENNReal.tsum_add,
          tsum_ofReal_boxMax_add_rpow, tsum_ofReal_boxMax_add_rpow]
        ring
    _ ≤ ENNReal.ofReal K * (3 * (ENNReal.ofReal (18 * 2 ^ (p - 1) * p / (p - 1)) *
          ENNReal.ofReal W)) := by gcongr
    _ = ENNReal.ofReal (3 * K * (18 * 2 ^ (p - 1) * p / (p - 1)) * W) := by
        have h18 : 0 ≤ 18 * 2 ^ (p - 1) * p / (p - 1) := by
          have : 0 < p - 1 := by linarith
          positivity
        have hW0 : 0 ≤ W := Finset.sum_nonneg fun y _ => mul_nonneg (coshW_pos a y).le
          (Real.rpow_nonneg (hf y) _)
        rw [← ENNReal.ofReal_mul h18, ← ENNReal.ofReal_ofNat 3,
          ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

end Rigidity.Poincare
