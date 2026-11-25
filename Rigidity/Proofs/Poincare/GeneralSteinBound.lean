import Rigidity.Proofs.Poincare.SteinBound
import Rigidity.Proofs.Poincare.GeneralSteinWeighted

/-!
# The weighted square function bound on `ℤ^d`: the maximal majorant

The extension of the maximal part of `SteinBound.lean` from `ℤ²` to `ℤ^d`, `d ≥ 1`: the maximal
function `M` of the lattice form of Armstrong, Kuusi and Mourrat, Proposition D.2, Step 2 ((D.9),
with the weights of Remark D.6):

* `heatF_le_boxMax`: `ω(y)^{1/p} heatF f (y) ≤ C boxMax (ω^{1/p} f) (y)` for `s ∈ [0, T]`;
* `steinMajorant`: `M(x) = C e^a ω(x)^{-1/p} (M(ω^{1/p}f)(x) + Σ_i M(ω^{1/p}f)(x + e_i))`;
* `tsum_ofReal_coshW_mul_steinMajorant_le`:
  `Σ_x ω M^p ≤ ((d + 1) C e^a)^p · 2 · 3^d · 2^{p-1} p/(p-1) · Σ ω f^p`, from the power mean
  inequality for the `d + 1` maximal terms and the strong type bound of the box maximal function.
-/

open scoped Classical
open LatticeProb LatticeProb.Percolation Rigidity.Green MeasureTheory

namespace Rigidity.Poincare.GeneralDim

variable {d : ℕ} {S : Finset (Vertex d)} {f : Vertex d → ℝ}

/-- `ω^{1/p} f`. -/
noncomputable def wf (a p : ℝ) (f : Vertex d → ℝ) (y : Vertex d) : ℝ :=
  coshW a y ^ (1 / p) * f y

theorem wf_nonneg (hf : ∀ y, 0 ≤ f y) (a p : ℝ) (y : Vertex d) : 0 ≤ wf a p f y :=
  mul_nonneg (Real.rpow_nonneg (coshW_pos a y).le _) (hf y)

theorem wf_eq_zero (hfS : ∀ y ∉ S, f y = 0) (a p : ℝ) {y : Vertex d} (hy : y ∉ S) :
    wf a p f y = 0 := by
  rw [wf, hfS y hy, mul_zero]

theorem summable_wf (hfS : ∀ y ∉ S, f y = 0) (a p : ℝ) : Summable (wf a p f) :=
  summable_of_ne_finset_zero fun _ hy => wf_eq_zero hfS a p hy

/-- **The heat flow is dominated by the maximal function of `ω^{1/p} f`**. -/
theorem heatF_le_boxMax [NeZero d] {C₃ : ℝ}
    (hmax : ∀ T a : ℝ, 0 ≤ T → 0 ≤ a → a ≤ 1 / 6 → a * max (Real.sqrt T) 1 ≤ 1 →
      ∀ s : ℝ, 0 ≤ s → s ≤ T → ∀ G : Vertex d → ℝ, (∀ z, 0 ≤ G z) → Summable G →
        ∀ x : Vertex d, ∑' y, ENNReal.ofReal (zdHeat d s x y *
          Real.exp (a * ∑ i, |(((y - x) i : ℤ) : ℝ)|) * G y) ≤ ENNReal.ofReal (C₃ * boxMax G x))
    (hC₃ : 0 < C₃) (hf : ∀ y, 0 ≤ f y) (hfS : ∀ y ∉ S, f y = 0) {p : ℝ} (hp : 1 ≤ p)
    {a T : ℝ} (hT : 0 ≤ T) (ha0 : 0 ≤ a) (ha6 : a ≤ 1 / 6) (haT : a * max (Real.sqrt T) 1 ≤ 1)
    {s : ℝ} (hs : 0 ≤ s) (hsT : s ≤ T) (y : Vertex d) :
    coshW a y ^ (1 / p) * heatF S f s y ≤ C₃ * boxMax (wf a p f) y := by
  set E : Vertex d → ℝ := fun z => Real.exp (a * ∑ i, |(((z - y) i : ℤ) : ℝ)|) with hE
  have hE1 : ∀ z, 1 ≤ E z := fun z =>
    Real.one_le_exp (mul_nonneg ha0 (Finset.sum_nonneg fun i _ => abs_nonneg _))
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
      ∑ z ∈ S, zdHeat d s y z * E z * wf a p f z := by
    unfold heatF
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun z _ => ?_
    have h0 := zdHeat_nonneg (d := d) hs y z
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hw z) (hf z)) h0
    simp only [wf]
    nlinarith
  have heq : ∑' z, ENNReal.ofReal (zdHeat d s y z * E z * wf a p f z) =
      ∑ z ∈ S, ENNReal.ofReal (zdHeat d s y z * E z * wf a p f z) :=
    tsum_eq_sum fun z hz => by rw [wf_eq_zero hfS a p hz, mul_zero, ENNReal.ofReal_zero]
  have hsum : ENNReal.ofReal (∑ z ∈ S, zdHeat d s y z * E z * wf a p f z) ≤
      ENNReal.ofReal (C₃ * boxMax (wf a p f) y) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun z _ => mul_nonneg (mul_nonneg
      (zdHeat_nonneg hs y z) (by linarith [hE1 z])) (wf_nonneg hf a p z), ← heq]
    exact hmax T a hT ha0 ha6 haT s hs hsT (wf a p f) (wf_nonneg hf a p) (summable_wf hfS a p) y
  have hM0 : 0 ≤ C₃ * boxMax (wf a p f) y :=
    mul_nonneg hC₃.le (boxMax_nonneg (wf_nonneg hf a p) (summable_wf hfS a p) y)
  exact hle.trans ((ENNReal.ofReal_le_ofReal_iff hM0).1 hsum)

theorem coshW_add_unit_le (a : ℝ) (ha : 0 ≤ a) (x : Vertex d) (i : Fin d) :
    coshW a x ≤ coshW a (x + unit i) * Real.exp a := by
  have h := coshW_le_mul_exp ha x (x + unit i)
  have e : x + unit i - x = unit i := by abel
  rw [e, abs_unit_sum, mul_one] at h
  exact h

theorem rpow_neg_coshW_add_unit_le {a p : ℝ} (ha : 0 ≤ a) (hp : 1 ≤ p) (x : Vertex d)
    (i : Fin d) :
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

/-- The `d + 1` points `x` and `x + e_i` of the majorant, indexed by `Option (Fin d)`. -/
def majPoint (x : Vertex d) : Option (Fin d) → Vertex d
  | none => x
  | some i => x + unit i

/-- The maximal majorant
`M(x) = C e^a ω(x)^{-1/p} (M(ω^{1/p}f)(x) + Σ_i M(ω^{1/p}f)(x + e_i))`. -/
noncomputable def steinMajorant (C a p : ℝ) (f : Vertex d → ℝ) (x : Vertex d) : ℝ :=
  C * Real.exp a * coshW a x ^ (-(1 / p)) * ∑ o : Option (Fin d), boxMax (wf a p f) (majPoint x o)

theorem sum_majPoint (F : Vertex d → ℝ) (x : Vertex d) :
    ∑ o : Option (Fin d), F (majPoint x o) = F x + ∑ i, F (x + unit i) :=
  Fintype.sum_option _

theorem steinMajorant_nonneg (hf : ∀ y, 0 ≤ f y) (hfS : ∀ y ∉ S, f y = 0) {C : ℝ} (hC : 0 ≤ C)
    (a p : ℝ) (x : Vertex d) : 0 ≤ steinMajorant C a p f x := by
  have h := fun z => boxMax_nonneg (wf_nonneg hf a p) (summable_wf hfS a p) z
  have hr := Real.rpow_nonneg (coshW_pos a x).le (-(1 / p))
  unfold steinMajorant
  exact mul_nonneg (mul_nonneg (mul_nonneg hC (Real.exp_pos a).le) hr)
    (Finset.sum_nonneg fun o _ => h _)

theorem tsum_ofReal_boxMax_add_rpow (F : Vertex d → ℝ) (e : Vertex d) (p : ℝ) :
    ∑' x, ENNReal.ofReal (boxMax F (x + e) ^ p) = ∑' x, ENNReal.ofReal (boxMax F x ^ p) :=
  (Equiv.addRight e).tsum_eq fun x => ENNReal.ofReal (boxMax F x ^ p)

theorem tsum_ofReal_boxMax_majPoint_rpow (F : Vertex d → ℝ) (o : Option (Fin d)) (p : ℝ) :
    ∑' x, ENNReal.ofReal (boxMax F (majPoint x o) ^ p) = ∑' x, ENNReal.ofReal (boxMax F x ^ p) := by
  cases o with
  | none => rfl
  | some i => exact tsum_ofReal_boxMax_add_rpow F (unit i) p

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

/-- **The weighted maximal bound**:
`Σ_x ω M^p ≤ ((d + 1) C e^a)^p · 2 · 3^d · 2^{p-1} p/(p-1) · Σ ω f^p`. -/
theorem tsum_ofReal_coshW_mul_steinMajorant_le (hf : ∀ y, 0 ≤ f y) (hfS : ∀ y ∉ S, f y = 0)
    {C : ℝ} (hC : 0 ≤ C) {a p : ℝ} (hp : 1 < p) :
    ∑' x, ENNReal.ofReal (coshW a x * steinMajorant C a p f x ^ p) ≤
      ENNReal.ofReal (((d + 1) * C * Real.exp a) ^ p * (2 * 3 ^ d * 2 ^ (p - 1) * p / (p - 1)) *
        ∑ y ∈ S, coshW a y * f y ^ p) := by
  have hp0 : 0 < p := by linarith
  set F := wf a p f with hF
  have hF0 := wf_nonneg hf a p
  have hFs := summable_wf hfS a p
  have hb := fun z => boxMax_nonneg hF0 hFs z
  set W := ∑ y ∈ S, coshW a y * f y ^ p with hW
  set N : ℝ := (d : ℝ) + 1 with hN
  have hN0 : 0 < N := by positivity
  have hcard : ((Finset.univ : Finset (Option (Fin d))).card : ℝ) = N := by
    rw [Finset.card_univ, Fintype.card_option, Fintype.card_fin]
    push_cast
    ring
  have hCe0 : 0 ≤ C * Real.exp a := mul_nonneg hC (Real.exp_pos a).le
  set K := (C * Real.exp a) ^ p * N ^ (p - 1) with hK
  have hK0 : 0 ≤ K := by positivity
  have hpt : ∀ x, coshW a x * steinMajorant C a p f x ^ p ≤
      K * ∑ o : Option (Fin d), boxMax F (majPoint x o) ^ p := by
    intro x
    have hω := coshW_pos a x
    have e1 : coshW a x * (coshW a x ^ (-(1 / p))) ^ p = 1 := by
      rw [← Real.rpow_mul hω.le, show -(1 / p) * p = -1 by field_simp, Real.rpow_neg_one,
        mul_inv_cancel₀ hω.ne']
    have hB := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (s := Finset.univ)
      (f := fun o : Option (Fin d) => boxMax F (majPoint x o)) hp.le (fun o _ => hb _)
    rw [hcard] at hB
    unfold steinMajorant
    have hsumb : 0 ≤ ∑ o : Option (Fin d), boxMax F (majPoint x o) :=
      Finset.sum_nonneg fun o _ => hb _
    rw [Real.mul_rpow (mul_nonneg hCe0 (Real.rpow_nonneg hω.le _)) hsumb,
      Real.mul_rpow hCe0 (Real.rpow_nonneg hω.le _)]
    have e2 : coshW a x * ((C * Real.exp a) ^ p * (coshW a x ^ (-(1 / p))) ^ p *
        (∑ o : Option (Fin d), boxMax F (majPoint x o)) ^ p) =
        (C * Real.exp a) ^ p * (∑ o : Option (Fin d), boxMax F (majPoint x o)) ^ p
          * (coshW a x * (coshW a x ^ (-(1 / p))) ^ p) := by ring
    rw [e2, e1, mul_one, hK, mul_assoc]
    exact mul_le_mul_of_nonneg_left hB (Real.rpow_nonneg hCe0 _)
  have hHL := tsum_boxMax_rpow_le hF0 hFs hp
  rw [tsum_ofReal_wf_rpow hf hfS hp.le] at hHL
  have hbp := fun z => Real.rpow_nonneg (hb z) p
  have hHL0 : 0 ≤ 2 * 3 ^ d * 2 ^ (p - 1) * p / (p - 1) := by
    have : 0 < p - 1 := by linarith
    positivity
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun y _ => mul_nonneg (coshW_pos a y).le
    (Real.rpow_nonneg (hf y) _)
  calc ∑' x, ENNReal.ofReal (coshW a x * steinMajorant C a p f x ^ p)
      ≤ ∑' x, ENNReal.ofReal K * ∑ o : Option (Fin d),
          ENNReal.ofReal (boxMax F (majPoint x o) ^ p) := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        rw [← ENNReal.ofReal_sum_of_nonneg fun o _ => hbp _, ← ENNReal.ofReal_mul hK0]
        exact ENNReal.ofReal_le_ofReal (hpt x)
    _ = ENNReal.ofReal K * ∑ o : Option (Fin d),
          ∑' x, ENNReal.ofReal (boxMax F (majPoint x o) ^ p) := by
        rw [ENNReal.tsum_mul_left, Summable.tsum_finsetSum (fun o _ => ENNReal.summable)]
    _ = ENNReal.ofReal K * (ENNReal.ofReal N * ∑' x, ENNReal.ofReal (boxMax F x ^ p)) := by
        simp only [tsum_ofReal_boxMax_majPoint_rpow]
        rw [Finset.sum_const, nsmul_eq_mul, ← hcard, ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal K * (ENNReal.ofReal N *
          (ENNReal.ofReal (2 * 3 ^ d * 2 ^ (p - 1) * p / (p - 1)) * ENNReal.ofReal W)) := by
        gcongr
    _ = ENNReal.ofReal ((N * C * Real.exp a) ^ p * (2 * 3 ^ d * 2 ^ (p - 1) * p / (p - 1)) *
          W) := by
        rw [← ENNReal.ofReal_mul hHL0, ← ENNReal.ofReal_mul hN0.le, ← ENNReal.ofReal_mul hK0]
        congr 1
        have hpow : N ^ (p - 1) * N = N ^ p := by
          rw [← Real.rpow_add_one hN0.ne', sub_add_cancel]
        have hKN : K * N = (N * C * Real.exp a) ^ p := by
          rw [hK, mul_assoc, hpow, mul_assoc N C, Real.mul_rpow hN0.le hCe0, mul_comm]
        calc K * (N * ((2 * 3 ^ d * 2 ^ (p - 1) * p / (p - 1)) * W)) =
            (K * N) * (2 * 3 ^ d * 2 ^ (p - 1) * p / (p - 1)) * W := by ring
          _ = _ := by rw [hKN]

end Rigidity.Poincare.GeneralDim
