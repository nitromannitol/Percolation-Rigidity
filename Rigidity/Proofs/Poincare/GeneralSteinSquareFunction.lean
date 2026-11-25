import Rigidity.Proofs.Poincare.SteinSquareFunction
import Rigidity.Proofs.Poincare.GeneralLatticeHeatFlow

/-!
# Stein's bound for the Littlewood-Paley function of the heat semigroup of `ℤ^d`, `1 < p ≤ 2`

The extension of `SteinSquareFunction.lean` from `ℤ²` to `ℤ^d`, `d ≥ 1`. For `f ≥ 0` supported in
a finite set `S`, `v_s = heatF S f s` and `T ≥ 0`,

  `Γ(x) = ∫_0^T Σ_i (v_s(x + e_i) - v_s(x))² ds`.

* `gam_le_mul_ipos`: `Γ(x) ≤ (2/(p(p-1))) M^{2-p} I(x)` whenever `v_s ≤ M` at `x` and its `d`
  forward neighbours for `s ∈ [0, T]`, with
  `I(x) = ∫_0^T (lap(v_s^p)(x) - p v_s(x)^{p-1} lap v_s(x)) ds ≥ 0` (`steinPointwise`);
* `ipos_eq`: `I = lap H + f^p - v_T^p`, `H(x) = ∫_0^T v_s(x)^p ds`;
* `hasSum_coshW_mul_lap`: `Σ_x ω lap H = 2d(cosh a - 1) Σ_x ω H` for `ω = coshW a`
  (summation by parts).
-/

open scoped Classical
open LatticeProb LatticeProb.Percolation Rigidity.Green MeasureTheory

namespace Rigidity.Poincare.GeneralDim

variable {d : ℕ}

section Flow

variable (S : Finset (Vertex d)) (f : Vertex d → ℝ)

/-- `Γ(x) = ∫_0^T Σ_i (v_s(x + e_i) - v_s(x))² ds`. -/
noncomputable def gam (T : ℝ) (x : Vertex d) : ℝ :=
  ∫ s in (0 : ℝ)..T, ∑ i : Fin d, (heatF S f s (x + unit i) - heatF S f s x) ^ 2

/-- `I(x) = ∫_0^T (lap(v_s^p)(x) - p v_s(x)^{p-1} lap v_s(x)) ds`. -/
noncomputable def ipos (p T : ℝ) (x : Vertex d) : ℝ :=
  ∫ s in (0 : ℝ)..T, (lap (fun z => heatF S f s z ^ p) x -
    p * heatF S f s x ^ (p - 1) * lap (heatF S f s) x)

/-- `H(x) = ∫_0^T v_s(x)^p ds`. -/
noncomputable def hint (p T : ℝ) (x : Vertex d) : ℝ :=
  ∫ s in (0 : ℝ)..T, heatF S f s x ^ p

variable {S f}

theorem continuous_lap_of_continuous {g : ℝ → Vertex d → ℝ} (hg : ∀ z, Continuous fun s => g s z)
    (x : Vertex d) : Continuous fun s => lap (g s) x := by
  simp only [lap]
  exact (continuous_finsetSum _ fun i _ => (hg _).add (hg _)).sub (continuous_const.mul (hg _))

theorem continuous_heatF_rpow [NeZero d] {p : ℝ} (hp : 0 < p) (x : Vertex d) :
    Continuous fun s => heatF S f s x ^ p :=
  (continuous_heatF S f x).rpow_const fun _ => Or.inr hp.le

theorem continuous_lap_heatF [NeZero d] (x : Vertex d) :
    Continuous fun s => lap (heatF S f s) x :=
  continuous_lap_of_continuous (fun z => continuous_heatF S f z) x

theorem continuous_lap_heatF_rpow [NeZero d] {p : ℝ} (hp : 0 < p) (x : Vertex d) :
    Continuous fun s => lap (fun z => heatF S f s z ^ p) x :=
  continuous_lap_of_continuous (g := fun s z => heatF S f s z ^ p)
    (fun z => continuous_heatF_rpow hp z) x

theorem continuous_ipos_integrand [NeZero d] {p : ℝ} (hp : 1 < p) (x : Vertex d) :
    Continuous fun s => lap (fun z => heatF S f s z ^ p) x -
      p * heatF S f s x ^ (p - 1) * lap (heatF S f s) x :=
  (continuous_lap_heatF_rpow (by linarith) x).sub
    ((continuous_const.mul (continuous_heatF_rpow (by linarith) x)).mul (continuous_lap_heatF x))

/-- **The fundamental theorem of calculus** for `v^p`. -/
theorem integral_rpow_deriv [NeZero d] (hfS : ∀ y ∉ S, f y = 0) {p : ℝ} (hp : 1 < p) (T : ℝ)
    (x : Vertex d) :
    ∫ s in (0 : ℝ)..T, p * heatF S f s x ^ (p - 1) * lap (heatF S f s) x =
      heatF S f T x ^ p - f x ^ p := by
  have hd : ∀ s ∈ Set.uIcc (0 : ℝ) T, HasDerivAt (fun s => heatF S f s x ^ p)
      (p * heatF S f s x ^ (p - 1) * lap (heatF S f s) x) s := by
    intro s _
    have := (hasDerivAt_heatF S f s x).rpow_const (p := p) (Or.inr hp.le)
    exact this.congr_deriv (by ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (((continuous_const.mul (continuous_heatF_rpow (by linarith) x)).mul
      (continuous_lap_heatF x)).intervalIntegrable _ _), heatF_zero hfS]

theorem integral_lap (g : ℝ → Vertex d → ℝ) (hg : ∀ z, Continuous fun s => g s z) (T : ℝ)
    (x : Vertex d) :
    ∫ s in (0 : ℝ)..T, lap (g s) x = lap (fun z => ∫ s in (0 : ℝ)..T, g s z) x := by
  have hi : ∀ z, IntervalIntegrable (fun s => g s z) volume 0 T :=
    fun z => (hg z).intervalIntegrable _ _
  have hpair : ∀ i ∈ (Finset.univ : Finset (Fin d)),
      IntervalIntegrable (fun s => g s (x + unit i) + g s (x - unit i)) volume 0 T :=
    fun i _ => (hi _).add (hi _)
  simp only [lap]
  have hsumI : IntervalIntegrable (fun s => ∑ i : Fin d, (g s (x + unit i) + g s (x - unit i)))
      volume 0 T :=
    (continuous_finsetSum _ fun i _ => (hg _).add (hg _)).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub hsumI ((hi _).const_mul _),
    intervalIntegral.integral_finsetSum hpair, intervalIntegral.integral_const_mul]
  congr 1
  exact Finset.sum_congr rfl fun i _ => intervalIntegral.integral_add (hi _) (hi _)

/-- `I = lap H + f^p - v_T^p`. -/
theorem ipos_eq [NeZero d] (hfS : ∀ y ∉ S, f y = 0) {p : ℝ} (hp : 1 < p) (T : ℝ)
    (x : Vertex d) : ipos S f p T x = lap (hint S f p T) x + f x ^ p - heatF S f T x ^ p := by
  have h1 : IntervalIntegrable (fun s => lap (fun z => heatF S f s z ^ p) x) volume 0 T :=
    (continuous_lap_heatF_rpow (by linarith) x).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun s => p * heatF S f s x ^ (p - 1) * lap (heatF S f s) x)
      volume 0 T :=
    ((continuous_const.mul (continuous_heatF_rpow (by linarith) x)).mul
      (continuous_lap_heatF x)).intervalIntegrable _ _
  rw [ipos, intervalIntegral.integral_sub h1 h2, integral_rpow_deriv hfS hp T x,
    integral_lap (fun s z => heatF S f s z ^ p)
      (fun z => continuous_heatF_rpow (by linarith) z) T x]
  unfold hint
  ring

theorem ipos_integrand_nonneg [NeZero d] (hf : ∀ y, 0 ≤ f y) {p : ℝ} (hp1 : 1 < p)
    (hp2 : p ≤ 2) {s : ℝ} (hs : 0 ≤ s) (x : Vertex d) :
    0 ≤ lap (fun z => heatF S f s z ^ p) x - p * heatF S f s x ^ (p - 1) * lap (heatF S f s) x := by
  have hv := fun z => heatF_nonneg (S := S) hf hs z
  set M := heatF S f s x + ∑ i : Fin d, heatF S f s (x + unit i) + 1 with hMdef
  have hsum0 : 0 ≤ ∑ i : Fin d, heatF S f s (x + unit i) := Finset.sum_nonneg fun i _ => hv _
  have hM : 0 < M := by have := hv x; linarith
  have hle : ∀ i, heatF S f s (x + unit i) ≤ M := by
    intro i
    have h1 := Finset.single_le_sum (f := fun i => heatF S f s (x + unit i)) (fun j _ => hv _)
      (Finset.mem_univ i)
    have := hv x
    linarith
  have h := steinPointwise hp1 hp2 (M := M) hv (x := x) (by linarith) hle
  refine le_trans ?_ h
  have : 0 ≤ p * (p - 1) / 2 := by nlinarith
  have := Real.rpow_nonneg hM.le (p - 2)
  positivity

theorem ipos_nonneg [NeZero d] (hf : ∀ y, 0 ≤ f y) {p : ℝ} (hp1 : 1 < p) (hp2 : p ≤ 2) {T : ℝ}
    (hT : 0 ≤ T) (x : Vertex d) : 0 ≤ ipos S f p T x :=
  intervalIntegral.integral_nonneg hT fun _ hs => ipos_integrand_nonneg hf hp1 hp2 hs.1 x

theorem gam_nonneg {T : ℝ} (hT : 0 ≤ T) (x : Vertex d) : 0 ≤ gam S f T x :=
  intervalIntegral.integral_nonneg hT fun _ _ => by positivity

/-- **The pointwise square function bound** `Γ(x) ≤ (2/(p(p-1))) M^{2-p} I(x)`. -/
theorem gam_le_mul_ipos [NeZero d] (hf : ∀ y, 0 ≤ f y) {p : ℝ} (hp1 : 1 < p) (hp2 : p ≤ 2)
    {T M : ℝ} (hT : 0 ≤ T) (hM : 0 ≤ M) (x : Vertex d)
    (hvx : ∀ s ∈ Set.Icc 0 T, heatF S f s x ≤ M)
    (hvi : ∀ s ∈ Set.Icc 0 T, ∀ i, heatF S f s (x + unit i) ≤ M) :
    gam S f T x ≤ 2 / (p * (p - 1)) * M ^ (2 - p) * ipos S f p T x := by
  have hpp : 0 < p * (p - 1) := by nlinarith
  have hI := ipos_nonneg (S := S) hf hp1 hp2 hT x
  rcases hM.lt_or_eq with hMpos | hM0
  · have hc : 0 < p * (p - 1) / 2 * M ^ (p - 2) := by positivity
    have hint : p * (p - 1) / 2 * M ^ (p - 2) * gam S f T x ≤ ipos S f p T x := by
      rw [gam, ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_mono_on hT ?_ ?_ fun s hs => ?_
      · exact (continuous_const.mul (continuous_finsetSum _ fun i _ =>
          ((continuous_heatF S f _).sub (continuous_heatF S f _)).pow 2)).intervalIntegrable _ _
      · exact (continuous_ipos_integrand hp1 x).intervalIntegrable _ _
      · exact steinPointwise hp1 hp2 (fun z => heatF_nonneg hf hs.1 z) (hvx s hs) (hvi s hs)
    have e : 2 / (p * (p - 1)) * M ^ (2 - p) = (p * (p - 1) / 2 * M ^ (p - 2))⁻¹ := by
      rw [show 2 - p = -(p - 2) by ring, Real.rpow_neg hMpos.le]
      field_simp
    rw [e, inv_mul_eq_div, le_div_iff₀ hc, mul_comm]
    exact hint
  · have hz : gam S f T x = 0 := by
      rw [gam]
      refine intervalIntegral.integral_congr_ae ?_ |>.trans intervalIntegral.integral_zero
      refine Filter.Eventually.of_forall fun s hs => ?_
      rw [Set.uIoc_of_le hT] at hs
      have hs' : s ∈ Set.Icc 0 T := ⟨hs.1.le, hs.2⟩
      have h0 : heatF S f s x = 0 :=
        le_antisymm (hM0 ▸ hvx s hs') (heatF_nonneg hf hs.1.le x)
      have hi : ∀ i, heatF S f s (x + unit i) = 0 := fun i =>
        le_antisymm (hM0 ▸ hvi s hs' i) (heatF_nonneg hf hs.1.le _)
      simp [h0, hi]
    rw [hz]
    have := Real.rpow_nonneg hM (2 - p)
    positivity

end Flow

/-! ### Sums against the weight `coshW` -/

section Weighted

theorem coshW_sub_le (a : ℝ) (ha : 0 ≤ a) (x e : Vertex d)
    (he : ∑ i, |((e i : ℤ) : ℝ)| = 1) : coshW a (x - e) ≤ Real.exp a * coshW a x := by
  have h := coshW_le_mul_exp ha (x - e) x
  have e1 : (x - (x - e)) = e := by abel
  rw [e1, he, mul_one, mul_comm] at h
  exact h

theorem abs_unit_sum (i : Fin d) : ∑ j, |(((unit i : Vertex d) j : ℤ) : ℝ)| = 1 := by
  simp [unit, Pi.single_apply, apply_ite]

theorem abs_neg_unit_sum (i : Fin d) : ∑ j, |(((-unit i : Vertex d) j : ℤ) : ℝ)| = 1 := by
  simp [unit, Pi.single_apply, apply_ite]

/-- **Summation by parts against the weight**: `Σ_x ω lap H = 2d(cosh a - 1) Σ_x ω H`. -/
theorem hasSum_coshW_mul_lap {a : ℝ} (ha : 0 ≤ a) {H : Vertex d → ℝ} (hH : ∀ x, 0 ≤ H x)
    (hs : Summable fun x => coshW a x * H x) :
    HasSum (fun x => coshW a x * lap H x)
      (2 * d * (Real.cosh a - 1) * ∑' x, coshW a x * H x) := by
  have hsum2 : ∀ e : Vertex d, ∑ i, |((e i : ℤ) : ℝ)| = 1 →
      Summable fun x => coshW a (x - e) * H x := fun e he =>
    (hs.mul_left (Real.exp a)).of_nonneg_of_le
      (fun x => mul_nonneg (coshW_pos a _).le (hH x))
      (fun x => by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (coshW_sub_le a ha x e he) (hH x))
  have hshift : ∀ e : Vertex d, ∑ i, |((e i : ℤ) : ℝ)| = 1 →
      HasSum (fun x => coshW a x * H (x + e)) (∑' x, coshW a (x - e) * H x) := by
    intro e he
    have := (hsum2 e he).hasSum
    rw [← (Equiv.addRight e).hasSum_iff] at this
    refine this.congr_fun fun x => ?_
    simp
  have hp : ∀ i : Fin d, HasSum (fun x => coshW a x * H (x + unit i))
      (∑' x, coshW a (x - unit i) * H x) := fun i => hshift _ (abs_unit_sum i)
  have hm : ∀ i : Fin d, HasSum (fun x => coshW a x * H (x - unit i))
      (∑' x, coshW a (x + unit i) * H x) := by
    intro i
    have := hshift (-unit i) (abs_neg_unit_sum i)
    simp only [sub_neg_eq_add, ← sub_eq_add_neg] at this
    exact this
  have hsp : ∀ i : Fin d, Summable fun x => coshW a (x + unit i) * H x := by
    intro i
    have := hsum2 (-unit i) (abs_neg_unit_sum i)
    simpa only [sub_neg_eq_add] using this
  have hsm : ∀ i : Fin d, Summable fun x => coshW a (x - unit i) * H x :=
    fun i => hsum2 _ (abs_unit_sum i)
  have hall := (hasSum_sum fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) =>
    (hp i).add (hm i)).sub (hs.hasSum.mul_left (2 * (d : ℝ)))
  have hval : ∑ i : Fin d, (∑' x, coshW a (x - unit i) * H x +
      ∑' x, coshW a (x + unit i) * H x) - 2 * d * ∑' x, coshW a x * H x =
      2 * d * (Real.cosh a - 1) * ∑' x, coshW a x * H x := by
    have hpair : ∀ i ∈ (Finset.univ : Finset (Fin d)), Summable fun x =>
        coshW a (x - unit i) * H x + coshW a (x + unit i) * H x :=
      fun i _ => (hsm i).add (hsp i)
    rw [Finset.sum_congr rfl fun i _ => ((hsm i).tsum_add (hsp i)).symm,
      ← Summable.tsum_finsetSum hpair, ← tsum_mul_left,
      ← (summable_sum hpair).tsum_sub (hs.mul_left _), ← tsum_mul_left]
    refine tsum_congr fun x => ?_
    have := lap_coshW (d := d) a x
    simp only [lap] at this
    have e : ∑ i : Fin d, (coshW a (x - unit i) * H x + coshW a (x + unit i) * H x) =
        (∑ i : Fin d, (coshW a (x + unit i) + coshW a (x - unit i))) * H x := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e]
    linear_combination H x * this
  rw [← hval]
  refine hall.congr_fun fun x => ?_
  simp only [lap]
  rw [mul_sub, Finset.mul_sum]
  simp only [mul_add]
  ring

end Weighted

end Rigidity.Poincare.GeneralDim
