import Rigidity.Proofs.Green.GeneralFluxKernelGradient
import Rigidity.Proofs.Green.DarioGuFluxHeatDifference
import Rigidity.Proofs.Poincare.GeneralLatticeHeatFlow
import Rigidity.Proofs.Poincare.GeneralDualityBilinear
import Rigidity.Proofs.Poincare.GeneralDualityLowFreq
import Rigidity.Proofs.Poincare.GeneralHeatKernelBounds
import LatticeProb.Prob.Percolation.LatticeRadialTail

/-!
# Increments in time of the heat flow and the duality with heat averages on `ℤ^d`

The extension of `DarioGuFluxHeatDifference.lean` from `ℤ²` to `ℤ^d`, deterministic ingredients
of the estimate (eq.gsmallH-1) of Dario–Gu, Appendix B, in the lattice form with dyadic heat times:

* `lap_heatF_eqD`: for `w` vanishing off a finite set, the Laplacian of its heat flow is
  `-Σ_j Σ_x ∇_j Φ_t(u, ·)(x) ∇_j w(x)` (summation by parts);
* `ofReal_abs_heatF_sub_leD`: `|Φ_b w(u) - Φ_a w(u)| ≤ Σ_j Σ_{x ∈ T} κ_j(a, b, x - u) |∇_j w(x)|`
  with the time-integrated kernel `κ = heatGradKernelD`;
* `heatAvgD t f x = Σ_z Φ_t(x, z) f(z)` for `f` summable against every heat kernel
  (`HeatSummableAllD`, for instance of linear growth, `heatSummableAllD_of_abs_le`), the semigroup
  property `hasSum_heatAvgD_semigroup` and the duality `sum_heatAvgD_sub_mul_eq`;
* `ofReal_abs_tsum_mul_heatF_sub_leD`: the Cauchy–Schwarz bound of the right side by
  `(Σ_u (Φ_c f)(u)² m(u))^{1/2} (K Σ_j Σ_{x ∈ T} |∇_j w(x)|²)^{1/2}`,
  `m(u) = Σ_j Σ_{x ∈ T} κ_j(a, b, x - u)`, `K` a bound of the mass of `κ`.
-/

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.Poincare.GeneralDim
open scoped ENNReal Classical

namespace Rigidity.Green.GeneralFlux

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
theorem heatF_eq_tsumD {S : Finset (Vertex d)} {w : Vertex d → ℝ} (hw : ∀ y ∉ S, w y = 0)
    (t : ℝ) (u : Vertex d) :
    heatF S w t u = ∑' y, zdHeat d t u y * w y := by
  rw [tsum_eq_sum (s := S) (fun y hy => by rw [hw y hy, mul_zero])]
  rfl

omit [NeZero d] in
theorem summable_mul_of_eq_zero_offD {S : Finset (Vertex d)} {w : Vertex d → ℝ}
    (hw : ∀ y ∉ S, w y = 0) (Φ : Vertex d → ℝ) (e : Vertex d) :
    Summable fun x => Φ x * w (x + e) := by
  refine summable_of_ne_finset_zero (s := S.image fun y => y - e) fun x hx => ?_
  have : x + e ∉ S := fun h => hx (Finset.mem_image.2 ⟨x + e, h, add_sub_cancel_right x e⟩)
  rw [hw _ this, mul_zero]

/-- **Summation by parts for the Laplacian of the heat flow.** -/
theorem lap_heatF_eqD {S : Finset (Vertex d)} {w : Vertex d → ℝ} (hw : ∀ y ∉ S, w y = 0)
    (t : ℝ) (u : Vertex d) :
    lap (heatF S w t) u = -∑ j : Fin d, ∑' x,
      (zdHeat d t u (x + unit j) - zdHeat d t u x) *
        (w (x + unit j) - w x) := by
  set Φ : Vertex d → ℝ := fun y => zdHeat d t u y with hΦ
  set F := heatF S w t with hF
  have hplus : ∀ e : Vertex d, HasSum (fun x => Φ x * w (x + e)) (F (u + e)) := by
    intro e
    have h1 : F (u + e) = ∑' y, Φ (y - e) * w y := by
      rw [hF, heatF_eq_tsumD hw]
      refine tsum_congr fun y => ?_
      simp only [hΦ]
      rw [← zdHeat_sub t (u + e) y e, add_sub_cancel_right]
    have h2 : ∑' y, Φ (y - e) * w y = ∑' x, Φ x * w (x + e) := by
      rw [← (Equiv.addRight e).tsum_eq]
      simp only [Equiv.coe_addRight, add_sub_cancel_right]
    rw [h1, h2]
    exact (summable_mul_of_eq_zero_offD hw Φ e).hasSum
  have hminus : ∀ e : Vertex d, HasSum (fun x => Φ (x + e) * w x) (F (u - e)) := by
    intro e
    have h1 : F (u - e) = ∑' x, Φ (x + e) * w x := by
      rw [hF, heatF_eq_tsumD hw]
      refine tsum_congr fun y => ?_
      simp only [hΦ]
      rw [← zdHeat_add t (u - e) y e, sub_add_cancel]
    rw [h1]
    refine Summable.hasSum ?_
    have := summable_mul_of_eq_zero_offD hw (fun x => Φ (x + e)) 0
    simpa only [add_zero] using this
  have hzero : HasSum (fun x => Φ x * w x) (F u) := by
    have := hplus 0
    simpa only [add_zero] using this
  have hshift : ∀ e : Vertex d, HasSum (fun x => Φ (x + e) * w (x + e)) (F u) := by
    intro e
    have h := hzero
    rw [← (Equiv.addRight e).hasSum_iff] at h
    exact h
  have hj : ∀ e : Vertex d, ∑' x, (Φ (x + e) - Φ x) * (w (x + e) - w x) =
      2 * F u - F (u + e) - F (u - e) := by
    intro e
    have h := (((hshift e).sub (hminus e)).sub (hplus e)).add hzero
    have hv : 2 * F u - F (u + e) - F (u - e) = F u - F (u - e) - F (u + e) + F u := by ring
    rw [hv, ← h.tsum_eq]
    refine tsum_congr fun x => ?_
    ring
  rw [Finset.sum_congr rfl fun j _ => hj (unit j)]
  simp only [lap, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **The time increments of the heat flow**, through the gradient of the test function. -/
theorem ofReal_abs_heatF_sub_leD {S T : Finset (Vertex d)} {w : Vertex d → ℝ}
    (hw : ∀ y ∉ S, w y = 0) (hT : ∀ x ∉ T, ∀ j : Fin d, w (x + unit j) = w x) {a b : ℝ}
    (hab : a ≤ b) (u : Vertex d) :
    ENNReal.ofReal |heatF S w b u - heatF S w a u| ≤
      ∑ j : Fin d, ∑ x ∈ T, heatGradKernelD j a b (x - u) * ENNReal.ofReal |w (x + unit j) - w x| := by
  set D : ℝ → ℝ := fun t => lap (heatF S w t) u with hD
  have hcont : Continuous D := by
    simp only [hD, lap]
    exact (continuous_finsetSum _ fun i _ =>
      (continuous_heatF S w _).add (continuous_heatF S w _)).sub
      (continuous_const.mul (continuous_heatF S w u))
  have hFTC : heatF S w b u - heatF S w a u = ∫ t in a..b, D t :=
    (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_heatF S w t u)
      (hcont.intervalIntegrable a b)).symm
  set A : Fin d → Vertex d → ℝ → ℝ := fun j x t =>
    zdHeat d t 0 (x - u + unit j) - zdHeat d t 0 (x - u) with hA
  have hDfin : ∀ t, D t = -∑ j : Fin d, ∑ x ∈ T, A j x t * (w (x + unit j) - w x) := by
    intro t
    simp only [hD]
    rw [lap_heatF_eqD hw]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [tsum_eq_sum (s := T) (fun x hx => by rw [hT x hx j, sub_self, mul_zero])]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [hA]
    rw [← zdHeat_sub t u (x + unit j) u, ← zdHeat_sub t u x u, sub_self,
      add_sub_right_comm]
  have hAm : ∀ j x, Measurable fun t => ENNReal.ofReal |A j x t| := fun j x =>
    ENNReal.measurable_ofReal.comp
      (((continuous_zdHeat 0 _).sub (continuous_zdHeat 0 _)).abs.measurable)
  rw [hFTC, intervalIntegral.integral_of_le hab]
  calc ENNReal.ofReal |∫ t in Set.Ioc a b, D t| = ‖∫ t in Set.Ioc a b, D t‖ₑ :=
        (Real.enorm_eq_ofReal_abs _).symm
    _ ≤ ∫⁻ t in Set.Ioc a b, ‖D t‖ₑ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ t in Set.Ioc a b, ∑ j : Fin d, ∑ x ∈ T,
          ENNReal.ofReal |A j x t| * ENNReal.ofReal |w (x + unit j) - w x| := by
        refine lintegral_mono fun t => ?_
        rw [Real.enorm_eq_ofReal_abs, hDfin t, abs_neg]
        refine (ofReal_abs_finset_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        refine (ofReal_abs_finset_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
        rw [abs_mul, ENNReal.ofReal_mul (abs_nonneg _)]
    _ = ∑ j : Fin d, ∑ x ∈ T, heatGradKernelD j a b (x - u) *
          ENNReal.ofReal |w (x + unit j) - w x| := by
        rw [lintegral_finsetSum _ fun j _ => Finset.measurable_sum _ fun x _ =>
          (hAm j x).mul_const _]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [lintegral_finsetSum _ fun x _ => (hAm j x).mul_const _]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [lintegral_mul_const _ (hAm j x)]
        rfl

/-! ### Heat averages of functions on `ℤ^d` -/

/-- `f` is summable against every heat kernel. -/
def HeatSummableAllD (f : Vertex d → ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → ∀ x : Vertex d, Summable fun z => zdHeat d t x z * |f z|

/-- The heat average `Φ_t f(x) = Σ_z Φ_t(x, z) f(z)`. -/
noncomputable def heatAvgD (t : ℝ) (f : Vertex d → ℝ) (x : Vertex d) : ℝ :=
  ∑' z, zdHeat d t x z * f z

theorem HeatSummableAllD.summable {f : Vertex d → ℝ} (hf : HeatSummableAllD f) {t : ℝ}
    (ht : 0 ≤ t) (x : Vertex d) : Summable fun z => zdHeat d t x z * f z := by
  refine Summable.of_norm ((hf t ht x).congr fun z => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (zdHeat_nonneg ht x z)]

omit [NeZero d] in
theorem heatAvgD_zero (f : Vertex d → ℝ) (x : Vertex d) : heatAvgD 0 f x = f x := by
  unfold heatAvgD
  simp only [zdHeat_zero, ite_mul, one_mul, zero_mul]
  rw [tsum_eq_single x (fun z hz => if_neg (Ne.symm hz)), if_pos rfl]

/-- **The semigroup property** `Φ_{s+t} f(x) = Σ_u Φ_s(x, u) Φ_t f(u)`. -/
theorem hasSum_heatAvgD_semigroup {f : Vertex d → ℝ} (hf : HeatSummableAllD f) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (x : Vertex d) :
    HasSum (fun u => zdHeat d s x u * heatAvgD t f u) (heatAvgD (s + t) f x) := by
  set F : Vertex d → Vertex d → ℝ := fun u z =>
    zdHeat d s x u * (zdHeat d t u z * f z) with hF
  have hfib : ∀ z, HasSum (fun u => |F u z|) (zdHeat d (s + t) x z * |f z|) := by
    intro z
    have h := (hasSum_zdHeat_mul hs ht x z).mul_right |f z|
    refine h.congr_fun fun u => ?_
    simp only [hF]
    rw [abs_mul, abs_mul, abs_of_nonneg (zdHeat_nonneg hs x u),
      abs_of_nonneg (zdHeat_nonneg ht u z)]
    ring
  have hsum : Summable (Function.uncurry fun z u => F u z) := by
    refine Summable.of_abs ?_
    have h0 : 0 ≤ fun q : Vertex d × Vertex d => |F q.2 q.1| := fun q => abs_nonneg _
    have : Summable fun q : Vertex d × Vertex d => |F q.2 q.1| := by
      rw [summable_prod_of_nonneg h0]
      exact ⟨fun z => (hfib z).summable, ((hf (s + t) (by linarith) x).congr
        fun z => ((hfib z).tsum_eq).symm)⟩
    exact this
  have hsum' : Summable (Function.uncurry F) :=
    (Equiv.prodComm (Vertex d) (Vertex d)).summable_iff.2 hsum
  have hcomm := hsum'.tsum_comm
  have hval : ∑' u, zdHeat d s x u * heatAvgD t f u = heatAvgD (s + t) f x := by
    unfold heatAvgD
    calc ∑' u, zdHeat d s x u * ∑' z, zdHeat d t u z * f z
        = ∑' u, ∑' z, F u z := tsum_congr fun u => tsum_mul_left.symm
      _ = ∑' z, ∑' u, F u z := hcomm.symm
      _ = ∑' z, zdHeat d (s + t) x z * f z := by
          refine tsum_congr fun z => ?_
          have h := (hasSum_zdHeat_mul hs ht x z).mul_right (f z)
          rw [← h.tsum_eq]
          exact tsum_congr fun u => by simp only [hF]; ring
  have hsu : Summable fun u => zdHeat d s x u * heatAvgD t f u := by
    refine hsum'.prod.congr fun u => ?_
    unfold heatAvgD
    show ∑' z, zdHeat d s x u * (zdHeat d t u z * f z) = _
    exact tsum_mul_left
  rw [← hval]
  exact hsu.hasSum

/-- **Duality between heat averages and the heat flow of a test function.** -/
theorem sum_heatAvgD_sub_mul_eq {f : Vertex d → ℝ} (hf : HeatSummableAllD f)
    (S : Finset (Vertex d)) (w : Vertex d → ℝ) {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) :
    ∑ x ∈ S, (heatAvgD (b + c) f x - heatAvgD (a + c) f x) * w x =
      ∑' u, heatAvgD c f u * (heatF S w b u - heatF S w a u) := by
  set G := heatAvgD c f
  have hb' := fun x => hasSum_heatAvgD_semigroup hf hb hc x
  have ha' := fun x => hasSum_heatAvgD_semigroup hf ha hc x
  have hterm : ∀ x ∈ S, (heatAvgD (b + c) f x - heatAvgD (a + c) f x) * w x =
      ∑' u, (zdHeat d b x u - zdHeat d a x u) * G u * w x := by
    intro x _
    rw [← (hb' x).tsum_eq, ← (ha' x).tsum_eq, ← ((hb' x).summable.tsum_sub (ha' x).summable),
      ← tsum_mul_right]
    exact tsum_congr fun u => by ring
  have hsumm : ∀ x ∈ S, Summable fun u =>
      (zdHeat d b x u - zdHeat d a x u) * G u * w x := by
    intro x _
    refine (((hb' x).summable.sub (ha' x).summable).mul_right (w x)).congr fun u => ?_
    ring
  rw [Finset.sum_congr rfl hterm, ← Summable.tsum_finsetSum hsumm]
  refine tsum_congr fun u => ?_
  unfold heatF
  rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [zdHeat_symm b x u, zdHeat_symm a x u]
  ring

theorem summable_exp_neg_norm_subD (y : Vertex d) {κ : ℝ} (hκ : 0 < κ) :
    Summable fun z : Vertex d => Real.exp (-‖latticeEuclideanEmbedding (z - y)‖ / κ) := by
  have h := tsum_exp_neg_norm_sub_le y hκ
  have hne : ∑' z : Vertex d,
      ENNReal.ofReal (Real.exp (-‖latticeEuclideanEmbedding (z - y)‖ / κ)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  have := ENNReal.summable_toReal hne
  simpa only [ENNReal.toReal_ofReal (Real.exp_pos _).le] using this

theorem one_add_mul_exp_neg_le {a e : ℝ} (ha : 0 < a) (he : 0 ≤ e) :
    (1 + e) * Real.exp (-(a * e)) ≤ (1 + 2 / a) * Real.exp (-e / (2 / a)) := by
  have h4 : 0 ≤ a * e / 2 := by positivity
  have h1 : 1 + a * e / 2 ≤ Real.exp (a * e / 2) := by
    have := Real.add_one_le_exp (a * e / 2)
    linarith
  have h5 : 1 ≤ Real.exp (a * e / 2) := Real.one_le_exp h4
  have h2 : 1 + e ≤ (1 + 2 / a) * Real.exp (a * e / 2) := by
    have h3 : e = 2 / a * (a * e / 2) := by field_simp
    have h6 : 0 < 2 / a := by positivity
    rw [add_mul, one_mul]
    nlinarith [mul_le_mul_of_nonneg_left h1 h6.le]
  have e3 : Real.exp (a * e / 2) * Real.exp (-(a * e)) = Real.exp (-e / (2 / a)) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  calc (1 + e) * Real.exp (-(a * e))
      ≤ (1 + 2 / a) * Real.exp (a * e / 2) * Real.exp (-(a * e)) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = (1 + 2 / a) * Real.exp (-e / (2 / a)) := by rw [mul_assoc, e3]

/-- **The heat average of a function of linear growth converges** on `ℤ^d`. -/
theorem summable_zdHeat_mul_of_abs_le {t : ℝ} (ht : 0 ≤ t) (x : Vertex d)
    {f : Vertex d → ℝ} {A : ℝ}
    (hf : ∀ z, |f z| ≤ A * (1 + ‖latticeEuclideanEmbedding z‖)) :
    Summable fun z => zdHeat d t x z * f z := by
  obtain ⟨C, hC, hK⟩ := exists_zdHeat_mul_exp_le (d := d)
  set σ := max (Real.sqrt t) 1 with hσ
  have hσ1 : 1 ≤ σ := le_max_right _ _
  have hσ0 : 0 < σ := lt_of_lt_of_le one_pos hσ1
  set a : ℝ := 1 / (6 * σ) with ha
  have ha0 : 0 < a := by positivity
  have ha6 : a ≤ 1 / 6 := by
    rw [ha]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have haσ : a * σ ≤ 1 := by
    rw [ha, div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
    linarith
  set K : ℝ := C ^ d / σ ^ d with hKdef
  have hK0 : 0 ≤ K := by positivity
  set B : ℝ := K * |A| * (1 + ‖latticeEuclideanEmbedding x‖) * (1 + 2 / a)
  refine Summable.of_norm_bounded
    ((summable_exp_neg_norm_subD x (by positivity : 0 < 2 / a)).mul_left B) fun z => ?_
  set ℓ := ∑ i, |((((z - x) i : ℤ)) : ℝ)|
  set e := ‖latticeEuclideanEmbedding (z - x)‖
  have hℓe : e ≤ ℓ := norm_euclid_le_sum_abs (z - x)
  have he0 : 0 ≤ e := norm_nonneg _
  have hΦ0 := zdHeat_nonneg ht x z
  have hΦ : zdHeat d t x z ≤ K * Real.exp (-(a * e)) := by
    have h1 := hK t ht a ha0.le ha6 haσ x z
    have h2 : K * Real.exp (-ℓ / σ) ≤ K := by
      refine mul_le_of_le_one_right hK0 ?_
      rw [Real.exp_le_one_iff, neg_div]
      exact neg_nonpos.2 (div_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _) hσ0.le)
    have h3 : zdHeat d t x z * Real.exp (a * ℓ) ≤ K := h1.trans h2
    have h4 : zdHeat d t x z ≤ K * Real.exp (-(a * ℓ)) := by
      rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)]
      exact h3
    exact h4.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith)) hK0)
  have hz : 1 + ‖latticeEuclideanEmbedding z‖ ≤
      (1 + ‖latticeEuclideanEmbedding x‖) * (1 + e) := by
    have : ‖latticeEuclideanEmbedding z‖ ≤ ‖latticeEuclideanEmbedding x‖ + e := by
      have e1 : latticeEuclideanEmbedding z =
          latticeEuclideanEmbedding x + latticeEuclideanEmbedding (z - x) := by
        rw [LatticeProb.Percolation.latticeEuclideanEmbedding_sub]; abel
      rw [e1]
      exact norm_add_le _ _
    nlinarith [norm_nonneg (latticeEuclideanEmbedding x)]
  have hfz : |f z| ≤ |A| * ((1 + ‖latticeEuclideanEmbedding x‖) * (1 + e)) :=
    (hf z).trans (by
      calc A * (1 + ‖latticeEuclideanEmbedding z‖)
          ≤ |A| * (1 + ‖latticeEuclideanEmbedding z‖) :=
            mul_le_mul_of_nonneg_right (le_abs_self A) (by positivity)
        _ ≤ |A| * ((1 + ‖latticeEuclideanEmbedding x‖) * (1 + e)) :=
            mul_le_mul_of_nonneg_left hz (abs_nonneg A))
  have hexp := one_add_mul_exp_neg_le ha0 he0
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hΦ0]
  calc zdHeat d t x z * |f z|
      ≤ (K * Real.exp (-(a * e))) * (|A| * ((1 + ‖latticeEuclideanEmbedding x‖) * (1 + e))) :=
        mul_le_mul hΦ hfz (abs_nonneg _) (by positivity)
    _ = K * |A| * (1 + ‖latticeEuclideanEmbedding x‖) * ((1 + e) * Real.exp (-(a * e))) := by
        ring
    _ ≤ K * |A| * (1 + ‖latticeEuclideanEmbedding x‖) * ((1 + 2 / a) * Real.exp (-e / (2 / a))) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = B * Real.exp (-e / (2 / a)) := by ring

/-- Functions of linear growth are summable against every heat kernel. -/
theorem heatSummableAllD_of_abs_le {f : Vertex d → ℝ} {A : ℝ}
    (hf : ∀ z, |f z| ≤ A * (1 + ‖latticeEuclideanEmbedding z‖)) : HeatSummableAllD f := by
  intro t ht x
  rcases ht.lt_or_eq with ht0 | rfl
  · exact summable_zdHeat_mul_of_abs_le ht0.le x
      (f := fun z => |f z|) (A := A) (fun z => by rw [abs_abs]; exact hf z)
  · refine summable_of_ne_finset_zero (s := {x}) fun z hz => ?_
    rw [Finset.mem_singleton] at hz
    rw [zdHeat_zero, if_neg (Ne.symm hz), zero_mul]

/-! ### The Cauchy–Schwarz bound -/

omit [NeZero d] in
/-- Cauchy–Schwarz for a countable sum of finite sums. -/
theorem tsum_sum_mul_leD {ι : Type*} (P : Finset ι) (f g : Vertex d → ι → ℝ≥0∞) :
    ∑' u, ∑ p ∈ P, f u p * g u p ≤
      (∑' u, ∑ p ∈ P, f u p ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
        (∑' u, ∑ p ∈ P, g u p ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  set α : Vertex d → ℝ≥0∞ := fun u => (∑ p ∈ P, f u p ^ (2 : ℝ)) ^ (1 / 2 : ℝ) with hα
  set β : Vertex d → ℝ≥0∞ := fun u => (∑ p ∈ P, g u p ^ (2 : ℝ)) ^ (1 / 2 : ℝ) with hβ
  have hinner : ∀ u, ∑ p ∈ P, f u p * g u p ≤ α u * β u := fun u =>
    ENNReal.inner_le_Lp_mul_Lq P (f u) (g u) Real.HolderConjugate.two_two
  have hsq : ∀ x : ℝ≥0∞, (x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = x := fun x => by
    rw [← ENNReal.rpow_mul]
    norm_num
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (Measure.count (α := Vertex d))
    Real.HolderConjugate.two_two (f := α) (g := β) (Measurable.of_discrete).aemeasurable
    (Measurable.of_discrete).aemeasurable
  simp only [lintegral_count, Pi.mul_apply, hα, hβ, hsq] at h
  exact (ENNReal.tsum_le_tsum hinner).trans h

/-- **The bound of the duality term.** -/
theorem ofReal_abs_tsum_mul_heatF_sub_leD (G : Vertex d → ℝ) {S T : Finset (Vertex d)}
    {w : Vertex d → ℝ} (hw : ∀ y ∉ S, w y = 0)
    (hT : ∀ x ∉ T, ∀ j : Fin d, w (x + unit j) = w x) {a b : ℝ} (hab : a ≤ b) {K : ℝ≥0∞}
    (hK : ∀ j : Fin d, ∑' v, heatGradKernelD j a b v ≤ K) :
    ENNReal.ofReal |∑' u, G u * (heatF S w b u - heatF S w a u)| ≤
      (∑' u, ENNReal.ofReal (G u ^ 2) *
          ∑ j : Fin d, ∑ x ∈ T, heatGradKernelD j a b (x - u)) ^ (1 / 2 : ℝ) *
        (K * ∑ j : Fin d, ∑ x ∈ T, ENNReal.ofReal ((w (x + unit j) - w x) ^ 2)) ^ (1 / 2 : ℝ) := by
  set P : Finset (Fin d × Vertex d) := Finset.univ ×ˢ T with hP
  set κ : Vertex d → Fin d × Vertex d → ℝ≥0∞ := fun u p => heatGradKernelD p.1 a b (p.2 - u)
    with hκ
  set B : Fin d × Vertex d → ℝ≥0∞ := fun p => ENNReal.ofReal |w (p.2 + unit p.1) - w p.2| with hB
  have hsqrt : ∀ x : ℝ≥0∞, x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x := fun x => by
    rw [← ENNReal.rpow_add_of_nonneg (x := x) (1 / 2 : ℝ) (1 / 2 : ℝ) (by norm_num) (by norm_num)]
    norm_num
  have hsq : ∀ x : ℝ≥0∞, (x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = x := fun x => by
    rw [← ENNReal.rpow_mul]
    norm_num
  have hprod : ∀ (F : Fin d × Vertex d → ℝ≥0∞),
      ∑ j : Fin d, ∑ x ∈ T, F (j, x) = ∑ p ∈ P, F p := fun F => by
    rw [hP, Finset.sum_product]
  have hterm : ∀ x k y : ℝ≥0∞, x * k * y = (x * k ^ (1 / 2 : ℝ)) * (k ^ (1 / 2 : ℝ) * y) := by
    intro x k y
    calc x * k * y = x * (k ^ (1 / 2 : ℝ) * k ^ (1 / 2 : ℝ)) * y := by rw [hsqrt]
      _ = _ := by ring
  -- the pointwise bound
  have hpt : ∀ u, ENNReal.ofReal |G u * (heatF S w b u - heatF S w a u)| ≤
      ∑ p ∈ P, (ENNReal.ofReal |G u| * κ u p ^ (1 / 2 : ℝ)) * (κ u p ^ (1 / 2 : ℝ) * B p) := by
    intro u
    rw [abs_mul, ENNReal.ofReal_mul (abs_nonneg _)]
    refine (mul_le_mul_right (ofReal_abs_heatF_sub_leD hw hT hab u) _).trans (le_of_eq ?_)
    rw [Finset.mul_sum, ← hprod]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [hκ, hB]
    rw [← mul_assoc]
    exact hterm _ _ _
  have hf2 : ∀ u p, (ENNReal.ofReal |G u| * κ u p ^ (1 / 2 : ℝ)) ^ (2 : ℝ) =
      ENNReal.ofReal (G u ^ 2) * κ u p := by
    intro u p
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), hsq, ENNReal.ofReal_rpow_of_nonneg
      (abs_nonneg _) (by norm_num)]
    congr 2
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  have hg2 : ∀ u p, (κ u p ^ (1 / 2 : ℝ) * B p) ^ (2 : ℝ) =
      κ u p * ENNReal.ofReal ((w (p.2 + unit p.1) - w p.2) ^ 2) := by
    intro u p
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), hsq]
    simp only [hB]
    rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num),
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  have hCS := tsum_sum_mul_leD P (fun u p => ENNReal.ofReal |G u| * κ u p ^ (1 / 2 : ℝ))
    (fun u p => κ u p ^ (1 / 2 : ℝ) * B p)
  simp only [hf2, hg2] at hCS
  have h1 : ∑' u, ∑ p ∈ P, ENNReal.ofReal (G u ^ 2) * κ u p =
      ∑' u, ENNReal.ofReal (G u ^ 2) * ∑ j : Fin d, ∑ x ∈ T, heatGradKernelD j a b (x - u) := by
    refine tsum_congr fun u => ?_
    rw [← Finset.mul_sum]
    congr 1
    exact (hprod (fun p => κ u p)).symm
  have h2 : ∑' u, ∑ p ∈ P, κ u p * ENNReal.ofReal ((w (p.2 + unit p.1) - w p.2) ^ 2) ≤
      K * ∑ j : Fin d, ∑ x ∈ T, ENNReal.ofReal ((w (x + unit j) - w x) ^ 2) := by
    rw [Summable.tsum_finsetSum fun _ _ => ENNReal.summable, ← hprod, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    simp only [hκ]
    rw [ENNReal.tsum_mul_right]
    refine mul_le_mul_left ?_ _
    rw [show (∑' u, heatGradKernelD j a b (x - u)) = ∑' v, heatGradKernelD j a b v from
      (Equiv.subLeft x).tsum_eq (fun v => heatGradKernelD j a b v)]
    exact hK j
  rw [h1] at hCS
  calc ENNReal.ofReal |∑' u, G u * (heatF S w b u - heatF S w a u)|
      ≤ ∑' u, ENNReal.ofReal |G u * (heatF S w b u - heatF S w a u)| :=
        Rigidity.Corrector.ofReal_abs_tsum_le _
    _ ≤ ∑' u, ∑ p ∈ P, (ENNReal.ofReal |G u| * κ u p ^ (1 / 2 : ℝ)) *
          (κ u p ^ (1 / 2 : ℝ) * B p) := ENNReal.tsum_le_tsum hpt
    _ ≤ _ := hCS
    _ ≤ _ := mul_le_mul_right (ENNReal.rpow_le_rpow h2 (by norm_num)) _

end Rigidity.Green.GeneralFlux
