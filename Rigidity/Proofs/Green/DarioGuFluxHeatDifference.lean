import Rigidity.Proofs.Green.DarioGuFluxKernelGradient
import Rigidity.Proofs.Green.DarioGuFluxHeat
import Rigidity.Proofs.Poincare.LatticeHeatFlow

/-!
# Increments in time of the heat flow and the duality with heat averages on `ℤ²`

Deterministic ingredients of the estimate (B.4) of Dario–Gu, Appendix B, in the lattice
form used here (dyadic heat times instead of the continuous multiscale Poincaré inequality (D.28)
of Armstrong, Kuusi and Mourrat):

* `lap_heatF_eq`: for `w` vanishing off a finite set, the Laplacian of its heat flow is
  `-Σ_j Σ_x ∇_j Φ_t(u, ·)(x) ∇_j w(x)` (summation by parts);
* `ofReal_abs_heatF_sub_le`: by the heat equation,
  `|Φ_b w(u) - Φ_a w(u)| ≤ Σ_j Σ_{x ∈ T} κ_j(a, b, x - u) |∇_j w(x)|` with the time-integrated
  kernel `κ = heatGradKernel` of `DarioGuFluxKernelGradient`;
* `heatAvg t f x = Σ_z Φ_t(x, z) f(z)` for `f` summable against every heat kernel
  (`HeatSummableAll`, for instance of linear growth), the semigroup property
  `hasSum_heatAvg_semigroup` and the duality
  `Σ_{x ∈ S} (Φ_{b+c} f - Φ_{a+c} f)(x) w(x) = Σ_u Φ_c f(u) (Φ_b w - Φ_a w)(u)`
  (`sum_heatAvg_sub_mul_eq`);
* `ofReal_abs_tsum_mul_heatF_sub_le`: the Cauchy–Schwarz bound of the right side by
  `(Σ_u (Φ_c f)(u)² m(u))^{1/2} (K Σ_j Σ_{x ∈ T} |∇_j w(x)|²)^{1/2}`,
  `m(u) = Σ_j Σ_{x ∈ T} κ_j(a, b, x - u)`, `K` a bound of the mass of `κ`.
-/

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.Poincare
open scoped ENNReal Classical

namespace Rigidity.Green

theorem ofReal_abs_finset_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ENNReal.ofReal |∑ i ∈ s, f i| ≤ ∑ i ∈ s, ENNReal.ofReal |f i| := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (Finset.abs_sum_le_sum_abs _ _)

/-! ### The heat flow of a finitely supported function -/

theorem heatF_eq_tsum {S : Finset (Vertex 2)} {w : Vertex 2 → ℝ} (hw : ∀ y ∉ S, w y = 0)
    (t : ℝ) (u : Vertex 2) :
    heatF S w t u = ∑' y, openHeat (allOpen 2) t u y * w y := by
  rw [tsum_eq_sum (s := S) (fun y hy => by rw [hw y hy, mul_zero])]
  rfl

theorem summable_mul_of_eq_zero_off {S : Finset (Vertex 2)} {w : Vertex 2 → ℝ}
    (hw : ∀ y ∉ S, w y = 0) (Φ : Vertex 2 → ℝ) (e : Vertex 2) :
    Summable fun x => Φ x * w (x + e) := by
  refine summable_of_ne_finset_zero (s := S.image fun y => y - e) fun x hx => ?_
  have : x + e ∉ S := fun h => hx (Finset.mem_image.2 ⟨x + e, h, add_sub_cancel_right x e⟩)
  rw [hw _ this, mul_zero]

/-- **Summation by parts for the Laplacian of the heat flow.** -/
theorem lap_heatF_eq {S : Finset (Vertex 2)} {w : Vertex 2 → ℝ} (hw : ∀ y ∉ S, w y = 0)
    (t : ℝ) (u : Vertex 2) :
    lap (heatF S w t) u = -∑ j : Fin 2, ∑' x,
      (openHeat (allOpen 2) t u (x + unit j) - openHeat (allOpen 2) t u x) *
        (w (x + unit j) - w x) := by
  set Φ : Vertex 2 → ℝ := fun y => openHeat (allOpen 2) t u y with hΦ
  set F := heatF S w t with hF
  have hplus : ∀ e : Vertex 2, HasSum (fun x => Φ x * w (x + e)) (F (u + e)) := by
    intro e
    have h1 : F (u + e) = ∑' y, Φ (y - e) * w y := by
      rw [hF, heatF_eq_tsum hw]
      refine tsum_congr fun y => ?_
      simp only [hΦ]
      rw [← openHeat_allOpen_sub t (u + e) y e, add_sub_cancel_right]
    have h2 : ∑' y, Φ (y - e) * w y = ∑' x, Φ x * w (x + e) := by
      rw [← (Equiv.addRight e).tsum_eq]
      simp only [Equiv.coe_addRight, add_sub_cancel_right]
    rw [h1, h2]
    exact (summable_mul_of_eq_zero_off hw Φ e).hasSum
  have hminus : ∀ e : Vertex 2, HasSum (fun x => Φ (x + e) * w x) (F (u - e)) := by
    intro e
    have h1 : F (u - e) = ∑' x, Φ (x + e) * w x := by
      rw [hF, heatF_eq_tsum hw]
      refine tsum_congr fun y => ?_
      simp only [hΦ]
      rw [← openHeat_allOpen_add t (u - e) y e, sub_add_cancel]
    rw [h1]
    refine Summable.hasSum ?_
    have := summable_mul_of_eq_zero_off hw (fun x => Φ (x + e)) 0
    simpa only [add_zero] using this
  have hzero : HasSum (fun x => Φ x * w x) (F u) := by
    have := hplus 0
    simpa only [add_zero] using this
  have hshift : ∀ e : Vertex 2, HasSum (fun x => Φ (x + e) * w (x + e)) (F u) := by
    intro e
    have h := hzero
    rw [← (Equiv.addRight e).hasSum_iff] at h
    exact h
  have hj : ∀ e : Vertex 2, ∑' x, (Φ (x + e) - Φ x) * (w (x + e) - w x) =
      2 * F u - F (u + e) - F (u - e) := by
    intro e
    have h := (((hshift e).sub (hminus e)).sub (hplus e)).add hzero
    have hv : 2 * F u - F (u + e) - F (u - e) = F u - F (u - e) - F (u + e) + F u := by ring
    rw [hv, ← h.tsum_eq]
    refine tsum_congr fun x => ?_
    ring
  have e2 : ∑' x, (Φ (x + unit 0) - Φ x) * (w (x + unit 0) - w x) +
      ∑' x, (Φ (x + unit 1) - Φ x) * (w (x + unit 1) - w x) =
      4 * F u - (F (u + unit 0) + F (u - unit 0)) - (F (u + unit 1) + F (u - unit 1)) := by
    rw [hj, hj]
    ring
  rw [Fin.sum_univ_two, e2]
  simp only [lap, Fin.sum_univ_two]
  ring

/-- **The time increments of the heat flow**, through the gradient of the test function. -/
theorem ofReal_abs_heatF_sub_le {S T : Finset (Vertex 2)} {w : Vertex 2 → ℝ}
    (hw : ∀ y ∉ S, w y = 0) (hT : ∀ x ∉ T, ∀ j : Fin 2, w (x + unit j) = w x) {a b : ℝ}
    (hab : a ≤ b) (u : Vertex 2) :
    ENNReal.ofReal |heatF S w b u - heatF S w a u| ≤
      ∑ j : Fin 2, ∑ x ∈ T, heatGradKernel j a b (x - u) * ENNReal.ofReal |w (x + unit j) - w x| := by
  set D : ℝ → ℝ := fun t => lap (heatF S w t) u with hD
  have hcont : Continuous D := by
    simp only [hD, lap]
    exact (continuous_finsetSum _ fun i _ =>
      (continuous_heatF S w _).add (continuous_heatF S w _)).sub
      (continuous_const.mul (continuous_heatF S w u))
  have hFTC : heatF S w b u - heatF S w a u = ∫ t in a..b, D t :=
    (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_heatF S w t u)
      (hcont.intervalIntegrable a b)).symm
  set A : Fin 2 → Vertex 2 → ℝ → ℝ := fun j x t =>
    openHeat (allOpen 2) t 0 (x - u + unit j) - openHeat (allOpen 2) t 0 (x - u) with hA
  have hDfin : ∀ t, D t = -∑ j : Fin 2, ∑ x ∈ T, A j x t * (w (x + unit j) - w x) := by
    intro t
    simp only [hD]
    rw [lap_heatF_eq hw]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [tsum_eq_sum (s := T) (fun x hx => by rw [hT x hx j, sub_self, mul_zero])]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [hA]
    rw [← openHeat_allOpen_sub t u (x + unit j) u, ← openHeat_allOpen_sub t u x u, sub_self,
      add_sub_right_comm]
  have hAm : ∀ j x, Measurable fun t => ENNReal.ofReal |A j x t| := fun j x =>
    ENNReal.measurable_ofReal.comp
      (((continuous_openHeat _ 0 _).sub (continuous_openHeat _ 0 _)).abs.measurable)
  rw [hFTC, intervalIntegral.integral_of_le hab]
  calc ENNReal.ofReal |∫ t in Set.Ioc a b, D t| = ‖∫ t in Set.Ioc a b, D t‖ₑ :=
        (Real.enorm_eq_ofReal_abs _).symm
    _ ≤ ∫⁻ t in Set.Ioc a b, ‖D t‖ₑ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ t in Set.Ioc a b, ∑ j : Fin 2, ∑ x ∈ T,
          ENNReal.ofReal |A j x t| * ENNReal.ofReal |w (x + unit j) - w x| := by
        refine lintegral_mono fun t => ?_
        rw [Real.enorm_eq_ofReal_abs, hDfin t, abs_neg]
        refine (ofReal_abs_finset_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        refine (ofReal_abs_finset_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
        rw [abs_mul, ENNReal.ofReal_mul (abs_nonneg _)]
    _ = ∑ j : Fin 2, ∑ x ∈ T, heatGradKernel j a b (x - u) *
          ENNReal.ofReal |w (x + unit j) - w x| := by
        rw [lintegral_finsetSum _ fun j _ => Finset.measurable_sum _ fun x _ =>
          (hAm j x).mul_const _]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [lintegral_finsetSum _ fun x _ => (hAm j x).mul_const _]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [lintegral_mul_const _ (hAm j x)]
        rfl

/-! ### Heat averages of functions on `ℤ²` -/

/-- `f` is summable against every heat kernel. -/
def HeatSummableAll (f : Vertex 2 → ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → ∀ x : Vertex 2, Summable fun z => openHeat (allOpen 2) t x z * |f z|

/-- The heat average `Φ_t f(x) = Σ_z Φ_t(x, z) f(z)`. -/
noncomputable def heatAvg (t : ℝ) (f : Vertex 2 → ℝ) (x : Vertex 2) : ℝ :=
  ∑' z, openHeat (allOpen 2) t x z * f z

theorem HeatSummableAll.summable {f : Vertex 2 → ℝ} (hf : HeatSummableAll f) {t : ℝ}
    (ht : 0 ≤ t) (x : Vertex 2) : Summable fun z => openHeat (allOpen 2) t x z * f z := by
  refine Summable.of_norm ((hf t ht x).congr fun z => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (openHeat_nonneg _ ht x z)]

theorem heatAvg_zero (f : Vertex 2 → ℝ) (x : Vertex 2) : heatAvg 0 f x = f x := by
  unfold heatAvg
  simp only [openHeat_zero, ite_mul, one_mul, zero_mul]
  rw [tsum_eq_single x (fun z hz => if_neg (Ne.symm hz)), if_pos rfl]

/-- **The semigroup property** `Φ_{s+t} f(x) = Σ_u Φ_s(x, u) Φ_t f(u)`. -/
theorem hasSum_heatAvg_semigroup {f : Vertex 2 → ℝ} (hf : HeatSummableAll f) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (x : Vertex 2) :
    HasSum (fun u => openHeat (allOpen 2) s x u * heatAvg t f u) (heatAvg (s + t) f x) := by
  set F : Vertex 2 → Vertex 2 → ℝ := fun u z =>
    openHeat (allOpen 2) s x u * (openHeat (allOpen 2) t u z * f z) with hF
  have hfib : ∀ z, HasSum (fun u => |F u z|) (openHeat (allOpen 2) (s + t) x z * |f z|) := by
    intro z
    have h := (hasSum_openHeat_mul (allOpen 2) hs ht x z).mul_right |f z|
    refine h.congr_fun fun u => ?_
    simp only [hF]
    rw [abs_mul, abs_mul, abs_of_nonneg (openHeat_nonneg _ hs x u),
      abs_of_nonneg (openHeat_nonneg _ ht u z)]
    ring
  have hsum : Summable (Function.uncurry fun z u => F u z) := by
    refine Summable.of_abs ?_
    have h0 : 0 ≤ fun q : Vertex 2 × Vertex 2 => |F q.2 q.1| := fun q => abs_nonneg _
    have : Summable fun q : Vertex 2 × Vertex 2 => |F q.2 q.1| := by
      rw [summable_prod_of_nonneg h0]
      exact ⟨fun z => (hfib z).summable, ((hf (s + t) (by linarith) x).congr
        fun z => ((hfib z).tsum_eq).symm)⟩
    exact this
  have hsum' : Summable (Function.uncurry F) :=
    (Equiv.prodComm (Vertex 2) (Vertex 2)).summable_iff.2 hsum
  have hcomm := hsum'.tsum_comm
  have hval : ∑' u, openHeat (allOpen 2) s x u * heatAvg t f u = heatAvg (s + t) f x := by
    unfold heatAvg
    calc ∑' u, openHeat (allOpen 2) s x u * ∑' z, openHeat (allOpen 2) t u z * f z
        = ∑' u, ∑' z, F u z := tsum_congr fun u => tsum_mul_left.symm
      _ = ∑' z, ∑' u, F u z := hcomm.symm
      _ = ∑' z, openHeat (allOpen 2) (s + t) x z * f z := by
          refine tsum_congr fun z => ?_
          have h := (hasSum_openHeat_mul (allOpen 2) hs ht x z).mul_right (f z)
          rw [← h.tsum_eq]
          exact tsum_congr fun u => by simp only [hF]; ring
  have hsu : Summable fun u => openHeat (allOpen 2) s x u * heatAvg t f u := by
    refine hsum'.prod.congr fun u => ?_
    unfold heatAvg
    show ∑' z, openHeat (allOpen 2) s x u * (openHeat (allOpen 2) t u z * f z) = _
    exact tsum_mul_left
  rw [← hval]
  exact hsu.hasSum

/-- **Duality between heat averages and the heat flow of a test function.** -/
theorem sum_heatAvg_sub_mul_eq {f : Vertex 2 → ℝ} (hf : HeatSummableAll f)
    (S : Finset (Vertex 2)) (w : Vertex 2 → ℝ) {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) :
    ∑ x ∈ S, (heatAvg (b + c) f x - heatAvg (a + c) f x) * w x =
      ∑' u, heatAvg c f u * (heatF S w b u - heatF S w a u) := by
  set G := heatAvg c f
  have hb' := fun x => hasSum_heatAvg_semigroup hf hb hc x
  have ha' := fun x => hasSum_heatAvg_semigroup hf ha hc x
  have hterm : ∀ x ∈ S, (heatAvg (b + c) f x - heatAvg (a + c) f x) * w x =
      ∑' u, (openHeat (allOpen 2) b x u - openHeat (allOpen 2) a x u) * G u * w x := by
    intro x _
    rw [← (hb' x).tsum_eq, ← (ha' x).tsum_eq, ← ((hb' x).summable.tsum_sub (ha' x).summable),
      ← tsum_mul_right]
    exact tsum_congr fun u => by ring
  have hsumm : ∀ x ∈ S, Summable fun u =>
      (openHeat (allOpen 2) b x u - openHeat (allOpen 2) a x u) * G u * w x := by
    intro x _
    refine (((hb' x).summable.sub (ha' x).summable).mul_right (w x)).congr fun u => ?_
    ring
  rw [Finset.sum_congr rfl hterm, ← Summable.tsum_finsetSum hsumm]
  refine tsum_congr fun u => ?_
  unfold heatF
  rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [openHeat_symm _ b x u, openHeat_symm _ a x u]
  ring

/-- Functions of linear growth are summable against every heat kernel. -/
theorem heatSummableAll_of_abs_le {f : Vertex 2 → ℝ} {A : ℝ}
    (hf : ∀ z, |f z| ≤ A * (1 + ‖latticeEuclideanEmbedding z‖)) : HeatSummableAll f := by
  intro t ht x
  rcases ht.lt_or_eq with ht0 | rfl
  · have h := summable_latticeHeat_mul_of_abs_le (Real.sqrt_pos.2 ht0) x
      (f := fun z => |f z|) (A := A) (fun z => by rw [abs_abs]; exact hf z)
    rw [Real.sq_sqrt ht0.le] at h
    exact h
  · refine summable_of_ne_finset_zero (s := {x}) fun z hz => ?_
    rw [Finset.mem_singleton] at hz
    rw [openHeat_zero, if_neg (Ne.symm hz), zero_mul]

/-! ### The Cauchy–Schwarz bound -/

/-- Cauchy–Schwarz for a countable sum of finite sums. -/
theorem tsum_sum_mul_le {ι : Type*} (P : Finset ι) (f g : Vertex 2 → ι → ℝ≥0∞) :
    ∑' u, ∑ p ∈ P, f u p * g u p ≤
      (∑' u, ∑ p ∈ P, f u p ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
        (∑' u, ∑ p ∈ P, g u p ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  set α : Vertex 2 → ℝ≥0∞ := fun u => (∑ p ∈ P, f u p ^ (2 : ℝ)) ^ (1 / 2 : ℝ) with hα
  set β : Vertex 2 → ℝ≥0∞ := fun u => (∑ p ∈ P, g u p ^ (2 : ℝ)) ^ (1 / 2 : ℝ) with hβ
  have hinner : ∀ u, ∑ p ∈ P, f u p * g u p ≤ α u * β u := fun u =>
    ENNReal.inner_le_Lp_mul_Lq P (f u) (g u) Real.HolderConjugate.two_two
  have hsq : ∀ x : ℝ≥0∞, (x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = x := fun x => by
    rw [← ENNReal.rpow_mul]
    norm_num
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (Measure.count (α := Vertex 2))
    Real.HolderConjugate.two_two (f := α) (g := β) (Measurable.of_discrete).aemeasurable
    (Measurable.of_discrete).aemeasurable
  simp only [lintegral_count, Pi.mul_apply, hα, hβ, hsq] at h
  exact (ENNReal.tsum_le_tsum hinner).trans h

/-- **The bound of the duality term.** -/
theorem ofReal_abs_tsum_mul_heatF_sub_le (G : Vertex 2 → ℝ) {S T : Finset (Vertex 2)}
    {w : Vertex 2 → ℝ} (hw : ∀ y ∉ S, w y = 0)
    (hT : ∀ x ∉ T, ∀ j : Fin 2, w (x + unit j) = w x) {a b : ℝ} (hab : a ≤ b) {K : ℝ≥0∞}
    (hK : ∀ j : Fin 2, ∑' v, heatGradKernel j a b v ≤ K) :
    ENNReal.ofReal |∑' u, G u * (heatF S w b u - heatF S w a u)| ≤
      (∑' u, ENNReal.ofReal (G u ^ 2) *
          ∑ j : Fin 2, ∑ x ∈ T, heatGradKernel j a b (x - u)) ^ (1 / 2 : ℝ) *
        (K * ∑ j : Fin 2, ∑ x ∈ T, ENNReal.ofReal ((w (x + unit j) - w x) ^ 2)) ^ (1 / 2 : ℝ) := by
  set P : Finset (Fin 2 × Vertex 2) := Finset.univ ×ˢ T with hP
  set κ : Vertex 2 → Fin 2 × Vertex 2 → ℝ≥0∞ := fun u p => heatGradKernel p.1 a b (p.2 - u)
    with hκ
  set B : Fin 2 × Vertex 2 → ℝ≥0∞ := fun p => ENNReal.ofReal |w (p.2 + unit p.1) - w p.2| with hB
  have hsqrt : ∀ x : ℝ≥0∞, x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x := fun x => by
    rw [← ENNReal.rpow_add_of_nonneg (x := x) (1 / 2 : ℝ) (1 / 2 : ℝ) (by norm_num) (by norm_num)]
    norm_num
  have hsq : ∀ x : ℝ≥0∞, (x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = x := fun x => by
    rw [← ENNReal.rpow_mul]
    norm_num
  have hprod : ∀ (F : Fin 2 × Vertex 2 → ℝ≥0∞),
      ∑ j : Fin 2, ∑ x ∈ T, F (j, x) = ∑ p ∈ P, F p := fun F => by
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
    refine (mul_le_mul_right (ofReal_abs_heatF_sub_le hw hT hab u) _).trans (le_of_eq ?_)
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
  have hCS := tsum_sum_mul_le P (fun u p => ENNReal.ofReal |G u| * κ u p ^ (1 / 2 : ℝ))
    (fun u p => κ u p ^ (1 / 2 : ℝ) * B p)
  simp only [hf2, hg2] at hCS
  have h1 : ∑' u, ∑ p ∈ P, ENNReal.ofReal (G u ^ 2) * κ u p =
      ∑' u, ENNReal.ofReal (G u ^ 2) * ∑ j : Fin 2, ∑ x ∈ T, heatGradKernel j a b (x - u) := by
    refine tsum_congr fun u => ?_
    rw [← Finset.mul_sum]
    congr 1
    exact (hprod (fun p => κ u p)).symm
  have h2 : ∑' u, ∑ p ∈ P, κ u p * ENNReal.ofReal ((w (p.2 + unit p.1) - w p.2) ^ 2) ≤
      K * ∑ j : Fin 2, ∑ x ∈ T, ENNReal.ofReal ((w (x + unit j) - w x) ^ 2) := by
    rw [Summable.tsum_finsetSum fun _ _ => ENNReal.summable, ← hprod, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    simp only [hκ]
    rw [ENNReal.tsum_mul_right]
    refine mul_le_mul_left ?_ _
    rw [show (∑' u, heatGradKernel j a b (x - u)) = ∑' v, heatGradKernel j a b v from
      (Equiv.subLeft x).tsum_eq (fun v => heatGradKernel j a b v)]
    exact hK j
  rw [h1] at hCS
  calc ENNReal.ofReal |∑' u, G u * (heatF S w b u - heatF S w a u)|
      ≤ ∑' u, ENNReal.ofReal |G u * (heatF S w b u - heatF S w a u)| :=
        Rigidity.Corrector.ofReal_abs_tsum_le _
    _ ≤ ∑' u, ∑ p ∈ P, (ENNReal.ofReal |G u| * κ u p ^ (1 / 2 : ℝ)) *
          (κ u p ^ (1 / 2 : ℝ) * B p) := ENNReal.tsum_le_tsum hpt
    _ ≤ _ := hCS
    _ ≤ _ := mul_le_mul_right (ENNReal.rpow_le_rpow h2 (by norm_num)) _

end Rigidity.Green
