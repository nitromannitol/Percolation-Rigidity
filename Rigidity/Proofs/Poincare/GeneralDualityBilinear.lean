import Rigidity.Proofs.Poincare.DualityBilinear
import Rigidity.Proofs.Poincare.GeneralSteinSigned
import Rigidity.Proofs.Poincare.GeneralBoxField

/-!
# The bilinear term of the duality identity on `ℤ^d`

The extension of `DualityBilinear.lean` from `ℤ²` to `ℤ^d`, `d ≥ 1`.

The main term of the duality identity of `HeatDuality.lean`,
`∫_0^{2T} Σ_i Σ_y ∇_i g(y) A_i(t, y) dt`, is bounded, as in (D.23) of Armstrong, Kuusi and
Mourrat, by the semigroup property `A_i(t) = Φ_{t/2} * A_i(t/2)`, the substitution `t = 2s`, the
Cauchy-Schwarz inequality in time, and the substitution `s = r²`:

  `|∫_0^{2T} …| ≤ 2 Σ_x Γ_g(x)^{1/2} (2 Sq(x))^{1/2}`

(`ofReal_abs_integral_le`), with `Γ_g(x) = ∫_0^T Σ_i (∇_i Φ_s g(x))² ds` the square function of
`SteinSigned.lean` and `Sq(x) = ∫_0^{√T} r |Φ_{r²} * ∇u(x)|² dr`, the quantity of Dario's (2.26)
(`hgrad` is the `ℓ¹` norm of the `d` components, as in `heatGradient`).
-/

open scoped Classical
open LatticeProb LatticeProb.Percolation Rigidity.Green MeasureTheory

namespace Rigidity.Poincare.GeneralDim

variable {d : ℕ} {u : Vertex d → ℝ}

/-- `|Φ_{r²} * ∇u(x)| = Σ_j |A_j(r², x)|`. -/
noncomputable def hgrad (u : Vertex d → ℝ) (r : ℝ) (x : Vertex d) : ℝ :=
  ∑ j : Fin d, |heatGrad u j (r ^ 2) x|

/-- `∫_0^L r |Φ_{r²} * ∇u(x)|² dr`. -/
noncomputable def sqInt (u : Vertex d → ℝ) (L : ℝ) (x : Vertex d) : ENNReal :=
  ∫⁻ r in Set.Ioc 0 L, ENNReal.ofReal (r * hgrad u r x ^ 2)

theorem zdHeat_symm [NeZero d] (t : ℝ) (x y : Vertex d) : zdHeat d t x y = zdHeat d t y x :=
  vsrwHeat_symm two_mul_pos_of_neZero (openGraph_degree_le (allOpen d)) t x y

/-- `Σ_i a_i² ≤ (Σ_i |a_i|)²`. -/
theorem sum_sq_le_sq_sum_abs (a : Fin d → ℝ) : ∑ i, a i ^ 2 ≤ (∑ i, |a i|) ^ 2 := by
  rw [sq, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← sq_abs, sq]
  exact mul_le_mul_of_nonneg_left (Finset.single_le_sum (f := fun j => |a j|)
    (fun j _ => abs_nonneg _) (Finset.mem_univ i)) (abs_nonneg _)

theorem ofReal_abs_tsum_le' {ι : Type*} (f : ι → ℝ) :
    ENNReal.ofReal |∑' i, f i| ≤ ∑' i, ENNReal.ofReal |f i| := by
  by_cases hs : Summable f
  · rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => abs_nonneg _) hs.abs]
    exact ENNReal.ofReal_le_ofReal (norm_tsum_le_tsum_norm hs.norm)
  · rw [tsum_eq_zero_of_not_summable hs, abs_zero, ENNReal.ofReal_zero]
    positivity

theorem summable_uncurry_heat [NeZero d] (hu : HeatSummable u) (j : Fin d) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (y : Vertex d) :
    Summable (Function.uncurry fun w z => zdHeat d (t - s) y w *
      (zdHeat d s w z * fd u j z)) := by
  have hts : 0 ≤ t - s := by linarith
  set F : Vertex d → Vertex d → ℝ := fun w z =>
    zdHeat d (t - s) y w * (zdHeat d s w z * fd u j z) with hF
  have hfib : ∀ z, HasSum (fun w => |F w z|)
      (zdHeat d t y z * |fd u j z|) := by
    intro z
    have h := (hasSum_zdHeat_mul hts hs y z).mul_right |fd u j z|
    rw [sub_add_cancel] at h
    refine h.congr_fun fun w => ?_
    simp only [hF]
    rw [abs_mul, abs_mul, abs_of_nonneg (zdHeat_nonneg hts y w),
      abs_of_nonneg (zdHeat_nonneg hs w z)]
    ring
  have h0 : 0 ≤ fun q : Vertex d × Vertex d => |F q.2 q.1| := fun q => abs_nonneg _
  have habs : Summable fun q : Vertex d × Vertex d => |F q.2 q.1| := by
    rw [summable_prod_of_nonneg h0]
    exact ⟨fun z => (hfib z).summable, ((summable_heat_abs_fd hu j (by linarith) y).congr
      fun z => ((hfib z).tsum_eq).symm)⟩
  have := (Equiv.prodComm (Vertex d) (Vertex d)).summable_iff.2 (Summable.of_abs habs)
  exact this

/-- `w ↦ Φ_{t-s}(y, w) A_j(s, w)` is summable. -/
theorem summable_heat_mul_heatGrad [NeZero d] (hu : HeatSummable u) (j : Fin d) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (y : Vertex d) :
    Summable fun w => zdHeat d (t - s) y w * heatGrad u j s w := by
  have h := (summable_uncurry_heat hu j hs hst y).prod
  refine h.congr fun w => ?_
  simp only [Function.uncurry_apply_pair, heatGrad]
  exact tsum_mul_left

/-- **The semigroup split of the bilinear integrand**:
`Σ_y ∇_i g(y) A_i(t, y) = Σ_w ∇_i (Φ_{t/2} g)(w) A_i(t/2, w)`. -/
theorem tsum_fd_mul_heatGrad_eq [NeZero d] (hu : HeatSummable u) {S : Finset (Vertex d)}
    {g : Vertex d → ℝ} (hgS : ∀ y ∉ S, g y = 0) (i : Fin d) {t : ℝ} (ht : 0 ≤ t) :
    ∑' y, (g (y + unit i) - g y) * heatGrad u i t y =
      ∑' w, (heatF S g (t / 2) (w + unit i) - heatF S g (t / 2) w) *
        heatGrad u i (t / 2) w := by
  have ht2 : 0 ≤ t / 2 := by linarith
  have hst : t / 2 ≤ t := by linarith
  have htt : t - t / 2 = t / 2 := by ring
  set S₁ := S ∪ S.image (· - unit i) with hS₁
  have hD : ∀ y ∉ S₁, g (y + unit i) - g y = 0 := by
    intro y hy
    rw [hS₁, Finset.mem_union, not_or] at hy
    rw [supp_shift hgS (unit i) y hy.2, hgS y hy.1, sub_zero]
  have hsplit : ∀ y, heatGrad u i t y =
      ∑' w, zdHeat d (t / 2) y w * heatGrad u i (t / 2) w := by
    intro y
    rw [heatGrad_eq_tsum hu i ht2 hst y, htt]
  have hsw : ∀ y, Summable fun w =>
      zdHeat d (t / 2) y w * heatGrad u i (t / 2) w := by
    intro y
    have := summable_heat_mul_heatGrad hu i ht2 hst y
    rwa [htt] at this
  have hfin : ∑' y, (g (y + unit i) - g y) * heatGrad u i t y =
      ∑ y ∈ S₁, (g (y + unit i) - g y) * heatGrad u i t y :=
    tsum_eq_sum fun y hy => by rw [hD y hy, zero_mul]
  have hswap : ∑ y ∈ S₁, (g (y + unit i) - g y) * heatGrad u i t y =
      ∑' w, ∑ y ∈ S₁, (g (y + unit i) - g y) *
        (zdHeat d (t / 2) y w * heatGrad u i (t / 2) w) := by
    rw [Summable.tsum_finsetSum fun y _ => (hsw y).mul_left (g (y + unit i) - g y)]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hsplit, ← tsum_mul_left]
  rw [hfin, hswap]
  refine tsum_congr fun w => ?_
  have e0 : ∑ y ∈ S₁, (g (y + unit i) - g y) *
      (zdHeat d (t / 2) y w * heatGrad u i (t / 2) w) =
      (∑ y ∈ S₁, (g (y + unit i) - g y) * zdHeat d (t / 2) y w) *
        heatGrad u i (t / 2) w := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [e0]
  congr 1
  -- `Σ_y ∇_i g(y) Φ_{t/2}(y, w) = ∇_i (Φ_{t/2} g)(w)`
  have h1 : ∑ y ∈ S₁, (g (y + unit i) - g y) * zdHeat d (t / 2) y w =
      ∑' y, (g (y + unit i) - g y) * zdHeat d (t / 2) y w :=
    (tsum_eq_sum fun y hy => by rw [hD y hy, zero_mul]).symm
  have hs1 := summable_mul_of_supp (supp_shift hgS (unit i))
    (fun y => zdHeat d (t / 2) y w)
  have hs2 := summable_mul_of_supp hgS (fun y => zdHeat d (t / 2) y w)
  have hΦ : ∀ y, zdHeat d (t / 2) (y - unit i) w =
      zdHeat d (t / 2) (w + unit i) y := by
    intro y
    rw [← zdHeat_add (t / 2) (y - unit i) w (unit i), sub_add_cancel, zdHeat_symm]
  have e1 : ∑' y, g (y + unit i) * zdHeat d (t / 2) y w =
      ∑' y, g y * zdHeat d (t / 2) (w + unit i) y := by
    rw [← tsum_mul_sub_eq g (fun y => zdHeat d (t / 2) y w) (unit i)]
    exact tsum_congr fun y => by rw [hΦ]
  have hheat : ∀ x, heatF S g (t / 2) x = ∑' y, g y * zdHeat d (t / 2) x y := by
    intro x
    unfold heatF
    have : ∑' y, g y * zdHeat d (t / 2) x y =
        ∑ y ∈ S, g y * zdHeat d (t / 2) x y :=
      tsum_eq_sum fun y hy => by rw [hgS y hy, zero_mul]
    rw [this]
    exact Finset.sum_congr rfl fun y _ => mul_comm _ _
  have e2 : ∑' y, g y * zdHeat d (t / 2) y w =
      ∑' y, g y * zdHeat d (t / 2) w y :=
    tsum_congr fun y => by rw [zdHeat_symm]
  rw [h1]
  simp only [sub_mul]
  rw [hs1.tsum_sub hs2, e1, e2, hheat, hheat]

theorem sq_image_Ioc {L : ℝ} (hL : 0 ≤ L) :
    (fun r : ℝ => r ^ 2) '' Set.Ioc 0 L = Set.Ioc 0 (L ^ 2) := by
  ext s
  simp only [Set.mem_image, Set.mem_Ioc]
  constructor
  · rintro ⟨r, ⟨hr0, hrL⟩, rfl⟩
    exact ⟨by positivity, pow_le_pow_left₀ hr0.le hrL 2⟩
  · rintro ⟨hs0, hsL⟩
    refine ⟨Real.sqrt s, ⟨Real.sqrt_pos.2 hs0, ?_⟩, Real.sq_sqrt hs0.le⟩
    rw [← Real.sqrt_sq hL]
    exact Real.sqrt_le_sqrt hsL

/-- **The substitution `s = r²`**: `∫_0^{L²} Σ_i A_i(s, x)² ds ≤ 2 ∫_0^L r |Φ_{r²} * ∇u(x)|² dr`. -/
theorem lintegral_sum_sq_heatGrad_le (u : Vertex d → ℝ) {L : ℝ} (hL : 0 ≤ L) (x : Vertex d) :
    ∫⁻ s in Set.Ioc 0 (L ^ 2), ENNReal.ofReal (∑ i : Fin d, heatGrad u i s x ^ 2) ≤
      2 * sqInt u L x := by
  rw [← sq_image_Ioc hL, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioc
    (f' := fun r => 2 * r) (fun r _ => by
      have := (hasDerivAt_pow 2 r).hasDerivWithinAt (s := Set.Ioc 0 L)
      simpa using this)
    (fun a ha b hb hab => by
      have := (pow_left_inj₀ (le_of_lt ha.1) (le_of_lt hb.1) (by norm_num : 2 ≠ 0)).1 hab
      exact this)]
  rw [sqInt, ← lintegral_const_mul' 2 _ ENNReal.ofNat_ne_top]
  refine setLIntegral_mono' measurableSet_Ioc fun r hr => ?_
  rw [abs_of_nonneg (by linarith [hr.1]), ← ENNReal.ofReal_mul (by linarith [hr.1]),
    ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hr0 : 0 ≤ r := hr.1.le
  have h : ∑ i : Fin d, heatGrad u i (r ^ 2) x ^ 2 ≤ hgrad u r x ^ 2 := by
    simp only [hgrad]
    exact sum_sq_le_sq_sum_abs _
  nlinarith

theorem sum_abs_mul_le_sqrt (a b : Fin d → ℝ) :
    ∑ i : Fin d, |a i| * |b i| ≤
      Real.sqrt (∑ i : Fin d, a i ^ 2) * Real.sqrt (∑ i : Fin d, b i ^ 2) := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => |a i|) (fun i => |b i|)
  simpa only [sq_abs] using h

/-- **The bilinear term**:
`|∫_0^{2T} Σ_i Σ_y ∇_i g A_i dt| ≤ 2 Σ_x Γ_g(x)^{1/2} (2 Sq(x))^{1/2}`. -/
theorem ofReal_abs_integral_le [NeZero d] (hu : HeatSummable u) {S : Finset (Vertex d)}
    {g : Vertex d → ℝ} (hgS : ∀ y ∉ S, g y = 0) {T : ℝ} (hT : 0 ≤ T) :
    ENNReal.ofReal |∫ t in (0 : ℝ)..(2 * T), ∑ i : Fin d, ∑' y,
        (g (y + unit i) - g y) * heatGrad u i t y| ≤
      2 * ∑' x, ENNReal.ofReal (gam S g T x) ^ (1 / 2 : ℝ) *
        (2 * sqInt u (Real.sqrt T) x) ^ (1 / 2 : ℝ) := by
  set Φt : ℝ → ℝ := fun s => ∑ i : Fin d, ∑' w,
    (heatF S g s (w + unit i) - heatF S g s w) * heatGrad u i s w with hΦt
  have hcongr : ∫ t in (0 : ℝ)..(2 * T), ∑ i : Fin d, ∑' y,
      (g (y + unit i) - g y) * heatGrad u i t y = ∫ t in (0 : ℝ)..(2 * T), Φt (t / 2) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le (by linarith)] at ht
    simp only [hΦt]
    exact Finset.sum_congr rfl fun i _ => tsum_fd_mul_heatGrad_eq hu hgS i ht.1
  rw [hcongr, intervalIntegral.integral_comp_div Φt (by norm_num : (2 : ℝ) ≠ 0),
    show (0 : ℝ) / 2 = 0 by norm_num, show 2 * T / 2 = T by ring, smul_eq_mul, abs_mul,
    ENNReal.ofReal_mul (by norm_num), abs_two, ENNReal.ofReal_ofNat]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  -- into lower integrals
  have hA : ∀ i w, ContinuousOn (fun s => heatGrad u i s w) (Set.Icc 0 T) :=
    fun i w => continuousOn_heatGrad hu i hT w
  have hv : ∀ w, Continuous fun s => heatF S g s w := fun w => continuous_heatF S g w
  have h1 : ENNReal.ofReal |∫ s in (0 : ℝ)..T, Φt s| ≤
      ∫⁻ s in Set.Ioc 0 T, ENNReal.ofReal |Φt s| := by
    rw [intervalIntegral.integral_of_le hT, ← Real.enorm_eq_ofReal_abs]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    exact lintegral_congr fun s => Real.enorm_eq_ofReal_abs _
  have h2 : ∀ s, ENNReal.ofReal |Φt s| ≤ ∑' w, ENNReal.ofReal (∑ i : Fin d,
      |heatF S g s (w + unit i) - heatF S g s w| * |heatGrad u i s w|) := by
    intro s
    calc ENNReal.ofReal |Φt s| ≤ ENNReal.ofReal (∑ i : Fin d, |∑' w,
          (heatF S g s (w + unit i) - heatF S g s w) * heatGrad u i s w|) :=
          ENNReal.ofReal_le_ofReal (Finset.abs_sum_le_sum_abs _ _)
      _ = ∑ i : Fin d, ENNReal.ofReal |∑' w,
          (heatF S g s (w + unit i) - heatF S g s w) * heatGrad u i s w| :=
          ENNReal.ofReal_sum_of_nonneg fun i _ => abs_nonneg _
      _ ≤ ∑ i : Fin d, ∑' w, ENNReal.ofReal
          |(heatF S g s (w + unit i) - heatF S g s w) * heatGrad u i s w| :=
          Finset.sum_le_sum fun i _ => ofReal_abs_tsum_le' _
      _ = ∑' w, ENNReal.ofReal (∑ i : Fin d,
          |heatF S g s (w + unit i) - heatF S g s w| * |heatGrad u i s w|) := by
          rw [← Summable.tsum_finsetSum fun i _ => ENNReal.summable]
          refine tsum_congr fun w => ?_
          rw [ENNReal.ofReal_sum_of_nonneg fun i _ => by positivity]
          exact Finset.sum_congr rfl fun i _ => by rw [abs_mul]
  have hmeas : ∀ w, AEMeasurable (fun s => ENNReal.ofReal (∑ i : Fin d,
      |heatF S g s (w + unit i) - heatF S g s w| * |heatGrad u i s w|))
      (volume.restrict (Set.Ioc 0 T)) := by
    intro w
    refine (ContinuousOn.aemeasurable ?_ measurableSet_Ioc).ennreal_ofReal
    refine continuousOn_finsetSum _ fun i _ => ?_
    exact (((hv _).sub (hv _)).continuousOn.abs).mul
      (((hA i w).mono Set.Ioc_subset_Icc_self).abs)
  refine h1.trans ((setLIntegral_mono' measurableSet_Ioc fun s _ => h2 s).trans ?_)
  rw [lintegral_tsum hmeas]
  refine ENNReal.tsum_le_tsum fun w => ?_
  -- Cauchy-Schwarz in time
  set X : ℝ → ℝ := fun s => ∑ i : Fin d, (heatF S g s (w + unit i) - heatF S g s w) ^ 2 with hX
  set Y : ℝ → ℝ := fun s => ∑ i : Fin d, heatGrad u i s w ^ 2 with hY
  have hX0 : ∀ s, 0 ≤ X s := fun s => by positivity
  have hY0 : ∀ s, 0 ≤ Y s := fun s => by positivity
  have hpt : ∀ s, ENNReal.ofReal (∑ i : Fin d,
      |heatF S g s (w + unit i) - heatF S g s w| * |heatGrad u i s w|) ≤
      ENNReal.ofReal (Real.sqrt (X s)) * ENNReal.ofReal (Real.sqrt (Y s)) := by
    intro s
    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (sum_abs_mul_le_sqrt
      (fun i => heatF S g s (w + unit i) - heatF S g s w) (fun i => heatGrad u i s w))
  have hXc : ContinuousOn X (Set.Icc 0 T) :=
    (continuous_finsetSum _ fun i _ => ((hv _).sub (hv _)).pow 2).continuousOn
  have hYc : ContinuousOn Y (Set.Icc 0 T) :=
    continuousOn_finsetSum _ fun i _ => (hA i w).pow 2
  have hmX : AEMeasurable (fun s => ENNReal.ofReal (Real.sqrt (X s)))
      (volume.restrict (Set.Ioc 0 T)) :=
    ((hXc.mono Set.Ioc_subset_Icc_self).sqrt.aemeasurable measurableSet_Ioc).ennreal_ofReal
  have hmY : AEMeasurable (fun s => ENNReal.ofReal (Real.sqrt (Y s)))
      (volume.restrict (Set.Ioc 0 T)) :=
    ((hYc.mono Set.Ioc_subset_Icc_self).sqrt.aemeasurable measurableSet_Ioc).ennreal_ofReal
  have hsq : ∀ Z : ℝ, 0 ≤ Z → ENNReal.ofReal (Real.sqrt Z) ^ (2 : ℝ) = ENNReal.ofReal Z := by
    intro Z hZ
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num),
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.sq_sqrt hZ]
  have hgam : ∫⁻ s in Set.Ioc 0 T, ENNReal.ofReal (X s) = ENNReal.ofReal (gam S g T w) := by
    rw [gam, intervalIntegral.integral_of_le hT, ofReal_integral_eq_lintegral_ofReal]
    · exact (hXc.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
    · exact Filter.Eventually.of_forall fun s => hX0 s
  have hYb : ∫⁻ s in Set.Ioc 0 T, ENNReal.ofReal (Y s) ≤ 2 * sqInt u (Real.sqrt T) w := by
    have := lintegral_sum_sq_heatGrad_le u (Real.sqrt_nonneg T) w
    rwa [Real.sq_sqrt hT] at this
  calc ∫⁻ s in Set.Ioc 0 T, ENNReal.ofReal (∑ i : Fin d,
        |heatF S g s (w + unit i) - heatF S g s w| * |heatGrad u i s w|)
      ≤ ∫⁻ s in Set.Ioc 0 T, (fun s => ENNReal.ofReal (Real.sqrt (X s))) s *
          (fun s => ENNReal.ofReal (Real.sqrt (Y s))) s :=
        setLIntegral_mono' measurableSet_Ioc fun s _ => hpt s
    _ ≤ (∫⁻ s in Set.Ioc 0 T, ENNReal.ofReal (Real.sqrt (X s)) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
          (∫⁻ s in Set.Ioc 0 T, ENNReal.ofReal (Real.sqrt (Y s)) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
        ENNReal.lintegral_mul_le_Lp_mul_Lq _ Real.HolderConjugate.two_two hmX hmY
    _ ≤ ENNReal.ofReal (gam S g T w) ^ (1 / 2 : ℝ) *
          (2 * sqInt u (Real.sqrt T) w) ^ (1 / 2 : ℝ) := by
        simp only [hsq _ (hX0 _), hsq _ (hY0 _)]
        rw [hgam]
        gcongr

end Rigidity.Poincare.GeneralDim
