import Rigidity.Proofs.Poincare.LatticeHeatFlow

/-!
# Heat-kernel averages of the gradient of a function on `ℤ²`

For `u : ℤ² → ℝ` whose gradient is summable against the heat kernel at every positive time
(`HeatSummable u`, the hypothesis of the multiscale Poincaré inequality (2.26) of Dario), the
averages `A_j(t, y) = Σ_z Φ_t(y, z) ∇_j u(z)` (Dario's `Φ_{r²} * ∇u` at `t = r²`) satisfy:

* `heatGrad_zero`: `A_j(0, ·) = ∇_j u`;
* `hasDerivAt_heatGrad`, `continuousOn_heatGrad`: the heat equation `∂_t A_j = lap A_j` on
  `(0, ∞)` and continuity on `[0, T]`, by domination `Φ_t ≤ e^{8T} Φ_{2T}`;
* `heatGrad_sub_eq_integral`: `A_j(T, y) - ∇_j u(y) = ∫_0^T lap A_j(t, ·)(y) dt`;
* `heatGrad_add_unit_sub`: `∇_i A_j = ∇_j A_i` (the gradient field stays curl-free);
* `heatGrad_eq_tsum`: the semigroup property `A_j(t, y) = Σ_w Φ_{t-s}(y, w) A_j(s, w)`.
-/

open scoped Classical
open LatticeProb LatticeProb.Percolation Rigidity.Green MeasureTheory

namespace Rigidity.Poincare

/-- The gradient of `u` is summable against the heat kernel of `ℤ²` at every positive time. -/
def HeatSummable (u : Vertex 2 → ℝ) : Prop :=
  ∀ (x : Vertex 2) (j : Fin 2) (t : ℝ), 0 < t →
    Summable fun y => openHeat (allOpen 2) t x y * (u (y + unit j) - u y)

/-- The forward difference `∇_j u(z) = u(z + e_j) - u(z)`. -/
def fd (u : Vertex 2 → ℝ) (j : Fin 2) (z : Vertex 2) : ℝ := u (z + unit j) - u z

/-- `A_j(t, y) = Σ_z Φ_t(y, z) ∇_j u(z)`. -/
noncomputable def heatGrad (u : Vertex 2 → ℝ) (j : Fin 2) (t : ℝ) (y : Vertex 2) : ℝ :=
  ∑' z, openHeat (allOpen 2) t y z * fd u j z

variable {u : Vertex 2 → ℝ}

theorem summable_heat_fd (hu : HeatSummable u) (j : Fin 2) {t : ℝ} (ht : 0 ≤ t)
    (y : Vertex 2) : Summable fun z => openHeat (allOpen 2) t y z * fd u j z := by
  rcases ht.lt_or_eq with ht | ht
  · exact hu y j t ht
  · subst ht
    refine summable_of_ne_finset_zero (s := {y}) fun z hz => ?_
    rw [openHeat_zero, if_neg (fun h => hz (by rw [h]; exact Finset.mem_singleton_self z)),
      zero_mul]

theorem summable_heat_abs_fd (hu : HeatSummable u) (j : Fin 2) {t : ℝ} (ht : 0 ≤ t)
    (y : Vertex 2) : Summable fun z => openHeat (allOpen 2) t y z * |fd u j z| :=
  (summable_heat_fd hu j ht y).abs.congr fun z => by
    rw [abs_mul, abs_of_nonneg (openHeat_nonneg _ ht y z)]

theorem heatGrad_zero (j : Fin 2) (y : Vertex 2) : heatGrad u j 0 y = fd u j y := by
  unfold heatGrad
  rw [tsum_eq_single y fun z hz => by rw [openHeat_zero, if_neg (fun h => hz h.symm), zero_mul],
    openHeat_zero, if_pos rfl, one_mul]

theorem abs_heat_fd_le {T t : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) (j : Fin 2) (y z : Vertex 2) :
    |openHeat (allOpen 2) t y z * fd u j z| ≤
      Real.exp (8 * T) * (openHeat (allOpen 2) (2 * T) y z * |fd u j z|) := by
  rw [abs_mul, abs_of_nonneg (openHeat_nonneg _ ht y z), ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (openHeat_allOpen_le_exp_mul ht htT y z) (abs_nonneg _)

theorem continuousOn_heatGrad (hu : HeatSummable u) (j : Fin 2) {T : ℝ} (hT : 0 ≤ T)
    (y : Vertex 2) : ContinuousOn (fun t => heatGrad u j t y) (Set.Icc 0 T) := by
  refine continuousOn_tsum (fun z => ((continuous_openHeat _ y z).mul
    continuous_const).continuousOn) ((summable_heat_abs_fd hu j (by linarith : (0 : ℝ) ≤ 2 * T)
      y).mul_left (Real.exp (8 * T))) fun z t ht => ?_
  rw [Real.norm_eq_abs]
  exact abs_heat_fd_le ht.1 ht.2 j y z

/-- `lap` of the heat kernel in its first variable, against `∇_j u`. -/
theorem lap_heatGrad (hu : HeatSummable u) (j : Fin 2) {t : ℝ} (ht : 0 ≤ t) (y : Vertex 2) :
    lap (heatGrad u j t) y =
      ∑' z, lap (fun w => openHeat (allOpen 2) t w z) y * fd u j z := by
  have hs := fun w => summable_heat_fd hu j ht w
  simp only [lap, Fin.sum_univ_two, heatGrad]
  rw [← (hs (y + unit 0)).tsum_add (hs (y - unit 0)),
    ← (hs (y + unit 1)).tsum_add (hs (y - unit 1)),
    ← ((hs (y + unit 0)).add (hs (y - unit 0))).tsum_add ((hs (y + unit 1)).add
      (hs (y - unit 1))), ← tsum_mul_left,
    ← (((hs (y + unit 0)).add (hs (y - unit 0))).add ((hs (y + unit 1)).add
      (hs (y - unit 1)))).tsum_sub ((hs y).mul_left 4)]
  exact tsum_congr fun z => by ring

theorem abs_lap_openHeat_le {s T : ℝ} (hs : 0 ≤ s) (hsT : s ≤ T) (y z : Vertex 2) :
    |lap (fun w => openHeat (allOpen 2) s w z) y| ≤ Real.exp (8 * T) *
      (∑ i : Fin 2, (openHeat (allOpen 2) (2 * T) (y + unit i) z +
        openHeat (allOpen 2) (2 * T) (y - unit i) z) + 4 * openHeat (allOpen 2) (2 * T) y z) := by
  have hd := fun w => openHeat_allOpen_le_exp_mul hs hsT w z
  have h0 := fun w => openHeat_nonneg (allOpen 2) hs w z
  simp only [lap, Fin.sum_univ_two]
  rw [abs_le]
  constructor
  · nlinarith [hd y, hd (y + unit 0), hd (y - unit 0), hd (y + unit 1), hd (y - unit 1),
      h0 y, h0 (y + unit 0), h0 (y - unit 0), h0 (y + unit 1), h0 (y - unit 1)]
  · nlinarith [hd y, hd (y + unit 0), hd (y - unit 0), hd (y + unit 1), hd (y - unit 1),
      h0 y, h0 (y + unit 0), h0 (y - unit 0), h0 (y + unit 1), h0 (y - unit 1)]

/-- **The heat equation** for `A_j` on `(0, T)`. -/
theorem hasDerivAt_heatGrad (hu : HeatSummable u) (j : Fin 2) {T t : ℝ}
    (ht : t ∈ Set.Ioo 0 T) (y : Vertex 2) :
    HasDerivAt (fun t => heatGrad u j t y) (lap (heatGrad u j t) y) t := by
  have hT : 0 ≤ T := le_trans ht.1.le ht.2.le
  have h2T : (0 : ℝ) ≤ 2 * T := by linarith
  set b : Vertex 2 → ℝ := fun z => Real.exp (8 * T) *
    (∑ i : Fin 2, (openHeat (allOpen 2) (2 * T) (y + unit i) z +
      openHeat (allOpen 2) (2 * T) (y - unit i) z) + 4 * openHeat (allOpen 2) (2 * T) y z) *
      |fd u j z| with hb
  have hbs : Summable b := by
    have hs := fun w => summable_heat_abs_fd hu j h2T w
    have h := ((((hs (y + unit 0)).add (hs (y - unit 0))).add ((hs (y + unit 1)).add
      (hs (y - unit 1)))).add ((hs y).mul_left 4)).mul_left (Real.exp (8 * T))
    refine h.congr fun z => ?_
    simp only [hb, Fin.sum_univ_two]
    ring
  have key := hasDerivAt_tsum_of_isPreconnected (u := b) hbs isOpen_Ioo isPreconnected_Ioo
    (t := Set.Ioo 0 T) (y₀ := t)
    (g := fun z s => openHeat (allOpen 2) s y z * fd u j z)
    (g' := fun z s => lap (fun w => openHeat (allOpen 2) s w z) y * fd u j z)
    (fun z s _ => by
      have := (hasDerivAt_openHeat (allOpen 2) s y z).mul_const (fd u j z)
      rwa [openLaplacian_allOpen] at this)
    (fun z s hs => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (abs_lap_openHeat_le hs.1.le hs.2.le y z)
        (abs_nonneg _))
    ht (summable_heat_fd hu j ht.1.le y) ht
  rw [lap_heatGrad hu j ht.1.le y]
  exact key

/-- **The fundamental theorem of calculus** for `A_j`. -/
theorem heatGrad_sub_eq_integral (hu : HeatSummable u) (j : Fin 2) {T : ℝ} (hT : 0 ≤ T)
    (y : Vertex 2) :
    heatGrad u j T y - fd u j y = ∫ t in (0 : ℝ)..T, lap (heatGrad u j t) y := by
  have hcont : ContinuousOn (fun t => lap (heatGrad u j t) y) (Set.Icc 0 T) := by
    have h := fun w => continuousOn_heatGrad hu j hT w
    simp only [lap, Fin.sum_univ_two]
    exact (((h _).add (h _)).add ((h _).add (h _))).sub (continuousOn_const.mul (h _))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT (continuousOn_heatGrad hu j hT y)
    (fun t ht => hasDerivAt_heatGrad hu j ht y) (hcont.intervalIntegrable_of_Icc hT),
    heatGrad_zero]

/-- Translating the base point is translating the gradient. -/
theorem heatGrad_add (j : Fin 2) (t : ℝ) (y e : Vertex 2) :
    heatGrad u j t (y + e) = ∑' z, openHeat (allOpen 2) t y z * fd u j (z + e) := by
  unfold heatGrad
  rw [← (Equiv.addRight e).tsum_eq]
  refine tsum_congr fun z => ?_
  simp only [Equiv.coe_addRight]
  rw [openHeat_allOpen_add]

theorem summable_heat_fd_add (hu : HeatSummable u) (j : Fin 2) {t : ℝ} (ht : 0 ≤ t)
    (y e : Vertex 2) : Summable fun z => openHeat (allOpen 2) t y z * fd u j (z + e) := by
  have h := summable_heat_fd hu j ht (y + e)
  rw [← (Equiv.addRight e).summable_iff] at h
  refine h.congr fun z => ?_
  simp only [Function.comp_apply, Equiv.coe_addRight]
  rw [openHeat_allOpen_add]

/-- **The averaged gradient stays curl-free**: `∇_i A_j = ∇_j A_i`. -/
theorem heatGrad_add_unit_sub (hu : HeatSummable u) (i j : Fin 2) {t : ℝ} (ht : 0 ≤ t)
    (y : Vertex 2) :
    heatGrad u j t (y + unit i) - heatGrad u j t y =
      heatGrad u i t (y + unit j) - heatGrad u i t y := by
  rw [heatGrad_add, heatGrad_add]
  unfold heatGrad
  rw [← (summable_heat_fd_add hu j ht y (unit i)).tsum_sub (summable_heat_fd hu j ht y),
    ← (summable_heat_fd_add hu i ht y (unit j)).tsum_sub (summable_heat_fd hu i ht y)]
  refine tsum_congr fun z => ?_
  simp only [fd]
  rw [add_right_comm z (unit i) (unit j)]
  ring

/-- **The semigroup property** `A_j(t, y) = Σ_w Φ_{t-s}(y, w) A_j(s, w)` for `0 ≤ s ≤ t`. -/
theorem heatGrad_eq_tsum (hu : HeatSummable u) (j : Fin 2) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (y : Vertex 2) :
    heatGrad u j t y =
      ∑' w, openHeat (allOpen 2) (t - s) y w * heatGrad u j s w := by
  have hts : 0 ≤ t - s := by linarith
  set F : Vertex 2 → Vertex 2 → ℝ := fun w z =>
    openHeat (allOpen 2) (t - s) y w * (openHeat (allOpen 2) s w z * fd u j z) with hF
  -- absolute summability, summing first over `w`
  have hfib : ∀ z, HasSum (fun w => |F w z|)
      (openHeat (allOpen 2) t y z * |fd u j z|) := by
    intro z
    have h := (hasSum_openHeat_mul (allOpen 2) hts hs y z).mul_right |fd u j z|
    rw [sub_add_cancel] at h
    refine h.congr_fun fun w => ?_
    simp only [hF]
    rw [abs_mul, abs_mul, abs_of_nonneg (openHeat_nonneg _ hts y w),
      abs_of_nonneg (openHeat_nonneg _ hs w z)]
    ring
  have hsum : Summable (Function.uncurry fun z w => F w z) := by
    have h0 : 0 ≤ fun q : Vertex 2 × Vertex 2 => |F q.2 q.1| := fun q => abs_nonneg _
    refine Summable.of_abs ?_
    have : Summable fun q : Vertex 2 × Vertex 2 => |F q.2 q.1| := by
      rw [summable_prod_of_nonneg h0]
      exact ⟨fun z => (hfib z).summable, ((summable_heat_abs_fd hu j (by linarith) y).congr
        fun z => ((hfib z).tsum_eq).symm)⟩
    exact this
  have hsum' : Summable (Function.uncurry F) := by
    have := (Equiv.prodComm (Vertex 2) (Vertex 2)).summable_iff.2 hsum
    exact this
  have hcomm := hsum'.tsum_comm
  unfold heatGrad
  calc ∑' z, openHeat (allOpen 2) t y z * fd u j z = ∑' z, ∑' w, F w z := by
        refine tsum_congr fun z => ?_
        have h := (hasSum_openHeat_mul (allOpen 2) hts hs y z).mul_right (fd u j z)
        rw [sub_add_cancel] at h
        rw [← h.tsum_eq]
        exact tsum_congr fun w => by simp only [hF]; ring
    _ = ∑' w, ∑' z, F w z := hcomm
    _ = ∑' w, openHeat (allOpen 2) (t - s) y w * ∑' z, openHeat (allOpen 2) s w z * fd u j z :=
        tsum_congr fun w => tsum_mul_left

end Rigidity.Poincare
