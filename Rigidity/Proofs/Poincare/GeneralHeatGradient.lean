import Rigidity.Proofs.Poincare.HeatGradient
import Rigidity.Proofs.Poincare.GeneralLatticeHeatFlow

/-!
# Heat-kernel averages of the gradient of a function on `ℤ^d`

The extension of `HeatGradient.lean` from `ℤ²` to `ℤ^d`, `d ≥ 1`. For `u : ℤ^d → ℝ` whose gradient
is summable against the heat kernel at every positive time (`HeatSummable u`, the hypothesis of the
multiscale Poincaré inequality (2.26) of Dario), the averages `A_j(t, y) = Σ_z Φ_t(y, z) ∇_j u(z)`
(Dario's `Φ_{r²} * ∇u` at `t = r²`) satisfy:

* `heatGrad_zero`: `A_j(0, ·) = ∇_j u`;
* `hasDerivAt_heatGrad`, `continuousOn_heatGrad`: the heat equation `∂_t A_j = lap A_j` on
  `(0, ∞)` and continuity on `[0, T]`, by domination `Φ_t ≤ e^{4dT} Φ_{2T}`
  (`zdHeat_le_exp_mul`);
* `heatGrad_sub_eq_integral`: `A_j(T, y) - ∇_j u(y) = ∫_0^T lap A_j(t, ·)(y) dt`;
* `heatGrad_add_unit_sub`: `∇_i A_j = ∇_j A_i` (the gradient field stays curl-free);
* `heatGrad_eq_tsum`: the semigroup property `A_j(t, y) = Σ_w Φ_{t-s}(y, w) A_j(s, w)`.
-/

open scoped Classical
open LatticeProb LatticeProb.Percolation Rigidity.Green MeasureTheory

namespace Rigidity.Poincare.GeneralDim

variable {d : ℕ}

/-- The Poisson weights at time `s ≤ T` are at most `e^{2DT}` times those at time `2T`. -/
theorem poissonWeight_le_exp_mul (D : ℕ) {s T : ℝ} (hs : 0 ≤ s) (hsT : s ≤ T) (n : ℕ) :
    poissonWeight D s n ≤ Real.exp (2 * D * T) * poissonWeight D (2 * T) n := by
  unfold poissonWeight
  have hT : 0 ≤ T := hs.trans hsT
  have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have h1 : Real.exp (-D * s) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have h2 : (D * s) ^ n ≤ (D * (2 * T)) ^ n :=
    pow_le_pow_left₀ (by positivity) (by nlinarith) n
  have h3 : Real.exp (2 * D * T) * Real.exp (-D * (2 * T)) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  rw [mul_div_assoc', ← mul_assoc, h3, one_mul]
  refine div_le_div_of_nonneg_right ?_ hf.le
  calc Real.exp (-D * s) * (D * s) ^ n ≤ 1 * (D * (2 * T)) ^ n :=
        mul_le_mul h1 h2 (by positivity) zero_le_one
    _ = (D * (2 * T)) ^ n := one_mul _

/-- **Domination in time**: `Φ_s ≤ e^{4dT} Φ_{2T}` for `0 ≤ s ≤ T`. -/
theorem zdHeat_le_exp_mul [NeZero d] {s T : ℝ} (hs : 0 ≤ s) (hsT : s ≤ T) (x y : Vertex d) :
    zdHeat d s x y ≤ Real.exp (4 * d * T) * zdHeat d (2 * T) x y := by
  have hdeg := openGraph_degree_le (allOpen d)
  rw [zdHeat, zdHeat, vsrwHeat, vsrwHeat, ← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun n => ?_)
    (summable_vsrwHeat two_mul_pos_of_neZero hdeg s x y)
    ((summable_vsrwHeat two_mul_pos_of_neZero hdeg (2 * T) x y).mul_left _)
  rw [← mul_assoc]
  have h := poissonWeight_le_exp_mul (2 * d) hs hsT n
  have e : Real.exp (2 * ((2 * d : ℕ) : ℝ) * T) = Real.exp (4 * d * T) := by
    push_cast
    ring_nf
  rw [e] at h
  exact mul_le_mul_of_nonneg_right h
    (lazyPow_mem_Icc two_mul_pos_of_neZero hdeg n x y).1

theorem continuous_zdHeat [NeZero d] (x y : Vertex d) : Continuous fun t => zdHeat d t x y :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_zdHeat t x y).continuousAt

/-- **The semigroup property** of the heat kernel of `ℤ^d`. -/
theorem hasSum_zdHeat_mul [NeZero d] {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (x z : Vertex d) :
    HasSum (fun y => zdHeat d s x y * zdHeat d t y z) (zdHeat d (s + t) x z) :=
  hasSum_vsrwHeat_mul two_mul_pos_of_neZero (openGraph_degree_le (allOpen d)) hs ht x z

/-- The gradient of `u` is summable against the heat kernel of `ℤ^d` at every positive time. -/
def HeatSummable (u : Vertex d → ℝ) : Prop :=
  ∀ (x : Vertex d) (j : Fin d) (t : ℝ), 0 < t →
    Summable fun y => zdHeat d t x y * (u (y + unit j) - u y)

/-- The forward difference `∇_j u(z) = u(z + e_j) - u(z)`. -/
def fd (u : Vertex d → ℝ) (j : Fin d) (z : Vertex d) : ℝ := u (z + unit j) - u z

/-- `A_j(t, y) = Σ_z Φ_t(y, z) ∇_j u(z)`. -/
noncomputable def heatGrad (u : Vertex d → ℝ) (j : Fin d) (t : ℝ) (y : Vertex d) : ℝ :=
  ∑' z, zdHeat d t y z * fd u j z

variable {u : Vertex d → ℝ}

theorem summable_heat_fd (hu : HeatSummable u) (j : Fin d) {t : ℝ} (ht : 0 ≤ t)
    (y : Vertex d) : Summable fun z => zdHeat d t y z * fd u j z := by
  rcases ht.lt_or_eq with ht | ht
  · exact hu y j t ht
  · subst ht
    refine summable_of_ne_finset_zero (s := {y}) fun z hz => ?_
    rw [zdHeat_zero, if_neg (fun h => hz (by rw [h]; exact Finset.mem_singleton_self z)),
      zero_mul]

theorem summable_heat_abs_fd [NeZero d] (hu : HeatSummable u) (j : Fin d) {t : ℝ} (ht : 0 ≤ t)
    (y : Vertex d) : Summable fun z => zdHeat d t y z * |fd u j z| :=
  (summable_heat_fd hu j ht y).abs.congr fun z => by
    rw [abs_mul, abs_of_nonneg (zdHeat_nonneg ht y z)]

theorem heatGrad_zero (j : Fin d) (y : Vertex d) : heatGrad u j 0 y = fd u j y := by
  unfold heatGrad
  rw [tsum_eq_single y fun z hz => by rw [zdHeat_zero, if_neg (fun h => hz h.symm), zero_mul],
    zdHeat_zero, if_pos rfl, one_mul]

theorem abs_heat_fd_le [NeZero d] {T t : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) (j : Fin d)
    (y z : Vertex d) :
    |zdHeat d t y z * fd u j z| ≤ Real.exp (4 * d * T) * (zdHeat d (2 * T) y z * |fd u j z|) := by
  rw [abs_mul, abs_of_nonneg (zdHeat_nonneg ht y z), ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (zdHeat_le_exp_mul ht htT y z) (abs_nonneg _)

theorem continuousOn_heatGrad [NeZero d] (hu : HeatSummable u) (j : Fin d) {T : ℝ} (hT : 0 ≤ T)
    (y : Vertex d) : ContinuousOn (fun t => heatGrad u j t y) (Set.Icc 0 T) := by
  refine continuousOn_tsum (fun z => ((continuous_zdHeat y z).mul
    continuous_const).continuousOn) ((summable_heat_abs_fd hu j (by linarith : (0 : ℝ) ≤ 2 * T)
      y).mul_left (Real.exp (4 * d * T))) fun z t ht => ?_
  rw [Real.norm_eq_abs]
  exact abs_heat_fd_le ht.1 ht.2 j y z

/-- `lap` of the heat kernel in its first variable, against `∇_j u`. -/
theorem lap_heatGrad (hu : HeatSummable u) (j : Fin d) {t : ℝ} (ht : 0 ≤ t) (y : Vertex d) :
    lap (heatGrad u j t) y = ∑' z, lap (fun w => zdHeat d t w z) y * fd u j z := by
  have hs := fun w => summable_heat_fd hu j ht w
  have hpair : ∀ i : Fin d, heatGrad u j t (y + unit i) + heatGrad u j t (y - unit i) =
      ∑' z, (zdHeat d t (y + unit i) z + zdHeat d t (y - unit i) z) * fd u j z := by
    intro i
    unfold heatGrad
    rw [← (hs (y + unit i)).tsum_add (hs (y - unit i))]
    exact tsum_congr fun z => by ring
  have hsum : ∀ i ∈ (Finset.univ : Finset (Fin d)), Summable fun z =>
      (zdHeat d t (y + unit i) z + zdHeat d t (y - unit i) z) * fd u j z := fun i _ =>
    ((hs (y + unit i)).add (hs (y - unit i))).congr fun z => by ring
  simp only [lap]
  rw [Finset.sum_congr rfl fun i _ => hpair i, ← Summable.tsum_finsetSum hsum]
  unfold heatGrad
  rw [← tsum_mul_left, ← (summable_sum hsum).tsum_sub ((hs y).mul_left _)]
  refine tsum_congr fun z => ?_
  rw [sub_mul, Finset.sum_mul]
  ring

theorem abs_lap_zdHeat_le [NeZero d] {s T : ℝ} (hs : 0 ≤ s) (hsT : s ≤ T) (y z : Vertex d) :
    |lap (fun w => zdHeat d s w z) y| ≤ Real.exp (4 * d * T) *
      (∑ i : Fin d, (zdHeat d (2 * T) (y + unit i) z + zdHeat d (2 * T) (y - unit i) z) +
        2 * d * zdHeat d (2 * T) y z) := by
  have hd := fun w => zdHeat_le_exp_mul hs hsT w z
  have h0 := fun w => zdHeat_nonneg (d := d) hs w z
  have hS0 : 0 ≤ ∑ i : Fin d, (zdHeat d s (y + unit i) z + zdHeat d s (y - unit i) z) :=
    Finset.sum_nonneg fun i _ => add_nonneg (h0 _) (h0 _)
  have hSle : ∑ i : Fin d, (zdHeat d s (y + unit i) z + zdHeat d s (y - unit i) z) ≤
      Real.exp (4 * d * T) *
        ∑ i : Fin d, (zdHeat d (2 * T) (y + unit i) z + zdHeat d (2 * T) (y - unit i) z) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => by rw [mul_add]; exact add_le_add (hd _) (hd _)
  have hdd : (0 : ℝ) ≤ 2 * d := by positivity
  have hc : 2 * d * zdHeat d s y z ≤ Real.exp (4 * d * T) * (2 * d * zdHeat d (2 * T) y z) := by
    calc 2 * (d : ℝ) * zdHeat d s y z ≤ 2 * d * (Real.exp (4 * d * T) * zdHeat d (2 * T) y z) :=
          mul_le_mul_of_nonneg_left (hd y) hdd
      _ = Real.exp (4 * d * T) * (2 * d * zdHeat d (2 * T) y z) := by ring
  have hc0 : 0 ≤ 2 * d * zdHeat d s y z := mul_nonneg hdd (h0 y)
  simp only [lap]
  rw [abs_le, mul_add]
  constructor <;> linarith

theorem mul_sum_add_mul_eq (e c C : ℝ) (A B : Fin d → ℝ) :
    e * (∑ i, (A i + B i) + 2 * d * C) * c = e * (∑ i, (A i * c + B i * c) + 2 * d * (C * c)) := by
  rw [mul_assoc, add_mul, Finset.sum_mul]
  simp only [add_mul]
  ring

/-- **The heat equation** for `A_j` on `(0, T)`. -/
theorem hasDerivAt_heatGrad [NeZero d] (hu : HeatSummable u) (j : Fin d) {T t : ℝ}
    (ht : t ∈ Set.Ioo 0 T) (y : Vertex d) :
    HasDerivAt (fun t => heatGrad u j t y) (lap (heatGrad u j t) y) t := by
  have h2T : (0 : ℝ) ≤ 2 * T := by linarith [ht.1, ht.2]
  set b : Vertex d → ℝ := fun z => Real.exp (4 * d * T) *
    (∑ i : Fin d, (zdHeat d (2 * T) (y + unit i) z + zdHeat d (2 * T) (y - unit i) z) +
      2 * d * zdHeat d (2 * T) y z) * |fd u j z| with hb
  have hbs : Summable b := by
    have hs := fun w => summable_heat_abs_fd hu j h2T w
    have hsum : Summable fun z => ∑ i : Fin d,
        (zdHeat d (2 * T) (y + unit i) z * |fd u j z| +
          zdHeat d (2 * T) (y - unit i) z * |fd u j z|) :=
      summable_sum fun i _ => (hs (y + unit i)).add (hs (y - unit i))
    have h := (hsum.add ((hs y).mul_left (2 * (d : ℝ)))).mul_left (Real.exp (4 * d * T))
    refine h.congr fun z => ?_
    simp only [hb]
    exact (mul_sum_add_mul_eq _ _ _ _ _).symm
  have key := hasDerivAt_tsum_of_isPreconnected (u := b) hbs isOpen_Ioo isPreconnected_Ioo
    (t := Set.Ioo 0 T) (y₀ := t)
    (g := fun z s => zdHeat d s y z * fd u j z)
    (g' := fun z s => lap (fun w => zdHeat d s w z) y * fd u j z)
    (fun z s _ => by
      have := (hasDerivAt_zdHeat s y z).mul_const (fd u j z)
      rwa [openLaplacian_allOpen] at this)
    (fun z s hs => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (abs_lap_zdHeat_le hs.1.le hs.2.le y z)
        (abs_nonneg _))
    ht (summable_heat_fd hu j ht.1.le y) ht
  rw [lap_heatGrad hu j ht.1.le y]
  exact key

/-- **The fundamental theorem of calculus** for `A_j`. -/
theorem heatGrad_sub_eq_integral [NeZero d] (hu : HeatSummable u) (j : Fin d) {T : ℝ}
    (hT : 0 ≤ T) (y : Vertex d) :
    heatGrad u j T y - fd u j y = ∫ t in (0 : ℝ)..T, lap (heatGrad u j t) y := by
  have hcont : ContinuousOn (fun t => lap (heatGrad u j t) y) (Set.Icc 0 T) := by
    have h := fun w => continuousOn_heatGrad hu j hT w
    simp only [lap]
    exact (continuousOn_finsetSum _ fun i _ => (h _).add (h _)).sub
      (continuousOn_const.mul (h _))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT (continuousOn_heatGrad hu j hT y)
    (fun t ht => hasDerivAt_heatGrad hu j ht y) (hcont.intervalIntegrable_of_Icc hT),
    heatGrad_zero]

/-- Translating the base point is translating the gradient. -/
theorem heatGrad_add [NeZero d] (j : Fin d) (t : ℝ) (y e : Vertex d) :
    heatGrad u j t (y + e) = ∑' z, zdHeat d t y z * fd u j (z + e) := by
  unfold heatGrad
  rw [← (Equiv.addRight e).tsum_eq]
  refine tsum_congr fun z => ?_
  simp only [Equiv.coe_addRight]
  rw [zdHeat_add]

theorem summable_heat_fd_add [NeZero d] (hu : HeatSummable u) (j : Fin d) {t : ℝ} (ht : 0 ≤ t)
    (y e : Vertex d) : Summable fun z => zdHeat d t y z * fd u j (z + e) := by
  have h := summable_heat_fd hu j ht (y + e)
  rw [← (Equiv.addRight e).summable_iff] at h
  refine h.congr fun z => ?_
  simp only [Function.comp_apply, Equiv.coe_addRight]
  rw [zdHeat_add]

/-- **The averaged gradient stays curl-free**: `∇_i A_j = ∇_j A_i`. -/
theorem heatGrad_add_unit_sub [NeZero d] (hu : HeatSummable u) (i j : Fin d) {t : ℝ}
    (ht : 0 ≤ t) (y : Vertex d) :
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
theorem heatGrad_eq_tsum [NeZero d] (hu : HeatSummable u) (j : Fin d) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (y : Vertex d) :
    heatGrad u j t y = ∑' w, zdHeat d (t - s) y w * heatGrad u j s w := by
  have hts : 0 ≤ t - s := by linarith
  set F : Vertex d → Vertex d → ℝ := fun w z =>
    zdHeat d (t - s) y w * (zdHeat d s w z * fd u j z) with hF
  have hfib : ∀ z, HasSum (fun w => |F w z|) (zdHeat d t y z * |fd u j z|) := by
    intro z
    have h := (hasSum_zdHeat_mul hts hs y z).mul_right |fd u j z|
    rw [sub_add_cancel] at h
    refine h.congr_fun fun w => ?_
    simp only [hF]
    rw [abs_mul, abs_mul, abs_of_nonneg (zdHeat_nonneg hts y w),
      abs_of_nonneg (zdHeat_nonneg hs w z)]
    ring
  have hsum : Summable (Function.uncurry fun z w => F w z) := by
    have h0 : 0 ≤ fun q : Vertex d × Vertex d => |F q.2 q.1| := fun q => abs_nonneg _
    refine Summable.of_abs ?_
    have : Summable fun q : Vertex d × Vertex d => |F q.2 q.1| := by
      rw [summable_prod_of_nonneg h0]
      exact ⟨fun z => (hfib z).summable, ((summable_heat_abs_fd hu j (by linarith) y).congr
        fun z => ((hfib z).tsum_eq).symm)⟩
    exact this
  have hsum' : Summable (Function.uncurry F) :=
    (Equiv.prodComm (Vertex d) (Vertex d)).summable_iff.2 hsum
  have hcomm := hsum'.tsum_comm
  unfold heatGrad
  calc ∑' z, zdHeat d t y z * fd u j z = ∑' z, ∑' w, F w z := by
        refine tsum_congr fun z => ?_
        have h := (hasSum_zdHeat_mul hts hs y z).mul_right (fd u j z)
        rw [sub_add_cancel] at h
        rw [← h.tsum_eq]
        exact tsum_congr fun w => by simp only [hF]; ring
    _ = ∑' w, ∑' z, F w z := hcomm
    _ = ∑' w, zdHeat d (t - s) y w * ∑' z, zdHeat d s w z * fd u j z :=
        tsum_congr fun w => tsum_mul_left

end Rigidity.Poincare.GeneralDim
