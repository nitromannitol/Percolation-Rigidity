import Rigidity.Proofs.Green.GeneralTwoScaleEnergy
import Rigidity.Proofs.Poincare.GeneralHeatGradient

/-!
# The function `w` of Proposition 4.3 of Dario–Gu on the cluster of `ℤ^d`

Step 1 of the proof of Proposition 4.3 of Dario–Gu in the form used by the energy argument, on
`ℤ^d`. On the cluster `K = 𝒞_∞`, with `f = 1_K h(τ, ·, y)` (`clusterInitD`), the function
`u(s, x) = 1_K(x) (h(s, x, y) - P_{s-τ} f(x))` (`clusterWD`), where `P` is the heat semigroup of the
open graph, vanishes off the cluster and:

* `clusterWD_self`: `u(τ, ·) = 0`;
* `hasDerivAt_clusterWD`: `∂_s u = Δ u + G` with `G = 1_K θ^{-1} twoScaleSourceD`
  (`clusterSourceD`), the equation (4.25) of `w`;
* `exists_clusterWD_dom`, `exists_clusterWD_deriv_dom`, `continuousOn_tsum_sq_clusterWD`: the
  domination and continuity used by the energy argument, when `1 ≤ τ` and the corrector grows at
  most linearly on the cluster.

The heat semigroup of a graph of bounded degree satisfies the heat equation on `ℓ²`
(`hasDerivAt_heatFlowG`) and the domination `|P_s f| ≤ e^{2DT} P_{2T} |f|` for `s ≤ T`
(`abs_heatFlowG_le_exp`). The Gaussian sums on `ℤ^d` are `tsum_exp_neg_sq_edzD_le`
(`Σ_x exp(-|x - y|²/(c r)) ≤ C r^{d/2}` for `r ≥ 1`) and `sq_add_mul_exp_le`.
-/

open scoped Classical
open LatticeProb LatticeProb.Percolation Rigidity.External

namespace Rigidity.Green.GeneralDim

section Graph

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] {D : ℕ}

/-- **Domination in time**: `p_s(x, z) ≤ e^{2DT} p_{2T}(x, z)` for `0 ≤ s ≤ T`. -/
theorem vsrwHeat_le_exp_mul (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) {s T : ℝ} (hs : 0 ≤ s)
    (hsT : s ≤ T) (x z : V) :
    vsrwHeat G D s x z ≤ Real.exp (2 * D * T) * vsrwHeat G D (2 * T) x z := by
  rw [vsrwHeat, vsrwHeat, ← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun n => ?_) (summable_vsrwHeat hD hdeg s x z)
    ((summable_vsrwHeat hD hdeg (2 * T) x z).mul_left _)
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right
    (Rigidity.Poincare.GeneralDim.poissonWeight_le_exp_mul D hs hsT n)
    (lazyPow_mem_Icc hD hdeg n x z).1

/-- **Domination**: `|P_s f(x)| ≤ e^{2DT} P_{2T} |f| (x)` for `0 ≤ s ≤ T`. -/
theorem abs_heatFlowG_le_exp (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) {s T : ℝ} (hs : 0 ≤ s)
    (hsT : s ≤ T) {f : V → ℝ} (hf : Summable fun z => f z ^ 2) (x : V) :
    |heatFlowG G D s f x| ≤ Real.exp (2 * D * T) * heatFlowG G D (2 * T) (fun z => |f z|) x := by
  have hT : 0 ≤ 2 * T := by linarith
  have hfa : Summable fun z => |f z| ^ 2 := by simpa only [sq_abs] using hf
  refine (abs_heatFlowG_le hD hdeg hs hf x).trans ?_
  unfold heatFlowG
  rw [← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun z => ?_) (summable_vsrwHeat_mul_l2 hD hdeg hs hfa x)
    ((summable_vsrwHeat_mul_l2 hD hdeg hT hfa x).mul_left _)
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (vsrwHeat_le_exp_mul hD hdeg hs hsT x z) (abs_nonneg _)

/-- The Laplacian of `P_s f`, under the sum. -/
theorem laplacian_heatFlowG_eq (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) {s : ℝ} (hs : 0 ≤ s)
    {f : V → ℝ} (hf : Summable fun z => f z ^ 2) (x : V) :
    LatticeProb.Graph.laplacian G (heatFlowG G D s f) x =
      ∑' z, LatticeProb.Graph.laplacian G (fun w => vsrwHeat G D s w z) x * f z := by
  have hs' := fun w => summable_vsrwHeat_mul_l2 hD hdeg hs hf w
  unfold LatticeProb.Graph.laplacian heatFlowG
  calc ∑ w ∈ G.neighborFinset x,
        (∑' z, vsrwHeat G D s w z * f z - ∑' z, vsrwHeat G D s x z * f z)
      = ∑ w ∈ G.neighborFinset x, ∑' z, (vsrwHeat G D s w z - vsrwHeat G D s x z) * f z :=
        Finset.sum_congr rfl fun w _ => by
          rw [← (hs' w).tsum_sub (hs' x)]
          exact tsum_congr fun z => by ring
    _ = ∑' z, ∑ w ∈ G.neighborFinset x, (vsrwHeat G D s w z - vsrwHeat G D s x z) * f z :=
        (Summable.tsum_finsetSum fun w _ => ((hs' w).sub (hs' x)).congr fun z => by ring).symm
    _ = _ := tsum_congr fun z => by rw [Finset.sum_mul]

theorem abs_laplacian_vsrwHeat_le (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) {s T : ℝ}
    (hs : 0 ≤ s) (hsT : s ≤ T) (x z : V) :
    |LatticeProb.Graph.laplacian G (fun w => vsrwHeat G D s w z) x| ≤
      Real.exp (2 * D * T) * ∑ w ∈ G.neighborFinset x,
        (vsrwHeat G D (2 * T) w z + vsrwHeat G D (2 * T) x z) := by
  unfold LatticeProb.Graph.laplacian
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w _ => ?_)
  have h1 := vsrwHeat_le_exp_mul hD hdeg hs hsT w z
  have h2 := vsrwHeat_le_exp_mul hD hdeg hs hsT x z
  have h3 := vsrwHeat_nonneg hD hdeg hs w z
  have h4 := vsrwHeat_nonneg hD hdeg hs x z
  rw [mul_add, abs_le]
  constructor <;> linarith

/-- **The heat equation** `∂_s P_s f = Δ P_s f` on `ℓ²`, for `s ∈ (0, T)`. -/
theorem hasDerivAt_heatFlowG (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) {f : V → ℝ}
    (hf : Summable fun z => f z ^ 2) {T s : ℝ} (hs : s ∈ Set.Ioo 0 T) (x : V) :
    HasDerivAt (fun r => heatFlowG G D r f x)
      (LatticeProb.Graph.laplacian G (heatFlowG G D s f) x) s := by
  have h2T : (0 : ℝ) ≤ 2 * T := by linarith [hs.1, hs.2]
  have hfa : Summable fun z => |f z| ^ 2 := by simpa only [sq_abs] using hf
  set b : V → ℝ := fun z => (Real.exp (2 * D * T) * ∑ w ∈ G.neighborFinset x,
      (vsrwHeat G D (2 * T) w z + vsrwHeat G D (2 * T) x z)) * |f z| with hb
  have hbs : Summable b := by
    have ha := fun w => summable_vsrwHeat_mul_l2 hD hdeg h2T hfa w
    have h := (summable_sum (s := G.neighborFinset x) fun w _ =>
      (ha w).add (ha x)).mul_left (Real.exp (2 * D * T))
    refine h.congr fun z => ?_
    simp only [hb, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun w _ => by ring
  have key := hasDerivAt_tsum_of_isPreconnected (u := b) hbs isOpen_Ioo isPreconnected_Ioo
    (t := Set.Ioo 0 T) (y₀ := s)
    (g := fun z r => vsrwHeat G D r x z * f z)
    (g' := fun z r => LatticeProb.Graph.laplacian G (fun w => vsrwHeat G D r w z) x * f z)
    (fun z r _ => (hasDerivAt_vsrwHeat hD hdeg r x z).mul_const (f z))
    (fun z r hr => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (abs_laplacian_vsrwHeat_le hD hdeg hr.1.le hr.2.le x z)
        (abs_nonneg _))
    hs (summable_vsrwHeat_mul_l2 hD hdeg hs.1.le hf x) hs
  rw [laplacian_heatFlowG_eq hD hdeg hs.1.le hf x]
  exact key

/-- The heat flow is continuous in time on `[0, T]`. -/
theorem continuousOn_heatFlowG (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) {f : V → ℝ}
    (hf : Summable fun z => f z ^ 2) {T : ℝ} (hT : 0 ≤ T) (x : V) :
    ContinuousOn (fun r => heatFlowG G D r f x) (Set.Icc 0 T) := by
  have h2T : 0 ≤ 2 * T := by linarith
  have hfa : Summable fun z => |f z| ^ 2 := by simpa only [sq_abs] using hf
  have hc : ∀ z, Continuous fun r => vsrwHeat G D r x z := fun z =>
    continuous_iff_continuousAt.2 fun r => (hasDerivAt_vsrwHeat hD hdeg r x z).continuousAt
  refine continuousOn_tsum (fun z => ((hc z).mul continuous_const).continuousOn)
    ((summable_vsrwHeat_mul_l2 hD hdeg h2T hfa x).mul_left (Real.exp (2 * D * T)))
    fun z r hr => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (vsrwHeat_nonneg hD hdeg hr.1 x z), ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (vsrwHeat_le_exp_mul hD hdeg hr.1 hr.2 x z) (abs_nonneg _)

end Graph

variable {d : ℕ}

/-! ### Gaussian sums on `ℤ^d` -/

theorem summable_exp_neg_sq_edzD {c : ℝ} (hc : 0 < c) (y : Vertex d) :
    Summable fun x : Vertex d => Real.exp (-(‖edzD x y‖ ^ 2 / c)) := by
  have h := (summable_gaussianHeatD (d := d) (σ := c / 2) (t := 1) (by positivity) one_pos
    y).mul_left ((2 * Real.pi * (c / 2) * 1) ^ ((d : ℝ) / 2))
  refine h.congr fun x => ?_
  unfold gaussianHeatD
  rw [← mul_assoc, ← Real.rpow_add (by positivity), add_neg_cancel, Real.rpow_zero, one_mul]
  congr 3
  ring

/-- `Σ_x exp(-|x - y|²/(c r)) ≤ C r^{d/2}` for `r ≥ 1`. -/
theorem tsum_exp_neg_sq_edzD_le {c r : ℝ} (hc : 0 < c) (hr : 1 ≤ r) (y : Vertex d) :
    ∑' x : Vertex d, Real.exp (-(‖edzD x y‖ ^ 2 / (c * r))) ≤
      (Real.pi * c) ^ ((d : ℝ) / 2) * gaussMassBoundD d (c / 2) * r ^ ((d : ℝ) / 2) := by
  have hr0 : 0 < r := by linarith
  have e : ∀ x : Vertex d, Real.exp (-(‖edzD x y‖ ^ 2 / (c * r))) =
      (2 * Real.pi * (c / 2) * r) ^ ((d : ℝ) / 2) * gaussianHeatD d (c / 2) r (edzD x y) := by
    intro x
    unfold gaussianHeatD
    rw [← mul_assoc, ← Real.rpow_add (by positivity), add_neg_cancel, Real.rpow_zero, one_mul]
    congr 3
    ring
  rw [tsum_congr e, tsum_mul_left]
  have h := tsum_gaussianHeatD_le (d := d) (σ := c / 2) (by positivity) hr y
  have hsplit : (2 * Real.pi * (c / 2) * r) ^ ((d : ℝ) / 2) =
      (Real.pi * c) ^ ((d : ℝ) / 2) * r ^ ((d : ℝ) / 2) := by
    rw [show 2 * Real.pi * (c / 2) * r = (Real.pi * c) * r by ring]
    exact Real.mul_rpow (by positivity) hr0.le
  rw [hsplit]
  calc (Real.pi * c) ^ ((d : ℝ) / 2) * r ^ ((d : ℝ) / 2) *
        ∑' x, gaussianHeatD d (c / 2) r (edzD x y)
      ≤ (Real.pi * c) ^ ((d : ℝ) / 2) * r ^ ((d : ℝ) / 2) * gaussMassBoundD d (c / 2) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

/-- `(a + v)² exp(-v²/c) ≤ (2a² + 2 √c √(2c)) exp(-v²/(4c))`. -/
theorem sq_add_mul_exp_le {a v c : ℝ} (hv : 0 ≤ v) (hc : 0 < c) :
    (a + v) ^ 2 * Real.exp (-(v ^ 2 / c)) ≤
      (2 * a ^ 2 + 2 * (Real.sqrt c * Real.sqrt (2 * c))) * Real.exp (-(v ^ 2 / (4 * c))) := by
  have h1 := mul_exp_neg_sq_le hc hv
  have h2 := mul_exp_neg_sq_le (by positivity : 0 < 2 * c) hv
  rw [show 2 * (2 * c) = 4 * c by ring] at h2
  have h3 : Real.exp (-(v ^ 2 / c)) ≤ Real.exp (-(v ^ 2 / (4 * c))) := by
    rw [Real.exp_le_exp, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left (sq_nonneg v) hc (by linarith)
  have hsc := Real.sqrt_nonneg c
  have hsq : v ^ 2 * Real.exp (-(v ^ 2 / c)) ≤
      Real.sqrt c * Real.sqrt (2 * c) * Real.exp (-(v ^ 2 / (4 * c))) := by
    calc v ^ 2 * Real.exp (-(v ^ 2 / c)) = v * (v * Real.exp (-(v ^ 2 / c))) := by ring
      _ ≤ v * (Real.sqrt c * Real.exp (-(v ^ 2 / (2 * c)))) := mul_le_mul_of_nonneg_left h1 hv
      _ = Real.sqrt c * (v * Real.exp (-(v ^ 2 / (2 * c)))) := by ring
      _ ≤ Real.sqrt c * (Real.sqrt (2 * c) * Real.exp (-(v ^ 2 / (4 * c)))) :=
          mul_le_mul_of_nonneg_left h2 hsc
      _ = _ := by ring
  have hE := Real.exp_pos (-(v ^ 2 / c))
  have hsq2 : (a + v) ^ 2 ≤ 2 * a ^ 2 + 2 * v ^ 2 := by nlinarith [sq_nonneg (a - v)]
  calc (a + v) ^ 2 * Real.exp (-(v ^ 2 / c))
      ≤ (2 * a ^ 2 + 2 * v ^ 2) * Real.exp (-(v ^ 2 / c)) :=
        mul_le_mul_of_nonneg_right hsq2 hE.le
    _ = 2 * a ^ 2 * Real.exp (-(v ^ 2 / c)) + 2 * (v ^ 2 * Real.exp (-(v ^ 2 / c))) := by ring
    _ ≤ 2 * a ^ 2 * Real.exp (-(v ^ 2 / (4 * c))) +
          2 * (Real.sqrt c * Real.sqrt (2 * c) * Real.exp (-(v ^ 2 / (4 * c)))) := by
        gcongr
    _ = _ := by ring

/-- The Gaussian envelope `λ_c(x) = (1 + |x - y|) exp(-|x - y|²/c)`. -/
noncomputable def gaussEnvD (c : ℝ) (y x : Vertex d) : ℝ :=
  (1 + ‖edzD x y‖) * Real.exp (-(‖edzD x y‖ ^ 2 / c))

theorem gaussEnvD_nonneg (c : ℝ) (y x : Vertex d) : 0 ≤ gaussEnvD c y x := by
  unfold gaussEnvD
  positivity

theorem summable_sq_gaussEnvD {c : ℝ} (hc : 0 < c) (y : Vertex d) :
    Summable fun x => gaussEnvD c y x ^ 2 := by
  refine Summable.of_nonneg_of_le (fun x => sq_nonneg _) (fun x => ?_)
    ((summable_exp_neg_sq_edzD (c := 4 * (c / 2)) (by positivity) y).mul_left
      (2 * 1 ^ 2 + 2 * (Real.sqrt (c / 2) * Real.sqrt (2 * (c / 2)))))
  have h := sq_add_mul_exp_le (a := 1) (norm_nonneg (edzD x y)) (by positivity : 0 < c / 2)
  have e : gaussEnvD c y x ^ 2 =
      (1 + ‖edzD x y‖) ^ 2 * Real.exp (-(‖edzD x y‖ ^ 2 / (c / 2))) := by
    unfold gaussEnvD
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2
    push_cast
    ring
  rw [e]
  exact h

/-- The neighbour envelope `Σ_i (D(x + e_i) + D(x - e_i) + 2 D(x))` of `D`. -/
noncomputable def nbrEnvD (D : Vertex d → ℝ) (x : Vertex d) : ℝ :=
  ∑ i, (D (x + Pi.single i 1) + D (x - Pi.single i 1) + 2 * D x)

theorem nbrEnvD_nonneg {D : Vertex d → ℝ} (h : ∀ x, 0 ≤ D x) (x : Vertex d) :
    0 ≤ nbrEnvD D x :=
  Finset.sum_nonneg fun i _ => by
    have := h (x + Pi.single i 1)
    have := h (x - Pi.single i 1)
    have := h x
    positivity

theorem abs_openCondD_mul_sub_le (ω : Configuration d) (i : Fin d) (x : Vertex d) (a b : ℝ) :
    |openCondD ω i x * (a - b)| ≤ |a| + |b| := by
  rw [abs_mul]
  calc |openCondD ω i x| * |a - b| ≤ 1 * |a - b| :=
        mul_le_mul_of_nonneg_right (abs_openCondD_le ω i x) (abs_nonneg _)
    _ ≤ |a| + |b| := by
        rw [one_mul]
        exact abs_sub _ _

/-- The Laplacian of the open graph is dominated by the neighbour envelope. -/
theorem abs_openLaplacian_le_nbrEnvD (ω : Configuration d) {u D : Vertex d → ℝ}
    (h : ∀ x, |u x| ≤ D x) (x : Vertex d) : |openLaplacian ω u x| ≤ nbrEnvD D x := by
  rw [openLaplacian_eq_sumD]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  have a1 := abs_openCondD_mul_sub_le ω i x (u (x + Pi.single i 1)) (u x)
  have a2 := abs_openCondD_mul_sub_le ω i (x - Pi.single i 1) (u (x - Pi.single i 1)) (u x)
  have b1 := h (x + Pi.single i 1)
  have b2 := h (x - Pi.single i 1)
  have b3 := h x
  refine (abs_add_le _ _).trans ?_
  linarith

theorem summable_sq_nbrEnvD {D : Vertex d → ℝ} (hD : Summable fun x => D x ^ 2) :
    Summable fun x => nbrEnvD D x ^ 2 := by
  have hs : ∀ i : Fin d, Summable fun x =>
      3 * (D (x + Pi.single i 1) ^ 2 + D (x - Pi.single i 1) ^ 2 + 4 * D x ^ 2) := fun i =>
    (((summable_sq_add_shiftD hD (Pi.single i 1)).add (summable_sq_sub_shiftD hD (Pi.single i 1))).add
      (hD.mul_left 4)).mul_left 3
  refine Summable.of_nonneg_of_le (fun x => sq_nonneg _) (fun x => ?_)
    ((summable_sum fun i (_ : i ∈ Finset.univ) => hs i).mul_left (d : ℝ))
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d)))
    (f := fun i => D (x + Pi.single i 1) + D (x - Pi.single i 1) + 2 * D x)
  simp only [Finset.card_univ, Fintype.card_fin] at h
  refine h.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (by positivity))
  nlinarith [sq_nonneg (D (x + Pi.single i 1) - D (x - Pi.single i 1)),
    sq_nonneg (D (x + Pi.single i 1) - 2 * D x), sq_nonneg (D (x - Pi.single i 1) - 2 * D x)]

/-! ### The bounds of the two-scale expansion -/

theorem exp_neg_div_mono {σ r t q : ℝ} (hσ : 0 < σ) (hr : 0 < r) (hrt : r ≤ t) (hq : 0 ≤ q) :
    Real.exp (-(q / (32 * σ * r))) ≤ Real.exp (-(q / (32 * σ * t))) := by
  rw [Real.exp_le_exp, neg_le_neg_iff]
  exact div_le_div_of_nonneg_left hq (by positivity) (by nlinarith)

theorem scale_le_one {r : ℝ} (hr : 1 ≤ r) : r ^ (-((d : ℝ) / 2)) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos hr (by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith)

/-- A bound `K B exp(-q/(32σr))` with `0 ≤ B ≤ 1` and `1 ≤ r ≤ t` is at most
`K exp(-q/(32σt))`. -/
theorem bound_mono {σ r t q K B : ℝ} (hσ : 0 < σ) (hr : 1 ≤ r) (hrt : r ≤ t) (hq : 0 ≤ q)
    (hK : 0 ≤ K) (hB : B ≤ 1) :
    K * B * Real.exp (-(q / (32 * σ * r))) ≤ K * Real.exp (-(q / (32 * σ * t))) := by
  have h1 := exp_neg_div_mono hσ (by linarith) hrt hq
  have h2 := Real.exp_pos (-(q / (32 * σ * r)))
  calc K * B * Real.exp (-(q / (32 * σ * r))) ≤ K * 1 * Real.exp (-(q / (32 * σ * r))) := by
        gcongr
    _ ≤ K * Real.exp (-(q / (32 * σ * t))) := by
        rw [mul_one]
        exact mul_le_mul_of_nonneg_left h1 hK

theorem abs_twoScale_comb_le {P : Vertex d → ℝ} {χ : Fin d → Vertex d → ℝ} {M₀ M₁ A E v : ℝ}
    {x : Vertex d} (hP : |P x| ≤ M₀ * E) (hDP : ∀ k, |fwdDiffD k P x| ≤ M₁ * E)
    (hχ : ∀ k, |χ k x| ≤ A * (1 + v)) (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁) (hE : 0 ≤ E)
    (hv : 0 ≤ v) :
    |P x + ∑ k, fwdDiffD k P x * χ k x| ≤ (M₀ + d * M₁ * A) * ((1 + v) * E) := by
  have hsum : |∑ k, fwdDiffD k P x * χ k x| ≤ d * (M₁ * A * ((1 + v) * E)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k, |fwdDiffD k P x * χ k x| ≤ ∑ _k : Fin d, M₁ * A * ((1 + v) * E) := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [abs_mul]
          calc |fwdDiffD k P x| * |χ k x| ≤ (M₁ * E) * (A * (1 + v)) :=
                mul_le_mul (hDP k) (hχ k) (abs_nonneg _) (by positivity)
            _ = M₁ * A * ((1 + v) * E) := by ring
      _ = d * (M₁ * A * ((1 + v) * E)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hP' : M₀ * E ≤ M₀ * ((1 + v) * E) :=
    mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hE (by linarith)) hM₀
  calc |P x + ∑ k, fwdDiffD k P x * χ k x| ≤ |P x| + |∑ k, fwdDiffD k P x * χ k x| :=
        abs_add_le _ _
    _ ≤ M₀ * ((1 + v) * E) + d * (M₁ * A * ((1 + v) * E)) := by linarith
    _ = _ := by ring

/-- `|h(s, x, y)| ≤ |θ^{-1}| (K₀ + d K₁ A) λ_{32σt}(x)` for `1 ≤ s ≤ t`. -/
theorem abs_dgTwoScaleD_le {σ θ s t A : ℝ} {χ : Fin d → Vertex d → ℝ} {y x : Vertex d}
    (hσ : 0 < σ) (hs : 1 ≤ s) (hst : s ≤ t)
    (hχ : ∀ k, |χ k x| ≤ A * (1 + ‖edzD x y‖)) :
    |dgTwoScaleD σ θ χ s x y| ≤
      |θ⁻¹| * ((gaussConstD d σ 0 + d * gaussConstD d σ 1 * A) * gaussEnvD (32 * σ * t) y x) := by
  have hs0 : 0 < s := by linarith
  have hq := sq_nonneg ‖edzD x y‖
  have hP : |latticeGaussianD σ s x y| ≤
      gaussConstD d σ 0 * Real.exp (-(‖edzD x y‖ ^ 2 / (32 * σ * t))) := by
    refine (abs_latticeGaussianD_le hσ hs x y).trans ?_
    exact bound_mono hσ hs hst hq (gaussConstD_pos hσ 0).le (scale_le_one hs)
  have hDP : ∀ k, |fwdDiffD k (fun z => latticeGaussianD σ s z y) x| ≤
      gaussConstD d σ 1 * Real.exp (-(‖edzD x y‖ ^ 2 / (32 * σ * t))) := by
    intro k
    refine (abs_fwdDiffD_latticeGaussianD_le hσ hs k x y).trans ?_
    rw [mul_div_assoc]
    exact bound_mono hσ hs hst hq (gaussConstD_pos hσ 1).le
      (div_le_one_of_le₀ ((scale_le_one hs).trans (Real.one_le_sqrt.2 hs)) (by positivity))
  have h := abs_twoScale_comb_le (P := fun z => latticeGaussianD σ s z y) (χ := χ) hP hDP hχ
    (gaussConstD_pos hσ 0).le (gaussConstD_pos hσ 1).le (Real.exp_pos _).le (norm_nonneg _)
  unfold dgTwoScaleD gaussEnvD
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left h (abs_nonneg _)

/-- The bound of `∂_s h(s, x, y)` for `1 ≤ s ≤ t`. -/
theorem abs_dgTwoScaleD_deriv_le {σ θ s t A : ℝ} {χ : Fin d → Vertex d → ℝ} {y x : Vertex d}
    (hσ : 0 < σ) (hs : 1 ≤ s) (hst : s ≤ t)
    (hχ : ∀ k, |χ k x| ≤ A * (1 + ‖edzD x y‖)) :
    |θ⁻¹ * (latticeGaussianTimeDerivD σ s x y +
        ∑ k, fwdDiffD k (fun z => latticeGaussianTimeDerivD σ s z y) x * χ k x)| ≤
      |θ⁻¹| * ((σ / 2 * d * gaussConstD d σ 2 + d * (σ / 2 * d * gaussConstD d σ 3) * A) *
        gaussEnvD (32 * σ * t) y x) := by
  have hs0 : 0 < s := by linarith
  have hq := sq_nonneg ‖edzD x y‖
  have hsq1 : 1 ≤ Real.sqrt s := Real.one_le_sqrt.2 hs
  have hP : |latticeGaussianTimeDerivD σ s x y| ≤
      σ / 2 * d * gaussConstD d σ 2 * Real.exp (-(‖edzD x y‖ ^ 2 / (32 * σ * t))) := by
    refine (abs_latticeGaussianTimeDerivD_le hσ hs x y).trans ?_
    rw [mul_div_assoc]
    exact bound_mono hσ hs hst hq (by have := gaussConstD_pos (d := d) hσ 2; positivity)
      (div_le_one_of_le₀ ((scale_le_one hs).trans hs) (by positivity))
  have hDP : ∀ k, |fwdDiffD k (fun z => latticeGaussianTimeDerivD σ s z y) x| ≤
      σ / 2 * d * gaussConstD d σ 3 * Real.exp (-(‖edzD x y‖ ^ 2 / (32 * σ * t))) := by
    intro k
    refine (abs_fwdDiffD_latticeGaussianTimeDerivD_le hσ hs k x y).trans ?_
    rw [mul_div_assoc]
    exact bound_mono hσ hs hst hq (by have := gaussConstD_pos (d := d) hσ 3; positivity)
      (div_le_one_of_le₀ ((scale_le_one hs).trans
        (by nlinarith : (1 : ℝ) ≤ s * Real.sqrt s)) (by positivity))
  have h := abs_twoScale_comb_le (P := fun z => latticeGaussianTimeDerivD σ s z y) (χ := χ) hP hDP
    hχ (by have := gaussConstD_pos (d := d) hσ 2; positivity)
    (by have := gaussConstD_pos (d := d) hσ 3; positivity) (Real.exp_pos _).le (norm_nonneg _)
  unfold gaussEnvD
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left h (abs_nonneg _)

/-! ### The function `u` -/

/-- `f = 1_K h(τ, ·, y)`. -/
noncomputable def clusterInitD {ω : Configuration d} (K : OpenComponent ω) (σ θ : ℝ)
    (χ : Fin d → Vertex d → ℝ) (τ : ℝ) (y z : Vertex d) : ℝ :=
  if z ∈ K.supp then dgTwoScaleD σ θ χ τ z y else 0

/-- `u(s, x) = 1_K(x) (h(s, x, y) - P_{s-τ} f(x))`. -/
noncomputable def clusterWD {ω : Configuration d} (K : OpenComponent ω) (σ θ : ℝ)
    (χ : Fin d → Vertex d → ℝ) (τ : ℝ) (y : Vertex d) (s : ℝ) (x : Vertex d) : ℝ :=
  if x ∈ K.supp then
    dgTwoScaleD σ θ χ s x y - heatFlowG (openGraph ω) (2 * d) (s - τ)
      (clusterInitD K σ θ χ τ y) x else 0

/-- The source term `G = 1_K θ^{-1} twoScaleSourceD` of the equation of `u`. -/
noncomputable def clusterSourceD {ω : Configuration d} (K : OpenComponent ω) (σ θ : ℝ)
    (χ : Fin d → Vertex d → ℝ) (y : Vertex d) (s : ℝ) (x : Vertex d) : ℝ :=
  if x ∈ K.supp then θ⁻¹ * twoScaleSourceD ω σ χ s y x else 0

/-- `f` is square summable when the corrector grows at most linearly on the cluster. -/
theorem summable_sq_clusterInitD {ω : Configuration d} {K : OpenComponent ω} {σ θ τ A : ℝ}
    {χ : Fin d → Vertex d → ℝ} {y : Vertex d} (hσ : 0 < σ) (hτ : 1 ≤ τ)
    (hχ : ∀ x ∈ K.supp, ∀ k, |χ k x| ≤ A * (1 + ‖edzD x y‖)) :
    Summable fun z => clusterInitD K σ θ χ τ y z ^ 2 := by
  refine Summable.of_nonneg_of_le (fun z => sq_nonneg _) (fun z => ?_)
    ((summable_sq_gaussEnvD (c := 32 * σ * τ) (by nlinarith) y).mul_left
      ((|θ⁻¹| * (gaussConstD d σ 0 + d * gaussConstD d σ 1 * A)) ^ 2))
  unfold clusterInitD
  split_ifs with hz
  · rw [← mul_pow]
    refine sq_le_sq_of_abs_leD ((abs_dgTwoScaleD_le hσ hτ le_rfl (hχ z hz)).trans
      (le_of_eq (by ring)))
  · rw [zero_pow two_ne_zero]
    positivity

theorem two_mul_d_pos [NeZero d] : 0 < 2 * d := by
  have := NeZero.pos d
  omega

/-- The initial condition `u(τ, ·) = 0`. -/
theorem clusterWD_self {ω : Configuration d} (K : OpenComponent ω) (σ θ : ℝ)
    (χ : Fin d → Vertex d → ℝ) (τ : ℝ) (y x : Vertex d) : clusterWD K σ θ χ τ y τ x = 0 := by
  unfold clusterWD
  split_ifs with hx
  · rw [sub_self, heatFlowG_zero]
    unfold clusterInitD
    rw [if_pos hx, sub_self]
  · rfl

theorem openLaplacian_eq_laplacian (ω : Configuration d) (u : Vertex d → ℝ) (x : Vertex d) :
    openLaplacian ω u x = LatticeProb.Graph.laplacian (openGraph ω) u x := rfl

/-- The Laplacian of `u` at a point of the cluster. -/
theorem openLaplacian_clusterWD {ω : Configuration d} {K : OpenComponent ω} {σ θ τ s : ℝ}
    {χ : Fin d → Vertex d → ℝ} {y x : Vertex d} (hx : x ∈ K.supp) :
    openLaplacian ω (clusterWD K σ θ χ τ y s) x =
      openLaplacian ω (fun z => dgTwoScaleD σ θ χ s z y) x -
        openLaplacian ω (heatFlowG (openGraph ω) (2 * d) (s - τ) (clusterInitD K σ θ χ τ y)) x := by
  unfold openLaplacian
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun z hz => ?_
  have hzK : z ∈ K.supp :=
    mem_supp_of_openAdjD hx ((SimpleGraph.mem_neighborFinset _ _ _).1 hz)
  simp only [clusterWD, if_pos hx, if_pos hzK]
  ring

/-- `Δ u + G` at a point of the cluster, in terms of `∂_s h`. -/
theorem openLaplacian_clusterWD_add_source {ω : Configuration d} {K : OpenComponent ω}
    {y : Vertex d} {χ : Fin d → Vertex d → ℝ} (hχK : IsDGCorrectorD K y χ) {σ θ τ s : ℝ}
    (hσ : 0 < σ) (hs0 : 0 < s) {x : Vertex d} (hx : x ∈ K.supp) :
    openLaplacian ω (clusterWD K σ θ χ τ y s) x + clusterSourceD K σ θ χ y s x =
      θ⁻¹ * (latticeGaussianTimeDerivD σ s x y +
        ∑ k, fwdDiffD k (fun z => latticeGaussianTimeDerivD σ s z y) x * χ k x) -
        openLaplacian ω (heatFlowG (openGraph ω) (2 * d) (s - τ) (clusterInitD K σ θ χ τ y)) x := by
  have h1 := hasDerivAt_dgTwoScaleD_eq (θ := θ) hχK hσ hs0 hx
  have h2 := hasDerivAt_dgTwoScaleD_time (θ := θ) hσ hs0 χ x y
  have hu := h1.unique h2
  rw [openLaplacian_clusterWD hx, clusterSourceD, if_pos hx, ← hu]
  ring

/-- `Δ u + G = 0` off the cluster. -/
theorem openLaplacian_clusterWD_add_source_of_notMem {ω : Configuration d} {K : OpenComponent ω}
    {σ θ τ s : ℝ} {χ : Fin d → Vertex d → ℝ} {y x : Vertex d} (hx : x ∉ K.supp) :
    openLaplacian ω (clusterWD K σ θ χ τ y s) x + clusterSourceD K σ θ χ y s x = 0 := by
  rw [clusterSourceD, if_neg hx, add_zero]
  unfold openLaplacian
  refine Finset.sum_eq_zero fun z hz => ?_
  have hzK : z ∉ K.supp := fun hzK =>
    hx (mem_supp_of_openAdjD hzK ((SimpleGraph.mem_neighborFinset _ _ _).1 hz).symm)
  simp only [clusterWD, if_neg hx, if_neg hzK, sub_self]

/-- **The equation (4.25) of `w` on the cluster**: `∂_s u = Δ u + G` for `s - τ ∈ (0, T)`. -/
theorem hasDerivAt_clusterWD [NeZero d] {ω : Configuration d} {K : OpenComponent ω}
    {y : Vertex d} {χ : Fin d → Vertex d → ℝ} (hχK : IsDGCorrectorD K y χ) {σ θ τ s T : ℝ}
    (hσ : 0 < σ) (hf : Summable fun z => clusterInitD K σ θ χ τ y z ^ 2)
    (hs : s - τ ∈ Set.Ioo 0 T) (hs0 : 0 < s) (x : Vertex d) :
    HasDerivAt (fun r => clusterWD K σ θ χ τ y r x)
      (openLaplacian ω (clusterWD K σ θ χ τ y s) x + clusterSourceD K σ θ χ y s x) s := by
  by_cases hx : x ∈ K.supp
  · have h1 := hasDerivAt_dgTwoScaleD_time (θ := θ) hσ hs0 χ x y
    have h2 := (hasDerivAt_heatFlowG two_mul_d_pos (openGraph_degree_le ω) hf hs x).comp_sub_const
      s τ
    have e : (fun r => clusterWD K σ θ χ τ y r x) = fun r =>
        dgTwoScaleD σ θ χ r x y -
          heatFlowG (openGraph ω) (2 * d) (r - τ) (clusterInitD K σ θ χ τ y) x :=
      funext fun r => by simp only [clusterWD, if_pos hx]
    rw [e, openLaplacian_clusterWD_add_source hχK hσ hs0 hx, openLaplacian_eq_laplacian]
    exact h1.sub h2
  · have e : (fun r => clusterWD K σ θ χ τ y r x) = fun _ => 0 :=
      funext fun r => by simp only [clusterWD, if_neg hx]
    rw [e, openLaplacian_clusterWD_add_source_of_notMem hx]
    exact hasDerivAt_const s (0 : ℝ)

/-- **Domination of `u` on `[τ, t]`.** -/
theorem exists_clusterWD_dom [NeZero d] {ω : Configuration d} {K : OpenComponent ω}
    {σ θ τ t A : ℝ} {χ : Fin d → Vertex d → ℝ} {y : Vertex d} (hσ : 0 < σ) (hτ : 1 ≤ τ)
    (hτt : τ ≤ t) (hA : 0 ≤ A) (hχ : ∀ x ∈ K.supp, ∀ k, |χ k x| ≤ A * (1 + ‖edzD x y‖)) :
    ∃ D : Vertex d → ℝ, Summable (fun x => D x ^ 2) ∧
      ∀ s ∈ Set.Icc τ t, ∀ x, |clusterWD K σ θ χ τ y s x| ≤ D x := by
  have hf := summable_sq_clusterInitD (θ := θ) hσ hτ hχ
  have hfa : Summable fun z => |clusterInitD K σ θ χ τ y z| ^ 2 := by
    simpa only [sq_abs] using hf
  have hT : 0 ≤ 2 * (t - τ) := by linarith
  have hdeg := openGraph_degree_le ω
  set c₁ := |θ⁻¹| * (gaussConstD d σ 0 + d * gaussConstD d σ 1 * A) with hc₁
  set E : Vertex d → ℝ := fun z => Real.exp (2 * ((2 * d : ℕ) : ℝ) * (t - τ)) *
    heatFlowG (openGraph ω) (2 * d) (2 * (t - τ)) (fun z => |clusterInitD K σ θ χ τ y z|) z
    with hE
  have hg0 := gaussConstD_pos (d := d) hσ 0
  have hg1 := gaussConstD_pos (d := d) hσ 1
  have hg2 := gaussConstD_pos (d := d) hσ 2
  have hg3 := gaussConstD_pos (d := d) hσ 3
  have hE0 : ∀ z, 0 ≤ E z := fun z => by
    have := heatFlowG_nonneg two_mul_d_pos hdeg hT
      (fun w => abs_nonneg (clusterInitD K σ θ χ τ y w)) z
    simp only [hE]
    positivity
  refine ⟨fun x => c₁ * gaussEnvD (32 * σ * t) y x + E x, ?_, ?_⟩
  · refine summable_sq_addD ?_ ?_
    · simpa only [mul_pow] using (summable_sq_gaussEnvD (c := 32 * σ * t) (by nlinarith)
        y).mul_left (c₁ ^ 2)
    · simpa only [hE, mul_pow] using (summable_sq_heatFlowG two_mul_d_pos hdeg hT hfa).mul_left
        (Real.exp (2 * ((2 * d : ℕ) : ℝ) * (t - τ)) ^ 2)
  · intro s hs x
    have h0 : 0 ≤ c₁ * gaussEnvD (32 * σ * t) y x + E x := by
      have hc₁0 : 0 ≤ c₁ := by rw [hc₁]; positivity
      have := gaussEnvD_nonneg (32 * σ * t) y x
      have := hE0 x
      positivity
    unfold clusterWD
    split_ifs with hx
    · have h1 := abs_dgTwoScaleD_le (θ := θ) hσ (hτ.trans hs.1) hs.2 (hχ x hx)
      have h2 := abs_heatFlowG_le_exp two_mul_d_pos hdeg (by linarith [hs.1] : 0 ≤ s - τ)
        (by linarith [hs.2] : s - τ ≤ t - τ) hf x
      have h3 := abs_sub (dgTwoScaleD σ θ χ s x y)
        (heatFlowG (openGraph ω) (2 * d) (s - τ) (clusterInitD K σ θ χ τ y) x)
      have e1 : |θ⁻¹| * ((gaussConstD d σ 0 + d * gaussConstD d σ 1 * A) *
          gaussEnvD (32 * σ * t) y x) = c₁ * gaussEnvD (32 * σ * t) y x := by
        rw [hc₁]; ring
      simp only [hE]
      linarith
    · rw [abs_zero]
      exact h0

/-- **Domination of `∂_s u = Δ u + G` on `(τ, t]`.** -/
theorem exists_clusterWD_deriv_dom [NeZero d] {ω : Configuration d} {K : OpenComponent ω}
    {σ θ τ t A : ℝ} {χ : Fin d → Vertex d → ℝ} {y : Vertex d} (hχK : IsDGCorrectorD K y χ)
    (hσ : 0 < σ) (hτ : 1 ≤ τ) (hτt : τ ≤ t) (hA : 0 ≤ A)
    (hχ : ∀ x ∈ K.supp, ∀ k, |χ k x| ≤ A * (1 + ‖edzD x y‖)) :
    ∃ D : Vertex d → ℝ, Summable (fun x => D x ^ 2) ∧
      ∀ s ∈ Set.Ioc τ t, ∀ x,
        |openLaplacian ω (clusterWD K σ θ χ τ y s) x + clusterSourceD K σ θ χ y s x| ≤ D x := by
  have hf := summable_sq_clusterInitD (θ := θ) hσ hτ hχ
  have hfa : Summable fun z => |clusterInitD K σ θ χ τ y z| ^ 2 := by
    simpa only [sq_abs] using hf
  have hT : 0 ≤ 2 * (t - τ) := by linarith
  have hdeg := openGraph_degree_le ω
  set c₂ := |θ⁻¹| * (σ / 2 * d * gaussConstD d σ 2 + d * (σ / 2 * d * gaussConstD d σ 3) * A)
    with hc₂
  set E : Vertex d → ℝ := fun z => Real.exp (2 * ((2 * d : ℕ) : ℝ) * (t - τ)) *
    heatFlowG (openGraph ω) (2 * d) (2 * (t - τ)) (fun z => |clusterInitD K σ θ χ τ y z|) z
    with hE
  have hg0 := gaussConstD_pos (d := d) hσ 0
  have hg1 := gaussConstD_pos (d := d) hσ 1
  have hg2 := gaussConstD_pos (d := d) hσ 2
  have hg3 := gaussConstD_pos (d := d) hσ 3
  have hE0 : ∀ z, 0 ≤ E z := fun z => by
    have := heatFlowG_nonneg two_mul_d_pos hdeg hT
      (fun w => abs_nonneg (clusterInitD K σ θ χ τ y w)) z
    simp only [hE]
    positivity
  refine ⟨fun x => c₂ * gaussEnvD (32 * σ * t) y x + nbrEnvD E x, ?_, ?_⟩
  · refine summable_sq_addD ?_ (summable_sq_nbrEnvD ?_)
    · simpa only [mul_pow] using (summable_sq_gaussEnvD (c := 32 * σ * t) (by nlinarith)
        y).mul_left (c₂ ^ 2)
    · simpa only [hE, mul_pow] using (summable_sq_heatFlowG two_mul_d_pos hdeg hT hfa).mul_left
        (Real.exp (2 * ((2 * d : ℕ) : ℝ) * (t - τ)) ^ 2)
  · intro s hs x
    have hs1 : 1 ≤ s := hτ.trans hs.1.le
    have hs0 : 0 < s := by linarith
    have h0 : 0 ≤ c₂ * gaussEnvD (32 * σ * t) y x + nbrEnvD E x := by
      have hc₂0 : 0 ≤ c₂ := by rw [hc₂]; positivity
      have := gaussEnvD_nonneg (32 * σ * t) y x
      have := nbrEnvD_nonneg hE0 x
      positivity
    by_cases hx : x ∈ K.supp
    · rw [openLaplacian_clusterWD_add_source hχK hσ hs0 hx]
      have h1 := abs_dgTwoScaleD_deriv_le (θ := θ) hσ hs1 hs.2 (hχ x hx)
      have h2 := abs_openLaplacian_le_nbrEnvD ω
        (u := heatFlowG (openGraph ω) (2 * d) (s - τ) (clusterInitD K σ θ χ τ y))
        (D := E) (fun z => abs_heatFlowG_le_exp two_mul_d_pos hdeg (by linarith [hs.1] : 0 ≤ s - τ)
          (by linarith [hs.2] : s - τ ≤ t - τ) hf z) x
      have e1 : |θ⁻¹| * ((σ / 2 * d * gaussConstD d σ 2 + d * (σ / 2 * d * gaussConstD d σ 3) * A) *
          gaussEnvD (32 * σ * t) y x) = c₂ * gaussEnvD (32 * σ * t) y x := by
        rw [hc₂]; ring
      refine (abs_sub _ _).trans ?_
      linarith
    · rw [openLaplacian_clusterWD_add_source_of_notMem hx, abs_zero]
      exact h0

/-- `u(·, x)` is continuous on `[τ, t]`. -/
theorem continuousOn_clusterWD [NeZero d] {ω : Configuration d} {K : OpenComponent ω}
    {σ θ τ t : ℝ} {χ : Fin d → Vertex d → ℝ} {y : Vertex d} (hσ : 0 < σ) (hτ : 0 < τ)
    (hf : Summable fun z => clusterInitD K σ θ χ τ y z ^ 2) (x : Vertex d) :
    ContinuousOn (fun s => clusterWD K σ θ χ τ y s x) (Set.Icc τ t) := by
  by_cases hx : x ∈ K.supp
  · have e : (fun s => clusterWD K σ θ χ τ y s x) = fun s =>
        dgTwoScaleD σ θ χ s x y -
          heatFlowG (openGraph ω) (2 * d) (s - τ) (clusterInitD K σ θ χ τ y) x :=
      funext fun s => by simp only [clusterWD, if_pos hx]
    rw [e]
    refine ContinuousOn.sub (fun s hs => ?_) ?_
    · exact (hasDerivAt_dgTwoScaleD_time (θ := θ) hσ (hτ.trans_le hs.1) χ x y).continuousAt
        |>.continuousWithinAt
    · rcases le_total τ t with hτt | hτt
      · refine (continuousOn_heatFlowG two_mul_d_pos (openGraph_degree_le ω) hf
          (by linarith : 0 ≤ t - τ) x).comp (continuousOn_id.sub continuousOn_const)
          fun s hs => ?_
        exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
      · refine (continuousOn_heatFlowG two_mul_d_pos (openGraph_degree_le ω) hf le_rfl x).comp
          (continuousOn_id.sub continuousOn_const) fun s hs => ?_
        exact ⟨by linarith [hs.1], by linarith [hs.1, hs.2]⟩
  · have e : (fun s => clusterWD K σ θ χ τ y s x) = fun _ => 0 :=
      funext fun s => by simp only [clusterWD, if_neg hx]
    rw [e]
    exact continuousOn_const

/-- The energy `Σ_x u(s, x)²` is continuous on `[τ, t]`. -/
theorem continuousOn_tsum_sq_clusterWD [NeZero d] {ω : Configuration d} {K : OpenComponent ω}
    {σ θ τ t A : ℝ} {χ : Fin d → Vertex d → ℝ} {y : Vertex d} (hσ : 0 < σ) (hτ : 1 ≤ τ)
    (hτt : τ ≤ t) (hA : 0 ≤ A) (hχ : ∀ x ∈ K.supp, ∀ k, |χ k x| ≤ A * (1 + ‖edzD x y‖)) :
    ContinuousOn (fun s => ∑' x, clusterWD K σ θ χ τ y s x ^ 2) (Set.Icc τ t) := by
  obtain ⟨D, hD, hDu⟩ := exists_clusterWD_dom (θ := θ) hσ hτ hτt hA hχ
  have hf := summable_sq_clusterInitD (θ := θ) hσ hτ hχ
  refine continuousOn_tsum (fun x => (continuousOn_clusterWD hσ (by linarith) hf x).pow 2) hD
    fun x s hs => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact sq_le_sq_of_abs_leD (hDu s hs x)

end Rigidity.Green.GeneralDim
