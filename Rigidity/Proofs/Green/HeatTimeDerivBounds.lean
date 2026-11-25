import Rigidity.Proofs.Green.OpenHeatSemigroup

/-!
# Time derivatives of the heat kernel

Let `G` be a locally finite graph with degrees at most `D > 0` and `p_t = vsrwHeat G D t` the heat
kernel of the variable speed random walk. `heatDeriv G D k t x y` is the `k`-th power of the
Laplacian in the first variable applied to `p_t(·, y)`, at `x`. It is the `k`-th time derivative
of `t ↦ p_t(x, y)` (`hasDerivAt_heatDeriv`, `heatDeriv_eq_iteratedDeriv`), hence symmetric in `x`
and `y` (`heatDeriv_symm`), and the semigroup property differentiates to

  `Σ_w ∂^i p_a(x, w) ∂^j p_b(w, y) = ∂^{i+j} p_{a+b}(x, y)`  (`hasSum_heatDeriv_mul`).

On the diagonal, `m(r) = p_r(z, z)` therefore satisfies `m^{(2i)}(2a) = Σ_w (∂^i p_a(z, w))² ≥ 0`
and `m^{(2i+1)}(2a) = Σ_w g(w) Δg(w) ≤ 0` with `g = ∂^i p_a(z, ·)` (the Dirichlet form,
`hasSum_mul_laplacian_nonpos`). The monotonicity of `m'` and `m''` gives `-m'(r) ≤ 2 m(r/2)/r` and
`m''(r) ≤ 8 m(r/4)/r²`, and the Cauchy–Schwarz inequality in `p_s = P_{s/2} P_{s/2}` bounds the
second time derivative:

  `|∂_s² p_s(z, x)| ≤ 8 s^{-2} (p_{s/4}(z, z) p_{s/4}(x, x))^{1/2}`  (`abs_heatDeriv_two_le`).

With the diagonal bound `p_t(z, z) ≤ C t^{-d/2}` this is the bound `|∂_s² p_s| ≤ C s^{-d/2-2}` used in
the proof of the gradient bound of Dario–Gu (Theorem 3), in place of the spectral bound
`‖Δ² P_{s/2}‖_{2→2} ≤ C s^{-2}`.
-/

open scoped Classical
open Finset

namespace Rigidity.Green

section Defs

variable {V : Type*} (G : SimpleGraph V) [G.LocallyFinite] (D : ℕ)

/-- `∂_t^k p_t(x, y) = (Δ^k p_t(·, y))(x)`: the `k`-th power of the Laplacian in the first
variable applied to the heat kernel. -/
noncomputable def heatDeriv : ℕ → ℝ → V → V → ℝ
  | 0 => fun t x y => vsrwHeat G D t x y
  | k + 1 => fun t x y => ∑ z ∈ G.neighborFinset x, (heatDeriv k t z y - heatDeriv k t x y)

end Defs

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] {D : ℕ}

theorem heatDeriv_zero (t : ℝ) (x y : V) : heatDeriv G D 0 t x y = vsrwHeat G D t x y := rfl

theorem heatDeriv_succ (k : ℕ) (t : ℝ) (x y : V) :
    heatDeriv G D (k + 1) t x y =
      ∑ z ∈ G.neighborFinset x, (heatDeriv G D k t z y - heatDeriv G D k t x y) := rfl

/-- `∂_t (∂_t^k p_t(x, y)) = ∂_t^{k+1} p_t(x, y)`. -/
theorem hasDerivAt_heatDeriv (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) (k : ℕ) (t : ℝ)
    (x y : V) : HasDerivAt (fun t => heatDeriv G D k t x y) (heatDeriv G D (k + 1) t x y) t := by
  induction k generalizing x with
  | zero => exact hasDerivAt_vsrwHeat hD hdeg t x y
  | succ k ih =>
    show HasDerivAt
      (fun t => ∑ z ∈ G.neighborFinset x, (heatDeriv G D k t z y - heatDeriv G D k t x y))
      (∑ z ∈ G.neighborFinset x, (heatDeriv G D (k + 1) t z y - heatDeriv G D (k + 1) t x y)) t
    exact HasDerivAt.fun_sum fun z _ => (ih z).fun_sub (ih x)

theorem continuous_heatDeriv (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) (k : ℕ) (x y : V) :
    Continuous fun t => heatDeriv G D k t x y :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_heatDeriv hD hdeg k t x y).continuousAt

/-- `heatDeriv G D k · x y` is the `k`-th derivative of `t ↦ p_t(x, y)`. -/
theorem heatDeriv_eq_iteratedDeriv (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) (k : ℕ) (x y : V) :
    (fun t => heatDeriv G D k t x y) = iteratedDeriv k (fun t => vsrwHeat G D t x y) := by
  induction k with
  | zero => rw [iteratedDeriv_zero]; rfl
  | succ k ih =>
    rw [iteratedDeriv_succ, ← ih]
    funext t
    exact (hasDerivAt_heatDeriv hD hdeg k t x y).deriv.symm

theorem heatDeriv_symm (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) (k : ℕ) (t : ℝ) (x y : V) :
    heatDeriv G D k t x y = heatDeriv G D k t y x := by
  have h1 := congrFun (heatDeriv_eq_iteratedDeriv hD hdeg k x y) t
  have h2 := congrFun (heatDeriv_eq_iteratedDeriv hD hdeg k y x) t
  have h3 : (fun t => vsrwHeat G D t x y) = fun t => vsrwHeat G D t y x :=
    funext fun t => vsrwHeat_symm hD hdeg t x y
  rw [h1, h2, h3]

/-- The Laplacian in the second variable: `Δ_y ∂^k p_t(x, ·) = ∂^{k+1} p_t(x, y)`. -/
theorem heatDeriv_succ_right (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) (k : ℕ) (t : ℝ)
    (x y : V) : heatDeriv G D (k + 1) t x y =
      ∑ w ∈ G.neighborFinset y, (heatDeriv G D k t x w - heatDeriv G D k t x y) := by
  rw [heatDeriv_symm hD hdeg (k + 1), heatDeriv_succ]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [heatDeriv_symm hD hdeg k t w x, heatDeriv_symm hD hdeg k t y x]

/-! ### The differentiated semigroup property -/

theorem hasSum_heatDeriv_mul_vsrwHeat (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) (i : ℕ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (x y : V) :
    HasSum (fun w => heatDeriv G D i a x w * vsrwHeat G D b w y)
      (heatDeriv G D i (a + b) x y) := by
  induction i generalizing x with
  | zero => exact hasSum_vsrwHeat_mul hD hdeg ha hb x y
  | succ i ih =>
    have hf : (fun w => heatDeriv G D (i + 1) a x w * vsrwHeat G D b w y) = fun w =>
        ∑ z ∈ G.neighborFinset x, (heatDeriv G D i a z w * vsrwHeat G D b w y -
          heatDeriv G D i a x w * vsrwHeat G D b w y) := by
      funext w
      rw [heatDeriv_succ, Finset.sum_mul]
      exact Finset.sum_congr rfl fun z _ => sub_mul _ _ _
    rw [hf, heatDeriv_succ]
    exact hasSum_sum fun z _ => (ih z).sub (ih x)

/-- **The differentiated semigroup property**:
`Σ_w ∂^i p_a(x, w) ∂^j p_b(w, y) = ∂^{i+j} p_{a+b}(x, y)` for `a, b ≥ 0`. -/
theorem hasSum_heatDeriv_mul (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) (i j : ℕ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (x y : V) :
    HasSum (fun w => heatDeriv G D i a x w * heatDeriv G D j b w y)
      (heatDeriv G D (i + j) (a + b) x y) := by
  induction i generalizing x with
  | zero =>
    have h := hasSum_heatDeriv_mul_vsrwHeat hD hdeg j hb ha y x
    have hf : (fun w => heatDeriv G D 0 a x w * heatDeriv G D j b w y) =
        fun w => heatDeriv G D j b y w * vsrwHeat G D a w x := by
      funext w
      rw [heatDeriv_zero, vsrwHeat_symm hD hdeg a x w, heatDeriv_symm hD hdeg j b w y, mul_comm]
    rw [hf, zero_add, add_comm a b, heatDeriv_symm hD hdeg j (b + a) x y]
    exact h
  | succ i ih =>
    have hf : (fun w => heatDeriv G D (i + 1) a x w * heatDeriv G D j b w y) = fun w =>
        ∑ z ∈ G.neighborFinset x, (heatDeriv G D i a z w * heatDeriv G D j b w y -
          heatDeriv G D i a x w * heatDeriv G D j b w y) := by
      funext w
      rw [heatDeriv_succ, Finset.sum_mul]
      exact Finset.sum_congr rfl fun z _ => sub_mul _ _ _
    rw [hf, show i + 1 + j = (i + j) + 1 by ring, heatDeriv_succ]
    exact hasSum_sum fun z _ => (ih z).sub (ih x)

/-! ### The Dirichlet form -/

theorem hasSum_of_tsum_ofReal_eq {ι : Type*} {F : ι → ℝ} (hF : ∀ i, 0 ≤ F i) {T : ℝ}
    (hT : 0 ≤ T) (h : ∑' i, ENNReal.ofReal (F i) = ENNReal.ofReal T) : HasSum F T := by
  have hs : Summable F := by
    have := ENNReal.summable_toReal (f := fun i => ENNReal.ofReal (F i))
      (by rw [h]; exact ENNReal.ofReal_ne_top)
    simpa [ENNReal.toReal_ofReal (hF _)] using this
  rw [hs.hasSum_iff]
  have := ENNReal.ofReal_tsum_of_nonneg hF hs
  rw [h] at this
  exact (ENNReal.ofReal_eq_ofReal_iff (tsum_nonneg hF) hT).1 this

theorem summable_degree_mul (hdeg : ∀ x, G.degree x ≤ D) {f : V → ℝ} (hf0 : ∀ w, 0 ≤ f w)
    (hf : Summable f) : Summable fun w => (G.degree w : ℝ) * f w :=
  (hf.mul_left (D : ℝ)).of_nonneg_of_le (fun w => mul_nonneg (Nat.cast_nonneg _) (hf0 w))
    (fun w => mul_le_mul_of_nonneg_right (by exact_mod_cast hdeg w) (hf0 w))

/-- Counting each edge from both ends: `Σ_w Σ_{u ∼ w} f(u) = Σ_u deg(u) f(u)` for `f ≥ 0`. -/
theorem hasSum_sum_neighborFinset (hdeg : ∀ x, G.degree x ≤ D) {f : V → ℝ} (hf0 : ∀ w, 0 ≤ f w)
    (hf : Summable f) :
    HasSum (fun w => ∑ u ∈ G.neighborFinset w, f u) (∑' u, (G.degree u : ℝ) * f u) := by
  have hs := summable_degree_mul hdeg hf0 hf
  refine hasSum_of_tsum_ofReal_eq (fun w => Finset.sum_nonneg fun u _ => hf0 u)
    (tsum_nonneg fun u => mul_nonneg (Nat.cast_nonneg _) (hf0 u)) ?_
  rw [ENNReal.ofReal_tsum_of_nonneg (fun u => mul_nonneg (Nat.cast_nonneg _) (hf0 u)) hs]
  have h1 : ∀ w, ENNReal.ofReal (∑ u ∈ G.neighborFinset w, f u) =
      ∑' u, if G.Adj w u then ENNReal.ofReal (f u) else 0 := by
    intro w
    rw [ENNReal.ofReal_sum_of_nonneg (fun u _ => hf0 u),
      tsum_eq_sum (s := G.neighborFinset w) (fun u hu => by
        rw [SimpleGraph.mem_neighborFinset] at hu
        rw [if_neg hu])]
    exact Finset.sum_congr rfl fun u hu => by
      rw [if_pos ((G.mem_neighborFinset w u).1 hu)]
  have h2 : ∀ u, (∑' w, if G.Adj w u then ENNReal.ofReal (f u) else 0) =
      ENNReal.ofReal ((G.degree u : ℝ) * f u) := by
    intro u
    have hc : ∀ w ∈ G.neighborFinset u,
        (if G.Adj w u then ENNReal.ofReal (f u) else 0) = ENNReal.ofReal (f u) :=
      fun w hw => if_pos (G.adj_symm ((G.mem_neighborFinset u w).1 hw))
    rw [tsum_eq_sum (s := G.neighborFinset u) (fun w hw => by
        rw [SimpleGraph.mem_neighborFinset] at hw
        rw [if_neg fun h => hw (G.adj_symm h)]),
      Finset.sum_congr rfl hc, Finset.sum_const, G.card_neighborFinset_eq_degree, nsmul_eq_mul,
      ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  simp_rw [h1]
  rw [ENNReal.tsum_comm]
  simp_rw [h2]

/-- **The Dirichlet form is nonpositive**: `Σ_w g(w) Δg(w) ≤ 0` for square summable `g`. -/
theorem hasSum_mul_laplacian_nonpos (hdeg : ∀ x, G.degree x ≤ D) {g : V → ℝ}
    (hg : Summable fun w => g w ^ 2) {S : ℝ}
    (hS : HasSum (fun w => g w * ∑ u ∈ G.neighborFinset w, (g u - g w)) S) : S ≤ 0 := by
  have hA := hasSum_sum_neighborFinset hdeg (fun w => sq_nonneg (g w)) hg
  have hB := (summable_degree_mul hdeg (fun w => sq_nonneg (g w)) hg).hasSum
  have hle : ∀ w, g w * ∑ u ∈ G.neighborFinset w, (g u - g w) ≤
      1 / 2 * ∑ u ∈ G.neighborFinset w, g u ^ 2 - 1 / 2 * ((G.degree w : ℝ) * g w ^ 2) := by
    intro w
    have hu : ∀ u, g w * (g u - g w) ≤ 1 / 2 * g u ^ 2 - 1 / 2 * g w ^ 2 := fun u => by
      nlinarith [sq_nonneg (g u - g w)]
    rw [Finset.mul_sum]
    calc ∑ u ∈ G.neighborFinset w, g w * (g u - g w)
        ≤ ∑ u ∈ G.neighborFinset w, (1 / 2 * g u ^ 2 - 1 / 2 * g w ^ 2) :=
          Finset.sum_le_sum fun u _ => hu u
      _ = _ := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul,
            G.card_neighborFinset_eq_degree]
          ring
  have := hasSum_le hle hS ((hA.mul_left (1 / 2)).sub (hB.mul_left (1 / 2)))
  linarith

/-! ### The diagonal -/

theorem hasSum_heatDeriv_sq (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) (i : ℕ) {a : ℝ}
    (ha : 0 ≤ a) (z : V) :
    HasSum (fun w => heatDeriv G D i a z w ^ 2) (heatDeriv G D (i + i) (a + a) z z) := by
  have h := hasSum_heatDeriv_mul hD hdeg i i ha ha z z
  have hf : (fun w => heatDeriv G D i a z w * heatDeriv G D i a w z) =
      fun w => heatDeriv G D i a z w ^ 2 :=
    funext fun w => by rw [heatDeriv_symm hD hdeg i a w z, sq]
  rwa [hf] at h

theorem heatDeriv_odd_nonpos (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) (i : ℕ) {a : ℝ}
    (ha : 0 ≤ a) (z : V) : heatDeriv G D (i + (i + 1)) (a + a) z z ≤ 0 := by
  have h := hasSum_heatDeriv_mul hD hdeg i (i + 1) ha ha z z
  have hf : (fun w => heatDeriv G D i a z w * heatDeriv G D (i + 1) a w z) = fun w =>
      heatDeriv G D i a z w *
        ∑ u ∈ G.neighborFinset w, (heatDeriv G D i a z u - heatDeriv G D i a z w) := by
    funext w
    rw [heatDeriv_succ]
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [heatDeriv_symm hD hdeg i a u z, heatDeriv_symm hD hdeg i a w z]
  rw [hf] at h
  exact hasSum_mul_laplacian_nonpos hdeg (hasSum_heatDeriv_sq hD hdeg i ha z).summable h

theorem heatDeriv_two_nonneg (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) {r : ℝ} (hr : 0 ≤ r)
    (z : V) : 0 ≤ heatDeriv G D 2 r z z := by
  have h := hasSum_heatDeriv_sq hD hdeg 1 (div_nonneg hr zero_le_two) z
  rw [add_halves] at h
  exact h.nonneg fun _ => sq_nonneg _

theorem heatDeriv_one_nonpos (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) {r : ℝ} (hr : 0 ≤ r)
    (z : V) : heatDeriv G D 1 r z z ≤ 0 := by
  have h := heatDeriv_odd_nonpos hD hdeg 0 (div_nonneg hr zero_le_two) z
  rwa [add_halves] at h

theorem heatDeriv_three_nonpos (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) {r : ℝ} (hr : 0 ≤ r)
    (z : V) : heatDeriv G D 3 r z z ≤ 0 := by
  have h := heatDeriv_odd_nonpos hD hdeg 1 (div_nonneg hr zero_le_two) z
  rwa [add_halves] at h

/-! ### Calculus on the diagonal -/

theorem sub_le_mul_of_hasDerivAt {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ s, HasDerivAt f (g s) s) (hg : ∀ s ∈ Set.Icc a b, g s ≤ g b) :
    f b - f a ≤ g b * (b - a) := by
  have hcont : ContinuousOn f (Set.Icc a b) := fun s _ => (hf s).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ f (interior (Set.Icc a b)) :=
    fun s _ => (hf s).differentiableAt.differentiableWithinAt
  exact (convex_Icc a b).image_sub_le_mul_sub_of_deriv_le hcont hdiff
    (fun s hs => by rw [(hf s).deriv]; exact hg s (interior_subset hs)) a
    (Set.left_mem_Icc.2 hab) b (Set.right_mem_Icc.2 hab) hab

theorem le_of_hasDerivAt_nonneg {g g' : ℝ → ℝ} {s b : ℝ} (hsb : s ≤ b)
    (hg : ∀ u, HasDerivAt g (g' u) u) (h : ∀ u ∈ Set.Icc s b, 0 ≤ g' u) : g s ≤ g b := by
  have hcont : ContinuousOn g (Set.Icc s b) := fun u _ => (hg u).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ g (interior (Set.Icc s b)) :=
    fun u _ => (hg u).differentiableAt.differentiableWithinAt
  exact monotoneOn_of_deriv_nonneg (convex_Icc s b) hcont hdiff
    (fun u hu => by rw [(hg u).deriv]; exact h u (interior_subset hu))
    (Set.left_mem_Icc.2 hsb) (Set.right_mem_Icc.2 hsb) hsb

/-- `-m'(r) ≤ 2 m(r/2)/r` for `m(r) = p_r(z, z)`. -/
theorem half_mul_neg_heatDeriv_one_le (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) {r : ℝ}
    (hr : 0 < r) (z : V) : r / 2 * -heatDeriv G D 1 r z z ≤ heatDeriv G D 0 (r / 2) z z := by
  have h := sub_le_mul_of_hasDerivAt (f := fun s => heatDeriv G D 0 s z z)
    (g := fun s => heatDeriv G D 1 s z z) (half_le_self hr.le)
    (fun s => hasDerivAt_heatDeriv hD hdeg 0 s z z) (fun s hs =>
      le_of_hasDerivAt_nonneg (g := fun s => heatDeriv G D 1 s z z) hs.2
        (fun u => hasDerivAt_heatDeriv hD hdeg 1 u z z)
        (fun u hu => heatDeriv_two_nonneg hD hdeg (by linarith [hu.1, hs.1]) z))
  have h0 : 0 ≤ heatDeriv G D 0 r z z := vsrwHeat_nonneg hD hdeg hr.le z z
  nlinarith

/-- `m''(r) ≤ -2 m'(r/2)/r` for `m(r) = p_r(z, z)`. -/
theorem half_mul_heatDeriv_two_le (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) {r : ℝ}
    (hr : 0 < r) (z : V) : r / 2 * heatDeriv G D 2 r z z ≤ -heatDeriv G D 1 (r / 2) z z := by
  have h := sub_le_mul_of_hasDerivAt (f := fun s => -heatDeriv G D 1 s z z)
    (g := fun s => -heatDeriv G D 2 s z z) (half_le_self hr.le)
    (fun s => (hasDerivAt_heatDeriv hD hdeg 1 s z z).fun_neg) (fun s hs =>
      le_of_hasDerivAt_nonneg (g := fun s => -heatDeriv G D 2 s z z) hs.2
        (fun u => (hasDerivAt_heatDeriv hD hdeg 2 u z z).fun_neg)
        (fun u hu => neg_nonneg.2 (heatDeriv_three_nonpos hD hdeg
          (by linarith [hu.1, hs.1]) z)))
  have h1 : heatDeriv G D 1 r z z ≤ 0 := heatDeriv_one_nonpos hD hdeg hr.le z
  nlinarith

/-- `m''(r) ≤ 8 m(r/4)/r²` for `m(r) = p_r(z, z)`. -/
theorem heatDeriv_two_le (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) {r : ℝ} (hr : 0 < r)
    (z : V) : heatDeriv G D 2 r z z ≤ 8 / r ^ 2 * vsrwHeat G D (r / 4) z z := by
  have h1 := half_mul_heatDeriv_two_le hD hdeg hr z
  have h2 := half_mul_neg_heatDeriv_one_le hD hdeg (half_pos hr) z
  rw [heatDeriv_zero, show r / 2 / 2 = r / 4 by ring] at h2
  have hr2 : 0 < r ^ 2 := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hr2]
  nlinarith [mul_le_mul_of_nonneg_left h1 hr.le]

/-! ### The second time derivative -/

/-- The Cauchy–Schwarz inequality for summable families. -/
theorem sq_le_mul_of_hasSum {ι : Type*} {f g : ι → ℝ} {P A B : ℝ}
    (hP : HasSum (fun i => f i * g i) P) (hA : HasSum (fun i => f i ^ 2) A)
    (hB : HasSum (fun i => g i ^ 2) B) : P ^ 2 ≤ A * B := by
  have key : ∀ c : ℝ, 0 ≤ B * (c * c) + (-2 * P) * c + A := by
    intro c
    have e : (fun i => (f i - c * g i) ^ 2) =
        fun i => f i ^ 2 - 2 * c * (f i * g i) + c ^ 2 * g i ^ 2 := funext fun i => by ring
    have h : HasSum (fun i => (f i - c * g i) ^ 2) (A - 2 * c * P + c ^ 2 * B) := by
      rw [e]
      exact (hA.sub (hP.mul_left (2 * c))).add (hB.mul_left (c ^ 2))
    have := h.nonneg fun i => sq_nonneg _
    nlinarith [this]
  have := discrim_le_zero key
  rw [discrim] at this
  nlinarith [this]

/-- **The second time derivative of the heat kernel**:
`|∂_s² p_s(z, x)| ≤ 8 s^{-2} (p_{s/4}(z, z) p_{s/4}(x, x))^{1/2}` for `s > 0`. -/
theorem abs_heatDeriv_two_le (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) {s : ℝ} (hs : 0 < s)
    (z x : V) : |heatDeriv G D 2 s z x| ≤
      8 / s ^ 2 * Real.sqrt (vsrwHeat G D (s / 4) z z * vsrwHeat G D (s / 4) x x) := by
  have hs2 : 0 ≤ s / 2 := by positivity
  have hP : HasSum (fun w => heatDeriv G D 1 (s / 2) z w * heatDeriv G D 1 (s / 2) w x)
      (heatDeriv G D 2 (s / 2 + s / 2) z x) := hasSum_heatDeriv_mul hD hdeg 1 1 hs2 hs2 z x
  have hA : HasSum (fun w => heatDeriv G D 1 (s / 2) z w ^ 2)
      (heatDeriv G D 2 (s / 2 + s / 2) z z) := hasSum_heatDeriv_sq hD hdeg 1 hs2 z
  have hB : HasSum (fun w => heatDeriv G D 1 (s / 2) w x ^ 2)
      (heatDeriv G D 2 (s / 2 + s / 2) x x) := by
    have h : HasSum (fun w => heatDeriv G D 1 (s / 2) x w ^ 2)
        (heatDeriv G D 2 (s / 2 + s / 2) x x) := hasSum_heatDeriv_sq hD hdeg 1 hs2 x
    have hf : (fun w => heatDeriv G D 1 (s / 2) x w ^ 2) =
        fun w => heatDeriv G D 1 (s / 2) w x ^ 2 :=
      funext fun w => by rw [heatDeriv_symm hD hdeg 1 (s / 2) x w]
    rwa [hf] at h
  rw [add_halves] at hP hA hB
  have hcs := sq_le_mul_of_hasSum hP hA hB
  have hz := heatDeriv_two_le hD hdeg hs z
  have hx := heatDeriv_two_le hD hdeg hs x
  have hx0 : 0 ≤ heatDeriv G D 2 s x x := hB.nonneg fun _ => sq_nonneg _
  have hmz : 0 ≤ vsrwHeat G D (s / 4) z z := vsrwHeat_nonneg hD hdeg (by positivity) z z
  have hmx : 0 ≤ vsrwHeat G D (s / 4) x x := vsrwHeat_nonneg hD hdeg (by positivity) x x
  have hc : 0 ≤ 8 / s ^ 2 := by positivity
  calc |heatDeriv G D 2 s z x| ≤ Real.sqrt (heatDeriv G D 2 s z z * heatDeriv G D 2 s x x) :=
        Real.abs_le_sqrt hcs
    _ ≤ Real.sqrt ((8 / s ^ 2 * vsrwHeat G D (s / 4) z z) *
          (8 / s ^ 2 * vsrwHeat G D (s / 4) x x)) :=
        Real.sqrt_le_sqrt (mul_le_mul hz hx hx0 (mul_nonneg hc hmz))
    _ = 8 / s ^ 2 * Real.sqrt (vsrwHeat G D (s / 4) z z * vsrwHeat G D (s / 4) x x) := by
        rw [show (8 / s ^ 2 * vsrwHeat G D (s / 4) z z) * (8 / s ^ 2 * vsrwHeat G D (s / 4) x x) =
            (8 / s ^ 2) ^ 2 * (vsrwHeat G D (s / 4) z z * vsrwHeat G D (s / 4) x x) by ring,
          Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hc]

end Rigidity.Green
