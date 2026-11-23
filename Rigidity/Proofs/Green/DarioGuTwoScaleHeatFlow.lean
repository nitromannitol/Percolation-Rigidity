import Rigidity.Proofs.Green.DarioGuTwoScaleEnergy
import Rigidity.Proofs.Poincare.LatticeHeatKernel

/-!
# The heat semigroup of the open graph on square summable functions

The summability layer of the proof of Proposition 4.3 of Dario–Gu: the function
`w = h - P_{t-τ} h(τ)` of Step 1 is handled in `ℓ²(ℤ²)`. For `f` square summable and
`P_s f(x) = Σ_z p(s, x, z) f(z)` (`heatFlow`):

* `openHeat_le_exp_mul`: `p(s, x, z) ≤ e^{8T} p(2T, x, z)` for `0 ≤ s ≤ T`, term by term in the
  Poisson series (as `openHeat_allOpen_le_exp_mul` for the full lattice);
* `sq_heatFlow_le`: Jensen's inequality `(P_s f)(x)² ≤ Σ_z p(s, x, z) f(z)²`;
* `summable_sq_heatFlow`, `tsum_sq_heatFlow_le`: `P_s` is a contraction of `ℓ²(ℤ²)`;
* `abs_heatFlow_le`: the domination `|P_s f| ≤ e^{8T} P_{2T} |f|` for `0 ≤ s ≤ T`;
* `hasDerivAt_heatFlow`: the heat equation `∂_s P_s f = Δ P_s f` for `s > 0`.
-/

open scoped Classical
open LatticeProb LatticeProb.Percolation

namespace Rigidity.Green

/-- `P_s f(x) = Σ_z p(s, x, z) f(z)`. -/
noncomputable def heatFlow (ω : Configuration 2) (s : ℝ) (f : Vertex 2 → ℝ) (x : Vertex 2) : ℝ :=
  ∑' z, openHeat ω s x z * f z

/-- **Domination in time**: `p(s, x, z) ≤ e^{8T} p(2T, x, z)` for `0 ≤ s ≤ T`. -/
theorem openHeat_le_exp_mul (ω : Configuration 2) {s T : ℝ} (hs : 0 ≤ s) (hsT : s ≤ T)
    (x z : Vertex 2) : openHeat ω s x z ≤ Real.exp (8 * T) * openHeat ω (2 * T) x z := by
  have hdeg := openGraph_degree_le_four ω
  rw [openHeat, openHeat, vsrwHeat, vsrwHeat, ← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun n => ?_) (summable_vsrwHeat (by norm_num) hdeg s x z)
    ((summable_vsrwHeat (by norm_num) hdeg (2 * T) x z).mul_left _)
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (Rigidity.Poincare.poissonWeight_le_exp_mul hs hsT n)
    (lazyPow_mem_Icc (by norm_num) hdeg n x z).1

theorem summable_openHeat_sq (ω : Configuration 2) {s : ℝ} (hs : 0 ≤ s) (x : Vertex 2) :
    Summable fun z => openHeat ω s x z ^ 2 := by
  refine Summable.of_nonneg_of_le (fun z => sq_nonneg _) (fun z => ?_)
    (hasSum_openHeat ω hs x).summable
  have h0 := openHeat_nonneg ω hs x z
  have h1 := openHeat_le_one ω hs x z
  nlinarith

theorem summable_openHeat_mul (ω : Configuration 2) {s : ℝ} (hs : 0 ≤ s) {f : Vertex 2 → ℝ}
    (hf : Summable fun z => f z ^ 2) (x : Vertex 2) :
    Summable fun z => openHeat ω s x z * f z :=
  summable_mul_of_sq (summable_openHeat_sq ω hs x) hf

theorem summable_openHeat_mul_abs (ω : Configuration 2) {s : ℝ} (hs : 0 ≤ s)
    {f : Vertex 2 → ℝ} (hf : Summable fun z => f z ^ 2) (x : Vertex 2) :
    Summable fun z => openHeat ω s x z * |f z| :=
  summable_openHeat_mul ω hs (f := fun z => |f z|) (by simpa only [sq_abs] using hf) x

theorem summable_openHeat_mul_sq (ω : Configuration 2) {s : ℝ} (hs : 0 ≤ s) {f : Vertex 2 → ℝ}
    (hf : Summable fun z => f z ^ 2) (x : Vertex 2) :
    Summable fun z => openHeat ω s x z * f z ^ 2 :=
  Summable.of_nonneg_of_le (fun z => mul_nonneg (openHeat_nonneg ω hs x z) (sq_nonneg _))
    (fun z => mul_le_of_le_one_left (sq_nonneg _) (openHeat_le_one ω hs x z)) hf

/-- **Jensen's inequality** for the heat kernel: `(P_s f)(x)² ≤ Σ_z p(s, x, z) f(z)²`. -/
theorem sq_heatFlow_le (ω : Configuration 2) {s : ℝ} (hs : 0 ≤ s) {f : Vertex 2 → ℝ}
    (hf : Summable fun z => f z ^ 2) (x : Vertex 2) :
    heatFlow ω s f x ^ 2 ≤ ∑' z, openHeat ω s x z * f z ^ 2 := by
  set m := heatFlow ω s f x with hm
  have h1 := hasSum_openHeat ω hs x
  have h2 : HasSum (fun z => openHeat ω s x z * f z) m := (summable_openHeat_mul ω hs hf x).hasSum
  have h3 := (summable_openHeat_mul_sq ω hs hf x).hasSum
  have h : HasSum (fun z => openHeat ω s x z * (f z - m) ^ 2)
      ((∑' z, openHeat ω s x z * f z ^ 2) - 2 * m * m + m ^ 2 * 1) := by
    have e : (fun z => openHeat ω s x z * (f z - m) ^ 2) = fun z =>
        openHeat ω s x z * f z ^ 2 - 2 * m * (openHeat ω s x z * f z) +
          m ^ 2 * openHeat ω s x z := by
      funext z
      ring
    rw [e]
    exact (h3.sub (h2.mul_left (2 * m))).add (h1.mul_left (m ^ 2))
  have h0 := hasSum_le (fun z => mul_nonneg (openHeat_nonneg ω hs x z) (sq_nonneg (f z - m)))
    hasSum_zero h
  nlinarith

/-- The double series `Σ_x Σ_z p(s, x, z) f(z)²` converges and equals `Σ_z f(z)²`. -/
theorem summable_tsum_openHeat_mul_sq (ω : Configuration 2) {s : ℝ} (hs : 0 ≤ s)
    {f : Vertex 2 → ℝ} (hf : Summable fun z => f z ^ 2) :
    Summable (fun x => ∑' z, openHeat ω s x z * f z ^ 2) ∧
      ∑' x, ∑' z, openHeat ω s x z * f z ^ 2 = ∑' z, f z ^ 2 := by
  set F : Vertex 2 × Vertex 2 → ℝ := fun q => openHeat ω s q.2 q.1 * f q.1 ^ 2 with hF
  have hF0 : 0 ≤ F := fun q => mul_nonneg (openHeat_nonneg ω hs _ _) (sq_nonneg _)
  have hrow : ∀ z, HasSum (fun x => F (z, x)) (f z ^ 2) := by
    intro z
    have e : (fun x => F (z, x)) = fun x => openHeat ω s z x * f z ^ 2 := by
      funext x
      simp only [hF]
      rw [openHeat_symm ω s x z]
    rw [e]
    simpa only [one_mul] using (hasSum_openHeat ω hs z).mul_right (f z ^ 2)
  have hFs : Summable F := by
    refine (summable_prod_of_nonneg hF0).2 ⟨fun z => (hrow z).summable, ?_⟩
    have e : (fun z => ∑' x, F (z, x)) = fun z => f z ^ 2 := funext fun z => (hrow z).tsum_eq
    rw [e]
    exact hf
  have hG0 : 0 ≤ fun q : Vertex 2 × Vertex 2 => F q.swap := fun q => hF0 q.swap
  have hGs := (summable_prod_of_nonneg hG0).1 hFs.prod_symm
  refine ⟨hGs.2, ?_⟩
  have hc := hFs.tsum_comm (f := fun z x => F (z, x))
  have e1 : ∑' x, ∑' z, openHeat ω s x z * f z ^ 2 = ∑' x, ∑' z, F (z, x) := rfl
  rw [e1, hc]
  exact tsum_congr fun z => (hrow z).tsum_eq

/-- `P_s f` is square summable. -/
theorem summable_sq_heatFlow (ω : Configuration 2) {s : ℝ} (hs : 0 ≤ s) {f : Vertex 2 → ℝ}
    (hf : Summable fun z => f z ^ 2) : Summable fun x => heatFlow ω s f x ^ 2 :=
  Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun x => sq_heatFlow_le ω hs hf x)
    (summable_tsum_openHeat_mul_sq ω hs hf).1

/-- **`P_s` is a contraction of `ℓ²(ℤ²)`**: `Σ_x (P_s f)(x)² ≤ Σ_z f(z)²`. -/
theorem tsum_sq_heatFlow_le (ω : Configuration 2) {s : ℝ} (hs : 0 ≤ s) {f : Vertex 2 → ℝ}
    (hf : Summable fun z => f z ^ 2) : ∑' x, heatFlow ω s f x ^ 2 ≤ ∑' z, f z ^ 2 := by
  rw [← (summable_tsum_openHeat_mul_sq ω hs hf).2]
  exact Summable.tsum_le_tsum (fun x => sq_heatFlow_le ω hs hf x) (summable_sq_heatFlow ω hs hf)
    (summable_tsum_openHeat_mul_sq ω hs hf).1

/-- **Domination**: `|P_s f(x)| ≤ e^{8T} P_{2T} |f| (x)` for `0 ≤ s ≤ T`. -/
theorem abs_heatFlow_le (ω : Configuration 2) {s T : ℝ} (hs : 0 ≤ s) (hsT : s ≤ T)
    {f : Vertex 2 → ℝ} (hf : Summable fun z => f z ^ 2) (x : Vertex 2) :
    |heatFlow ω s f x| ≤ Real.exp (8 * T) * heatFlow ω (2 * T) (fun z => |f z|) x := by
  have hT : 0 ≤ 2 * T := by linarith
  have hn : Summable fun z => ‖openHeat ω s x z * f z‖ := (summable_openHeat_mul ω hs hf x).norm
  unfold heatFlow
  rw [← tsum_mul_left]
  calc |∑' z, openHeat ω s x z * f z| = ‖∑' z, openHeat ω s x z * f z‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∑' z, ‖openHeat ω s x z * f z‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' z, Real.exp (8 * T) * (openHeat ω (2 * T) x z * |f z|) := by
        refine Summable.tsum_le_tsum (fun z => ?_) hn
          ((summable_openHeat_mul_abs ω hT hf x).mul_left _)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (openHeat_nonneg ω hs x z), ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (openHeat_le_exp_mul ω hs hsT x z) (abs_nonneg _)

/-- The Laplacian of `P_s f`, under the sum. -/
theorem openLaplacian_heatFlow (ω : Configuration 2) {s : ℝ} (hs : 0 ≤ s) {f : Vertex 2 → ℝ}
    (hf : Summable fun z => f z ^ 2) (x : Vertex 2) :
    openLaplacian ω (heatFlow ω s f) x =
      ∑' z, openLaplacian ω (fun w => openHeat ω s w z) x * f z := by
  have hs' := fun w => summable_openHeat_mul ω hs hf w
  unfold openLaplacian heatFlow
  calc ∑ w ∈ (openGraph ω).neighborFinset x,
        (∑' z, openHeat ω s w z * f z - ∑' z, openHeat ω s x z * f z)
      = ∑ w ∈ (openGraph ω).neighborFinset x,
          ∑' z, (openHeat ω s w z - openHeat ω s x z) * f z :=
        Finset.sum_congr rfl fun w _ => by
          rw [← (hs' w).tsum_sub (hs' x)]
          exact tsum_congr fun z => by ring
    _ = ∑' z, ∑ w ∈ (openGraph ω).neighborFinset x,
          (openHeat ω s w z - openHeat ω s x z) * f z :=
        (Summable.tsum_finsetSum fun w _ => ((hs' w).sub (hs' x)).congr fun z => by ring).symm
    _ = _ := tsum_congr fun z => by rw [Finset.sum_mul]

theorem abs_openLaplacian_openHeat_le (ω : Configuration 2) {s T : ℝ} (hs : 0 ≤ s)
    (hsT : s ≤ T) (x z : Vertex 2) :
    |openLaplacian ω (fun w => openHeat ω s w z) x| ≤
      Real.exp (8 * T) * ∑ w ∈ (openGraph ω).neighborFinset x,
        (openHeat ω (2 * T) w z + openHeat ω (2 * T) x z) := by
  unfold openLaplacian
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w _ => ?_)
  have h1 := openHeat_le_exp_mul ω hs hsT w z
  have h2 := openHeat_le_exp_mul ω hs hsT x z
  have h3 := openHeat_nonneg ω hs w z
  have h4 := openHeat_nonneg ω hs x z
  rw [mul_add, abs_le]
  constructor <;> linarith

/-- **The heat equation** `∂_s P_s f = Δ P_s f` for `f` square summable and `s ∈ (0, T)`. -/
theorem hasDerivAt_heatFlow (ω : Configuration 2) {f : Vertex 2 → ℝ}
    (hf : Summable fun z => f z ^ 2) {T s : ℝ} (hs : s ∈ Set.Ioo 0 T) (x : Vertex 2) :
    HasDerivAt (fun r => heatFlow ω r f x) (openLaplacian ω (heatFlow ω s f) x) s := by
  have h2T : (0 : ℝ) ≤ 2 * T := by linarith [hs.1, hs.2]
  set b : Vertex 2 → ℝ := fun z => (Real.exp (8 * T) * ∑ w ∈ (openGraph ω).neighborFinset x,
      (openHeat ω (2 * T) w z + openHeat ω (2 * T) x z)) * |f z| with hb
  have hbs : Summable b := by
    have ha := fun w => summable_openHeat_mul_abs ω h2T hf w
    have h := (summable_sum (s := (openGraph ω).neighborFinset x) fun w _ =>
      (ha w).add (ha x)).mul_left (Real.exp (8 * T))
    refine h.congr fun z => ?_
    simp only [hb, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun w _ => by ring
  have key := hasDerivAt_tsum_of_isPreconnected (u := b) hbs isOpen_Ioo isPreconnected_Ioo
    (t := Set.Ioo 0 T) (y₀ := s)
    (g := fun z r => openHeat ω r x z * f z)
    (g' := fun z r => openLaplacian ω (fun w => openHeat ω r w z) x * f z)
    (fun z r _ => (hasDerivAt_openHeat ω r x z).mul_const (f z))
    (fun z r hr => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (abs_openLaplacian_openHeat_le ω hr.1.le hr.2.le x z)
        (abs_nonneg _))
    hs (summable_openHeat_mul ω hs.1.le hf x) hs
  rw [openLaplacian_heatFlow ω hs.1.le hf x]
  exact key

end Rigidity.Green
