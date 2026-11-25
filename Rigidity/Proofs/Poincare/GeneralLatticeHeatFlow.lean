import Rigidity.Proofs.Poincare.LatticeHeatFlow
import Rigidity.Proofs.Poincare.GeneralHeatMaximal

/-!
# The heat flow of finitely supported functions on `ℤ^d` and the weights `cosh`

The extension of `LatticeHeatFlow.lean` from `ℤ²` to `ℤ^d`, `d ≥ 1`:

* `lap u x = Σ_i (u(x + e_i) + u(x - e_i)) - 2d u(x)`, the Laplacian of `ℤ^d`
  (`openLaplacian_allOpen`);
* `heatF S f s x = Σ_{y ∈ S} Φ_s(x, y) f(y)`, the heat flow of `f` supported in `S`: it solves
  `∂_s heatF = lap heatF` (`hasDerivAt_heatF`), starts at `f` (`heatF_zero`), and satisfies
  Jensen's inequality `(heatF f)^p ≤ heatF (f^p)` for `p ≥ 1`, `f ≥ 0` (`heatF_rpow_le`);
* `steinPointwise`: the lattice form of the identity (D.11) of Armstrong, Kuusi and Mourrat,
  `lap(v^p) - p v^{p-1} lap v ≥ (p(p-1)/2) M^{p-2} Σ_i (v(x + e_i) - v(x))²` for `0 ≤ v ≤ M`;
* `coshW a x = Π_i cosh(a x_i)`: `lap coshW = 2d(cosh a - 1) coshW`, and the heat kernel acts on
  it by `e^{2ds(cosh a - 1)}` (`hasSum_zdHeat_mul_coshW`); the comparison
  `coshW a x ≤ coshW a y e^{a|y - x|₁}` and `e^{a|x|₁} ≤ 2^d coshW a x`.
-/

open scoped Classical
open LatticeProb LatticeProb.Percolation Rigidity.Green

namespace Rigidity.Poincare.GeneralDim

variable {d : ℕ}

/-- The Laplacian of `ℤ^d`. -/
noncomputable def lap (u : Vertex d → ℝ) (x : Vertex d) : ℝ :=
  ∑ i : Fin d, (u (x + unit i) + u (x - unit i)) - 2 * d * u x

theorem openLaplacian_allOpen (u : Vertex d → ℝ) (x : Vertex d) :
    openLaplacian (allOpen d) u x = lap u x := by
  rw [openLaplacian, Finset.sum_sub_distrib, Finset.sum_const,
    SimpleGraph.card_neighborFinset_eq_degree, degree_allOpen, sum_neighborFinset_allOpen, lap,
    nsmul_eq_mul]
  push_cast
  ring

theorem lap_finset_sum {ι : Type*} (S : Finset ι) (g : ι → Vertex d → ℝ) (x : Vertex d) :
    lap (fun z => ∑ y ∈ S, g y z) x = ∑ y ∈ S, lap (g y) x := by
  simp only [lap]
  rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_comm (s := S)]
  simp only [Finset.sum_add_distrib]

theorem lap_mul_const (u : Vertex d → ℝ) (c : ℝ) (x : Vertex d) :
    lap (fun z => u z * c) x = lap u x * c := by
  simp only [lap]
  rw [sub_mul, Finset.sum_mul]
  simp only [add_mul]
  ring

/-- The heat flow `Σ_{y ∈ S} Φ_s(x, y) f(y)` of a function supported in `S`. -/
noncomputable def heatF (S : Finset (Vertex d)) (f : Vertex d → ℝ) (s : ℝ) (x : Vertex d) : ℝ :=
  ∑ y ∈ S, zdHeat d s x y * f y

/-- **The heat equation** for `heatF`. -/
theorem hasDerivAt_heatF [NeZero d] (S : Finset (Vertex d)) (f : Vertex d → ℝ) (s : ℝ)
    (x : Vertex d) : HasDerivAt (fun s => heatF S f s x) (lap (heatF S f s) x) s := by
  have h : ∀ y ∈ S, HasDerivAt (fun s => zdHeat d s x y * f y)
      (lap (fun z => zdHeat d s z y) x * f y) s := by
    intro y _
    have := (hasDerivAt_zdHeat s x y).mul_const (f y)
    rwa [openLaplacian_allOpen] at this
  refine (HasDerivAt.fun_sum h).congr_deriv ?_
  unfold heatF
  rw [lap_finset_sum]
  simp only [lap_mul_const]

theorem continuous_heatF [NeZero d] (S : Finset (Vertex d)) (f : Vertex d → ℝ) (x : Vertex d) :
    Continuous fun s => heatF S f s x :=
  continuous_iff_continuousAt.2 fun s => (hasDerivAt_heatF S f s x).continuousAt

theorem heatF_zero {S : Finset (Vertex d)} {f : Vertex d → ℝ} (hfS : ∀ y ∉ S, f y = 0)
    (x : Vertex d) : heatF S f 0 x = f x := by
  unfold heatF
  simp only [zdHeat_zero, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · exact (hfS x h).symm

theorem heatF_nonneg [NeZero d] {S : Finset (Vertex d)} {f : Vertex d → ℝ} (hf : ∀ y, 0 ≤ f y)
    {s : ℝ} (hs : 0 ≤ s) (x : Vertex d) : 0 ≤ heatF S f s x :=
  Finset.sum_nonneg fun y _ => mul_nonneg (zdHeat_nonneg hs x y) (hf y)

theorem hasSum_zdHeat [NeZero d] {t : ℝ} (ht : 0 ≤ t) (x : Vertex d) :
    HasSum (fun y => zdHeat d t x y) 1 :=
  hasSum_vsrwHeat two_mul_pos_of_neZero (openGraph_degree_le (allOpen d)) ht x

theorem sum_zdHeat_le_one [NeZero d] (S : Finset (Vertex d)) {s : ℝ} (hs : 0 ≤ s)
    (x : Vertex d) : ∑ y ∈ S, zdHeat d s x y ≤ 1 :=
  sum_le_hasSum S (fun y _ => zdHeat_nonneg hs x y) (hasSum_zdHeat hs x)

/-- **Jensen's inequality** for the heat flow: `(heatF f)^p ≤ heatF (f^p)`, `p ≥ 1`, `f ≥ 0`. -/
theorem heatF_rpow_le [NeZero d] {S : Finset (Vertex d)} {f : Vertex d → ℝ} (hf : ∀ y, 0 ≤ f y)
    {s p : ℝ} (hs : 0 ≤ s) (hp : 1 ≤ p) (x : Vertex d) :
    heatF S f s x ^ p ≤ ∑ y ∈ S, zdHeat d s x y * f y ^ p := by
  set w : Vertex d → ℝ := fun y => zdHeat d s x y with hw
  set W := ∑ y ∈ S, w y with hW
  have hw0 : ∀ y, 0 ≤ w y := fun y => zdHeat_nonneg hs x y
  have hW1 : W ≤ 1 := sum_zdHeat_le_one S hs x
  have hR0 : 0 ≤ ∑ y ∈ S, w y * f y ^ p :=
    Finset.sum_nonneg fun y _ => mul_nonneg (hw0 y) (Real.rpow_nonneg (hf y) _)
  rcases (Finset.sum_nonneg fun y (_ : y ∈ S) => hw0 y).lt_or_eq with hWpos | hW0
  · have hWpos' : 0 < W := hWpos
    have hmean := Real.rpow_arith_mean_le_arith_mean_rpow S (fun y => w y / W) f
      (fun y _ => div_nonneg (hw0 y) hWpos'.le)
      (by rw [← Finset.sum_div, div_self hWpos'.ne']) (fun y _ => hf y) hp
    have e1 : heatF S f s x = W * ∑ y ∈ S, w y / W * f y := by
      unfold heatF
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      field_simp
      simp only [hw]
      ring
    have e2 : ∑ y ∈ S, w y / W * f y ^ p = W⁻¹ * ∑ y ∈ S, w y * f y ^ p := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      field_simp
    rw [e1, Real.mul_rpow hWpos'.le (Finset.sum_nonneg fun y _ =>
      mul_nonneg (div_nonneg (hw0 y) hWpos'.le) (hf y))]
    calc W ^ p * (∑ y ∈ S, w y / W * f y) ^ p ≤ W ^ p * (W⁻¹ * ∑ y ∈ S, w y * f y ^ p) :=
          mul_le_mul_of_nonneg_left (e2 ▸ hmean) (Real.rpow_nonneg hWpos'.le _)
      _ = W ^ (p - 1) * ∑ y ∈ S, w y * f y ^ p := by
          rw [← mul_assoc, Real.rpow_sub_one hWpos'.ne', div_eq_mul_inv]
      _ ≤ 1 * ∑ y ∈ S, w y * f y ^ p := by
          refine mul_le_mul_of_nonneg_right ?_ hR0
          exact Real.rpow_le_one hWpos'.le hW1 (by linarith)
      _ = ∑ y ∈ S, w y * f y ^ p := one_mul _
  · have hzero : ∀ y ∈ S, w y = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun y _ => hw0 y).1 hW0.symm
    have hv : heatF S f s x = 0 := by
      unfold heatF
      exact Finset.sum_eq_zero fun y hy => by
        have := hzero y hy
        simp only [hw] at this
        rw [this, zero_mul]
    rw [hv, Real.zero_rpow (by linarith)]
    exact hR0

/-- **The lattice form of (D.11)**: for `0 ≤ v` with `v(x), v(x + e_i) ≤ M`,
`(p(p-1)/2) M^{p-2} Σ_i (v(x + e_i) - v(x))² ≤ lap(v^p)(x) - p v(x)^{p-1} lap v(x)`. -/
theorem steinPointwise {p M : ℝ} (hp1 : 1 < p) (hp2 : p ≤ 2) {v : Vertex d → ℝ}
    (hv : ∀ z, 0 ≤ v z) {x : Vertex d} (hvx : v x ≤ M) (hvi : ∀ i, v (x + unit i) ≤ M) :
    p * (p - 1) / 2 * M ^ (p - 2) * ∑ i : Fin d, (v (x + unit i) - v x) ^ 2 ≤
      lap (fun z => v z ^ p) x - p * v x ^ (p - 1) * lap v x := by
  set T : Vertex d → ℝ := fun y => v y ^ p - v x ^ p - p * v x ^ (p - 1) * (v y - v x) with hT
  have e : lap (fun z => v z ^ p) x - p * v x ^ (p - 1) * lap v x =
      ∑ i : Fin d, (T (x + unit i) + T (x - unit i)) := by
    simp only [lap, hT]
    rw [mul_sub, Finset.mul_sum]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_add, mul_sub]
    ring
  have h1 : ∀ i, p * (p - 1) / 2 * M ^ (p - 2) * (v (x + unit i) - v x) ^ 2 ≤ T (x + unit i) :=
    fun i => rpow_sub_tangent_ge hp1 hp2 (hv x) hvx (hv _) (hvi i)
  have h2 : ∀ i, 0 ≤ T (x - unit i) := by
    intro i
    have := rpow_sub_tangent_ge hp1 hp2 (M := max M (v (x - unit i))) (hv x)
      (hvx.trans (le_max_left _ _)) (hv _) (le_max_right _ _)
    have h0 : 0 ≤ p * (p - 1) / 2 * max M (v (x - unit i)) ^ (p - 2) *
        (v (x - unit i) - v x) ^ 2 := by
      have hm : 0 ≤ max M (v (x - unit i)) := (hv _).trans (le_max_right _ _)
      have : 0 ≤ p * (p - 1) / 2 := by nlinarith
      positivity
    exact h0.trans this
  rw [e, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => by linarith [h1 i, h2 i]

/-- The weight `Π_i cosh(a x_i)`. -/
noncomputable def coshW (a : ℝ) (x : Vertex d) : ℝ :=
  ∏ i, Real.cosh (a * ((x i : ℤ) : ℝ))

theorem coshW_pos (a : ℝ) (x : Vertex d) : 0 < coshW a x :=
  Finset.prod_pos fun _ _ => Real.cosh_pos _

theorem coshW_add_unit (a : ℝ) (x : Vertex d) (i : Fin d) (s : ℤ) :
    coshW a (x + s • unit i) =
      Real.cosh (a * (((x i : ℤ) : ℝ) + s)) * ∏ j ∈ Finset.univ.erase i,
        Real.cosh (a * ((x j : ℤ) : ℝ)) := by
  rw [coshW, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  congr 1
  · simp [unit]
  · refine Finset.prod_congr rfl fun j hj => ?_
    simp [unit, Finset.ne_of_mem_erase hj]

theorem coshW_eq_mul_prod_erase (a : ℝ) (x : Vertex d) (i : Fin d) :
    coshW a x = Real.cosh (a * ((x i : ℤ) : ℝ)) * ∏ j ∈ Finset.univ.erase i,
      Real.cosh (a * ((x j : ℤ) : ℝ)) := by
  rw [coshW, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]

theorem sum_neighbors_coshW (a : ℝ) (x : Vertex d) :
    ∑ i : Fin d, (coshW a (x + unit i) + coshW a (x - unit i)) =
      2 * d * Real.cosh a * coshW a x := by
  have h : ∀ i : Fin d, coshW a (x + unit i) + coshW a (x - unit i) =
      2 * Real.cosh a * coshW a x := by
    intro i
    have e1 : x + unit i = x + (1 : ℤ) • unit i := by rw [one_smul]
    have e2 : x - unit i = x + (-1 : ℤ) • unit i := by rw [neg_one_smul, ← sub_eq_add_neg]
    rw [e1, e2, coshW_add_unit, coshW_add_unit, coshW_eq_mul_prod_erase a x i]
    push_cast
    rw [mul_add, mul_add, Real.cosh_add, mul_neg, mul_one, Real.cosh_add, Real.cosh_neg,
      Real.sinh_neg]
    ring
  rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring

theorem lap_coshW (a : ℝ) (x : Vertex d) :
    lap (coshW a) x = 2 * d * (Real.cosh a - 1) * coshW a x := by
  rw [lap, sum_neighbors_coshW]
  ring

/-- The lazy kernel powers of `ℤ^d` on the weight: `Σ_x Qⁿ(y, x) coshW(x) = cosh(a)ⁿ coshW(y)`. -/
theorem hasSum_lazyPow_mul_coshW [NeZero d] (a : ℝ) (n : ℕ) (y : Vertex d) :
    HasSum (fun x => lazyPow (openGraph (allOpen d)) (2 * d) n y x * coshW a x)
      (Real.cosh a ^ n * coshW a y) := by
  induction n generalizing y with
  | zero =>
      have e : (fun x => lazyPow (openGraph (allOpen d)) (2 * d) 0 y x * coshW a x) =
          fun x => if x = y then coshW a y else 0 := by
        funext x
        rw [lazyPow_zero]
        by_cases hxy : y = x
        · subst hxy
          simp
        · rw [if_neg hxy, if_neg (Ne.symm hxy), zero_mul]
      rw [e, pow_zero, one_mul]
      exact hasSum_ite_eq y (coshW a y)
  | succ n ih =>
      have h := (hasSum_sum fun z (_ : z ∈ (openGraph (allOpen d)).neighborFinset y) =>
        ih z).mul_left (1 / ((2 * d : ℕ) : ℝ))
      have e : (fun x => lazyPow (openGraph (allOpen d)) (2 * d) (n + 1) y x * coshW a x) =
          fun x => 1 / ((2 * d : ℕ) : ℝ) * ∑ z ∈ (openGraph (allOpen d)).neighborFinset y,
            lazyPow (openGraph (allOpen d)) (2 * d) n z x * coshW a x := by
        funext x
        rw [lazyPow_succ, degree_allOpen, div_self two_mul_ne_zero_of_neZero, sub_self, zero_mul,
          zero_add, mul_assoc, Finset.sum_mul]
      have hv : 1 / ((2 * d : ℕ) : ℝ) * ∑ z ∈ (openGraph (allOpen d)).neighborFinset y,
          Real.cosh a ^ n * coshW a z = Real.cosh a ^ (n + 1) * coshW a y := by
        rw [← Finset.mul_sum, sum_neighborFinset_allOpen, sum_neighbors_coshW, pow_succ]
        have hd' : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
        push_cast
        field_simp
      rw [e, ← hv]
      exact h

/-- The Poisson weights against a geometric sequence (real form). -/
theorem hasSum_poissonWeight_mul_pow_real (D : ℕ) (t μ : ℝ) :
    HasSum (fun n => poissonWeight D t n * μ ^ n) (Real.exp (D * t * (μ - 1))) := by
  have h := NormedSpace.expSeries_div_hasSum_exp (D * t * μ)
  rw [← Real.exp_eq_exp_ℝ] at h
  have h2 := h.mul_left (Real.exp (-(D * t)))
  have he : Real.exp (-(D * t)) * Real.exp (D * t * μ) = Real.exp (D * t * (μ - 1)) := by
    rw [← Real.exp_add]
    ring_nf
  rw [he] at h2
  refine h2.congr_fun fun n => ?_
  unfold poissonWeight
  rw [mul_pow]
  ring_nf

/-- **The heat kernel on the weight**: `Σ_x Φ_s(y, x) coshW(x) = e^{2ds(cosh a - 1)} coshW(y)`. -/
theorem hasSum_zdHeat_mul_coshW [NeZero d] (a : ℝ) {s : ℝ} (hs : 0 ≤ s) (y : Vertex d) :
    HasSum (fun x => zdHeat d s y x * coshW a x)
      (Real.exp (2 * d * s * (Real.cosh a - 1)) * coshW a y) := by
  have hdeg := openGraph_degree_le (allOpen d)
  set F : ℕ × Vertex d → ℝ := fun q =>
    poissonWeight (2 * d) s q.1 *
      (lazyPow (openGraph (allOpen d)) (2 * d) q.1 y q.2 * coshW a q.2) with hF
  have hF0 : 0 ≤ F := fun q => mul_nonneg (poissonWeight_nonneg hs _)
    (mul_nonneg (lazyPow_mem_Icc two_mul_pos_of_neZero hdeg _ _ _).1 (coshW_pos a _).le)
  have hfib : ∀ n, HasSum (fun x => F (n, x))
      (poissonWeight (2 * d) s n * (Real.cosh a ^ n * coshW a y)) := fun n =>
    (hasSum_lazyPow_mul_coshW a n y).mul_left _
  have htot : HasSum (fun n => poissonWeight (2 * d) s n * (Real.cosh a ^ n * coshW a y))
      (Real.exp (2 * d * s * (Real.cosh a - 1)) * coshW a y) := by
    have := (hasSum_poissonWeight_mul_pow_real (2 * d) s (Real.cosh a)).mul_right (coshW a y)
    push_cast at this
    refine this.congr_fun fun n => ?_
    ring
  have hFs : Summable F := by
    rw [summable_prod_of_nonneg hF0]
    exact ⟨fun n => (hfib n).summable, htot.summable.congr fun n => ((hfib n).tsum_eq).symm⟩
  have hval := (hFs.hasSum.prod_fiberwise hfib).unique htot
  have hfib2 : ∀ x, HasSum (fun n => F (n, x)) (zdHeat d s y x * coshW a x) := by
    intro x
    have h := (summable_vsrwHeat (G := openGraph (allOpen d)) (D := 2 * d) two_mul_pos_of_neZero
      hdeg s y x).hasSum.mul_right (coshW a x)
    refine h.congr_fun fun n => ?_
    simp only [hF]
    ring
  have h2 := ((Equiv.prodComm (Vertex d) ℕ).hasSum_iff.2 hFs.hasSum).prod_fiberwise
    fun x => hfib2 x
  rw [hval] at h2
  exact h2

/-- `coshW a x ≤ coshW a y e^{a |y - x|₁}` for `a ≥ 0`. -/
theorem coshW_le_mul_exp {a : ℝ} (ha : 0 ≤ a) (x y : Vertex d) :
    coshW a x ≤ coshW a y * Real.exp (a * ∑ i, |(((y - x) i : ℤ) : ℝ)|) := by
  have h : ∀ i : Fin d, Real.cosh (a * ((x i : ℤ) : ℝ)) ≤
      Real.cosh (a * ((y i : ℤ) : ℝ)) * Real.exp (a * |(((y - x) i : ℤ) : ℝ)|) := by
    intro i
    have := Rigidity.Poincare.cosh_le_cosh_mul_exp (a * ((x i : ℤ) : ℝ)) (a * ((y i : ℤ) : ℝ))
    have e : |a * ((x i : ℤ) : ℝ) - a * ((y i : ℤ) : ℝ)| = a * |(((y - x) i : ℤ) : ℝ)| := by
      rw [← mul_sub, abs_mul, abs_of_nonneg ha, Pi.sub_apply, Int.cast_sub, abs_sub_comm]
    rwa [e] at this
  rw [coshW, coshW, Finset.mul_sum, Real.exp_sum, ← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod (fun i _ => (Real.cosh_pos _).le) fun i _ => h i

/-- `e^{a|x|₁} ≤ 2^d coshW a x`. -/
theorem exp_le_two_pow_mul_coshW (a : ℝ) (x : Vertex d) :
    Real.exp (∑ i, a * |((x i : ℤ) : ℝ)|) ≤ 2 ^ d * coshW a x := by
  have h : ∀ i : Fin d, Real.exp (a * |((x i : ℤ) : ℝ)|) ≤ 2 * Real.cosh (a * ((x i : ℤ) : ℝ)) := by
    intro i
    rcases le_total 0 a with ha | ha
    · have e : a * |((x i : ℤ) : ℝ)| = |a * ((x i : ℤ) : ℝ)| := by
        rw [abs_mul, abs_of_nonneg ha]
      rw [e, ← Real.cosh_abs (a * ((x i : ℤ) : ℝ)), Real.cosh_eq]
      have := Real.exp_pos (-|a * ((x i : ℤ) : ℝ)|)
      linarith
    · have e0 : Real.exp (a * |((x i : ℤ) : ℝ)|) ≤ 1 :=
        Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg ha (abs_nonneg _))
      have c0 := Real.one_le_cosh (a * ((x i : ℤ) : ℝ))
      linarith
  rw [Real.exp_sum]
  calc ∏ i, Real.exp (a * |((x i : ℤ) : ℝ)|) ≤ ∏ i, (2 * Real.cosh (a * ((x i : ℤ) : ℝ))) :=
        Finset.prod_le_prod (fun i _ => (Real.exp_pos _).le) fun i _ => h i
    _ = 2 ^ d * coshW a x := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, coshW]

end Rigidity.Poincare.GeneralDim
