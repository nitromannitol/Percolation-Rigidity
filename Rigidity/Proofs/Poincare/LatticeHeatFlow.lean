import Rigidity.Proofs.Poincare.HeatMaximal
import Rigidity.Proofs.Poincare.SteinScalar

/-!
# The heat flow of finitely supported functions on `ℤ²` and the weights `cosh`

* `lap u x = Σ_i (u(x + e_i) + u(x - e_i)) - 4 u(x)`, the Laplacian of `ℤ²`
  (`openLaplacian_allOpen`);
* `heatF S f s x = Σ_{y ∈ S} Φ_s(x, y) f(y)`, the heat flow of `f` supported in `S`: it solves
  `∂_s heatF = lap heatF` (`hasDerivAt_heatF`), starts at `f` (`heatF_zero`), and satisfies
  Jensen's inequality `(heatF f)^p ≤ heatF (f^p)` for `p ≥ 1`, `f ≥ 0` (`heatF_rpow_le`);
* `steinPointwise`: the lattice form of the identity (D.11) of Armstrong, Kuusi and Mourrat,
  `lap(v^p) - p v^{p-1} lap v ≥ (p(p-1)/2) M^{p-2} Σ_i (v(x + e_i) - v(x))²` for `0 ≤ v ≤ M`;
* `coshW a x = cosh(a x₀) cosh(a x₁)`: `lap coshW = 4(cosh a - 1) coshW`, and the heat kernel
  acts on it by `e^{4s(cosh a - 1)}` (`hasSum_openHeat_mul_coshW`); the comparison
  `coshW a x ≤ coshW a y e^{a|y - x|₁}`.
-/

open scoped Classical
open LatticeProb LatticeProb.Percolation Rigidity.Green

namespace Rigidity.Poincare

/-- The Laplacian of `ℤ²`. -/
noncomputable def lap (u : Vertex 2 → ℝ) (x : Vertex 2) : ℝ :=
  ∑ i : Fin 2, (u (x + unit i) + u (x - unit i)) - 4 * u x

theorem openLaplacian_allOpen (u : Vertex 2 → ℝ) (x : Vertex 2) :
    openLaplacian (allOpen 2) u x = lap u x := by
  rw [openLaplacian, Finset.sum_sub_distrib, Finset.sum_const,
    SimpleGraph.card_neighborFinset_eq_degree, Rigidity.Corrector.degree_allOpen,
    sum_neighborFinset_allOpen_real, lap, nsmul_eq_mul]
  norm_num

theorem lap_finset_sum {ι : Type*} (S : Finset ι) (g : ι → Vertex 2 → ℝ) (x : Vertex 2) :
    lap (fun z => ∑ y ∈ S, g y z) x = ∑ y ∈ S, lap (g y) x := by
  simp only [lap, Fin.sum_univ_two, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.mul_sum]

theorem lap_mul_const (u : Vertex 2 → ℝ) (c : ℝ) (x : Vertex 2) :
    lap (fun z => u z * c) x = lap u x * c := by
  simp only [lap, Fin.sum_univ_two]
  ring

/-- The heat flow `Σ_{y ∈ S} Φ_s(x, y) f(y)` of a function supported in `S`. -/
noncomputable def heatF (S : Finset (Vertex 2)) (f : Vertex 2 → ℝ) (s : ℝ) (x : Vertex 2) : ℝ :=
  ∑ y ∈ S, openHeat (allOpen 2) s x y * f y

/-- **The heat equation** for `heatF`. -/
theorem hasDerivAt_heatF (S : Finset (Vertex 2)) (f : Vertex 2 → ℝ) (s : ℝ) (x : Vertex 2) :
    HasDerivAt (fun s => heatF S f s x) (lap (heatF S f s) x) s := by
  have h : ∀ y ∈ S, HasDerivAt (fun s => openHeat (allOpen 2) s x y * f y)
      (lap (fun z => openHeat (allOpen 2) s z y) x * f y) s := by
    intro y _
    have := (hasDerivAt_openHeat (allOpen 2) s x y).mul_const (f y)
    rwa [openLaplacian_allOpen] at this
  refine (HasDerivAt.fun_sum h).congr_deriv ?_
  unfold heatF
  rw [lap_finset_sum]
  simp only [lap_mul_const]

theorem continuous_heatF (S : Finset (Vertex 2)) (f : Vertex 2 → ℝ) (x : Vertex 2) :
    Continuous fun s => heatF S f s x :=
  continuous_iff_continuousAt.2 fun s => (hasDerivAt_heatF S f s x).continuousAt

theorem heatF_zero {S : Finset (Vertex 2)} {f : Vertex 2 → ℝ} (hfS : ∀ y ∉ S, f y = 0)
    (x : Vertex 2) : heatF S f 0 x = f x := by
  unfold heatF
  simp only [openHeat_zero, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · exact (hfS x h).symm

theorem heatF_nonneg {S : Finset (Vertex 2)} {f : Vertex 2 → ℝ} (hf : ∀ y, 0 ≤ f y) {s : ℝ}
    (hs : 0 ≤ s) (x : Vertex 2) : 0 ≤ heatF S f s x :=
  Finset.sum_nonneg fun y _ => mul_nonneg (openHeat_nonneg _ hs x y) (hf y)

theorem sum_openHeat_le_one (S : Finset (Vertex 2)) {s : ℝ} (hs : 0 ≤ s) (x : Vertex 2) :
    ∑ y ∈ S, openHeat (allOpen 2) s x y ≤ 1 :=
  sum_le_hasSum S (fun y _ => openHeat_nonneg _ hs x y) (hasSum_openHeat _ hs x)

/-- **Jensen's inequality** for the heat flow: `(heatF f)^p ≤ heatF (f^p)`, `p ≥ 1`, `f ≥ 0`. -/
theorem heatF_rpow_le {S : Finset (Vertex 2)} {f : Vertex 2 → ℝ} (hf : ∀ y, 0 ≤ f y) {s p : ℝ}
    (hs : 0 ≤ s) (hp : 1 ≤ p) (x : Vertex 2) :
    heatF S f s x ^ p ≤ ∑ y ∈ S, openHeat (allOpen 2) s x y * f y ^ p := by
  set w : Vertex 2 → ℝ := fun y => openHeat (allOpen 2) s x y with hw
  set W := ∑ y ∈ S, w y with hW
  have hw0 : ∀ y, 0 ≤ w y := fun y => openHeat_nonneg _ hs x y
  have hW1 : W ≤ 1 := sum_openHeat_le_one S hs x
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
theorem steinPointwise {p M : ℝ} (hp1 : 1 < p) (hp2 : p ≤ 2) {v : Vertex 2 → ℝ}
    (hv : ∀ z, 0 ≤ v z) {x : Vertex 2} (hvx : v x ≤ M) (hvi : ∀ i, v (x + unit i) ≤ M) :
    p * (p - 1) / 2 * M ^ (p - 2) * ∑ i : Fin 2, (v (x + unit i) - v x) ^ 2 ≤
      lap (fun z => v z ^ p) x - p * v x ^ (p - 1) * lap v x := by
  set T : Vertex 2 → ℝ := fun y => v y ^ p - v x ^ p - p * v x ^ (p - 1) * (v y - v x) with hT
  have e : lap (fun z => v z ^ p) x - p * v x ^ (p - 1) * lap v x =
      ∑ i : Fin 2, (T (x + unit i) + T (x - unit i)) := by
    simp only [lap, hT, Fin.sum_univ_two]
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
  rw [e, Fin.sum_univ_two, Fin.sum_univ_two, mul_add]
  linarith [h1 0, h1 1, h2 0, h2 1]

/-- The weight `cosh(a x₀) cosh(a x₁)`. -/
noncomputable def coshW (a : ℝ) (x : Vertex 2) : ℝ :=
  Real.cosh (a * ((x 0 : ℤ) : ℝ)) * Real.cosh (a * ((x 1 : ℤ) : ℝ))

theorem coshW_pos (a : ℝ) (x : Vertex 2) : 0 < coshW a x :=
  mul_pos (Real.cosh_pos _) (Real.cosh_pos _)

theorem sum_neighbors_coshW (a : ℝ) (x : Vertex 2) :
    ∑ i : Fin 2, (coshW a (x + unit i) + coshW a (x - unit i)) = 4 * Real.cosh a * coshW a x := by
  simp only [coshW, Fin.sum_univ_two, unit, Pi.add_apply, Pi.sub_apply, Pi.single_eq_same]
  simp only [Pi.single_apply, one_ne_zero, if_false, zero_ne_one,
    add_zero, sub_zero, Int.cast_add, Int.cast_sub, Int.cast_one, mul_add, mul_sub, mul_one,
    Real.cosh_add, Real.cosh_sub]
  ring

theorem lap_coshW (a : ℝ) (x : Vertex 2) :
    lap (coshW a) x = 4 * (Real.cosh a - 1) * coshW a x := by
  rw [lap, sum_neighbors_coshW]
  ring

/-- The lazy kernel powers of `ℤ²` on the weight: `Σ_x Qⁿ(y, x) coshW(x) = cosh(a)ⁿ coshW(y)`. -/
theorem hasSum_lazyPow_mul_coshW (a : ℝ) (n : ℕ) (y : Vertex 2) :
    HasSum (fun x => lazyPow (openGraph (allOpen 2)) 4 n y x * coshW a x)
      (Real.cosh a ^ n * coshW a y) := by
  induction n generalizing y with
  | zero =>
      have e : (fun x => lazyPow (openGraph (allOpen 2)) 4 0 y x * coshW a x) =
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
      have h := (hasSum_sum fun z (_ : z ∈ (openGraph (allOpen 2)).neighborFinset y) =>
        ih z).mul_left (1 / (4 : ℝ))
      have h4 : (1 - ((4 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) = 0 := by norm_num
      have e : (fun x => lazyPow (openGraph (allOpen 2)) 4 (n + 1) y x * coshW a x) =
          fun x => 1 / (4 : ℝ) * ∑ z ∈ (openGraph (allOpen 2)).neighborFinset y,
            lazyPow (openGraph (allOpen 2)) 4 n z x * coshW a x := by
        funext x
        rw [lazyPow_succ, Rigidity.Corrector.degree_allOpen, h4, zero_mul, zero_add, mul_assoc,
          Finset.sum_mul]
        norm_num
      have hv : 1 / (4 : ℝ) * ∑ z ∈ (openGraph (allOpen 2)).neighborFinset y,
          Real.cosh a ^ n * coshW a z = Real.cosh a ^ (n + 1) * coshW a y := by
        rw [← Finset.mul_sum, sum_neighborFinset_allOpen_real, sum_neighbors_coshW, pow_succ]
        ring
      rw [e, ← hv]
      exact h

/-- The Poisson weights against a geometric sequence (real form). -/
theorem hasSum_poissonWeight_mul_pow_real (t μ : ℝ) :
    HasSum (fun n => poissonWeight 4 t n * μ ^ n) (Real.exp (4 * t * (μ - 1))) := by
  have h := NormedSpace.expSeries_div_hasSum_exp (4 * t * μ)
  rw [← Real.exp_eq_exp_ℝ] at h
  have h2 := h.mul_left (Real.exp (-(4 * t)))
  have he : Real.exp (-(4 * t)) * Real.exp (4 * t * μ) = Real.exp (4 * t * (μ - 1)) := by
    rw [← Real.exp_add]
    ring_nf
  rw [he] at h2
  refine h2.congr_fun fun n => ?_
  unfold poissonWeight
  push_cast
  rw [mul_pow]
  ring

/-- **The heat kernel on the weight**: `Σ_x Φ_s(y, x) coshW(x) = e^{4s(cosh a - 1)} coshW(y)`. -/
theorem hasSum_openHeat_mul_coshW (a : ℝ) {s : ℝ} (hs : 0 ≤ s) (y : Vertex 2) :
    HasSum (fun x => openHeat (allOpen 2) s y x * coshW a x)
      (Real.exp (4 * s * (Real.cosh a - 1)) * coshW a y) := by
  have hdeg := openGraph_degree_le_four (allOpen 2)
  set F : ℕ × Vertex 2 → ℝ := fun q =>
    poissonWeight 4 s q.1 * (lazyPow (openGraph (allOpen 2)) 4 q.1 y q.2 * coshW a q.2) with hF
  have hF0 : 0 ≤ F := fun q => mul_nonneg (poissonWeight_nonneg hs _)
    (mul_nonneg (lazyPow_mem_Icc (by norm_num) hdeg _ _ _).1 (coshW_pos a _).le)
  have hfib : ∀ n, HasSum (fun x => F (n, x))
      (poissonWeight 4 s n * (Real.cosh a ^ n * coshW a y)) := fun n =>
    (hasSum_lazyPow_mul_coshW a n y).mul_left _
  have htot : HasSum (fun n => poissonWeight 4 s n * (Real.cosh a ^ n * coshW a y))
      (Real.exp (4 * s * (Real.cosh a - 1)) * coshW a y) := by
    have := (hasSum_poissonWeight_mul_pow_real s (Real.cosh a)).mul_right (coshW a y)
    refine this.congr_fun fun n => ?_
    ring
  have hFs : Summable F := by
    rw [summable_prod_of_nonneg hF0]
    exact ⟨fun n => (hfib n).summable, htot.summable.congr fun n => ((hfib n).tsum_eq).symm⟩
  have hval := (hFs.hasSum.prod_fiberwise hfib).unique htot
  have hfib2 : ∀ x, HasSum (fun n => F (n, x))
      (openHeat (allOpen 2) s y x * coshW a x) := by
    intro x
    have h := (summable_vsrwHeat (G := openGraph (allOpen 2)) (D := 4) (by norm_num) hdeg s y
      x).hasSum.mul_right (coshW a x)
    refine h.congr_fun fun n => ?_
    simp only [hF]
    ring
  have h2 := ((Equiv.prodComm (Vertex 2) ℕ).hasSum_iff.2 hFs.hasSum).prod_fiberwise
    fun x => hfib2 x
  rw [hval] at h2
  exact h2

theorem cosh_le_cosh_mul_exp (u v : ℝ) : Real.cosh u ≤ Real.cosh v * Real.exp |u - v| := by
  have e : u = v + (u - v) := by ring
  set d := u - v
  have hs : |Real.sinh v| ≤ Real.cosh v := by
    have h1 := Real.cosh_sq v
    have h2 := Real.cosh_pos v
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (Real.sinh v + Real.cosh v),
      sq_nonneg (Real.sinh v - Real.cosh v)]
  have hd : Real.cosh d + |Real.sinh d| = Real.exp |d| := by
    rw [← Real.cosh_abs, Real.abs_sinh, Real.cosh_add_sinh]
  rw [e, Real.cosh_add]
  calc Real.cosh v * Real.cosh d + Real.sinh v * Real.sinh d
      ≤ Real.cosh v * Real.cosh d + |Real.sinh v| * |Real.sinh d| := by
        rw [← abs_mul]
        linarith [le_abs_self (Real.sinh v * Real.sinh d)]
    _ ≤ Real.cosh v * Real.cosh d + Real.cosh v * |Real.sinh d| := by
        gcongr
    _ = Real.cosh v * Real.exp |d| := by rw [← hd]; ring

/-- `coshW a x ≤ coshW a y e^{a |y - x|₁}` for `a ≥ 0`. -/
theorem coshW_le_mul_exp {a : ℝ} (ha : 0 ≤ a) (x y : Vertex 2) :
    coshW a x ≤ coshW a y *
      Real.exp (a * (|(((y - x) 0 : ℤ) : ℝ)| + |(((y - x) 1 : ℤ) : ℝ)|)) := by
  have h : ∀ i : Fin 2, Real.cosh (a * ((x i : ℤ) : ℝ)) ≤
      Real.cosh (a * ((y i : ℤ) : ℝ)) * Real.exp (a * |(((y - x) i : ℤ) : ℝ)|) := by
    intro i
    have := cosh_le_cosh_mul_exp (a * ((x i : ℤ) : ℝ)) (a * ((y i : ℤ) : ℝ))
    have e : |a * ((x i : ℤ) : ℝ) - a * ((y i : ℤ) : ℝ)| = a * |(((y - x) i : ℤ) : ℝ)| := by
      rw [← mul_sub, abs_mul, abs_of_nonneg ha, Pi.sub_apply, Int.cast_sub, abs_sub_comm]
    rwa [e] at this
  rw [coshW, coshW, mul_add, Real.exp_add]
  calc Real.cosh (a * ((x 0 : ℤ) : ℝ)) * Real.cosh (a * ((x 1 : ℤ) : ℝ))
      ≤ (Real.cosh (a * ((y 0 : ℤ) : ℝ)) * Real.exp (a * |(((y - x) 0 : ℤ) : ℝ)|)) *
          (Real.cosh (a * ((y 1 : ℤ) : ℝ)) * Real.exp (a * |(((y - x) 1 : ℤ) : ℝ)|)) :=
        mul_le_mul (h 0) (h 1) (Real.cosh_pos _).le (by positivity)
    _ = _ := by ring

theorem exp_le_four_mul_coshW (a : ℝ) (x : Vertex 2) :
    Real.exp (a * |((x 0 : ℤ) : ℝ)| + a * |((x 1 : ℤ) : ℝ)|) ≤ 4 * coshW a x := by
  have h : ∀ t : ℝ, Real.exp |t| ≤ 2 * Real.cosh t := by
    intro t
    rw [← Real.cosh_abs t, Real.cosh_eq]
    have := Real.exp_pos (-|t|)
    linarith
  rw [Real.exp_add, coshW]
  have h0 := h (a * ((x 0 : ℤ) : ℝ))
  have h1 := h (a * ((x 1 : ℤ) : ℝ))
  rw [abs_mul] at h0 h1
  rcases le_total 0 a with ha | ha
  · rw [abs_of_nonneg ha] at h0 h1
    nlinarith [Real.exp_pos (a * |((x 0 : ℤ) : ℝ)|), Real.exp_pos (a * |((x 1 : ℤ) : ℝ)|)]
  · have e0 : Real.exp (a * |((x 0 : ℤ) : ℝ)|) ≤ 1 :=
      Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg ha (abs_nonneg _))
    have e1 : Real.exp (a * |((x 1 : ℤ) : ℝ)|) ≤ 1 :=
      Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg ha (abs_nonneg _))
    have c0 := Real.one_le_cosh (a * ((x 0 : ℤ) : ℝ))
    have c1 := Real.one_le_cosh (a * ((x 1 : ℤ) : ℝ))
    nlinarith [Real.exp_pos (a * |((x 0 : ℤ) : ℝ)|), Real.exp_pos (a * |((x 1 : ℤ) : ℝ)|)]

end Rigidity.Poincare
