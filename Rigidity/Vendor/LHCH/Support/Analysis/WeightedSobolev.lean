/-
Copied from Lattice-High-Contrast-Homogenization (https://github.com/nitromannitol/Lattice-High-Contrast-Homogenization),
commit f47a932a9f7a07e1692bfe4aae564d02e8ca0944, file `LatticeHC/Support/Analysis/WeightedSobolev.lean` (Apache License 2.0,
Copyright 2026 Ahmed Bou-Rabee and Yuval Peres).
Changes: imports `LatticeHC.*` renamed to `Rigidity.Vendor.LHCH.*`; namespace `LatticeHC` kept.
-/
import Rigidity.Vendor.LHCH.Model.Conductance
import Rigidity.Vendor.LHCH.Support.Analysis.LatticeSobolev
import Rigidity.Vendor.LHCH.Support.Lattice.Membership

/-!
# The weighted Sobolev inequality

The inequality (e:weighted-Sobolev), proved here rather than cited from ADS15
(3.13): `‖v‖²_{4d/(2d−3),B} ≤ C R² ‖ν‖_{2d,B} |B|⁻¹ Σ_e c_e|∇v(e)|²` for `v` vanishing outside a
lattice cube `B` of side `R ≥ 1`, with `C = 8α²`, `α = 4(d−1)/(2d−3)`. Apply the lattice ℓ¹ Sobolev
inequality to `|v|^α`, bound its gradient by `α(|v(x)|^{α−1} + |v(y)|^{α−1})|∇v|`, and use
Cauchy–Schwarz with the weights `c_e^{±1}` and Hölder with exponents `2d` and `2d/(2d−1)`.
-/

open LatticeProb
open scoped ENNReal

noncomputable section

namespace LatticeHC

variable {d : ℕ}

/-- Tangent line bound: for `0 ≤ a ≤ b` and `1 ≤ α`, `b^α − a^α ≤ α b^{α−1} (b − a)`. -/
theorem rpow_sub_rpow_le_mul_rpow_sub {a b α : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hα : 1 ≤ α) :
    b ^ α - a ^ α ≤ α * b ^ (α - 1) * (b - a) := by
  rcases eq_or_lt_of_le (ha.trans hab) with hb | hb
  · have : a = 0 := le_antisymm (hb ▸ hab) ha
    subst this; rw [← hb]; simp
  · have hu : (-1 : ℝ) ≤ a / b - 1 := by
      have : 0 ≤ a / b := div_nonneg ha hb.le
      linarith
    have key := one_add_mul_self_le_rpow_one_add hu hα
    simp only [add_sub_cancel] at key
    have hbα : b ^ α = b ^ (α - 1) * b := by
      rw [← Real.rpow_add_one hb.ne']; ring_nf
    have hau : a ^ α = b ^ α * (a / b) ^ α := by
      rw [← Real.mul_rpow hb.le (div_nonneg ha hb.le), mul_div_cancel₀ _ hb.ne']
    have hb0 : 0 < b ^ α := Real.rpow_pos_of_pos hb α
    have h1 : b ^ α * (1 + α * (a / b - 1)) ≤ a ^ α := by
      rw [hau]; exact mul_le_mul_of_nonneg_left key hb0.le
    have h2 : b ^ α * (1 + α * (a / b - 1)) = b ^ α - α * b ^ (α - 1) * (b - a) := by
      rw [hbα]; field_simp; ring
    linarith

/-- Pointwise bound for the difference of `α`-th powers of absolute values. -/
theorem abs_abs_rpow_sub_le (a b : ℝ) {α : ℝ} (hα : 1 ≤ α) :
    |(|b| ^ α) - |a| ^ α| ≤ α * (|a| ^ (α - 1) + |b| ^ (α - 1)) * |b - a| := by
  have hα0 : 0 ≤ α := by linarith
  have hα1 : 0 ≤ α - 1 := by linarith
  have habs : ∀ x y : ℝ, |x| ≤ |y| →
      |(|y| ^ α) - |x| ^ α| ≤ α * |y| ^ (α - 1) * |y - x| := by
    intro x y hxy
    have h1 := rpow_sub_rpow_le_mul_rpow_sub (abs_nonneg x) hxy hα
    have h2 : |x| ^ α ≤ |y| ^ α := Real.rpow_le_rpow (abs_nonneg x) hxy hα0
    rw [abs_of_nonneg (by linarith)]
    calc _ ≤ α * |y| ^ (α - 1) * (|y| - |x|) := h1
      _ ≤ α * |y| ^ (α - 1) * |y - x| := by
        gcongr
        exact (le_abs_self _).trans (abs_abs_sub_abs_le_abs_sub y x)
  have hnn : 0 ≤ α * |b - a| := by positivity
  rcases le_total |a| |b| with h | h
  · have := habs a b h
    calc _ ≤ α * |b| ^ (α - 1) * |b - a| := this
      _ ≤ _ := by
        have : 0 ≤ |a| ^ (α - 1) := Real.rpow_nonneg (abs_nonneg a) _
        nlinarith [mul_nonneg hnn this]
  · have := habs b a h
    rw [abs_sub_comm a b, abs_sub_comm] at this
    calc _ ≤ α * |a| ^ (α - 1) * |b - a| := this
      _ ≤ _ := by
        have : 0 ≤ |b| ^ (α - 1) := Real.rpow_nonneg (abs_nonneg b) _
        nlinarith [mul_nonneg hnn this]

/-- The coordinate `i` of `y − e_j` is `y_i − 1` if `i = j` and `y_i` otherwise. -/
theorem sub_unit_apply_coord (y : Site d) (j i : Fin d) :
    (y - unit j) i = y i - if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst h; simp [unit]
  · simp [unit, h]

/-- The cube `z + {0, …, R}^d` lies in the enlarged cube `z − 𝟙 + {0, …, R + 1}^d`. -/
theorem latticeCube_subset_shift (z : Site d) (R : ℕ) :
    latticeCube z R ⊆ latticeCube (z - fun _ => 1) (R + 1) := by
  intro x hx
  rw [mem_latticeCube_iff_coord] at hx ⊢
  intro i
  obtain ⟨h1, h2⟩ := hx i
  simp only [Pi.sub_apply]
  push_cast
  constructor <;> omega

/-- Every site of the cube `z + {0, …, R}^d` minus a unit vector lies in the enlarged cube
`z − 𝟙 + {0, …, R + 1}^d`. -/
theorem sub_unit_mem_shift {z y : Site d} {R : ℕ} (hy : y ∈ latticeCube z R) (j : Fin d) :
    y - unit j ∈ latticeCube (z - fun _ => 1) (R + 1) := by
  rw [mem_latticeCube_iff_coord] at hy ⊢
  intro i
  obtain ⟨h1, h2⟩ := hy i
  rw [sub_unit_apply_coord, Pi.sub_apply]
  push_cast
  split_ifs <;> constructor <;> omega

/-- A function vanishing off the cube `z + {0, …, R}^d` has all its nonzero gradients at sites
of the enlarged cube `z − 𝟙 + {0, …, R + 1}^d`. -/
theorem mem_shift_of_gradient_ne {z : Site d} {R : ℕ} {v : Site d → ℝ}
    (hv : ∀ x, x ∉ latticeCube z R → v x = 0) (x : Site d) (j : Fin d)
    (h : v (x + unit j) ≠ v x) : x ∈ latticeCube (z - fun _ => 1) (R + 1) := by
  by_cases hx : x ∈ latticeCube z R
  · exact latticeCube_subset_shift z R hx
  · have hx' : x + unit j ∈ latticeCube z R := by
      by_contra hc
      exact h (by rw [hv _ hc, hv _ hx])
    have := sub_unit_mem_shift hx' j
    simpa using this

/-- The real-valued field `ν_x = Σ_{y ∼ x} c_{xy}⁻¹`. -/
def nuReal (c : Edge d → ℝ) (x : Site d) : ℝ :=
  ∑ j : Fin d, ((c (x, j))⁻¹ + (c (x - unit j, j))⁻¹)

/-- For positive conductances, `ν` is the `ℝ≥0∞`-valued image of the real field `nuReal`. -/
theorem nuField_eq_ofReal_nuReal {c : Edge d → ℝ} (hc : ∀ e, 0 < c e) (x : Site d) :
    nuField c x = ENNReal.ofReal (nuReal c x) := by
  unfold nuField nuReal
  rw [ENNReal.ofReal_sum_of_nonneg]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [ENNReal.ofReal_add (inv_nonneg.2 (hc _).le) (inv_nonneg.2 (hc _).le),
      ENNReal.ofReal_inv_of_pos (hc _), ENNReal.ofReal_inv_of_pos (hc _)]
  · intro j _
    have := hc (x, j)
    have := hc (x - unit j, j)
    positivity

/-- The nonnegativity of `nuReal` for positive conductances. -/
theorem nuReal_nonneg {c : Edge d → ℝ} (hc : ∀ e, 0 < c e) (x : Site d) : 0 ≤ nuReal c x := by
  unfold nuReal
  refine Finset.sum_nonneg fun j _ => ?_
  have := hc (x, j)
  have := hc (x - unit j, j)
  positivity

/-- The sum over the edges of `c_e⁻¹ (|v(x)|^q + |v(x+e_j)|^q)` is the sum over the vertices of
`ν_y |v(y)|^q`: each edge contributes its inverse conductance to both endpoints. -/
theorem sum_edge_inv_mul_rpow {c : Edge d → ℝ} {z : Site d} {R : ℕ} {v : Site d → ℝ} {q : ℝ}
    (hq : 0 < q) (hv : ∀ x, x ∉ latticeCube z R → v x = 0) :
    ∑ x ∈ latticeCube (z - fun _ => 1) (R + 1), ∑ j : Fin d,
      (c (x, j))⁻¹ * (|v x| ^ q + |v (x + unit j)| ^ q) =
    ∑ y ∈ latticeCube z R, nuReal c y * |v y| ^ q := by
  have hzero : ∀ x, x ∉ latticeCube z R → |v x| ^ q = 0 := fun x hx => by
    rw [hv x hx, abs_zero, Real.zero_rpow hq.ne']
  have h1 : ∀ j : Fin d, ∑ x ∈ latticeCube (z - fun _ => 1) (R + 1), (c (x, j))⁻¹ * |v x| ^ q =
      ∑ y ∈ latticeCube z R, (c (y, j))⁻¹ * |v y| ^ q := fun j => by
    symm
    refine Finset.sum_subset (latticeCube_subset_shift z R) fun x _ hx => ?_
    rw [hzero x hx, mul_zero]
  have h2 : ∀ j : Fin d, ∑ x ∈ latticeCube (z - fun _ => 1) (R + 1),
      (c (x, j))⁻¹ * |v (x + unit j)| ^ q =
      ∑ y ∈ latticeCube z R, (c (y - unit j, j))⁻¹ * |v y| ^ q := fun j => by
    have hinj : Function.Injective fun y : Site d => y - unit j := fun a b h => by
      simpa using h
    calc _ = ∑ x ∈ (latticeCube z R).image (fun y : Site d => y - unit j),
          (c (x, j))⁻¹ * |v (x + unit j)| ^ q := by
          symm
          refine Finset.sum_subset ?_ fun x _ hx => ?_
          · intro x hx
            obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
            exact sub_unit_mem_shift hy j
          · rw [hzero (x + unit j) (fun hm => hx (Finset.mem_image.2 ⟨_, hm, by simp⟩)),
              mul_zero]
      _ = _ := by
          rw [Finset.sum_image (fun a _ b _ h => hinj h)]
          simp
  simp only [mul_add, Finset.sum_add_distrib]
  rw [Finset.sum_comm, Finset.sum_comm (s := latticeCube (z - fun _ => 1) (R + 1))]
  simp only [h1, h2, nuReal, Finset.sum_mul, add_mul, Finset.sum_add_distrib]
  rw [Finset.sum_comm (s := latticeCube z R), Finset.sum_comm (s := latticeCube z R)]

/-- Weighted Cauchy–Schwarz: `(Σ P_i |D_i|)² ≤ (Σ c_i D_i²)(Σ P_i² / c_i)` for positive weights. -/
theorem sq_sum_mul_abs_le_sum_mul_sum_div {ι : Type*} (I : Finset ι) (c P D : ι → ℝ)
    (hc : ∀ i, 0 < c i) :
    (∑ i ∈ I, P i * |D i|) ^ 2 ≤ (∑ i ∈ I, c i * D i ^ 2) * ∑ i ∈ I, P i ^ 2 / c i := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq I (fun i => Real.sqrt (c i) * |D i|)
    (fun i => P i / Real.sqrt (c i))
  have hs : ∀ i, 0 < Real.sqrt (c i) := fun i => Real.sqrt_pos.2 (hc i)
  have e1 : ∀ i, Real.sqrt (c i) * |D i| * (P i / Real.sqrt (c i)) = P i * |D i| := fun i => by
    field_simp [(hs i).ne']
  have e2 : ∀ i, (Real.sqrt (c i) * |D i|) ^ 2 = c i * D i ^ 2 := fun i => by
    rw [mul_pow, Real.sq_sqrt (hc i).le, sq_abs]
  have e3 : ∀ i, (P i / Real.sqrt (c i)) ^ 2 = P i ^ 2 / c i := fun i => by
    rw [div_pow, Real.sq_sqrt (hc i).le]
  simpa only [e1, e2, e3] using h

/-- Hölder's inequality with exponents `2d` and `2d/(2d−1)`, for `d ≥ 1`. -/
theorem sum_mul_le_rpow_mul_rpow_two_mul {ι : Type*} (I : Finset ι) (f g : ι → ℝ)
    {D : ℝ} (hD : 1 ≤ D) (hf : ∀ i ∈ I, 0 ≤ f i) (hg : ∀ i ∈ I, 0 ≤ g i) :
    ∑ i ∈ I, f i * g i ≤ (∑ i ∈ I, f i ^ (2 * D)) ^ (1 / (2 * D)) *
      (∑ i ∈ I, g i ^ (2 * D / (2 * D - 1))) ^ ((2 * D - 1) / (2 * D)) := by
  have hp : (2 * D).HolderConjugate (2 * D / (2 * D - 1)) := by
    rw [Real.holderConjugate_iff]
    refine ⟨by linarith, ?_⟩
    have : 2 * D - 1 ≠ 0 := by linarith
    have : D ≠ 0 := by linarith
    field_simp
    ring
  have := Real.inner_le_Lp_mul_Lq_of_nonneg I hp hf hg
  convert this using 3
  have : 2 * D - 1 ≠ 0 := by linarith
  have : D ≠ 0 := by linarith
  field_simp

/-- **The unnormalized weighted Sobolev inequality**, in real numbers (ADS15 Prop. 3.5): with
`α = 4(d−1)/(2d−3)` and `ρ = 4d/(2d−3)`,
`(Σ_B |v|^ρ)^{(2d−3)/(2d)} ≤ 2 α² (Σ_e c_e |∇v(e)|²) (Σ_B ν^{2d})^{1/(2d)}`. -/
theorem weighted_sobolev_real (hd : 3 ≤ d) {c : Edge d → ℝ} (hc : ∀ e, 0 < c e) (z : Site d)
    (R : ℕ) {v : Site d → ℝ} (hv : ∀ x, x ∉ latticeCube z R → v x = 0) :
    (∑ x ∈ latticeCube z R, |v x| ^ (4 * (d : ℝ) / (2 * d - 3))) ^ (((2 : ℝ) * d - 3) / (2 * d)) ≤
      2 * (4 * ((d : ℝ) - 1) / (2 * d - 3)) ^ 2 *
        (∑ x ∈ latticeCube (z - fun _ => 1) (R + 1), ∑ j : Fin d,
          c (x, j) * (v (x + unit j) - v x) ^ 2) *
        (∑ x ∈ latticeCube z R, nuReal c x ^ (2 * (d : ℝ))) ^ (1 / (2 * (d : ℝ))) := by
  classical
  have hD : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hD1 : (0 : ℝ) < d - 1 := by linarith
  have hD2 : (0 : ℝ) < 2 * d - 3 := by linarith
  have hD3 : (0 : ℝ) < 2 * d - 1 := by linarith
  have hD0 : (0 : ℝ) < d := by linarith
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = 4 * ((d : ℝ) - 1) / (2 * d - 3) := ⟨_, rfl⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = 4 * (d : ℝ) / (2 * d - 3) := ⟨_, rfl⟩
  rw [← hα, ← hρ]
  have hα1 : 1 < α := by rw [hα, lt_div_iff₀ hD2]; linarith
  have hαs : α * ((d : ℝ) / (d - 1)) = ρ := by rw [hα, hρ]; field_simp
  obtain ⟨q, hq'⟩ : ∃ q : ℝ, q = 2 * (α - 1) := ⟨_, rfl⟩
  have hqpos : 0 < q := by rw [hq']; linarith
  have hqρ : q * (2 * (d : ℝ) / (2 * d - 1)) = ρ := by
    rw [hq', hα, hρ]; field_simp; ring
  set B := latticeCube z R with hB
  set S' := latticeCube (z - fun _ => 1) (R + 1) with hS'
  set N := ∑ x ∈ B, |v x| ^ ρ with hN
  set Nu := ∑ x ∈ B, nuReal c x ^ (2 * (d : ℝ)) with hNu
  set E := ∑ x ∈ S', ∑ j : Fin d, c (x, j) * (v (x + unit j) - v x) ^ 2 with hE
  have hN0 : 0 ≤ N := Finset.sum_nonneg fun x _ => Real.rpow_nonneg (abs_nonneg _) _
  have hNu0 : 0 ≤ Nu := Finset.sum_nonneg fun x _ => Real.rpow_nonneg (nuReal_nonneg hc x) _
  have hE0 : 0 ≤ E := Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (hc _).le (sq_nonneg _)
  -- the `ℓ¹` Sobolev inequality for `|v|^α`
  have hsob := sum_rpow_le_sum_abs_grad (d := d) (by omega) B S' (fun x => |v x| ^ α)
    (fun x hx => by simp [hv x hx, Real.zero_rpow (by linarith : α ≠ 0)])
    (fun x j h => mem_shift_of_gradient_ne hv x j fun h' => h (by simp only [h']))
  have hLHS : (∑ x ∈ B, |(|v x| ^ α)| ^ ((d : ℝ) / (d - 1))) = N := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _), ← Real.rpow_mul (abs_nonneg _), hαs]
  rw [hLHS] at hsob
  -- the pointwise bound on the gradient of `|v|^α`
  set P : Site d → Fin d → ℝ := fun x j => |v x| ^ (α - 1) + |v (x + unit j)| ^ (α - 1) with hP
  have hpt : ∑ x ∈ S', ∑ j : Fin d, |(|v (x + unit j)| ^ α) - |v x| ^ α| ≤
      α * ∑ x ∈ S', ∑ j : Fin d, P x j * |v (x + unit j) - v x| := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    calc _ ≤ α * (|v x| ^ (α - 1) + |v (x + unit j)| ^ (α - 1)) * |v (x + unit j) - v x| :=
          abs_abs_rpow_sub_le (v x) (v (x + unit j)) hα1.le
      _ = _ := by simp only [hP]; ring
  -- Cauchy–Schwarz
  have hcs : (∑ x ∈ S', ∑ j : Fin d, P x j * |v (x + unit j) - v x|) ^ 2 ≤
      E * ∑ x ∈ S', ∑ j : Fin d, P x j ^ 2 / c (x, j) := by
    have := sq_sum_mul_abs_le_sum_mul_sum_div (S' ×ˢ (Finset.univ : Finset (Fin d)))
      (fun e => c e) (fun e => P e.1 e.2) (fun e => v (e.1 + unit e.2) - v e.1) hc
    simpa only [Finset.sum_product] using this
  -- from edges to vertices
  have hP2 : ∑ x ∈ S', ∑ j : Fin d, P x j ^ 2 / c (x, j) ≤
      2 * ∑ y ∈ B, nuReal c y * |v y| ^ q := by
    rw [← sum_edge_inv_mul_rpow hqpos hv, Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    have h1 : ∀ y : ℝ, (|y| ^ (α - 1)) ^ 2 = |y| ^ q := fun y => by
      rw [hq', ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
      norm_num
      ring_nf
    have : P x j ^ 2 ≤ 2 * (|v x| ^ q + |v (x + unit j)| ^ q) := by
      rw [← h1, ← h1]
      nlinarith [sq_nonneg (|v x| ^ (α - 1) - |v (x + unit j)| ^ (α - 1))]
    calc P x j ^ 2 / c (x, j) ≤ 2 * (|v x| ^ q + |v (x + unit j)| ^ q) / c (x, j) := by
          gcongr
          exact (hc _).le
      _ = _ := by rw [div_eq_inv_mul]; ring
  -- Hölder
  have hH : ∑ y ∈ B, nuReal c y * |v y| ^ q ≤
      Nu ^ (1 / (2 * (d : ℝ))) * N ^ ((2 * (d : ℝ) - 1) / (2 * d)) := by
    have := sum_mul_le_rpow_mul_rpow_two_mul B (nuReal c) (fun y => |v y| ^ q)
      (by linarith : (1 : ℝ) ≤ d) (fun y _ => nuReal_nonneg hc y)
      (fun y _ => Real.rpow_nonneg (abs_nonneg _) _)
    have hN' : ∑ y ∈ B, (|v y| ^ q) ^ (2 * (d : ℝ) / (2 * d - 1)) = N := by
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [← Real.rpow_mul (abs_nonneg _), hqρ]
    rwa [hN'] at this
  have hX : (N ^ (((d : ℝ) - 1) / d)) ^ 2 ≤
      2 * α ^ 2 * E * (Nu ^ (1 / (2 * (d : ℝ))) * N ^ ((2 * (d : ℝ) - 1) / (2 * d))) := by
    have hα0 : 0 ≤ α := by linarith
    calc (N ^ (((d : ℝ) - 1) / d)) ^ 2
        ≤ (α * ∑ x ∈ S', ∑ j : Fin d, P x j * |v (x + unit j) - v x|) ^ 2 :=
          pow_le_pow_left₀ (Real.rpow_nonneg hN0 _) (hsob.trans hpt) 2
      _ = α ^ 2 * (∑ x ∈ S', ∑ j : Fin d, P x j * |v (x + unit j) - v x|) ^ 2 := mul_pow _ _ _
      _ ≤ α ^ 2 * (E * ∑ x ∈ S', ∑ j : Fin d, P x j ^ 2 / c (x, j)) := by gcongr
      _ ≤ α ^ 2 * (E * (2 * (Nu ^ (1 / (2 * (d : ℝ))) *
            N ^ ((2 * (d : ℝ) - 1) / (2 * d))))) := by
          gcongr
          linarith
      _ = _ := by ring
  rcases hN0.eq_or_lt with h0 | hpos
  · rw [← h0, Real.zero_rpow (by positivity)]
    positivity
  · have hsplit : (N ^ (((d : ℝ) - 1) / d)) ^ 2 =
        N ^ (((2 : ℝ) * d - 3) / (2 * d)) * N ^ ((2 * (d : ℝ) - 1) / (2 * d)) := by
      rw [← Real.rpow_add hpos, ← Real.rpow_natCast, ← Real.rpow_mul hN0]
      congr 1
      push_cast
      field_simp
      ring
    rw [hsplit] at hX
    have hb : 0 < N ^ ((2 * (d : ℝ) - 1) / (2 * d)) := Real.rpow_pos_of_pos hpos _
    refine le_of_mul_le_mul_right ?_ hb
    calc _ ≤ _ := hX
      _ = _ := by ring

/-- **The weighted Sobolev inequality for averages**, in real numbers: normalizing
`weighted_sobolev_real` by `|B| = (R + 1)^d` gives the stated `R²` scaling, `(R + 1)² ≤ 4 R²`. -/
theorem weighted_sobolev_avg_real (hd : 3 ≤ d) {c : Edge d → ℝ} (hc : ∀ e, 0 < c e) (z : Site d)
    (R : ℕ) (hR : 1 ≤ R) {v : Site d → ℝ} (hv : ∀ x, x ∉ latticeCube z R → v x = 0) :
    ((((latticeCube z R).card : ℝ)⁻¹ *
        ∑ x ∈ latticeCube z R, |v x| ^ (4 * (d : ℝ) / (2 * d - 3))) ^
          (1 / (4 * (d : ℝ) / (2 * d - 3)))) ^ 2 ≤
      8 * (4 * ((d : ℝ) - 1) / (2 * d - 3)) ^ 2 * (R : ℝ) ^ 2 *
        (((latticeCube z R).card : ℝ)⁻¹ *
          ∑ x ∈ latticeCube z R, nuReal c x ^ (2 * (d : ℝ))) ^ (1 / (2 * (d : ℝ))) *
        (((latticeCube z R).card : ℝ)⁻¹ *
          ∑ x ∈ latticeCube (z - fun _ => 1) (R + 1), ∑ j : Fin d,
            c (x, j) * (v (x + unit j) - v x) ^ 2) := by
  have hD : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hD2 : (0 : ℝ) < 2 * d - 3 := by linarith
  have hD0 : (0 : ℝ) < d := by linarith
  have hcore := weighted_sobolev_real hd hc z R hv
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = 4 * ((d : ℝ) - 1) / (2 * d - 3) := ⟨_, rfl⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = 4 * (d : ℝ) / (2 * d - 3) := ⟨_, rfl⟩
  rw [← hα, ← hρ] at hcore ⊢
  set B := latticeCube z R with hB
  set N := ∑ x ∈ B, |v x| ^ ρ with hN
  set Nu := ∑ x ∈ B, nuReal c x ^ (2 * (d : ℝ)) with hNu
  set E := ∑ x ∈ latticeCube (z - fun _ => 1) (R + 1), ∑ j : Fin d,
    c (x, j) * (v (x + unit j) - v x) ^ 2 with hE
  have hN0 : 0 ≤ N := Finset.sum_nonneg fun x _ => Real.rpow_nonneg (abs_nonneg _) _
  have hNu0 : 0 ≤ Nu := Finset.sum_nonneg fun x _ => Real.rpow_nonneg (nuReal_nonneg hc x) _
  have hE0 : 0 ≤ E := Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (hc _).le (sq_nonneg _)
  have ht0 : (0 : ℝ) < (R : ℝ) + 1 := by positivity
  have hRr : (1 : ℝ) ≤ R := by exact_mod_cast hR
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = (B.card : ℝ) := ⟨_, rfl⟩
  have hM : M = ((R : ℝ) + 1) ^ (d : ℝ) := by
    rw [hMdef, hB, latticeCube, card_qbox, Real.rpow_natCast]
    push_cast
    ring
  rw [← hMdef]
  have hM0 : 0 < M := by rw [hM]; positivity
  have hρa : 1 / ρ * 2 = ((2 : ℝ) * d - 3) / (2 * d) := by
    rw [hρ]; field_simp; ring
  have hMa : M ^ (((2 : ℝ) * d - 3) / (2 * d)) = ((R : ℝ) + 1) ^ (((2 : ℝ) * d - 3) / 2) := by
    rw [hM, ← Real.rpow_mul ht0.le]
    congr 1
    field_simp
  have hMb : M ^ (1 / (2 * (d : ℝ))) = ((R : ℝ) + 1) ^ ((1 : ℝ) / 2) := by
    rw [hM, ← Real.rpow_mul ht0.le]
    congr 1
    field_simp
  have key : M ^ (((2 : ℝ) * d - 3) / (2 * d)) * ((R : ℝ) + 1) ^ 2 =
      M ^ (1 / (2 * (d : ℝ))) * M := by
    rw [hMa, hMb]
    rw [hM, ← Real.rpow_natCast, ← Real.rpow_add ht0, ← Real.rpow_add ht0]
    congr 1
    push_cast
    ring
  have hLHS : (((M⁻¹ * N) ^ (1 / ρ)) ^ 2) = (M ^ (((2 : ℝ) * d - 3) / (2 * d)))⁻¹ *
      N ^ (((2 : ℝ) * d - 3) / (2 * d)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    push_cast
    rw [hρa, Real.mul_rpow (by positivity) hN0, Real.inv_rpow hM0.le]
  have hRHS : (M⁻¹ * Nu) ^ (1 / (2 * (d : ℝ))) = (M ^ (1 / (2 * (d : ℝ))))⁻¹ *
      Nu ^ (1 / (2 * (d : ℝ))) := by
    rw [Real.mul_rpow (by positivity) hNu0, Real.inv_rpow hM0.le]
  rw [hLHS, hRHS]
  have hMa0 : 0 < M ^ (((2 : ℝ) * d - 3) / (2 * d)) := Real.rpow_pos_of_pos hM0 _
  have hMb0 : 0 < M ^ (1 / (2 * (d : ℝ))) := Real.rpow_pos_of_pos hM0 _
  have hinv : (M ^ (((2 : ℝ) * d - 3) / (2 * d)))⁻¹ =
      (M ^ (1 / (2 * (d : ℝ))))⁻¹ * M⁻¹ * ((R : ℝ) + 1) ^ 2 := by
    field_simp
    linarith [key]
  have hQ : 0 ≤ (M ^ (1 / (2 * (d : ℝ))))⁻¹ * M⁻¹ * Nu ^ (1 / (2 * (d : ℝ))) * E := by
    positivity
  calc (M ^ (((2 : ℝ) * d - 3) / (2 * d)))⁻¹ * N ^ (((2 : ℝ) * d - 3) / (2 * d))
      ≤ (M ^ (((2 : ℝ) * d - 3) / (2 * d)))⁻¹ * (2 * α ^ 2 * E * Nu ^ (1 / (2 * (d : ℝ)))) :=
        mul_le_mul_of_nonneg_left hcore (by positivity)
    _ = ((M ^ (1 / (2 * (d : ℝ))))⁻¹ * M⁻¹ * Nu ^ (1 / (2 * (d : ℝ))) * E) *
          (2 * α ^ 2 * ((R : ℝ) + 1) ^ 2) := by rw [hinv]; ring
    _ ≤ ((M ^ (1 / (2 * (d : ℝ))))⁻¹ * M⁻¹ * Nu ^ (1 / (2 * (d : ℝ))) * E) *
          (8 * α ^ 2 * (R : ℝ) ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ hQ
        have : ((R : ℝ) + 1) ^ 2 ≤ 4 * (R : ℝ) ^ 2 := by nlinarith
        have hα2 : 0 ≤ α ^ 2 := sq_nonneg _
        nlinarith [mul_le_mul_of_nonneg_left this hα2]
    _ = _ := by ring

/-- The local norm of the `ℝ≥0∞`-image of a nonnegative real function on a nonempty set is the
`ℝ≥0∞`-image of the corresponding real expression. -/
theorem localNorm_ofReal {p : ℝ} (hp : 0 < p) {B : Finset (Site d)} (hB : B.card ≠ 0)
    (f : Site d → ℝ) (hf : ∀ x, 0 ≤ f x) :
    localNorm p B (fun x => ENNReal.ofReal (f x)) =
      ENNReal.ofReal (((B.card : ℝ)⁻¹ * ∑ x ∈ B, f x ^ p) ^ (1 / p)) := by
  have hc0 : (0 : ℝ) < B.card := by exact_mod_cast Nat.pos_of_ne_zero hB
  have hs : 0 ≤ ∑ x ∈ B, f x ^ p := Finset.sum_nonneg fun x _ => Real.rpow_nonneg (hf x) _
  have hsum : ∑ x ∈ B, (ENNReal.ofReal (f x)) ^ p = ENNReal.ofReal (∑ x ∈ B, f x ^ p) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun x _ => Real.rpow_nonneg (hf x) _]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [ENNReal.ofReal_rpow_of_nonneg (hf x) hp.le]
  show ((B.card : ENNReal)⁻¹ * ∑ x ∈ B, (ENNReal.ofReal (f x)) ^ p) ^ (1 / p) = _
  rw [hsum, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_inv_of_pos hc0,
    ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]

/-- **The weighted Sobolev inequality** (e:weighted-Sobolev), ADS15 (3.13)
with `q = 2d`: there is `C(d)` such that for all positive conductances, every lattice cube `B` of
side `R ≥ 1` and every `v` vanishing outside `B`,
`‖v‖²_{4d/(2d−3),B} ≤ C R² ‖ν‖_{2d,B} |B|⁻¹ Σ_e c_e |∇v(e)|²`. The edges carrying a nonzero
gradient start in `z − 𝟙 + {0, …, R + 1}^d`. -/
theorem weighted_sobolev (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : Edge d → ℝ), (∀ e, 0 < c e) → ∀ (z : Site d) (R : ℕ), 1 ≤ R →
      ∀ v : Site d → ℝ, (∀ x, x ∉ latticeCube z R → v x = 0) →
        localNorm (4 * d / (2 * d - 3)) (latticeCube z R) (fun x => ENNReal.ofReal |v x|) ^ 2 ≤
          ENNReal.ofReal (C * (R : ℝ) ^ 2) *
            localNorm (2 * d) (latticeCube z R) (nuField c) *
            ENNReal.ofReal (((latticeCube z R).card : ℝ)⁻¹ *
              ∑ x ∈ latticeCube (z - fun _ => 1) (R + 1), ∑ j : Fin d,
                c (x, j) * (v (x + unit j) - v x) ^ 2) := by
  refine ⟨8 * (4 * ((d : ℝ) - 1) / (2 * d - 3)) ^ 2, by positivity, ?_⟩
  intro c hc z R hR v hv
  have hD : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hD2 : (0 : ℝ) < 2 * d - 3 := by linarith
  have hD0 : (0 : ℝ) < d := by linarith
  have hreal := weighted_sobolev_avg_real hd hc z R hR hv
  have hcard : (latticeCube z R).card ≠ 0 := by
    rw [latticeCube, card_qbox]
    positivity
  have h1 := localNorm_ofReal (p := 4 * (d : ℝ) / (2 * d - 3)) (by positivity) hcard
    (fun x => |v x|) fun x => abs_nonneg _
  have h2 := localNorm_ofReal (p := 2 * (d : ℝ)) (by positivity) hcard (nuReal c)
    fun x => nuReal_nonneg hc x
  have hnu : nuField c = fun x => ENNReal.ofReal (nuReal c x) :=
    funext (nuField_eq_ofReal_nuReal hc)
  rw [hnu, h2, h1]
  have hcr : (0 : ℝ) ≤ ((latticeCube z R).card : ℝ)⁻¹ := by positivity
  have ha : 0 ≤ (((latticeCube z R).card : ℝ)⁻¹ *
      ∑ x ∈ latticeCube z R, |v x| ^ (4 * (d : ℝ) / (2 * d - 3))) ^
        (1 / (4 * (d : ℝ) / (2 * d - 3))) :=
    Real.rpow_nonneg (mul_nonneg hcr (Finset.sum_nonneg fun x _ =>
      Real.rpow_nonneg (abs_nonneg _) _)) _
  have hb : 0 ≤ (((latticeCube z R).card : ℝ)⁻¹ *
      ∑ x ∈ latticeCube z R, nuReal c x ^ (2 * (d : ℝ))) ^ (1 / (2 * (d : ℝ))) :=
    Real.rpow_nonneg (mul_nonneg hcr (Finset.sum_nonneg fun x _ =>
      Real.rpow_nonneg (nuReal_nonneg hc x) _)) _
  have hCR : (0 : ℝ) ≤ 8 * (4 * ((d : ℝ) - 1) / (2 * d - 3)) ^ 2 * (R : ℝ) ^ 2 := by positivity
  rw [← ENNReal.ofReal_pow ha, ← ENNReal.ofReal_mul hCR, ← ENNReal.ofReal_mul (mul_nonneg hCR hb)]
  exact ENNReal.ofReal_le_ofReal hreal

end LatticeHC

end
