import Rigidity.Proofs.Dirichlet.BoundaryData
import Rigidity.Vendor.LHCH.Support.WeakNorm.CutoffIdentity

/-!
# Caccioppoli inequality and interior second differences

For nonnegative conductances `c`, a function `φ` that is `c`-harmonic on a finite set `U` and a
cutoff `η` vanishing off `U`, the Caccioppoli inequality
`Σ η(x + e_j)² c(x,j) (∇_jφ(x))² ≤ 5 Σ c(x,j) (∇_jη(x))² ((φ(x + e_j) − m)² + (φ(x) − m)²)`
holds for every constant `m`; it follows from the cutoff identity of `LatticeHC` by Young's
inequality.

For constant conductances `c(x, j) = a_j` the operator commutes with translations, so the
difference `∇_i v` of a function `v` harmonic on `U` is harmonic where both `x` and `x + e_i` lie
in `U`, and the Caccioppoli inequality bounds the second differences `∇_j∇_i v` on the region
where `η = 1` by the first differences on the support of `∇η`. This is the discrete form of the
interior `H²` estimate of Armstrong–Dario, Proposition 6.5 (from [Giu]), used in the proof of
Lemma 6.3 for the homogenized solution; the discrete homogenized problem replaces the
continuum one.
-/

open LatticeProb LatticeHC

namespace Rigidity.Dirichlet

variable {d : ℕ}

/-- The elementary inequality behind the Caccioppoli inequality: with `g = A − B`,
`−B (a² − b²) g ≤ a² g² / 2 + 5 (a − b)² (A² + B²) / 2`. -/
theorem neg_mul_sq_sub_sq_mul_le (a b A B : ℝ) :
    -(B * (a ^ 2 - b ^ 2) * (A - B)) ≤
      1 / 2 * (a ^ 2 * (A - B) ^ 2) + 5 / 2 * ((a - b) ^ 2 * (A ^ 2 + B ^ 2)) := by
  nlinarith [sq_nonneg (a * (A - B) + 2 * B * (a - b)),
    mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (A - B)),
    mul_nonneg (sq_nonneg (a - b)) (sq_nonneg A), mul_nonneg (sq_nonneg (a - b)) (sq_nonneg B)]

/-- **Caccioppoli inequality**: for nonnegative conductances, `φ` `c`-harmonic on `U`, `η`
vanishing off `U`, `S` covering the edges at `U` and any constant `m`,
`Σ_{x∈S} Σ_j η(x + e_j)² c(x,j) (∇_jφ(x))² ≤
  5 Σ_{x∈S} Σ_j c(x,j) (∇_jη(x))² ((φ(x + e_j) − m)² + (φ(x) − m)²)`. -/
theorem sum_cutoff_energy_le (c : Edge d → ℝ) (hc : ∀ e, 0 ≤ c e) {U S : Finset (Site d)}
    (hS : CoversEdges U S) (φ η : Site d → ℝ) (m : ℝ)
    (hφ : ∀ x ∈ U, condLaplacian c φ x = 0) (hη : ∀ x, x ∉ U → η x = 0) :
    ∑ x ∈ S, ∑ j : Fin d, η (x + unit j) ^ 2 * c (x, j) * (φ (x + unit j) - φ x) ^ 2 ≤
      5 * ∑ x ∈ S, ∑ j : Fin d, c (x, j) * (η (x + unit j) - η x) ^ 2 *
        ((φ (x + unit j) - m) ^ 2 + (φ x - m) ^ 2) := by
  have hid := sum_cutoff_energy_eq c U S φ (fun x => η x ^ 2) m hφ
    (fun x hx => by simp [hη x hx]) hS
  have hpt : ∀ x (j : Fin d),
      -((φ x - m) * (η (x + unit j) ^ 2 - η x ^ 2) * (c (x, j) * (φ (x + unit j) - φ x))) ≤
        1 / 2 * (η (x + unit j) ^ 2 * c (x, j) * (φ (x + unit j) - φ x) ^ 2) +
          5 / 2 * (c (x, j) * (η (x + unit j) - η x) ^ 2 *
            ((φ (x + unit j) - m) ^ 2 + (φ x - m) ^ 2)) := by
    intro x j
    have key := neg_mul_sq_sub_sq_mul_le (η (x + unit j)) (η x) (φ (x + unit j) - m) (φ x - m)
    have hg : φ (x + unit j) - m - (φ x - m) = φ (x + unit j) - φ x := by ring
    rw [hg] at key
    have := mul_le_mul_of_nonneg_left key (hc (x, j))
    nlinarith [this]
  have hsum : -∑ x ∈ S, ∑ j : Fin d,
      (φ x - m) * (η (x + unit j) ^ 2 - η x ^ 2) * (c (x, j) * (φ (x + unit j) - φ x)) ≤
      1 / 2 * ∑ x ∈ S, ∑ j : Fin d, η (x + unit j) ^ 2 * c (x, j) * (φ (x + unit j) - φ x) ^ 2 +
        5 / 2 * ∑ x ∈ S, ∑ j : Fin d, c (x, j) * (η (x + unit j) - η x) ^ 2 *
          ((φ (x + unit j) - m) ^ 2 + (φ x - m) ^ 2) := by
    rw [← Finset.sum_neg_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun x _ => ?_
    rw [← Finset.sum_neg_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun j _ => hpt x j
  linarith

/-- Constant diagonal conductances `c(x, j) = a_j`. -/
def constCond (a : Fin d → ℝ) : Edge d → ℝ := fun e => a e.2

/-- The constant-coefficient operator commutes with translations. -/
theorem condLaplacian_constCond_comp_add (a : Fin d → ℝ) (v : Site d → ℝ) (z x : Site d) :
    condLaplacian (constCond a) (fun y => v (y + z)) x = condLaplacian (constCond a) v (x + z) := by
  simp only [condLaplacian, constCond]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show x + unit j + z = x + z + unit j by abel, show x - unit j + z = x + z - unit j by abel]

/-- The constant-coefficient operator commutes with the difference `∇_i`. -/
theorem condLaplacian_constCond_grad (a : Fin d → ℝ) (v : Site d → ℝ) (i : Fin d) (x : Site d) :
    condLaplacian (constCond a) (fun y => v (y + unit i) - v y) x =
      condLaplacian (constCond a) v (x + unit i) - condLaplacian (constCond a) v x := by
  have h := condLaplacian_sub (constCond a) (fun y => v (y + unit i)) v x
  rw [condLaplacian_constCond_comp_add] at h
  exact h

/-- The difference `∇_i v` of a constant-coefficient harmonic function `v` on `U` is harmonic on
the points `x` of `U` with `x + e_i ∈ U`. -/
theorem condLaplacian_constCond_grad_eq_zero (a : Fin d → ℝ) {U : Finset (Site d)}
    {v : Site d → ℝ} (hv : ∀ x ∈ U, condLaplacian (constCond a) v x = 0) (i : Fin d) :
    ∀ x ∈ U.filter (fun x => x + unit i ∈ U),
      condLaplacian (constCond a) (fun y => v (y + unit i) - v y) x = 0 := by
  intro x hx
  obtain ⟨hxU, hxiU⟩ := Finset.mem_filter.mp hx
  rw [condLaplacian_constCond_grad, hv _ hxiU, hv _ hxU, sub_zero]

/-- **Interior second differences** (discrete interior `H²` estimate): for constant nonnegative
conductances `a`, `v` harmonic on `U`, a cutoff `η` vanishing off `{x ∈ U : x + e_i ∈ U}` with
`|∇_jη| ≤ K` on the edges at `S`, and `S` covering the edges at that set,
`Σ_{x∈S} Σ_j η(x + e_j)² a_j (∇_j∇_i v(x))² ≤
  5 K² Σ_{x∈S} Σ_j a_j ((∇_i v(x + e_j))² + (∇_i v(x))²)`. -/
theorem sum_cutoff_second_difference_le (a : Fin d → ℝ) (ha : ∀ j, 0 ≤ a j)
    {U S : Finset (Site d)} {v : Site d → ℝ}
    (hv : ∀ x ∈ U, condLaplacian (constCond a) v x = 0) (i : Fin d)
    (hS : CoversEdges (U.filter fun x => x + unit i ∈ U) S) (η : Site d → ℝ)
    (hη : ∀ x, x ∉ U.filter (fun x => x + unit i ∈ U) → η x = 0) {K : ℝ}
    (hK : ∀ x ∈ S, ∀ j : Fin d, |η (x + unit j) - η x| ≤ K) :
    ∑ x ∈ S, ∑ j : Fin d, η (x + unit j) ^ 2 * a j *
        ((v (x + unit j + unit i) - v (x + unit j)) - (v (x + unit i) - v x)) ^ 2 ≤
      5 * K ^ 2 * ∑ x ∈ S, ∑ j : Fin d, a j *
        ((v (x + unit j + unit i) - v (x + unit j)) ^ 2 + (v (x + unit i) - v x) ^ 2) := by
  have h := sum_cutoff_energy_le (constCond a) (fun e => ha e.2) hS
    (fun y => v (y + unit i) - v y) η 0 (condLaplacian_constCond_grad_eq_zero a hv i) hη
  simp only [constCond, sub_zero] at h
  refine h.trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun x hx => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have hsq : (η (x + unit j) - η x) ^ 2 ≤ K ^ 2 := by
    have := hK x hx j
    nlinarith [abs_nonneg (η (x + unit j) - η x), sq_abs (η (x + unit j) - η x)]
  have hnn : 0 ≤ a j * ((v (x + unit j + unit i) - v (x + unit j)) ^ 2 +
      (v (x + unit i) - v x) ^ 2) := mul_nonneg (ha j) (by positivity)
  nlinarith [mul_le_mul_of_nonneg_right hsq hnn]

end Rigidity.Dirichlet
