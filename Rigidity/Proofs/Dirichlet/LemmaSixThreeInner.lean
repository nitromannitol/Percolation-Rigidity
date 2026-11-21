import Rigidity.Proofs.Dirichlet.LemmaSixThreeNormalized
import Rigidity.Proofs.Dirichlet.LemmaSixTwoInner

/-!
# Lemma 6.3 on the lattice with the edges inside the cube

Applying `edgeEnergy_patch_dirichletSolution_div_le` to the projected datum `w ∘ cubeProj Q`, whose
homogenized solution agrees with that of `w` on `Q`, gives the energy estimate (ii) of Lemma 6.3
for the energies of the edges inside `Q` (`innerEdgeEnergy_patch_dirichletSolution_div_le`), with
the mesoscopic hypotheses stated for the homogenized solution of `w` and all sums of `w` over the
edges inside `Q`. Together with `innerEdgeEnergy_dirichletSolution_div_le_of_mu_test` (Lemma 6.2)
both comparisons are for the same energy, as needed in the chain of Proposition 6.1.
-/

open Finset LatticeProb LatticeHC

namespace Rigidity.Dirichlet

open Rigidity.Percolation LatticeProb.Percolation

variable {d : ℕ}

/-- The mesoscopic slope only depends on the function on the cube and its steps. -/
theorem cubeSlope_congr {N : ℕ} {g g' : Vertex d → ℝ} {y : Vertex d}
    (h0 : ∀ x ∈ (cornerCube y N).vertices, g x = g' x)
    (h1 : ∀ x ∈ (cornerCube y N).vertices, ∀ k : Fin d, g (x + unit k) = g' (x + unit k))
    (k : Fin d) : cubeSlope N g y k = cubeSlope N g' y k := by
  simp only [cubeSlope, cubeAverage]
  congr 1
  exact Finset.sum_congr rfl fun x hx => by rw [h0 x hx, h1 x hx k]

/-- The affine approximation only depends on the function on the cube and its steps. -/
theorem cubeAffine_congr {N : ℕ} {g g' : Vertex d → ℝ} {y : Vertex d}
    (h0 : ∀ x ∈ (cornerCube y N).vertices, g x = g' x)
    (h1 : ∀ x ∈ (cornerCube y N).vertices, ∀ k : Fin d, g (x + unit k) = g' (x + unit k))
    (x : Vertex d) : cubeAffine N g y x = cubeAffine N g' y x := by
  simp only [cubeAffine, cubeAverage, cubeSlope_congr h0 h1]
  congr 2
  exact Finset.sum_congr rfl fun z hz => by rw [h0 z hz]

/-- Points at depth at least one in `Q` stay in `Q` after a step `e_k`. -/
theorem add_unit_mem_of_mem_shrinkCube (Q : IntegerCube d) {t : ℕ} (ht : 1 ≤ t) {x : Vertex d}
    (hx : x ∈ (shrinkCube Q t).vertices) (k : Fin d) :
    x ∈ Q.vertices ∧ x + unit k ∈ Q.vertices := by
  rw [mem_shrinkCube_iff] at hx
  constructor
  · rw [IntegerCube.mem_vertices]
    intro i
    have h := hx i
    have : ((Q.size - 2 * t : ℕ) : ℤ) ≤ (Q.size : ℤ) - 2 * t ∨ Q.size < 2 * t := by omega
    constructor <;> omega
  · rw [IntegerCube.mem_vertices]
    intro i
    rw [add_unit_apply]
    have h := hx i
    have : ((Q.size - 2 * t : ℕ) : ℤ) ≤ (Q.size : ℤ) - 2 * t ∨ Q.size < 2 * t := by omega
    split_ifs <;> constructor <;> omega

/-- The homogenized solutions of `w` and `w ∘ cubeProj Q` agree on `Q`. -/
theorem dirichletSolution_comp_cubeProj_of_mem (a : Fin d → ℝ) (Q : IntegerCube d)
    (w : Vertex d → ℝ) {x : Vertex d} (hx : x ∈ Q.vertices) :
    dirichletSolution (constCond a) (cubeInterior Q) (fun y => w (cubeProj Q y)) x =
      dirichletSolution (constCond a) (cubeInterior Q) w x :=
  dirichletSolution_comp_cubeProj _ Q w hx

/-- The squared gradient sums of the homogenized solution of the projected datum are the sums
over the edges inside `Q`. -/
theorem sum_sq_grad_dirichletSolution_comp_cubeProj (a : Fin d → ℝ) (Q : IntegerCube d)
    (w : Vertex d → ℝ) :
    ∑ x ∈ Q.vertices, ∑ k : Fin d,
        (dirichletSolution (constCond a) (cubeInterior Q) (fun y => w (cubeProj Q y)) (x + unit k) -
          dirichletSolution (constCond a) (cubeInterior Q) (fun y => w (cubeProj Q y)) x) ^ 2 =
      ∑ x ∈ Q.vertices, ∑ k : Fin d, (if x + unit k ∈ Q.vertices then
        (dirichletSolution (constCond a) (cubeInterior Q) w (x + unit k) -
          dirichletSolution (constCond a) (cubeInterior Q) w x) ^ 2 else 0) := by
  refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun k _ => ?_
  split_ifs with h
  · rw [dirichletSolution_comp_cubeProj _ Q w hx, dirichletSolution_comp_cubeProj _ Q w h]
  · have hnot : ∀ y, y ∉ Q.vertices → y ∉ cubeInterior Q := fun y hy hi =>
      hy (Finset.mem_filter.mp hi).1
    have hxint : x ∉ cubeInterior Q := fun hi => h (add_unit_mem_of_mem_cubeInterior Q hi k).1
    rw [dirichletSolution_eq_of_not_mem _ _ _ (hnot _ h),
      dirichletSolution_eq_of_not_mem _ _ _ hxint, cubeProj_add_unit_of_not_mem Q hx h,
      cubeProj_of_mem Q hx, sub_self, zero_pow two_ne_zero]

/-- The weighted squared gradient sums of the projected datum over a subset of `Q`. -/
theorem sum_weighted_sq_grad_comp_cubeProj (a : Fin d → ℝ) (Q : IntegerCube d)
    {S : Finset (Vertex d)} (hS : S ⊆ Q.vertices) (w : Vertex d → ℝ) :
    ∑ x ∈ S, ∑ k : Fin d, a k * (w (cubeProj Q (x + unit k)) - w (cubeProj Q x)) ^ 2 =
      ∑ x ∈ S, ∑ k : Fin d,
        (if x + unit k ∈ Q.vertices then a k * (w (x + unit k) - w x) ^ 2 else 0) := by
  refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun k _ => ?_
  rw [cubeProj_of_mem Q (hS hx)]
  split_ifs with h
  · rw [cubeProj_of_mem Q h]
  · rw [cubeProj_add_unit_of_not_mem Q (hS hx) h, sub_self, zero_pow two_ne_zero, mul_zero]

/-- The gradient magnitudes of the projected datum on `Q`. -/
theorem sqrt_sum_sq_grad_comp_cubeProj (Q : IntegerCube d) (w : Vertex d → ℝ) {x : Vertex d}
    (hx : x ∈ Q.vertices) :
    √(∑ k : Fin d, (w (cubeProj Q (x + unit k)) - w (cubeProj Q x)) ^ 2) =
      √(∑ k : Fin d, (if x + unit k ∈ Q.vertices then (w (x + unit k) - w x) ^ 2 else 0)) := by
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [cubeProj_of_mem Q hx]
  split_ifs with h
  · rw [cubeProj_of_mem Q h]
  · rw [cubeProj_add_unit_of_not_mem Q hx h, sub_self, zero_pow two_ne_zero]

end Rigidity.Dirichlet
