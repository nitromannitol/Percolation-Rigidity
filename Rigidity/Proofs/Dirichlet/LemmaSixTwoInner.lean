import Rigidity.Proofs.Dirichlet.LemmaSixTwoHomogenized
import Rigidity.Proofs.Dirichlet.TiledEnergy

/-!
# Lemma 6.2 on the lattice with the edges inside the cube

The energy `edgeEnergy (constCond ā) Q.vertices` also counts the edges leaving `Q` through its
upper faces, on which the homogenized solution equals its datum. Composing the datum with the
nearest-point projection onto `Q` (`cubeProj`) does not change the homogenized solution on `Q`
and makes the gradient of the datum vanish on these edges, so the lattice form of Lemma 6.2 holds
with the energy `innerEdgeEnergy (constCond ā) Q u_hom` of the edges inside `Q` and with all
sums of the datum over the edges inside `Q` (`innerEdgeEnergy_dirichletSolution_div_le_of_mu_test`).
These are the sums that Lemma 6.4 (iii) controls (`sum_abs_grad_boundaryInterpolation_rpow_div_le`
with domain `Q`).
-/

open Finset LatticeProb LatticeHC

namespace Rigidity.Dirichlet

open Rigidity.Percolation LatticeProb.Percolation

variable {d : ℕ}

/-- The nearest-point projection onto the cube `Q` (coordinatewise clamping). -/
def cubeProj (Q : IntegerCube d) (x : Vertex d) : Vertex d :=
  fun k => max (Q.corner k) (min (x k) (Q.corner k + Q.size - 1))

theorem cubeProj_of_mem (Q : IntegerCube d) {x : Vertex d} (hx : x ∈ Q.vertices) :
    cubeProj Q x = x := by
  rw [IntegerCube.mem_vertices] at hx
  funext k
  have h := hx k
  simp only [cubeProj]
  rw [min_eq_left (by linarith [h.2]), max_eq_right h.1]

theorem cubeProj_add_unit_of_not_mem (Q : IntegerCube d) {x : Vertex d} (hx : x ∈ Q.vertices)
    {j : Fin d} (hxj : x + unit j ∉ Q.vertices) : cubeProj Q (x + unit j) = x := by
  have hface := (add_unit_mem_vertices_iff Q hx j).not.mp hxj
  push Not at hface
  have hup := ((IntegerCube.mem_upperFace Q j x).mp hface).2
  rw [IntegerCube.mem_vertices] at hx
  funext k
  have h := hx k
  simp only [cubeProj]
  rw [add_unit_apply]
  by_cases hk : k = j
  · subst hk
    rw [if_pos rfl, min_eq_right (by linarith), max_eq_right (by linarith [h.1, h.2])]
    linarith
  · rw [if_neg hk, add_zero, min_eq_left (by linarith [h.2]), max_eq_right h.1]

theorem add_unit_mem_of_mem_cubeInterior (Q : IntegerCube d) {x : Vertex d}
    (hx : x ∈ cubeInterior Q) (j : Fin d) :
    x + unit j ∈ Q.vertices ∧ x - unit j ∈ Q.vertices := by
  obtain ⟨_, hint⟩ := Finset.mem_filter.mp hx
  constructor
  · rw [IntegerCube.mem_vertices]
    intro k
    rw [add_unit_apply]
    have := hint k
    split_ifs <;> constructor <;> linarith [this.1, this.2]
  · rw [IntegerCube.mem_vertices]
    intro k
    rw [sub_unit_apply]
    have := hint k
    split_ifs <;> constructor <;> linarith [this.1, this.2]

/-- On `Q`, the Dirichlet solution only depends on the datum on `Q`. -/
theorem dirichletSolution_comp_cubeProj (c : Edge d → ℝ) (Q : IntegerCube d)
    (w : Vertex d → ℝ) {x : Vertex d} (hx : x ∈ Q.vertices) :
    dirichletSolution c (cubeInterior Q) (fun y => w (cubeProj Q y)) x =
      dirichletSolution c (cubeInterior Q) w x := by
  have hL : ∀ z ∈ cubeInterior Q,
      condLaplacian c (fun y => w (cubeProj Q y)) z = condLaplacian c w z := by
    intro z hz
    have hzQ := (Finset.mem_filter.mp hz).1
    simp only [condLaplacian]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h := add_unit_mem_of_mem_cubeInterior Q hz j
    rw [cubeProj_of_mem Q hzQ, cubeProj_of_mem Q h.1, cubeProj_of_mem Q h.2]
  simp only [dirichletSolution]
  rw [cubeProj_of_mem Q hx]
  congr 1
  exact Finset.sum_congr rfl fun z hz => by rw [hL z hz]

/-- The energy of the homogenized solution with the projected datum is its energy on the edges
inside `Q`. -/
theorem edgeEnergy_dirichletSolution_comp_cubeProj (a : Fin d → ℝ) (Q : IntegerCube d)
    (w : Vertex d → ℝ) :
    edgeEnergy (constCond a) Q.vertices
        (dirichletSolution (constCond a) (cubeInterior Q) (fun y => w (cubeProj Q y))) =
      innerEdgeEnergy (constCond a) Q (dirichletSolution (constCond a) (cubeInterior Q) w) := by
  rw [edgeEnergy, Finset.sum_comm, innerEdgeEnergy]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sum_vertices_eq_sum_inner_add_sum_upperFace Q j]
  have hface : ∑ x ∈ Q.upperFace j, constCond a (x, j) *
      (dirichletSolution (constCond a) (cubeInterior Q) (fun y => w (cubeProj Q y)) (x + unit j) -
        dirichletSolution (constCond a) (cubeInterior Q) (fun y => w (cubeProj Q y)) x) ^ 2 =
      0 := by
    refine Finset.sum_eq_zero fun x hx => ?_
    have hxQ := ((IntegerCube.mem_upperFace Q j x).mp hx).1
    have hxj : x + unit j ∉ Q.vertices := (add_unit_mem_vertices_iff Q hxQ j).not.mpr (by
      push Not
      exact hx)
    have hnot : ∀ y, y ∉ Q.vertices → y ∉ cubeInterior Q := fun y hy h =>
      hy (Finset.mem_filter.mp h).1
    have hxint : x ∉ cubeInterior Q := by
      intro h
      exact hxj (add_unit_mem_of_mem_cubeInterior Q h j).1
    rw [dirichletSolution_eq_of_not_mem _ _ _ (hnot _ hxj),
      dirichletSolution_eq_of_not_mem _ _ _ hxint, cubeProj_add_unit_of_not_mem Q hxQ hxj,
      cubeProj_of_mem Q hxQ, sub_self, zero_pow two_ne_zero, mul_zero]
  rw [hface, add_zero]
  refine Finset.sum_congr rfl fun x hx => ?_
  obtain ⟨hxQ, hxjQ⟩ := Finset.mem_filter.mp hx
  rw [dirichletSolution_comp_cubeProj _ Q w hxQ, dirichletSolution_comp_cubeProj _ Q w hxjQ]

/-- The gradient sums of the projected datum are the sums over the edges inside `Q`. -/
theorem sum_abs_grad_comp_cubeProj_rpow (Q : IntegerCube d) (w : Vertex d → ℝ) {s : ℝ}
    (hs : 0 < s) :
    ∑ y ∈ Q.vertices, ∑ k : Fin d, |w (cubeProj Q (y + unit k)) - w (cubeProj Q y)| ^ s =
      ∑ y ∈ Q.vertices, ∑ k : Fin d,
        (if y + unit k ∈ Q.vertices then |w (y + unit k) - w y| ^ s else 0) := by
  refine Finset.sum_congr rfl fun y hy => Finset.sum_congr rfl fun k _ => ?_
  rw [cubeProj_of_mem Q hy]
  split_ifs with h
  · rw [cubeProj_of_mem Q h]
  · rw [cubeProj_add_unit_of_not_mem Q hy h, sub_self, abs_zero, Real.zero_rpow hs.ne']

theorem sum_sq_grad_comp_cubeProj (Q : IntegerCube d) (w : Vertex d → ℝ) :
    ∑ y ∈ Q.vertices, ∑ k : Fin d, (w (cubeProj Q (y + unit k)) - w (cubeProj Q y)) ^ 2 =
      ∑ y ∈ Q.vertices, ∑ k : Fin d,
        (if y + unit k ∈ Q.vertices then (w (y + unit k) - w y) ^ 2 else 0) := by
  refine Finset.sum_congr rfl fun y hy => Finset.sum_congr rfl fun k _ => ?_
  rw [cubeProj_of_mem Q hy]
  split_ifs with h
  · rw [cubeProj_of_mem Q h]
  · rw [cubeProj_add_unit_of_not_mem Q hy h, sub_self, zero_pow two_ne_zero]

end Rigidity.Dirichlet
