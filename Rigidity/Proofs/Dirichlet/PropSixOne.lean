import Rigidity.Proofs.Dirichlet.LemmaSixThreeInner
import Rigidity.Proofs.Dirichlet.DirichletError

/-!
# Proposition 6.1 on the lattice with the energies of the edges inside the cube

The energy of the edges inside a cube `Q` is the full energy from `Q` for the conductance masked
to these edges (`innerCond`), and the masked conductance has the same Laplacian on the interior
of `Q`. So the chain of `sum_sq_sub_le_of_energy_chain` applies to the comparisons of
Lemmas 6.2 and 6.3 for the energies of the edges inside `Q`
(`innerEdgeEnergy_dirichletSolution_div_le_of_mu_test`,
`innerEdgeEnergy_patch_dirichletSolution_div_le`): if `u` is `c`-harmonic on the interior of `Q`,
`v = ũ_hom` equals `u` off the interior, `E_hom ≤ E_c(u) + δ₁` and `E_c(v) ≤ E_hom + δ₂`, then
`Σ_T (u − u_hom)² ≤ 2 P (δ₁ + δ₂)/λ + 2 δ₃` for a Poincaré constant `P` of `v − u` and
`Σ_T (v − u_hom)² ≤ δ₃` (`sum_sq_sub_le_of_inner_energy_chain`). This is the proof of
Armstrong–Dario, Proposition 6.1, on the lattice.
-/

open Finset LatticeProb LatticeHC

namespace Rigidity.Dirichlet

open Rigidity.Percolation LatticeProb.Percolation

variable {d : ℕ}

/-- The conductance masked to the edges inside `Q`. -/
noncomputable def innerCond (c : Edge d → ℝ) (Q : IntegerCube d) (e : Edge d) : ℝ :=
  if e.1 + unit e.2 ∈ Q.vertices then c e else 0

theorem innerEdgeEnergy_eq_edgeEnergy_innerCond (c : Edge d → ℝ) (Q : IntegerCube d)
    (g : Vertex d → ℝ) : innerEdgeEnergy c Q g = edgeEnergy (innerCond c Q) Q.vertices g := by
  rw [edgeEnergy, Finset.sum_comm, innerEdgeEnergy]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [innerCond]
  split_ifs <;> simp

theorem condLaplacian_innerCond (c : Edge d → ℝ) (Q : IntegerCube d) (g : Vertex d → ℝ)
    {x : Vertex d} (hx : x ∈ cubeInterior Q) :
    condLaplacian (innerCond c Q) g x = condLaplacian c g x := by
  simp only [condLaplacian]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 := (add_unit_mem_of_mem_cubeInterior Q hx j).1
  have h2 : x - unit j + unit j ∈ Q.vertices := by
    rw [sub_add_cancel]
    exact (Finset.mem_filter.mp hx).1
  simp only [innerCond, if_pos h1, if_pos h2]

/-- **Armstrong–Dario, Proposition 6.1, on the lattice, from the comparisons for the energies of
the edges inside `Q`.** -/
theorem sum_sq_sub_le_of_inner_energy_chain (c : Edge d → ℝ) {lam : ℝ} (hlam : 0 < lam)
    (hc : ∀ e, c e = 0 ∨ lam ≤ c e) (Q : IntegerCube d) {u v uHom : Vertex d → ℝ}
    (hu : ∀ x ∈ cubeInterior Q, condLaplacian c u x = 0)
    (hvu : ∀ x, x ∉ cubeInterior Q → v x = u x) {eHom δ₁ δ₂ δ₃ P : ℝ} (hP0 : 0 ≤ P)
    (h₁ : eHom ≤ innerEdgeEnergy c Q u + δ₁) (h₂ : innerEdgeEnergy c Q v ≤ eHom + δ₂)
    (T : Finset (Vertex d))
    (hP : ∑ x ∈ T, (v x - u x) ^ 2 ≤ P * ∑ x ∈ Q.vertices, ∑ j : Fin d,
      (if innerCond c Q (x, j) = 0 then 0 else ((v - u) (x + unit j) - (v - u) x) ^ 2))
    (h₃ : ∑ x ∈ T, (v x - uHom x) ^ 2 ≤ δ₃) :
    ∑ x ∈ T, (u x - uHom x) ^ 2 ≤ 2 * (P * ((δ₁ + δ₂) / lam)) + 2 * δ₃ := by
  have hc' : ∀ e, innerCond c Q e = 0 ∨ lam ≤ innerCond c Q e := fun e => by
    simp only [innerCond]
    split_ifs
    · exact hc e
    · exact Or.inl rfl
  rw [innerEdgeEnergy_eq_edgeEnergy_innerCond] at h₁ h₂
  exact sum_sq_sub_le_of_energy_chain (innerCond c Q) hlam hc' (coversEdges_cubeInterior Q)
    (fun x hx => by rw [condLaplacian_innerCond c Q u hx]; exact hu x hx) hvu hP0 le_rfl h₁ h₂
    T hP h₃

end Rigidity.Dirichlet
