import Rigidity.Proofs.Dirichlet.PlanarDatumBounds

/-!
# The error terms of Lemmas 6.2 and 6.3 in terms of the datum

Lattice estimates used to bound the error terms of the planar Lemmas 6.2 and 6.3 by the normalized
`L^t` norm `𝔅_t = L⁻² Σ_{edges in Q} |∇w̃|^t` of the datum:

* the affine approximations of the homogenized solution on the tiles of a block at depth `r + 3`:
  `Σ_i Σ_{tile} (u_h − ℓ_i)² ≤ C N⁴ r⁻² Σ_{edges in Q} |∇w̃|²`
  (`exists_sum_tiles_sq_dirichletSolution_sub_le`, from the interior second differences);
* the energy of the datum in a boundary layer of width `ℓ`, by Hölder's inequality:
  `L⁻² Σ_{layer} σ |∇w̃|² ≤ σ (4ℓ/L)^{1-2/t} (2^{t/2-1} 𝔅_t)^{2/t}` (`layer_energy_div_le`);
* the Hardy term: `(L⁻² Σ_Q |∇w̃|^t)^{2/t} ≤ (2^{t/2-1} 𝔅_t)^{2/t}` (`hardy_term_le`).
-/

open Finset LatticeProb LatticeHC LatticeProb.Percolation Rigidity.Percolation
open Rigidity.Proofs.Section5
open scoped Classical

namespace Rigidity.Dirichlet

/-- **The affine approximations of the homogenized solution on the tiles.** -/
theorem exists_sum_tiles_sq_dirichletSolution_sub_le {σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q : IntegerCube 2) (w : Vertex 2 → ℝ) (r : ℕ), 0 < r →
      ∀ (z : Vertex 2) (M N : ℕ), 0 < N →
      (cornerCube z ((M + 1) * N)).vertices ⊆ (shrinkCube Q (r + 3)).vertices →
      ∑ i ∈ (cornerCube 0 M).vertices, ∑ x ∈ (cornerCube (z + (N : ℤ) • i) N).vertices,
          (dirichletSolution (constCond fun _ => σ) (cubeInterior Q) w x -
            cubeAffine N (dirichletSolution (constCond fun _ => σ) (cubeInterior Q) w)
              (z + (N : ℤ) • i) x) ^ 2 ≤
        C * (N : ℝ) ^ 4 / (r : ℝ) ^ 2 * ∑ x ∈ Q.vertices, ∑ k : Fin 2,
          (if x + unit k ∈ Q.vertices then (w (x + unit k) - w x) ^ 2 else 0) := by
  obtain ⟨C, hC, hbound⟩ := exists_sum_tiles_sq_sub_cubeAffine_le_energy (d := 2) (by norm_num)
    (fun _ => σ) hσ (fun _ => ⟨le_rfl, le_rfl⟩)
  refine ⟨C, hC, fun Q w r hr z M N hN hsub => ?_⟩
  set w' : Vertex 2 → ℝ := fun y => w (cubeProj Q y)
  set u' := dirichletSolution (constCond fun _ => σ) (cubeInterior Q) w'
  set u := dirichletSolution (constCond fun _ => σ) (cubeInterior Q) w
  have hagree : ∀ x ∈ Q.vertices, u' x = u x := fun x hx => dirichletSolution_comp_cubeProj _ Q w hx
  have hu' : ∀ x ∈ (shrinkCube Q 1).vertices, condLaplacian (constCond fun _ => σ) u' x = 0 :=
    fun x hx => condLaplacian_dirichletSolution (d := 2) (by norm_num) (constCond fun _ => σ)
      (fun _ => hσ) _ w' x (shrinkCube_one_vertices_subset_cubeInterior Q hx)
  have htile : ∀ i ∈ (cornerCube 0 (M + 1)).vertices,
      ∀ x ∈ (cornerCube (z + (N : ℤ) • i) N).vertices, ∀ k : Fin 2,
        x ∈ Q.vertices ∧ x + unit k ∈ Q.vertices := fun i hi x hx k =>
    add_unit_mem_of_mem_shrinkCube Q (by omega) (hsub (tile_subset z (M + 1) hi hx)) k
  have haff : ∀ i ∈ (cornerCube 0 (M + 1)).vertices, ∀ x,
      cubeAffine N u' (z + (N : ℤ) • i) x = cubeAffine N u (z + (N : ℤ) • i) x :=
    fun i hi => cubeAffine_congr (fun x hx => hagree x (htile i hi x hx 0).1)
      (fun x hx k => hagree _ (htile i hi x hx k).2)
  have h := hbound Q u' hu' r hr z M N hN ((cornerCube_mul_subset_succ z M N).trans hsub)
  have hX : ∑ i ∈ (cornerCube 0 M).vertices, ∑ x ∈ (cornerCube (z + (N : ℤ) • i) N).vertices,
      (u' x - cubeAffine N u' (z + (N : ℤ) • i) x) ^ 2 =
      ∑ i ∈ (cornerCube 0 M).vertices, ∑ x ∈ (cornerCube (z + (N : ℤ) • i) N).vertices,
        (u x - cubeAffine N u (z + (N : ℤ) • i) x) ^ 2 :=
    Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun x hx => by
      rw [haff i (mem_cornerCube_succ hi), hagree x (htile i (mem_cornerCube_succ hi) x hx 0).1]
  have hE : ∑ x ∈ Q.vertices, ∑ j : Fin 2, (u' (x + unit j) - u' x) ^ 2 ≤
      ∑ x ∈ Q.vertices, ∑ k : Fin 2,
        (if x + unit k ∈ Q.vertices then (w (x + unit k) - w x) ^ 2 else 0) := by
    rw [sum_sq_grad_dirichletSolution_comp_cubeProj]
    have := sum_sq_inner_grad_dirichletSolution_le (d := 2) (by norm_num) (fun _ => σ) hσ
      (fun _ => ⟨le_rfl, le_rfl⟩) Q w
    rwa [div_self hσ.ne', one_mul] at this
  rw [hX] at h
  refine h.trans (mul_le_mul_of_nonneg_left hE (by positivity))

/-- **The energy of the datum in a boundary layer**, by Hölder's inequality. -/
theorem layer_energy_div_le (Q : IntegerCube 2) (hL : 0 < Q.size) (w : Vertex 2 → ℝ)
    {σ : ℝ} (hσ : 0 ≤ σ) (ℓ : ℕ) {t : ℝ} (ht : 2 ≤ t) :
    (∑ x ∈ cubeLayer Q ℓ, ∑ j : Fin 2,
        (if x + unit j ∈ Q.vertices then σ * (w (x + unit j) - w x) ^ 2 else 0)) /
        (Q.size : ℝ) ^ 2 ≤
      σ * ((2 * 2 * (ℓ : ℝ) / Q.size) ^ (1 - 2 / t) *
        ((2 : ℝ) ^ (t / 2 - 1) * ((∑ x ∈ Q.vertices, ∑ j : Fin 2,
          (if x + unit j ∈ Q.vertices then |w (x + unit j) - w x| ^ t else 0)) /
            (Q.size : ℝ) ^ 2)) ^ (2 / t)) := by
  have hV : (0 : ℝ) < (Q.size : ℝ) ^ 2 := by positivity
  set G : Vertex 2 → ℝ := innerGradNorm Q w
  have hG0 : ∀ x, 0 ≤ G x := fun x => Real.sqrt_nonneg _
  have hGt : (∑ x ∈ Q.vertices, |G x| ^ t) / (Q.size : ℝ) ^ 2 ≤
      (2 : ℝ) ^ (t / 2 - 1) * ((∑ x ∈ Q.vertices, ∑ j : Fin 2,
        (if x + unit j ∈ Q.vertices then |w (x + unit j) - w x| ^ t else 0)) /
          (Q.size : ℝ) ^ 2) := by
    rw [← mul_div_assoc]
    refine div_le_div_of_nonneg_right ?_ hV.le
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    rw [abs_of_nonneg (hG0 x)]
    have := innerGradNorm_rpow_le Q w x ht
    simpa using this
  have hlay1 : ∑ x ∈ cubeLayer Q ℓ, ∑ j : Fin 2,
      (if x + unit j ∈ Q.vertices then σ * (w (x + unit j) - w x) ^ 2 else 0) =
      σ * ∑ x ∈ cubeLayer Q ℓ, G x ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hG2 : G x ^ 2 = ∑ j : Fin 2,
        (if x + unit j ∈ Q.vertices then (w (x + unit j) - w x) ^ 2 else 0) :=
      Real.sq_sqrt (Finset.sum_nonneg fun j _ => by split_ifs <;> positivity)
    rw [hG2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs
    · rfl
    · rw [mul_zero]
  have hhol := sum_sq_div_le_card_div_rpow_mul (cubeLayer_subset Q ℓ) G ht hV
  have he : 0 ≤ 1 - 2 / t := by
    rw [sub_nonneg, div_le_one (by linarith)]
    exact ht
  have hcard := Real.rpow_le_rpow (by positivity) (card_cubeLayer_div_le Q hL ℓ) he
  have h0t : (0 : ℝ) ≤ 2 / t := by positivity
  rw [hlay1, mul_div_assoc]
  refine mul_le_mul_of_nonneg_left (hhol.trans ?_) hσ
  refine mul_le_mul ?_ (Real.rpow_le_rpow (by positivity) hGt h0t) (by positivity) (by positivity)
  have e : (2 * 2 * (ℓ : ℝ) / Q.size) = 2 * ((2 : ℕ) : ℝ) * ℓ / Q.size := by
    push_cast
    ring
  rw [e]
  exact hcard

/-- **The Hardy term**, by the power mean inequality. -/
theorem hardy_term_le (Q : IntegerCube 2) (w : Vertex 2 → ℝ) {t : ℝ} (ht : 2 ≤ t) :
    ((∑ x ∈ Q.vertices, √(∑ j : Fin 2,
        (if x + unit j ∈ Q.vertices then (w (x + unit j) - w x) ^ 2 else 0)) ^ t) /
        (Q.size : ℝ) ^ 2) ^ (2 / t) ≤
      ((2 : ℝ) ^ (t / 2 - 1) * ((∑ x ∈ Q.vertices, ∑ j : Fin 2,
        (if x + unit j ∈ Q.vertices then |w (x + unit j) - w x| ^ t else 0)) /
          (Q.size : ℝ) ^ 2)) ^ (2 / t) := by
  have hV : (0 : ℝ) ≤ (Q.size : ℝ) ^ 2 := by positivity
  refine Real.rpow_le_rpow (div_nonneg (Finset.sum_nonneg fun _ _ => by positivity) hV) ?_
    (by positivity)
  rw [← mul_div_assoc]
  refine div_le_div_of_nonneg_right ?_ hV
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  have := innerGradNorm_rpow_le Q w x ht
  simpa [innerGradNorm] using this

end Rigidity.Dirichlet
