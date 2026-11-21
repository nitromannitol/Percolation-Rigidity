import Rigidity.Proofs.Dirichlet.MesoscopicInterpolation
import Rigidity.Proofs.Dirichlet.LayerEnergy
import Rigidity.Proofs.Dirichlet.CubeCutoff
import Rigidity.Proofs.Dirichlet.AffineApproximation

/-!
# The trial function of Lemma 6.2

With the cutoff `η = η_Q` of the cube `Q` at depth `r ≥ 1`, the interpolation
`ũ = w + η (ξ_N(w) − w)` between the boundary datum `w` and its mesoscopic average equals `w` off
the interior of `Q`, so it is an admissible competitor for the homogenized Dirichlet problem with
datum `w`, and off the boundary layer of width `r + 1` its gradient is the mesoscopic slope
`p(x) = ⟨∇w⟩_{x + □_N}`. Hence its homogenized energy is at most `Σ_{Q ∖ layer} p·ā p` plus `Λ`
times its energy in the layer.

This is the construction `ũ = η ξ + (1 − η) w` and Step 5 of the proof of Armstrong–Dario,
Lemma 6.2 ((6.27)–(6.28)), on the lattice; the energy in the layer is then small by the
boundary-layer estimate and the `L^{p'}` bound of `∇ũ`.
-/

open Finset LatticeProb LatticeHC

namespace Rigidity.Dirichlet

open Rigidity.Percolation LatticeProb.Percolation

variable {d : ℕ}

/-- The trial function equals the datum off the interior of `Q`. -/
theorem mesoInterpolation_cubeCutoff_of_not_mem (Q : IntegerCube d) (N r : ℕ)
    (w : Vertex d → ℝ) {x : Vertex d} (hx : x ∉ cubeInterior Q) :
    mesoInterpolation N (cubeCutoff Q r) w x = w x := by
  apply mesoInterpolation_eq_of_eq_zero
  by_contra h
  obtain ⟨hxQ, hnb⟩ := mem_vertices_of_cubeCutoff_ne_zero Q r h
  apply hx
  refine Finset.mem_filter.mpr ⟨hxQ, fun k => ?_⟩
  have h1 := (IntegerCube.mem_vertices Q _).mp (hnb k).1 k
  have h2 := (IntegerCube.mem_vertices Q _).mp (hnb k).2 k
  rw [add_unit_apply, if_pos rfl] at h1
  rw [sub_unit_apply, if_pos rfl] at h2
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- Off the boundary layer of width `r + 1`, the gradient of the trial function is the mesoscopic
slope of the datum. -/
theorem mesoInterpolation_cubeCutoff_grad (Q : IntegerCube d) (N : ℕ) {r : ℕ} (hr : 0 < r)
    (w : Vertex d → ℝ) {x : Vertex d} (hxQ : x ∈ Q.vertices) (hx : x ∉ cubeLayer Q (r + 1))
    (k : Fin d) :
    mesoInterpolation N (cubeCutoff Q r) w (x + unit k) -
        mesoInterpolation N (cubeCutoff Q r) w x = cubeSlope N w x k := by
  have hc : ∀ j, Q.corner j + (r + 1) ≤ x j ∧ x j + (r + 1) < Q.corner j + Q.size := by
    intro j
    by_contra h
    apply hx
    refine Finset.mem_filter.mpr ⟨hxQ, j, ?_⟩
    push_cast
    omega
  have h1 : cubeCutoff Q r x = 1 :=
    cubeCutoff_eq_one Q hr fun j => ⟨by linarith [(hc j).1], by linarith [(hc j).2]⟩
  have h2 : cubeCutoff Q r (x + unit k) = 1 := by
    refine cubeCutoff_eq_one Q hr fun j => ?_
    rw [add_unit_apply]
    split_ifs <;> constructor <;> linarith [(hc j).1, (hc j).2]
  rw [mesoInterpolation_eq_of_eq_one N w h2, mesoInterpolation_eq_of_eq_one N w h1,
    cubeAverage_add_unit_sub]
  rfl

/-- **The energy of the trial function**: for `a_k ≤ Λ` and `r ≥ 1`,
`Σ_{x∈Q} Σ_k a_k (∇_k ũ)² ≤ Σ_{x ∈ Q ∖ layer} Σ_k a_k p_k(x)² + Λ Σ_{x ∈ layer} Σ_k (∇_k ũ)²`. -/
theorem sum_energy_mesoInterpolation_le (a : Fin d → ℝ) {Λ : ℝ}
    (haΛ : ∀ k, a k ≤ Λ) (Q : IntegerCube d) (N : ℕ) {r : ℕ} (hr : 0 < r)
    (w : Vertex d → ℝ) :
    ∑ x ∈ Q.vertices, ∑ k : Fin d, a k * (mesoInterpolation N (cubeCutoff Q r) w (x + unit k) -
        mesoInterpolation N (cubeCutoff Q r) w x) ^ 2 ≤
      ∑ x ∈ Q.vertices \ cubeLayer Q (r + 1), ∑ k : Fin d, a k * cubeSlope N w x k ^ 2 +
        Λ * ∑ x ∈ cubeLayer Q (r + 1), ∑ k : Fin d,
          (mesoInterpolation N (cubeCutoff Q r) w (x + unit k) -
            mesoInterpolation N (cubeCutoff Q r) w x) ^ 2 := by
  rw [← Finset.sum_sdiff (cubeLayer_subset Q (r + 1))]
  refine add_le_add (le_of_eq (Finset.sum_congr rfl fun x hx => ?_)) ?_
  · obtain ⟨hxQ, hxL⟩ := Finset.mem_sdiff.mp hx
    exact Finset.sum_congr rfl fun k _ => by
      rw [mesoInterpolation_cubeCutoff_grad Q N hr w hxQ hxL k]
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (haΛ k) (sq_nonneg _)

end Rigidity.Dirichlet
