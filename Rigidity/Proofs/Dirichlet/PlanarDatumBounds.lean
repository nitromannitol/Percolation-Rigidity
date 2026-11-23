import Rigidity.Proofs.Dirichlet.PlanarPropSixOne
import Rigidity.Proofs.Dirichlet.PlanarInterpolation

/-!
# Bounds on the datum and on the homogenized solution

Under moment bounds `|□_m|⁻¹ Σ_{x ∈ □_m} size(□_𝒫(x))^t ≤ C_M` (the first bound of (2.12) of
Armstrong and Dario above the minimal scale), the planar Lemma 6.4 (iii) and the bounds of the
moments of the reach scales give, for `1 ≤ s < p'`,
`|□_m|⁻¹ Σ_{edges in □_m} |∇w̃|^s ≤ C(s, p', C_M) M^s`, `M = planarGradNorm`
(`sum_abs_grad_planarDatum_rpow_div_le`). The homogenized solution for `ā = σ I` is harmonic for
the discrete Laplacian, equals the datum off the interior and its energy is at most that of the
datum (`condLaplacian_constCond_one_eq_zero`, `innerEdgeEnergy_constCond_one_le`).
-/

open Finset LatticeProb LatticeHC LatticeProb.Percolation Rigidity.Percolation
open Rigidity.Proofs.Section5
open scoped Classical

namespace Rigidity.Dirichlet

variable {ω : Configuration 2}

/-- The constant of the planar Lemma 6.4 (iii) under the moment bound `C_M`. -/
noncomputable def planarDatumConst (s p' CM : ℝ) : ℝ :=
  (3 : ℝ) ^ (s - 1) * (((2 : ℕ) : ℝ) * (2 : ℝ) ^ (s / 2) * planarConstThree ^ s *
      (1 + 324 * CM) ^ (1 - s / p') +
    2 * ((2 : ℕ) : ℝ) * planarConstTwo ^ s * (81 * CM) ^ (1 - s / p'))

/-- **The gradient of the datum under the moment bounds.** -/
theorem sum_abs_grad_planarDatum_rpow_div_le (hP : PlanarPartitionEvent ω) {m : ℕ}
    (hU : PlanarResolved ω ⟨m, 0⟩) {s p' CM : ℝ} (hs : 1 ≤ s) (hsp : s < p')
    (hmom3 : (∑ x ∈ (⟨m, 0⟩ : TriadicCube 2).toIntegerCube.vertices,
        ((3 : ℝ) ^ (planarPartCube ω x).scale) ^ ((s * ((2 : ℕ) : ℝ) - 1) * (p' / (p' - s)) + 2)) /
        9 ^ m ≤ CM)
    (hmom2 : (∑ x ∈ (⟨m, 0⟩ : TriadicCube 2).toIntegerCube.vertices,
        ((3 : ℝ) ^ (planarPartCube ω x).scale) ^ ((s * ((2 : ℕ) : ℝ)) * (p' / (p' - s)) + 2)) /
        9 ^ m ≤ CM)
    (u : Vertex 2 → ℝ) :
    (∑ x ∈ (⟨m, 0⟩ : TriadicCube 2).toIntegerCube.vertices, ∑ j : Fin 2,
        (if x + unit j ∈ (⟨m, 0⟩ : TriadicCube 2).toIntegerCube.vertices then
          |planarDatum hP m hU u (x + unit j) - planarDatum hP m hU u x| ^ s else 0)) / 9 ^ m ≤
      planarDatumConst s p' CM * planarGradNorm ω m p' u ^ s := by
  have hV : (0 : ℝ) < 9 ^ m := by positivity
  have h := planar_sum_abs_grad_boundaryInterpolation_rpow_div_le hP hU
    (clusterBoundary_subset ω m) u hs hsp hV
  refine h.trans ?_
  unfold planarInterpolationBound planarDatumConst
  have hs0 : 0 < s := by linarith
  have he : 0 ≤ 1 - s / p' := by
    rw [sub_nonneg, div_le_one (by linarith)]
    exact hsp.le
  have hCcard : ((clusterVertices ω ⟨m, 0⟩).card : ℝ) ≤ 9 ^ m := by
    have h1 : (clusterVertices ω ⟨m, 0⟩).card ≤
        (⟨m, 0⟩ : TriadicCube 2).toIntegerCube.vertices.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    rw [IntegerCube.card_vertices] at h1
    have h2 : (((⟨m, 0⟩ : TriadicCube 2).toIntegerCube.size : ℕ) : ℝ) ^ 2 = 9 ^ m := by
      change ((3 ^ m : ℕ) : ℝ) ^ 2 = 9 ^ m
      push_cast
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    have : ((clusterVertices ω ⟨m, 0⟩).card : ℝ) ≤
        (((⟨m, 0⟩ : TriadicCube 2).toIntegerCube.size : ℕ) : ℝ) ^ 2 := by exact_mod_cast h1
    linarith
  -- the moments of the pair reach scale
  have hM3 : (∑ z ∈ clusterVertices ω ⟨m, 0⟩,
      (((3 : ℝ) ^ (planarCoarseData hP ⟨m, 0⟩ hU).pairReachScale z) ^
        (s * ((2 : ℕ) : ℝ) - 1)) ^ (p' / (p' - s))) / 9 ^ m ≤ 1 + 324 * CM := by
    have e : ∀ z, (((3 : ℝ) ^ (planarCoarseData hP ⟨m, 0⟩ hU).pairReachScale z) ^
        (s * ((2 : ℕ) : ℝ) - 1)) ^ (p' / (p' - s)) =
        ((3 : ℝ) ^ (planarCoarseData hP ⟨m, 0⟩ hU).pairReachScale z) ^
          ((s * ((2 : ℕ) : ℝ) - 1) * (p' / (p' - s))) := fun z => by
      rw [← Real.rpow_mul (by positivity)]
    simp only [e]
    have h1 := sum_three_pow_pairReachScale_rpow_le hP hU
      ((s * ((2 : ℕ) : ℝ) - 1) * (p' / (p' - s)))
    rw [div_le_iff₀ hV]
    rw [div_le_iff₀ hV] at hmom3
    nlinarith
  have hM2 : (∑ z ∈ clusterVertices ω ⟨m, 0⟩,
      (((3 : ℝ) ^ (planarCoarseData hP ⟨m, 0⟩ hU).reachScale z) ^
        (s * ((2 : ℕ) : ℝ))) ^ (p' / (p' - s))) / 9 ^ m ≤ 81 * CM := by
    have e : ∀ z, (((3 : ℝ) ^ (planarCoarseData hP ⟨m, 0⟩ hU).reachScale z) ^
        (s * ((2 : ℕ) : ℝ))) ^ (p' / (p' - s)) =
        ((3 : ℝ) ^ (planarCoarseData hP ⟨m, 0⟩ hU).reachScale z) ^
          ((s * ((2 : ℕ) : ℝ)) * (p' / (p' - s))) := fun z => by
      rw [← Real.rpow_mul (by positivity)]
    simp only [e]
    have h1 := sum_three_pow_reachScale_rpow_le hP hU ((s * ((2 : ℕ) : ℝ)) * (p' / (p' - s)))
    rw [div_le_iff₀ hV]
    rw [div_le_iff₀ hV] at hmom2
    nlinarith
  have hG : ((∑ z ∈ clusterVertices ω ⟨m, 0⟩,
      gradNormIn (openGraph ω) (clusterVertices ω ⟨m, 0⟩) u z ^ p') / 9 ^ m) ^ (s / p') =
      planarGradNorm ω m p' u ^ s := by
    unfold planarGradNorm
    rw [← Real.rpow_mul (div_nonneg (Finset.sum_nonneg fun z _ =>
      Real.rpow_nonneg (gradNormIn_nonneg _ _ _ _) _) hV.le)]
    congr 1
    field_simp
  rw [hG]
  have hGs : 0 ≤ planarGradNorm ω m p' u ^ s := by
    unfold planarGradNorm
    exact Real.rpow_nonneg (Real.rpow_nonneg (div_nonneg (Finset.sum_nonneg fun z _ =>
      Real.rpow_nonneg (gradNormIn_nonneg _ _ _ _) _) hV.le) _) _
  refine mul_le_mul_of_nonneg_right ?_ hGs
  refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by positivity)
  · refine mul_le_mul_of_nonneg_left ?_ (by
      have := planarConstThree_nonneg
      positivity)
    exact Real.rpow_le_rpow (by positivity) hM3 he
  · refine mul_le_mul_of_nonneg_left ?_ (by
      have := planarConstTwo_nonneg
      positivity)
    exact Real.rpow_le_rpow (by positivity) hM2 he

/-- The Laplacian of a constant conductance is proportional to the conductance. -/
theorem condLaplacian_constCond_smul (σ : ℝ) (u : Vertex 2 → ℝ) (x : Vertex 2) :
    condLaplacian (constCond fun _ => σ) u x =
      σ * condLaplacian (constCond fun _ => (1 : ℝ)) u x := by
  unfold condLaplacian constCond
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **The homogenized solution is harmonic for the discrete Laplacian.** -/
theorem condLaplacian_constCond_one_eq_zero {σ : ℝ} (hσ : 0 < σ) (Q : IntegerCube 2)
    (w : Vertex 2 → ℝ) {x : Vertex 2} (hx : x ∈ cubeInterior Q) :
    condLaplacian (constCond fun _ => (1 : ℝ))
      (dirichletSolution (constCond fun _ => σ) (cubeInterior Q) w) x = 0 := by
  have h := condLaplacian_dirichletSolution (d := 2) (by norm_num) (constCond fun _ => σ)
    (fun _ => hσ) (cubeInterior Q) w x hx
  rw [condLaplacian_constCond_smul] at h
  rcases mul_eq_zero.1 h with h | h
  · exact absurd h hσ.ne'
  · exact h

/-- **The energy of the homogenized solution is at most that of the datum.** -/
theorem innerEdgeEnergy_constCond_one_le {σ : ℝ} (hσ : 0 < σ) (Q : IntegerCube 2)
    (w : Vertex 2 → ℝ) :
    innerEdgeEnergy (constCond fun _ => (1 : ℝ)) Q
        (dirichletSolution (constCond fun _ => σ) (cubeInterior Q) w) ≤
      ∑ x ∈ Q.vertices, ∑ j : Fin 2,
        (if x + unit j ∈ Q.vertices then (w (x + unit j) - w x) ^ 2 else 0) := by
  have h := sum_sq_inner_grad_dirichletSolution_le (d := 2) (by norm_num) (fun _ => σ) hσ
    (fun _ => ⟨le_rfl, le_rfl⟩) Q w
  rw [div_self hσ.ne', one_mul] at h
  rw [innerEdgeEnergy_eq_sum_ite]
  refine le_trans (le_of_eq ?_) h
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · simp [constCond]
  · rfl

end Rigidity.Dirichlet
