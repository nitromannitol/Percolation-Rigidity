import Rigidity.Proofs.Dirichlet.PlanarBlockGeometry

/-!
# The error chain of Section 6 in dimension two

The planar Lemmas 6.2 and 6.3 and Proposition 6.1 combined, with the mesoscopic cubes of side
`3^{2k}` for the `μ` test, the tiles of side `K = 3^k` for the maximizers of `ν`, the layer depth
`r = 3^{4k}`, the cutoff width `ρ = 3^{3k}` and the block of `blockGeometry`: for `u` harmonic on
`C_*(□_m)` off `∂□_m` and the homogenized solution `u_h`,
`Σ_{C_*(□_m)} (u − u_h)² ≤ 2 P (δ₁ + δ₂) + 2 δ₃`, with the errors `δ₁, δ₂, δ₃` explicit in the
normalized sums `S₂ = Σ_{edges in □_m} |∇w̃|²` and `S_t = Σ_{edges in □_m} |∇w̃|^t` of the datum
(`planar_error_chain`).
-/

open Finset LatticeProb LatticeHC LatticeProb.Percolation Rigidity.Percolation
open Rigidity.Proofs.Section5
open scoped Classical

namespace Rigidity.Dirichlet

variable {ω : Configuration 2}

/-- The sum of the squared increments of `w` over the edges inside `Q`. -/
noncomputable def innerSqSum (Q : IntegerCube 2) (w : Vertex 2 → ℝ) : ℝ :=
  ∑ y ∈ Q.vertices, ∑ j : Fin 2, (if y + unit j ∈ Q.vertices then (w (y + unit j) - w y) ^ 2 else 0)

/-- The sum of the `t`-th powers of the increments of `w` over the edges inside `Q`. -/
noncomputable def innerRpowSum (Q : IntegerCube 2) (w : Vertex 2 → ℝ) (t : ℝ) : ℝ :=
  ∑ y ∈ Q.vertices, ∑ j : Fin 2,
    (if y + unit j ∈ Q.vertices then |w (y + unit j) - w y| ^ t else 0)

theorem innerSqSum_nonneg (Q : IntegerCube 2) (w : Vertex 2 → ℝ) : 0 ≤ innerSqSum Q w :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity

theorem innerRpowSum_nonneg (Q : IntegerCube 2) (w : Vertex 2 → ℝ) (t : ℝ) :
    0 ≤ innerRpowSum Q w t :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity

/-- The homogenized solution has at most the energy of its datum on the edges inside `Q`. -/
theorem innerSqSum_dirichletSolution_le {σ : ℝ} (hσ : 0 < σ) (Q : IntegerCube 2)
    (w : Vertex 2 → ℝ) :
    innerSqSum Q (dirichletSolution (constCond fun _ => σ) (cubeInterior Q) w) ≤
      innerSqSum Q w := by
  have := sum_sq_inner_grad_dirichletSolution_le (d := 2) (by norm_num) (fun _ => σ) hσ
    (fun _ => ⟨le_rfl, le_rfl⟩) Q w
  rwa [div_self hσ.ne', one_mul] at this

theorem origin_vertices_subset_succ' (m : ℕ) :
    (⟨m, 0⟩ : TriadicCube 2).vertices ⊆ (⟨m + 1, 0⟩ : TriadicCube 2).vertices :=
  (⟨m, 0⟩ : TriadicCube 2).vertices_subset_parent

/-- The Poincaré constant of `□_m` in the error chain. -/
noncomputable def chainP (K₀ : ℝ) (m k₀ : ℕ) : ℝ :=
  4 * (1 + 9 / 8 * 9 ^ k₀) * K₀ * 9 ^ (m + 1) * 81 ^ k₀

/-- The Poincaré constant of the tiles in the error chain. -/
noncomputable def chainPT (K₀ : ℝ) (k k₀ : ℕ) : ℝ :=
  4 * (1 + 9 / 8 * 9 ^ k₀) * K₀ * 9 ^ (k + 1) * 81 ^ k₀

/-- The error `δ₁` of Lemma 6.2 in the error chain, for the normalized sums `S₂`, `S_t`. -/
noncomputable def chainDeltaOne (σ ε t : ℝ) (m k : ℕ) (S2 St : ℝ) : ℝ :=
  2 * ((ε * σ ^ 2 + σ * (1 - ((((3 ^ (2 * k - k) - 1) * 3 ^ k : ℕ) : ℝ)) ^ 2 /
        ((3 ^ (2 * k) : ℕ) : ℝ) ^ 2) / 2 +
      σ * (√(1 / ((3 ^ (2 * k) : ℕ) : ℝ)) +
        √(1 - ((((3 ^ (2 * k - k) - 1) * 3 ^ k : ℕ) : ℝ)) ^ 2 /
          ((3 ^ (2 * k) : ℕ) : ℝ) ^ 2) + √(1 / ((3 ^ k : ℕ) : ℝ)))) * S2) +
    2 * (σ / √((3 ^ (2 * k) : ℕ) : ℝ) * S2) +
    ((3 ^ m : ℕ) : ℝ) ^ 2 *
      (σ * ((2 * 2 * ((3 ^ (4 * k) + 1 + 3 ^ (2 * k) : ℕ) : ℝ) / ((3 ^ m : ℕ) : ℝ)) ^ (1 - 2 / t) *
        (((2 : ℕ) : ℝ) ^ (t / 2 - 1) *
          ((1 + (3 : ℝ) ^ (t - 1) * (1 + 2 ^ t + ((2 : ℕ) : ℝ) ^ t *
            (((3 ^ (2 * k) : ℕ) : ℝ) / ((3 ^ (4 * k) : ℕ) : ℝ)) ^ t)) * St) /
          ((3 ^ m : ℕ) : ℝ) ^ 2) ^ (2 / t)))

/-- The error `δ₂` of Lemma 6.3 in the error chain. -/
noncomputable def chainDeltaTwo (σ ε γ t K₀ CA : ℝ) (m k k₀ : ℕ) (S2 St : ℝ) : ℝ :=
  (6 * ((3 ^ k : ℕ) : ℝ) ^ 2 * ((ε + 2 * (5 * 3 ^ k₀ + 1) / ((3 ^ k : ℕ) : ℝ)) *
      (S2 / ((3 ^ k : ℕ) : ℝ) ^ 2)) +
    3 * (max σ 1 * ((2 : ℕ) * (3 * ((1 + (2 : ℕ)) * 2 ^ 2 * ((3 ^ k : ℕ) : ℝ) ^ 3 *
      (10 * (2 : ℕ) * max σ 1 / (σ * (((3 ^ (4 * k) : ℕ) : ℝ)) ^ 2)) +
        1 / ((3 ^ k : ℕ) : ℝ)) * S2))) +
    6 * max σ 1 * ((2 : ℕ) * (1 / ((3 ^ (3 * k) : ℕ) : ℝ)) ^ 2) *
      (chainPT K₀ k k₀ * (4 * S2) +
        CA * ((3 ^ k : ℕ) : ℝ) ^ 4 / (((3 ^ (4 * k) : ℕ) : ℝ)) ^ 2 * S2)) +
  ((3 ^ m : ℕ) : ℝ) ^ 2 *
    ((2 + 3 * max σ 1 / σ) *
      (2 * (σ * ((2 * 2 * ((3 ^ (4 * k) + 3 + 3 * 3 ^ k + 3 ^ (3 * k) + 3 ^ k + 1 : ℕ) : ℝ) /
          ((3 ^ m : ℕ) : ℝ)) ^ (1 - 2 / t) *
        ((2 : ℝ) ^ (t / 2 - 1) * (St / ((3 ^ m : ℕ) : ℝ) ^ 2)) ^ (2 / t))) +
        88 * max σ 1 * Real.exp (γ + 4 * γ ^ 2) *
          ((2 * ((2 : ℕ) : ℝ)) ^ (t / (t - 2)) / (1 - γ * (t / (t - 2)))) ^ (1 - 2 / t) *
          ((((3 ^ (4 * k) + 3 + 3 * 3 ^ k + 3 ^ (3 * k) + 3 ^ k : ℕ) : ℝ) + 1) /
            ((3 ^ m : ℕ) : ℝ)) ^ γ *
          ((2 : ℝ) ^ (t / 2 - 1) * (St / ((3 ^ m : ℕ) : ℝ) ^ 2)) ^ (2 / t)))

/-- The `L²` error `δ₃` of Lemma 6.3 (iii) in the error chain. -/
noncomputable def chainDeltaThree (σ K₀ C₃ : ℝ) (k k₀ : ℕ) (S2 : ℝ) : ℝ :=
  2 * (chainPT K₀ k k₀ * (4 * S2)) +
    2 * (C₃ * ((3 ^ k : ℕ) : ℝ) ^ 4 / (((3 ^ (4 * k) : ℕ) : ℝ)) ^ 2 * (σ / σ * S2))

theorem le_add_mul_of_div_le {a b c L : ℝ} (hL : 0 < L) (h : a / L ≤ b / L + c) :
    a ≤ b + L * c := by
  rw [div_le_iff₀ hL, add_mul, div_mul_cancel₀ _ hL.ne'] at h
  linarith

theorem le_add_add_mul_of_div_le {a b c d L : ℝ} (hL : 0 < L) (h : a / L ≤ b / L + c / L + d) :
    a ≤ b + (c + L * d) := by
  rw [div_le_iff₀ hL, add_mul, add_mul, div_mul_cancel₀ _ hL.ne', div_mul_cancel₀ _ hL.ne'] at h
  linarith

/-- **The error chain of Section 6 in dimension two.** -/
theorem planar_error_chain {σ : ℝ} (hσ : 0 < σ) :
    ∃ K₀ C₃ CA : ℝ, 0 ≤ K₀ ∧ 0 ≤ C₃ ∧ 0 ≤ CA ∧
    ∀ (ω : Configuration 2) (hP : PlanarPartitionEvent ω) (m k k₀ : ℕ), k₀ ≤ k →
      2 * (3 ^ (4 * k) + 3) + 3 * 3 ^ k ≤ 3 ^ m →
      (∀ x ∈ (⟨m + 1, 0⟩ : TriadicCube 2).vertices, (planarPartCube ω x).scale ≤ k₀) →
      ∀ (hU : PlanarResolved ω ⟨m, 0⟩) {ε : ℝ}, 0 ≤ ε →
      (∀ T : TriadicCube 2, T.scale = k → T.vertices ⊆ (⟨m, 0⟩ : TriadicCube 2).vertices →
        ∀ q : Fin 2 → ℝ, |(∑ j, q j ^ 2 / σ) / 2 + planarMu ω T q| ≤ ε * ∑ j, q j ^ 2) →
      (∀ T : TriadicCube 2, T.scale = k → T.vertices ⊆ (⟨m, 0⟩ : TriadicCube 2).vertices →
        ∀ ξ : Fin 2 → ℝ, |planarNu ω T ξ - σ * (∑ j, ξ j ^ 2) / 2| ≤ ε * ∑ j, ξ j ^ 2) →
      ∀ {γ t : ℝ}, 0 < γ → γ ≤ 1 / 16 → 2 < t → γ * (t / (t - 2)) < 1 →
      ∀ u : Vertex 2 → ℝ,
      (fun x : ↥(clusterVertices ω ⟨m, 0⟩) => u x) ∈ clusterHarmonic ω ⟨m, 0⟩ →
      ∑ x ∈ clusterVertices ω ⟨m, 0⟩, (u x - dirichletSolution (constCond fun _ => σ)
          (cubeInterior (⟨m, 0⟩ : TriadicCube 2).toIntegerCube) (planarDatum hP m hU u) x) ^ 2 ≤
        2 * (chainP K₀ m k₀ *
          ((chainDeltaOne σ ε t m k
              (innerSqSum (⟨m, 0⟩ : TriadicCube 2).toIntegerCube (planarDatum hP m hU u))
              (innerRpowSum (⟨m, 0⟩ : TriadicCube 2).toIntegerCube (planarDatum hP m hU u) t) +
            chainDeltaTwo σ ε γ t K₀ CA m k k₀
              (innerSqSum (⟨m, 0⟩ : TriadicCube 2).toIntegerCube (planarDatum hP m hU u))
              (innerRpowSum (⟨m, 0⟩ : TriadicCube 2).toIntegerCube (planarDatum hP m hU u) t)) /
            1)) +
        2 * chainDeltaThree σ K₀ C₃ k k₀
          (innerSqSum (⟨m, 0⟩ : TriadicCube 2).toIntegerCube (planarDatum hP m hU u)) := by
  obtain ⟨K₀, hK₀0, hK₀⟩ := exists_planar_sum_sq_le_of_eq_zero
  obtain ⟨C₃, hC₃, h3⟩ := exists_sum_sq_patch_sub_le_inner (d := 2) (by norm_num) (fun _ => σ)
    hσ (fun _ => ⟨le_rfl, le_rfl⟩)
  obtain ⟨CA, hCA, hA⟩ := exists_sum_tiles_sq_dirichletSolution_sub_le hσ
  refine ⟨K₀, C₃, CA, hK₀0, hC₃, hCA, ?_⟩
  intro ω hP m k k₀ hk₀k hbig hk₀ hU ε hε0 hμ hν γ t hγ0 hγ ht hγt u hu
  obtain ⟨hsub, hT1, hT2⟩ := blockGeometry (m := m) (k := k) (r := 3 ^ (4 * k)) hbig
  have hdiv := blockCorner_dvd m k (3 ^ (4 * k))
  have hkm : k + 1 ≤ m := by
    have h1 : 3 ^ (k + 1) ≤ 3 ^ m := by
      have : 3 ^ (k + 1) ≤ 2 * (3 ^ (4 * k) + 3) + 3 * 3 ^ k := by
        rw [pow_succ]
        have : 3 ^ k ≤ 3 ^ (4 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      omega
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h1
  have hk₀m : k₀ ≤ m := by omega
  have hkU : ∀ x ∈ (⟨m, 0⟩ : TriadicCube 2).vertices, (planarPartCube ω x).scale ≤ k₀ :=
    fun x hx => hk₀ x (origin_vertices_subset_succ' m hx)
  have hkUk : ∀ x ∈ (⟨m, 0⟩ : TriadicCube 2).vertices, (planarPartCube ω x).scale ≤ k :=
    fun x hx => (hkU x hx).trans hk₀k
  have hsz : (⟨m, 0⟩ : TriadicCube 2).toIntegerCube.size = 3 ^ m := rfl
  have hV : (0 : ℝ) < ((3 ^ m : ℕ) : ℝ) ^ 2 := by
    have : (0 : ℝ) < ((3 ^ m : ℕ) : ℝ) := by exact_mod_cast pow_pos (by norm_num : 0 < 3) m
    exact pow_pos this 2
  -- Lemma 6.2
  have h62 := planar_lemmaSixTwo (n := 2 * k) (r := 3 ^ (4 * k)) hP (by omega) (by positivity) hU
    hkUk hσ hε0 hμ hu ht.le
  rw [hsz] at h62
  have h₁ : innerEdgeEnergy (constCond fun _ => σ) (⟨m, 0⟩ : TriadicCube 2).toIntegerCube
        (dirichletSolution (constCond fun _ => σ)
          (cubeInterior (⟨m, 0⟩ : TriadicCube 2).toIntegerCube) (planarDatum hP m hU u)) ≤
      innerEdgeEnergy (clusterCond ω ⟨m, 0⟩) (⟨m, 0⟩ : TriadicCube 2).toIntegerCube u +
        chainDeltaOne σ ε t m k
          (innerSqSum (⟨m, 0⟩ : TriadicCube 2).toIntegerCube (planarDatum hP m hU u))
          (innerRpowSum (⟨m, 0⟩ : TriadicCube 2).toIntegerCube (planarDatum hP m hU u) t) := by
    refine (le_add_mul_of_div_le hV h62).trans_eq ?_
    simp only [chainDeltaOne, innerSqSum, innerRpowSum]
    ring
  -- Lemma 6.3 (ii)
  have h63 := planar_lemmaSixThree (ρ := 3 ^ (3 * k)) hP hkUk hσ (planarDatum hP m hU u)
    (by positivity) hdiv (blockCount m k (3 ^ (4 * k))) hsub hT1 hT2 (by positivity) hγ0 hγ ht hγt
  rw [hsz] at h63
  have h63' := le_add_add_mul_of_div_le hV h63
  have hS2uh := innerSqSum_dirichletSolution_le hσ (⟨m, 0⟩ : TriadicCube 2).toIntegerCube
    (planarDatum hP m hU u)
  have htile := sum_tileError_le hP hU hkU hε0 hν hdiv
    (dirichletSolution (constCond fun _ => σ)
      (cubeInterior (⟨m, 0⟩ : TriadicCube 2).toIntegerCube) (planarDatum hP m hU u)) hsub
  have hpatch := sum_sq_tilePatch_tiles_le hK₀0 hK₀ hP hk₀k hkm hkU hdiv
    (dirichletSolution (constCond fun _ => σ)
      (cubeInterior (⟨m, 0⟩ : TriadicCube 2).toIntegerCube) (planarDatum hP m hU u)) hsub
  have haff := hA (⟨m, 0⟩ : TriadicCube 2).toIntegerCube (planarDatum hP m hU u) (3 ^ (4 * k))
    (by positivity) (blockCorner m k (3 ^ (4 * k))) (blockCount m k (3 ^ (4 * k))) (3 ^ k)
    (by positivity) hsub
  have hlay := layer_energy_div_le (⟨m, 0⟩ : TriadicCube 2).toIntegerCube
    (by rw [hsz]; positivity) (planarDatum hP m hU u) hσ.le
    (3 ^ (4 * k) + 3 + 3 * 3 ^ k + 3 ^ (3 * k) + 3 ^ k + 1) ht.le
  have hhardy := hardy_term_le (⟨m, 0⟩ : TriadicCube 2).toIntegerCube (planarDatum hP m hU u) ht.le
  rw [hsz] at hlay hhardy
  have hγt' : 0 < 1 - γ * (t / (t - 2)) := by linarith
  have h₂ : innerEdgeEnergy (clusterCond ω ⟨m, 0⟩) (⟨m, 0⟩ : TriadicCube 2).toIntegerCube
        (patch (cubeCutoff (cornerCube (blockCorner m k (3 ^ (4 * k)))
            (blockCount m k (3 ^ (4 * k)) * 3 ^ k)) (3 ^ (3 * k)))
          (tilePatch ω k (blockCorner m k (3 ^ (4 * k))) (dirichletSolution (constCond fun _ => σ)
            (cubeInterior (⟨m, 0⟩ : TriadicCube 2).toIntegerCube) (planarDatum hP m hU u)))
          (dirichletSolution (constCond fun _ => σ)
            (cubeInterior (⟨m, 0⟩ : TriadicCube 2).toIntegerCube) (planarDatum hP m hU u))) ≤
      innerEdgeEnergy (constCond fun _ => σ) (⟨m, 0⟩ : TriadicCube 2).toIntegerCube
        (dirichletSolution (constCond fun _ => σ)
          (cubeInterior (⟨m, 0⟩ : TriadicCube 2).toIntegerCube) (planarDatum hP m hU u)) +
        chainDeltaTwo σ ε γ t K₀ CA m k k₀
          (innerSqSum (⟨m, 0⟩ : TriadicCube 2).toIntegerCube (planarDatum hP m hU u))
          (innerRpowSum (⟨m, 0⟩ : TriadicCube 2).toIntegerCube (planarDatum hP m hU u) t) := by
    refine h63'.trans (add_le_add le_rfl ?_)
    unfold chainDeltaTwo
    refine add_le_add ?_ (mul_le_mul_of_nonneg_left ?_ hV.le)
    · refine add_le_add (add_le_add ?_ ?_) ?_
      · exact mul_le_mul_of_nonneg_left (htile.trans (mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right hS2uh (by positivity)) (by positivity))) (by positivity)
      · gcongr
        exact hS2uh
      · refine mul_le_mul_of_nonneg_left (add_le_add ?_ haff) (by positivity)
        refine hpatch.trans (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hS2uh (by norm_num)) ?_)
        positivity
    · refine mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hlay (by norm_num))
        (mul_le_mul_of_nonneg_left hhardy ?_)) (by positivity)
      have h1 : 0 ≤ ((2 * ((2 : ℕ) : ℝ)) ^ (t / (t - 2)) / (1 - γ * (t / (t - 2)))) ^ (1 - 2 / t) :=
        Real.rpow_nonneg (div_nonneg (by positivity) hγt'.le) _
      positivity
  -- Lemma 6.3 (iii)
  have h3' := h3 (⟨m, 0⟩ : TriadicCube 2).toIntegerCube (planarDatum hP m hU u) (3 ^ (4 * k))
    (by positivity) (blockCorner m k (3 ^ (4 * k))) (blockCount m k (3 ^ (4 * k))) (3 ^ k)
    (by positivity) hsub (3 ^ (3 * k)) (clusterVertices ω ⟨m, 0⟩) (Finset.filter_subset _ _)
    (tilePatch ω k (blockCorner m k (3 ^ (4 * k))) (dirichletSolution (constCond fun _ => σ)
      (cubeInterior (⟨m, 0⟩ : TriadicCube 2).toIntegerCube) (planarDatum hP m hU u)))
  have h₃ := h3'.trans (show _ ≤ chainDeltaThree σ K₀ C₃ k k₀
      (innerSqSum (⟨m, 0⟩ : TriadicCube 2).toIntegerCube (planarDatum hP m hU u)) by
    unfold chainDeltaThree
    refine add_le_add (mul_le_mul_of_nonneg_left (hpatch.trans
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hS2uh (by norm_num)) ?_))
      (by norm_num)) le_rfl
    positivity)
  -- the patch equals the homogenized solution off the interior
  have hv : ∀ x, x ∉ cubeInterior (⟨m, 0⟩ : TriadicCube 2).toIntegerCube →
      patch (cubeCutoff (cornerCube (blockCorner m k (3 ^ (4 * k)))
          (blockCount m k (3 ^ (4 * k)) * 3 ^ k)) (3 ^ (3 * k)))
        (tilePatch ω k (blockCorner m k (3 ^ (4 * k))) (dirichletSolution (constCond fun _ => σ)
          (cubeInterior (⟨m, 0⟩ : TriadicCube 2).toIntegerCube) (planarDatum hP m hU u)))
        (dirichletSolution (constCond fun _ => σ)
          (cubeInterior (⟨m, 0⟩ : TriadicCube 2).toIntegerCube) (planarDatum hP m hU u)) x =
      dirichletSolution (constCond fun _ => σ)
        (cubeInterior (⟨m, 0⟩ : TriadicCube 2).toIntegerCube) (planarDatum hP m hU u) x := by
    intro x hx
    refine patch_cubeCutoff_of_not_mem _ _ _ _ fun hxT => hx ?_
    refine shrinkCube_one_vertices_subset_cubeInterior _ (shrinkCube_vertices_mono _
      (show 1 ≤ 3 ^ (4 * k) + 3 from le_trans (by norm_num) (Nat.le_add_left 3 _))
      (hsub (cornerCube_mul_subset_succ _ _ _ hxT)))
  exact planar_sum_sq_sub_uhom_le hK₀0 hK₀ hP hk₀m hk₀ hU hu hv h₁ h₂ h₃

end Rigidity.Dirichlet
