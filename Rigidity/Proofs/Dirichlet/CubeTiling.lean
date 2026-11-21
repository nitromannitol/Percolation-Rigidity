import Rigidity.Proofs.Dirichlet.CubeStokes

/-!
# Tiling a lattice cube by subcubes

The cube with corner `z` and side `M K` is the disjoint union of the `M^d` cubes with corners
`z + K i`, `i ∈ {0, …, M − 1}^d`, and side `K`, so a sum over it is the sum over the subcubes of
the sums over them. This is the partition of `□°_int` into the mesh cubes `y + □_k`
(`y ∈ 3^k ℤ^d`) in Step 4 of the proof of Armstrong–Dario, Lemma 6.2, and into the mesoscopic
cubes `y + □_n` in the proof of Lemma 6.3.
-/

open Finset LatticeProb

namespace Rigidity.Dirichlet

open Rigidity.Percolation LatticeProb.Percolation

variable {d : ℕ}

/-- **Sums over a cube are sums over its subcubes.** -/
theorem sum_cornerCube_mul {K : ℕ} (hK : 0 < K) (z : Vertex d) (M : ℕ)
    (F : Vertex d → ℝ) :
    ∑ x ∈ (cornerCube z (M * K)).vertices, F x =
      ∑ i ∈ (cornerCube 0 M).vertices, ∑ x ∈ (cornerCube (z + (K : ℤ) • i) K).vertices, F x := by
  classical
  have hK' : (0 : ℤ) < K := by exact_mod_cast hK
  rw [Finset.sum_sigma']
  refine (Finset.sum_bij' (fun x _ => (⟨fun t => (x t - z t) / K, x⟩ : Σ _ : Vertex d, Vertex d))
    (fun p _ => p.2) ?_ ?_ ?_ ?_ ?_)
  · intro x hx
    rw [IntegerCube.mem_vertices] at hx
    simp only [cornerCube] at hx
    refine Finset.mem_sigma.mpr ⟨?_, ?_⟩
    · rw [IntegerCube.mem_vertices]
      intro t
      simp only [cornerCube, Pi.zero_apply, zero_add]
      have h1 := hx t
      push_cast at h1
      refine ⟨Int.ediv_nonneg (by linarith) hK'.le, Int.ediv_lt_of_lt_mul hK' (by linarith)⟩
    · rw [IntegerCube.mem_vertices]
      intro t
      simp only [cornerCube, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have h2 := Int.mul_ediv_add_emod (x t - z t) K
      have h3 := Int.emod_nonneg (x t - z t) hK'.ne'
      have h4 := Int.emod_lt_of_pos (x t - z t) hK'
      constructor <;> linarith
  · intro p hp
    obtain ⟨hi, hx⟩ := Finset.mem_sigma.mp hp
    rw [IntegerCube.mem_vertices] at hi hx ⊢
    intro t
    simp only [cornerCube, Pi.zero_apply, zero_add, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul] at hi hx ⊢
    have h1 := hi t
    have h2 := hx t
    push_cast
    constructor
    · nlinarith
    · have : (K : ℤ) * p.1 t + K ≤ (M : ℤ) * K := by nlinarith
      nlinarith
  · intro x _
    rfl
  · intro p hp
    obtain ⟨hi, hx⟩ := Finset.mem_sigma.mp hp
    rw [IntegerCube.mem_vertices] at hi hx
    simp only [cornerCube, Pi.zero_apply, zero_add, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul] at hi hx
    have hfst : (fun t => (p.2 t - z t) / K) = p.1 := by
      funext t
      have h2 := hx t
      exact ((Int.ediv_emod_unique (a := p.2 t - z t) (r := p.2 t - z t - K * p.1 t)
        (q := p.1 t) hK').mpr ⟨by ring, by linarith [h2.1], by linarith [h2.2]⟩).1
    exact Sigma.ext hfst HEq.rfl
  · intro x _
    rfl

/-- **Sums over all translates of a cube**: for `F ≥ 0` and `B ⊇ A + {0, …, N − 1}^d`,
`Σ_{x∈A} Σ_{y ∈ x + □} F(y) ≤ N^d Σ_{y∈B} F(y)`; each point of `B` lies in at most `N^d` of the
translated cubes. With all translates in place of a mesh, this is the counting in Step 3 of the
proof of Armstrong–Dario, Lemma 6.2, on the lattice. -/
theorem sum_translates_le (A B : Finset (Vertex d)) (N : ℕ) (F : Vertex d → ℝ)
    (hF : ∀ y, 0 ≤ F y) (hB : ∀ x ∈ A, ∀ o ∈ (cornerCube 0 N).vertices, x + o ∈ B) :
    ∑ x ∈ A, ∑ y ∈ (cornerCube x N).vertices, F y ≤
      (N : ℝ) ^ d * ∑ y ∈ B, F y := by
  classical
  have hshift : ∀ x, ∑ y ∈ (cornerCube x N).vertices, F y =
      ∑ o ∈ (cornerCube 0 N).vertices, F (o + x) := by
    intro x
    have h := sum_cornerCube_add (0 : Vertex d) x N F
    rwa [zero_add] at h
  simp only [hshift]
  rw [Finset.sum_comm]
  have hcard : ((cornerCube (0 : Vertex d) N).vertices.card : ℝ) = (N : ℝ) ^ d := by
    rw [card_vertices]
    simp [cornerCube]
  calc ∑ o ∈ (cornerCube 0 N).vertices, ∑ x ∈ A, F (o + x)
      ≤ ∑ _o ∈ (cornerCube (0 : Vertex d) N).vertices, ∑ y ∈ B, F y := by
        refine Finset.sum_le_sum fun o ho => ?_
        calc ∑ x ∈ A, F (o + x) = ∑ y ∈ A.map (addRightEmbedding o), F y := by
              rw [Finset.sum_map]
              exact Finset.sum_congr rfl fun x _ => by rw [addRightEmbedding_apply, add_comm]
          _ ≤ ∑ y ∈ B, F y := by
              refine Finset.sum_le_sum_of_subset_of_nonneg (fun y hy => ?_) fun y _ _ => hF y
              obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
              exact hB x hx o ho
    _ = (N : ℝ) ^ d * ∑ y ∈ B, F y := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard]

end Rigidity.Dirichlet
