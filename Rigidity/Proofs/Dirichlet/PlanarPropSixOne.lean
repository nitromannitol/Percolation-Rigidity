import Rigidity.Proofs.Dirichlet.PlanarLemmaSixThree

/-!
# Proposition 6.1 of Armstrong and Dario in dimension two

Let `u` be harmonic on `C_*(□_m)` off `∂□_m`, `u_h` the solution of the discrete homogenized
problem with the datum `w̃ = planarDatum` (equal to `u` on `C_*(□_m) ∩ ∂□_m`), and `v` a function
equal to `u_h` off the interior of `□_m` (in the source, the patch of Lemma 6.3). Modify `u` off
the cluster to `u' = u` on `C_*(□_m)` and `u' = v` elsewhere. Then `u'` is harmonic for the
cluster conductance on the interior of `□_m`, `v = u'` off the interior, and `v − u'` vanishes off
the interior vertices of `C_*(□_m)`, so the Poincaré inequality on the cluster
(`exists_planar_sum_sq_le_of_eq_zero`) applies to `v − u'`. With the energy comparisons
`E_ā(u_h) ≤ E(u) + δ₁` (Lemma 6.2) and `E(v) ≤ E_ā(u_h) + δ₂` (Lemma 6.3 (ii)) and
`Σ_{C_*} (v − u_h)² ≤ δ₃` (Lemma 6.3 (iii)), the error chain of the lattice Proposition 6.1
(`sum_sq_sub_le_of_inner_energy_chain`) gives
`Σ_{C_*(□_m)} (u − u_h)² ≤ 2 P (δ₁ + δ₂) + 2 δ₃`, with `P` the Poincaré constant
(`planar_sum_sq_sub_uhom_le`).
-/

open Finset LatticeProb LatticeHC LatticeProb.Percolation Rigidity.Percolation
open Rigidity.Proofs.Section5
open scoped Classical

namespace Rigidity.Dirichlet

variable {ω : Configuration 2}

/-- The interior of the lattice cube of a triadic cube consists of its interior vertices. -/
theorem mem_cubeInterior_iff_isInterior (U : TriadicCube 2) (x : Vertex 2) :
    x ∈ cubeInterior U.toIntegerCube ↔ x ∈ U.vertices ∧ U.IsInterior x := by
  constructor
  · intro hx
    have hxU : x ∈ U.vertices :=
      (U.mem_toIntegerCube_vertices x).1 (Finset.mem_filter.1 hx).1
    refine ⟨hxU, fun y hy => ?_⟩
    have hb := (Finset.mem_filter.1 hx).2
    rw [← U.mem_toIntegerCube_vertices, IntegerCube.mem_vertices]
    intro i
    have h1 := hb i
    have h2 := abs_le.1 (hy i)
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  · rintro ⟨hxU, hint⟩
    have hxQ := (U.mem_toIntegerCube_vertices x).2 hxU
    refine Finset.mem_filter.2 ⟨hxQ, fun i => ?_⟩
    have hp := (TriadicCube.add_sub_unit_mem_of_isInterior hint i)
    rw [← U.mem_toIntegerCube_vertices, ← U.mem_toIntegerCube_vertices,
      IntegerCube.mem_vertices, IntegerCube.mem_vertices] at hp
    have h1 := (hp.1 i)
    have h2 := (hp.2 i)
    simp only [Pi.add_apply, Pi.sub_apply, unit, Pi.single_eq_same] at h1 h2
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- **Armstrong and Dario, Proposition 6.1, in dimension two.** -/
theorem planar_sum_sq_sub_uhom_le {K₀ : ℝ} (hK₀0 : 0 ≤ K₀)
    (hK₀ : ∀ (ω : Configuration 2), PlanarPartitionEvent ω → ∀ (U : TriadicCube 2)
      (k : ℕ), k ≤ U.scale →
      (∀ x ∈ U.parent.vertices, (planarPartCube ω x).scale ≤ k) →
      ∀ f : Vertex 2 → ℝ,
      (∀ x, ¬(x ∈ clusterVertices ω U ∧ U.IsInterior x) → f x = 0) →
      ∑ x ∈ clusterVertices ω U, f x ^ 2 ≤
        4 * (1 + 9 / 8 * 9 ^ k) * K₀ * 9 ^ (U.scale + 1) * 81 ^ k *
          ∑ z ∈ clusterVertices ω U, ∑ j : Fin 2,
            (if z + unit j ∈ clusterVertices ω U ∧ (openGraph ω).Adj z (z + unit j) then
              (f (z + unit j) - f z) ^ 2 else 0))
    (hP : PlanarPartitionEvent ω) {m k₀ : ℕ} (hk₀m : k₀ ≤ m)
    (hk₀ : ∀ x ∈ (⟨m + 1, 0⟩ : TriadicCube 2).vertices, (planarPartCube ω x).scale ≤ k₀)
    (hU : PlanarResolved ω ⟨m, 0⟩) {σ : ℝ} {u : Vertex 2 → ℝ}
    (hu : (fun x : ↥(clusterVertices ω ⟨m, 0⟩) => u x) ∈ clusterHarmonic ω ⟨m, 0⟩)
    {v : Vertex 2 → ℝ}
    (hv : ∀ x, x ∉ cubeInterior (⟨m, 0⟩ : TriadicCube 2).toIntegerCube →
      v x = dirichletSolution (constCond fun _ => σ)
        (cubeInterior (⟨m, 0⟩ : TriadicCube 2).toIntegerCube) (planarDatum hP m hU u) x)
    {δ₁ δ₂ δ₃ : ℝ}
    (h₁ : innerEdgeEnergy (constCond fun _ => σ) (⟨m, 0⟩ : TriadicCube 2).toIntegerCube
        (dirichletSolution (constCond fun _ => σ)
          (cubeInterior (⟨m, 0⟩ : TriadicCube 2).toIntegerCube) (planarDatum hP m hU u)) ≤
      innerEdgeEnergy (clusterCond ω ⟨m, 0⟩) (⟨m, 0⟩ : TriadicCube 2).toIntegerCube u + δ₁)
    (h₂ : innerEdgeEnergy (clusterCond ω ⟨m, 0⟩) (⟨m, 0⟩ : TriadicCube 2).toIntegerCube v ≤
      innerEdgeEnergy (constCond fun _ => σ) (⟨m, 0⟩ : TriadicCube 2).toIntegerCube
        (dirichletSolution (constCond fun _ => σ)
          (cubeInterior (⟨m, 0⟩ : TriadicCube 2).toIntegerCube) (planarDatum hP m hU u)) + δ₂)
    (h₃ : ∑ x ∈ clusterVertices ω ⟨m, 0⟩, (v x - dirichletSolution (constCond fun _ => σ)
        (cubeInterior (⟨m, 0⟩ : TriadicCube 2).toIntegerCube) (planarDatum hP m hU u) x) ^ 2 ≤
      δ₃) :
    ∑ x ∈ clusterVertices ω ⟨m, 0⟩, (u x - dirichletSolution (constCond fun _ => σ)
        (cubeInterior (⟨m, 0⟩ : TriadicCube 2).toIntegerCube) (planarDatum hP m hU u) x) ^ 2 ≤
      2 * (4 * (1 + 9 / 8 * 9 ^ k₀) * K₀ * 9 ^ (m + 1) * 81 ^ k₀ * ((δ₁ + δ₂) / 1)) +
        2 * δ₃ := by
  set U : TriadicCube 2 := ⟨m, 0⟩
  set Q := U.toIntegerCube
  set C := clusterVertices ω U
  set uh := dirichletSolution (constCond fun _ => σ) (cubeInterior Q) (planarDatum hP m hU u)
  set c := clusterCond ω U
  set u' : Vertex 2 → ℝ := fun x => if x ∈ C then u x else v x with hu'
  have hu'C : ∀ x ∈ C, u' x = u x := fun x hx => by simp only [hu', if_pos hx]
  -- the energy only sees the cluster
  have hE : innerEdgeEnergy c Q u' = innerEdgeEnergy c Q u := by
    unfold innerEdgeEnergy
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun x _ => ?_
    by_cases hc : c (x, j) = 0
    · rw [hc, zero_mul, zero_mul]
    · have hcl : x ∈ C ∧ x + unit j ∈ C := by
        by_contra h
        apply hc
        unfold c clusterCond
        rw [if_neg]
        exact fun h' => h ⟨h'.1, h'.2.1⟩
      rw [hu'C _ hcl.1, hu'C _ hcl.2]
  -- `u'` is harmonic for the cluster conductance
  have hharm : (fun x : ↥C => u' x) ∈ clusterHarmonic ω U := by
    have e : (fun x : ↥C => u' x) = fun x : ↥C => u x := funext fun x => hu'C x.1 x.2
    rw [e]
    exact hu
  have hlap : ∀ x ∈ cubeInterior Q, condLaplacian c u' x = 0 := fun x hx =>
    condLaplacian_clusterCond_eq_zero hharm ((mem_cubeInterior_iff_isInterior U x).1 hx).2
  -- `v = u'` off the interior
  have hvu : ∀ x, x ∉ cubeInterior Q → v x = u' x := by
    intro x hx
    by_cases hxC : x ∈ C
    · rw [hu'C x hxC, hv x hx]
      change dirichletSolution _ _ (planarDatum hP m hU u) x = u x
      rw [dirichletSolution_eq_of_not_mem _ _ _ hx]
      unfold planarDatum
      exact boundaryInterpolation_of_mem _ _ (Finset.mem_filter.2 ⟨hxC, hx⟩)
    · simp only [hu', if_neg hxC]
  -- the Poincaré inequality for `v − u'`
  have hscaleU : ∀ x ∈ U.parent.vertices, (planarPartCube ω x).scale ≤ k₀ := fun x hx => hk₀ x hx
  set f : Vertex 2 → ℝ := fun x => v x - u' x with hf
  have hf0 : ∀ x, ¬(x ∈ C ∧ U.IsInterior x) → f x = 0 := by
    intro x hx
    simp only [hf]
    by_cases hxC : x ∈ C
    · have hxi : x ∉ cubeInterior Q := fun h =>
        hx ⟨hxC, ((mem_cubeInterior_iff_isInterior U x).1 h).2⟩
      rw [hvu x hxi, sub_self]
    · simp only [hu', if_neg hxC, sub_self]
  have hpoinc := hK₀ ω hP U k₀ hk₀m hscaleU f hf0
  have hCQ : C ⊆ Q.vertices := Finset.filter_subset _ _
  have hedges : ∑ z ∈ C, ∑ j : Fin 2,
      (if z + unit j ∈ C ∧ (openGraph ω).Adj z (z + unit j) then (f (z + unit j) - f z) ^ 2
        else 0) =
      ∑ x ∈ Q.vertices, ∑ j : Fin 2,
        (if innerCond c Q (x, j) = 0 then 0 else ((v - u') (x + unit j) - (v - u') x) ^ 2) := by
    rw [← Finset.sum_subset hCQ]
    · refine Finset.sum_congr rfl fun z hz => Finset.sum_congr rfl fun j _ => ?_
      unfold innerCond
      by_cases h : z + unit j ∈ C ∧ (openGraph ω).Adj z (z + unit j)
      · have hcz : c (z, j) = 1 := by
          unfold c clusterCond
          exact if_pos ⟨hz, h.1, h.2⟩
        rw [if_pos h, if_pos (hCQ h.1), hcz, if_neg one_ne_zero]
        rfl
      · rw [if_neg h]
        have hcz : c (z, j) = 0 := by
          unfold c clusterCond
          rw [if_neg]
          exact fun h' => h ⟨h'.2.1, h'.2.2⟩
        rw [hcz, ite_self, if_pos rfl]
    · intro x _ hxC
      refine Finset.sum_eq_zero fun j _ => ?_
      have hcx : innerCond c Q (x, j) = 0 := by
        unfold innerCond c clusterCond
        split_ifs with h1 h2
        · exact absurd h2.1 hxC
        · rfl
        · rfl
      rw [if_pos hcx]
  rw [hedges] at hpoinc
  have hP0 : 0 ≤ 4 * (1 + 9 / 8 * 9 ^ k₀) * K₀ * 9 ^ (m + 1) * 81 ^ k₀ := by positivity
  have hfin := sum_sq_sub_le_of_inner_energy_chain c (lam := 1) one_pos
    (fun e => clusterCond_eq_zero_or U e) Q hlap hvu hP0
    (h₁.trans_eq (by rw [hE])) h₂ C hpoinc h₃
  calc ∑ x ∈ C, (u x - uh x) ^ 2 = ∑ x ∈ C, (u' x - uh x) ^ 2 :=
        Finset.sum_congr rfl fun x hx => by rw [hu'C x hx]
    _ ≤ _ := hfin

end Rigidity.Dirichlet
