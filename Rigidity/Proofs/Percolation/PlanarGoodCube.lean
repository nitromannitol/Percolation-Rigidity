import Rigidity.Proofs.Percolation.PlanarMeshProbability

/-!
# Good planar cubes from supercritical crossings

A square-root strip width makes the crossing mesh narrow enough to absorb the paths in the
good-cube definition.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External
open scoped ENNReal

namespace Rigidity.Percolation

/-- Strip width for the planar good-cube construction. -/
def planarMeshWidth (N : ℕ) : ℕ := Nat.sqrt N / 100

/-- The square-root strip width satisfies the size requirements of a good cube. -/
theorem planarMeshWidth_size (N : ℕ) (hN : 10000 ≤ N) :
    (2 * planarMeshWidth N + 1) ^ 2 ≤ 2 * N + 1 ∧
      ∀ n : ℕ, (N : ℝ) / 100 ≤ n → (2 * planarMeshWidth N + 1) ^ 2 < n + 1 := by
  let t := Nat.sqrt N
  let w := planarMeshWidth N
  have ht : 100 ≤ t := Nat.le_sqrt.mpr (by dsimp [t]; omega)
  have hw1 : 1 ≤ w := by
    dsimp [w, planarMeshWidth, t] at *
    exact (Nat.le_div_iff_mul_le (by norm_num)).2 (by omega)
  have hw : 100 * w ≤ t := by
    dsimp [w, planarMeshWidth, t]
    have h := Nat.div_mul_le_self (Nat.sqrt N) 100
    omega
  have hsqrt : t * t ≤ N := Nat.sqrt_le N
  have hsq : (100 * w) * (100 * w) ≤ t * t := Nat.mul_self_le_mul_self hw
  have hbound : 100 * (2 * w + 1) ^ 2 ≤ N := by nlinarith
  constructor
  · dsimp [w] at *
    nlinarith
  · intro n hn
    have hboundR : (100 : ℝ) * ((2 * w + 1) ^ 2 : ℕ) ≤ N := by exact_mod_cast hbound
    have hNn : (N : ℝ) ≤ 100 * n := by linarith
    have hcomp : ((2 * w + 1) ^ 2 : ℕ) ≤ n := by exact_mod_cast (show
      (((2 * w + 1) ^ 2 : ℕ) : ℝ) ≤ n by linarith)
    dsimp [w] at *
    omega

/-- Failure of a large good cube is covered by failure of its mesh or its crossing cluster. -/
theorem not_goodSubcube_subset (x : Vertex 2) (N : ℕ) (hN : 10000 ≤ N) :
    {ω | ¬ IsGoodSubcube ω x N} ⊆
      {ω | ¬ HasStripCrossings ω x N (planarMeshWidth N)} ∪
        {ω | ¬ ∃! V, IsCrossingCluster ω x N V} := by
  intro ω hω
  simp only [Set.mem_union, Set.mem_setOf_eq]
  by_contra h
  push Not at h
  obtain ⟨V, hV, _⟩ := h.2
  obtain ⟨hsize, hlength⟩ := planarMeshWidth_size N hN
  exact hω (isGoodSubcube_of_mesh h.1 hV hsize hlength)

/-- A large planar cube fails to be good only when a mesh or crossing-cluster estimate fails. -/
theorem goodSubcube_failure_bound_raw (p : unitInterval) (hp : criticalProbability 2 < (p : ℝ)) :
    ∃ C₁ c₁ C₂ c₂ : ℝ, 0 < C₁ ∧ 0 < c₁ ∧ 0 < C₂ ∧ 0 < c₂ ∧
      ∀ (x : Vertex 2) (N : ℕ), 10000 ≤ N →
        latticeBondLaw 2 p {ω | ¬ IsGoodSubcube ω x N} ≤
          ((2 * (2 * N + 1) : ℕ) : ℝ≥0∞) *
            ENNReal.ofReal (C₁ * ((2 * N : ℕ) + 1) *
              Real.exp (-(c₁ * planarMeshWidth N))) +
          ENNReal.ofReal (C₂ * ((2 * N : ℕ) + 1) * Real.exp (-(c₂ * (2 * N : ℕ)))) := by
  obtain ⟨C₁, c₁, hC₁, hc₁, hmesh⟩ := stripCrossings_failure_bound p hp
  obtain ⟨C₂, c₂, hC₂, hc₂, hcluster⟩ := unique_crossing_cluster_failure_bound p hp
  refine ⟨C₁, c₁, C₂, c₂, hC₁, hc₁, hC₂, hc₂, fun x N hN => ?_⟩
  exact (measure_mono (not_goodSubcube_subset x N hN)).trans
    ((measure_union_le _ _).trans (add_le_add (hmesh x N (planarMeshWidth N)) (hcluster x N)))

end Rigidity.Percolation
