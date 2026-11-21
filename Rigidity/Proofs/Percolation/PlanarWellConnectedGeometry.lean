import Rigidity.Proofs.Percolation.PlanarGoodCubeTail

/-!
# Multiscale planar well-connectedness

The failure of well-connectedness is covered by a failure of the outer cube or of one of a
finite family of subcubes.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External
open scoped ENNReal

namespace Rigidity.Percolation

/-- Candidate subcubes at scales relevant to well-connectedness. -/
noncomputable def relevantSubcubes (x : Vertex 2) (R : ℕ) : Finset (Vertex 2 × ℕ) := by
  classical
  exact ((Rigidity.Proofs.S3.cubeFinset x (2 * R)) ×ˢ Finset.range (R + 1)).filter
    (fun q => (R : ℝ) ^ (1 / 400 : ℝ) / 2 ≤ q.2)

/-- The number of relevant subcubes is bounded by a cubic polynomial in the outer radius. -/
theorem card_relevantSubcubes_le (x : Vertex 2) (R : ℕ) :
    (relevantSubcubes x R).card ≤ (4 * R + 1) ^ 2 * (R + 1) := by
  classical
  have h := Finset.card_filter_le
    (s := (Rigidity.Proofs.S3.cubeFinset x (2 * R)) ×ˢ Finset.range (R + 1))
    (p := fun q => (R : ℝ) ^ (1 / 400 : ℝ) / 2 ≤ (q.2 : ℝ))
  have heq : 2 * (2 * R) + 1 = 4 * R + 1 := by omega
  simpa only [relevantSubcubes, Finset.card_product, Rigidity.Proofs.S3.card_cubeFinset,
    Finset.card_range, heq] using h

/-- A cube meeting the outer cube and no larger than it has its centre in the doubled cube. -/
theorem centre_mem_doubled_cube {x z : Vertex 2} {R M : ℕ} (hM : M ≤ R)
    (hmeet : (cubeAt z M ∩ cubeAt x R).Nonempty) : z ∈ cubeAt x (2 * R) := by
  obtain ⟨y, hyz, hyx⟩ := hmeet
  intro i
  have h₁ := abs_sub_le (z i) (y i) (x i)
  have h₂ : |z i - y i| ≤ M := by simpa only [abs_sub_comm] using hyz i
  have h₃ := hyx i
  have hM' : (M : ℤ) ≤ R := by exact_mod_cast hM
  push_cast
  omega

/-- Failure of well-connectedness is covered by finitely many failures of good cubes. -/
theorem not_wellConnected_subset (x : Vertex 2) (R : ℕ)
    (hpower : (R : ℝ) ^ (1 / 400 : ℝ) ≤ R / 100) :
    {ω | ¬ IsWellConnected ω x R} ⊆
      {ω | ¬ IsGoodSubcube ω x R} ∪
        ⋃ q ∈ relevantSubcubes x R, {ω | ¬ IsGoodSubcube ω q.1 q.2} := by
  classical
  intro ω hbad
  by_contra h
  have hmain : IsGoodSubcube ω x R := by
    by_contra hm
    exact h (Set.mem_union_left _ hm)
  have hall : ∀ q ∈ relevantSubcubes x R, IsGoodSubcube ω q.1 q.2 := by
    intro q hq
    by_contra hq'
    exact h (Set.mem_union_right _ (Set.mem_iUnion.2 ⟨q, Set.mem_iUnion.2 ⟨hq, hq'⟩⟩))
  apply hbad
  refine ⟨?_, ?_, ?_⟩
  · convert hpower using 1; norm_num
  · obtain ⟨V, hV, hcross, _⟩ := hmain
    exact ⟨V, hV, hcross⟩
  · intro z M hlow hM hmeet
    have hlow' : (R : ℝ) ^ (1 / 400 : ℝ) / 2 ≤ M := by
      convert hlow using 1; norm_num
    have hMR : M ≤ R := by
      have : (M : ℝ) ≤ R := by linarith
      exact_mod_cast this
    have hz : z ∈ Rigidity.Proofs.S3.cubeFinset x (2 * R) :=
      Rigidity.Proofs.S3.mem_cubeFinset.mpr (centre_mem_doubled_cube hMR hmeet)
    have hq : (z, M) ∈ relevantSubcubes x R := by
      simp only [relevantSubcubes, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      exact ⟨⟨hz, by omega⟩, hlow'⟩
    exact hall (z, M) hq

end Rigidity.Percolation
