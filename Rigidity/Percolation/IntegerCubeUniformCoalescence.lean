import Rigidity.Percolation.IntegerCubeCoalescenceScales

/-!
# Uniform coalescence at an ambient scale

A common pair of subcube sizes controls path coalescence in every cube whose
side is at least one tenth of a prescribed ambient side.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation Rigidity.External MeasureTheory
open scoped ENNReal

/-- A common pair of subcube sizes fits every test cube of side at least one
 tenth of the ambient side and detects paths at the overlap scale. -/
theorem exists_uniform_overlap_scales (S : ℕ) (hS : 620 ≤ S) :
    ∃ t : ℕ, 3 ≤ t ∧ 20 * t + 1 ≤ S / 10 ∧
      2 * t ≤ S / 20 - 1 ∧ S ≤ 200 * t + 219 := by
  refine ⟨(S - 20) / 200, ?_⟩
  have hdiv := Nat.div_add_mod (S - 20) 200
  have hmod := Nat.mod_lt (S - 20) (by omega : 0 < 200)
  have hdiv10 := Nat.div_add_mod S 10
  have hmod10 := Nat.mod_lt S (by omega : 0 < 10)
  have hdiv20 := Nat.div_add_mod S 20
  have hmod20 := Nat.mod_lt S (by omega : 0 < 20)
  omega

/-- Uniform crossing-component estimates at the two common subcube sizes
control coalescence at the ambient overlap threshold. -/
theorem IntegerCube.measure_not_coalesces_le_at_uniform_overlap_scale {d : ℕ}
    (hd : 0 < d) (S : ℕ) (hS : 620 ≤ S) (Q : IntegerCube d)
    (hQ : S ≤ 10 * Q.size) (μ : Measure (Configuration d)) (a b : ℕ → ℝ≥0∞)
    (ha : ∀ t : ℕ, 3 ≤ t → ∀ T : IntegerCube d, T.size = 20 * t + 1 →
      (↑T.vertices : Set (Vertex d)) ⊆ Q.vertices →
      μ {ω | ¬ HasCrossingComponentConnectingPaths ω (↑T.vertices)
        (fun i => ↑(T.lowerFace i)) (fun i => ↑(T.upperFace i))
        (pathDiameterAtLeast (2 * (t : ℤ)))} ≤ a t)
    (hb : ∀ t : ℕ, 3 ≤ t → ∀ T : IntegerCube d, T.size = 10 * t + 1 →
      (↑T.vertices : Set (Vertex d)) ⊆ Q.vertices →
      μ {ω | ¬ HasCrossingComponentConnectingPaths ω (↑T.vertices)
        (fun i => ↑(T.lowerFace i)) (fun i => ↑(T.upperFace i))
        (pathDiameterAtLeast (2 * (t : ℤ)))} ≤ b t) :
    ∃ t : ℕ, 3 ≤ t ∧ S ≤ 200 * t + 219 ∧
      μ {ω | ¬ LargePathsCoalesce ω (↑Q.vertices)
        (pathDiameterAtLeast (((S / 20 : ℕ) : ℤ) - 1))} ≤
        (Q.size ^ d : ℕ) * (a t + b t) := by
  obtain ⟨t, ht, hfit, hthreshold, hSt⟩ := exists_uniform_overlap_scales S hS
  refine ⟨t, ht, hSt, ?_⟩
  have hR : (0 : ℤ) < 2 * (t : ℤ) := by omega
  have hsR : 2 * (2 * (t : ℤ)) + 1 ≤ ((20 * t + 1 : ℕ) : ℤ) := by omega
  have hks : 10 * t + 1 + 1 ≤ 20 * t + 1 := by omega
  have hRk : 2 * (t : ℤ) ≤ ((10 * t + 1 : ℕ) : ℤ) - 1 := by omega
  have hsQ : 20 * t + 1 ≤ Q.size := by omega
  have hthreshold' : 2 * (t : ℤ) ≤ ((S / 20 : ℕ) : ℤ) - 1 := by omega
  have hdiam : ∀ (n : ℕ) (γ : Fin (n + 1) → Vertex d), pathDiameterAtLeast (((S / 20 : ℕ) : ℤ) - 1) n γ →
      pathDiameterAtLeast (2 * (t : ℤ)) n γ := by
    intro n γ hγ
    obtain ⟨i, j, k, hk⟩ := hγ
    exact ⟨i, j, k, hthreshold'.trans hk⟩
  have h := Q.measure_not_coalesces_le_of_crossing_paths hd (20 * t + 1)
    (10 * t + 1) (2 * (t : ℤ)) hR hsR hks hRk hsQ _ hdiam μ (a t) (b t)
    (ha t ht) (hb t ht)
  simpa only [Q.card_vertices] using h

end Rigidity.Percolation
