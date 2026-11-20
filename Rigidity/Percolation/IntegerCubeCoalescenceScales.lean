import Rigidity.Percolation.IntegerCubeCoalescenceProbability
import Rigidity.Percolation.IntegerCubeScaleChoice

/-!
# Scaled coalescence bounds

Compatible subcube scales turn uniform crossing-component estimates into a
bound on long-path coalescence in a large cube.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation Rigidity.External MeasureTheory
open scoped ENNReal

/-- A lattice cube has its side length to the dimension many vertices. -/
theorem IntegerCube.card_vertices {d : ℕ} (Q : IntegerCube d) :
    Q.vertices.card = Q.size ^ d := by
  classical
  simp only [IntegerCube.vertices, Fintype.card_piFinset, Int.card_Ico]
  have hcard : ∀ i : Fin d, (Q.corner i + (Q.size : ℤ) - Q.corner i).toNat = Q.size := by
    intro i
    simp only [add_sub_cancel_left, Int.toNat_natCast]
  simp only [hcard, Finset.prod_const, Finset.card_fin]

/-- Crossing-component bounds at two compatible scales control the probability
that paths of one-tenth the ambient side fail to coalesce. -/
theorem IntegerCube.measure_not_coalesces_le_at_compatible_scales {d : ℕ}
    (hd : 0 < d) (Q : IntegerCube d) (hS : 61 ≤ Q.size)
    (large : (n : ℕ) → (Fin (n + 1) → Vertex d) → Prop)
    (hdiam : ∀ n γ, large n γ → pathDiameterAtLeast (Q.size / 10 : ℕ) n γ)
    (μ : Measure (Configuration d)) (a b : ℕ → ℝ≥0∞)
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
    ∃ t : ℕ, 3 ≤ t ∧ Q.size ≤ 20 * t + 20 ∧
      μ {ω | ¬ LargePathsCoalesce ω (↑Q.vertices) large} ≤
        (Q.size ^ d : ℕ) * (a t + b t) := by
  obtain ⟨t, ht, _, _, hsR, hks, hRk, hsQ, hRS, hSt⟩ :=
    exists_compatible_subcube_scales Q.size hS
  refine ⟨t, ht, hSt, ?_⟩
  have hR : (0 : ℤ) < 2 * (t : ℤ) := by omega
  have hsR' : 2 * (2 * (t : ℤ)) + 1 ≤ ((20 * t + 1 : ℕ) : ℤ) := by
    exact_mod_cast hsR
  have hRk' : 2 * (t : ℤ) ≤ ((10 * t + 1 : ℕ) : ℤ) - 1 := by
    have h : 2 * t + 1 ≤ 10 * t + 1 := hRk
    omega
  have hdiam' : ∀ n γ, large n γ → pathDiameterAtLeast (2 * (t : ℤ)) n γ := by
    intro n γ hγ
    obtain ⟨i, j, k, hk⟩ := hdiam n γ hγ
    have hbound : 2 * t ≤ Q.size / 10 := by omega
    have hbound' : (2 * (t : ℤ)) ≤ (Q.size / 10 : ℕ) := by exact_mod_cast hbound
    exact ⟨i, j, k, hbound'.trans hk⟩
  have h := Q.measure_not_coalesces_le_of_crossing_paths hd (20 * t + 1)
    (10 * t + 1) (2 * (t : ℤ)) hR hsR' hks hRk' hsQ large hdiam' μ (a t) (b t)
    (ha t ht) (hb t ht)
  simpa only [Q.card_vertices] using h

end Rigidity.Percolation
