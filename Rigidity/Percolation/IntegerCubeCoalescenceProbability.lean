import Rigidity.Percolation.IntegerCubeCoalescence
import Rigidity.Percolation.CrossingPathCoalescence

/-!
# A union bound for subcube coalescence

Uniform bounds for crossing and coalescence failures on small cubes give a
finite union bound for coalescence in a larger cube.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation Rigidity.External MeasureTheory
open scoped ENNReal

/-- Subcube crossing and coalescence failure probabilities control the
failure probability for long-path coalescence in the ambient cube. -/
theorem IntegerCube.measure_not_coalesces_le {d : ℕ}
    (hd : 0 < d) (Q : IntegerCube d) (s k : ℕ) (R : ℤ)
    (hR : 0 < R) (hsR : 2 * R + 1 ≤ (s : ℤ))
    (hks : k + 1 ≤ s) (hRk : R ≤ (k : ℤ) - 1) (hsQ : s ≤ Q.size)
    (large : (n : ℕ) → (Fin (n + 1) → Vertex d) → Prop)
    (hdiam : ∀ n γ, large n γ → pathDiameterAtLeast R n γ)
    (μ : Measure (Configuration d)) (a b : ℝ≥0∞)
    (hcoal : ∀ T : IntegerCube d, T.size = s →
      (↑T.vertices : Set (Vertex d)) ⊆ Q.vertices →
      μ {ω | ¬ LargePathsCoalesce ω (↑T.vertices) (pathDiameterAtLeast R)} ≤ a)
    (hcross : ∀ T : IntegerCube d, T.size = k →
      (↑T.vertices : Set (Vertex d)) ⊆ Q.vertices →
      μ {ω | ¬ HasCrossingComponent ω (↑T.vertices)
        (fun i => ↑(T.lowerFace i)) (fun i => ↑(T.upperFace i))} ≤ b) :
    μ {ω | ¬ LargePathsCoalesce ω (↑Q.vertices) large} ≤
      (Q.vertices.card : ℝ≥0∞) * (a + b) := by
  classical
  let cs := Q.vertices.filter fun x =>
    (↑(IntegerCube.atCorner x s).vertices : Set (Vertex d)) ⊆ Q.vertices
  let ck := Q.vertices.filter fun x =>
    (↑(IntegerCube.atCorner x k).vertices : Set (Vertex d)) ⊆ Q.vertices
  let A : Vertex d → Set (Configuration d) := fun x =>
    {ω | ¬ LargePathsCoalesce ω (↑(IntegerCube.atCorner x s).vertices)
      (pathDiameterAtLeast R)}
  let B : Vertex d → Set (Configuration d) := fun x =>
    {ω | ¬ HasCrossingComponent ω (↑(IntegerCube.atCorner x k).vertices)
      (fun i => ↑((IntegerCube.atCorner x k).lowerFace i))
      (fun i => ↑((IntegerCube.atCorner x k).upperFace i))}
  have hspos : 0 < s := by
    have : (0 : ℤ) < s := by omega
    exact_mod_cast this
  have hkpos : 0 < k := by
    have : (0 : ℤ) < k := by omega
    exact_mod_cast this
  have hcorner (T : IntegerCube d) (hpos : 0 < T.size)
      (hT : (↑T.vertices : Set (Vertex d)) ⊆ Q.vertices) : T.corner ∈ Q.vertices := by
    apply hT
    change T.corner ∈ T.vertices
    rw [IntegerCube.mem_vertices]
    intro i
    constructor
    · exact le_rfl
    · have hp : (0 : ℤ) < T.size := by exact_mod_cast hpos
      exact lt_add_of_pos_right _ hp
  have hsubset : {ω | ¬ LargePathsCoalesce ω (↑Q.vertices) large} ⊆
      (⋃ x ∈ cs, A x) ∪ ⋃ x ∈ ck, B x := by
    intro ω hω
    by_contra hbad
    have hgoodS : ∀ T : IntegerCube d, T.size = s →
        (↑T.vertices : Set (Vertex d)) ⊆ Q.vertices →
        LargePathsCoalesce ω (↑T.vertices) (pathDiameterAtLeast R) := by
      intro T hTs hT
      have ht : IntegerCube.atCorner T.corner s = T := by cases T; simp_all only [atCorner]
      have hc : T.corner ∈ cs := by
        apply Finset.mem_filter.mpr
        refine ⟨hcorner T (by rw [hTs]; exact hspos) hT, ?_⟩
        rw [ht]
        exact hT
      have hn : ω ∉ A T.corner := by
        intro hh
        exact hbad (Or.inl (Set.mem_iUnion₂.mpr ⟨T.corner, hc, hh⟩))
      change ¬ ¬ LargePathsCoalesce ω (↑(IntegerCube.atCorner T.corner s).vertices)
        (pathDiameterAtLeast R) at hn
      rw [ht] at hn
      exact Classical.not_not.mp hn
    have hgoodK : ∀ T : IntegerCube d, T.size = k →
        (↑T.vertices : Set (Vertex d)) ⊆ Q.vertices →
        HasCrossingComponent ω (↑T.vertices)
          (fun i => ↑(T.lowerFace i)) (fun i => ↑(T.upperFace i)) := by
      intro T hTk hT
      have ht : IntegerCube.atCorner T.corner k = T := by cases T; simp_all only [atCorner]
      have hc : T.corner ∈ ck := by
        apply Finset.mem_filter.mpr
        refine ⟨hcorner T (by rw [hTk]; exact hkpos) hT, ?_⟩
        rw [ht]
        exact hT
      have hn : ω ∉ B T.corner := by
        intro hh
        exact hbad (Or.inr (Set.mem_iUnion₂.mpr ⟨T.corner, hc, hh⟩))
      change ¬ ¬ HasCrossingComponent ω (↑(IntegerCube.atCorner T.corner k).vertices)
        (fun i => ↑((IntegerCube.atCorner T.corner k).lowerFace i))
        (fun i => ↑((IntegerCube.atCorner T.corner k).upperFace i)) at hn
      rw [ht] at hn
      exact Classical.not_not.mp hn
    exact hω (Q.largePathsCoalesce_of_subcube_estimates hd s k R hR hsR hks hRk hsQ
      large hdiam hgoodS hgoodK)
  calc
    μ {ω | ¬ LargePathsCoalesce ω (↑Q.vertices) large} ≤
        μ ((⋃ x ∈ cs, A x) ∪ ⋃ x ∈ ck, B x) := measure_mono hsubset
    _ ≤ μ (⋃ x ∈ cs, A x) + μ (⋃ x ∈ ck, B x) := measure_union_le _ _
    _ ≤ (∑ x ∈ cs, μ (A x)) + ∑ x ∈ ck, μ (B x) :=
      add_le_add (measure_biUnion_finset_le cs A) (measure_biUnion_finset_le ck B)
    _ ≤ (cs.card : ℝ≥0∞) * a + (ck.card : ℝ≥0∞) * b := by
      apply add_le_add
      · calc
          _ ≤ ∑ _x ∈ cs, a := Finset.sum_le_sum fun x hx =>
            hcoal (IntegerCube.atCorner x s) rfl (Finset.mem_filter.mp hx).2
          _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
      · calc
          _ ≤ ∑ _x ∈ ck, b := Finset.sum_le_sum fun x hx =>
            hcross (IntegerCube.atCorner x k) rfl (Finset.mem_filter.mp hx).2
          _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
      have hcs : (cs.card : ℝ≥0∞) ≤ Q.vertices.card := by
        exact_mod_cast Finset.card_filter_le _ _
      have hck : (ck.card : ℝ≥0∞) ≤ Q.vertices.card := by
        exact_mod_cast Finset.card_filter_le _ _
      calc
        _ ≤ (Q.vertices.card : ℝ≥0∞) * a + (Q.vertices.card : ℝ≥0∞) * b :=
          add_le_add (mul_le_mul_left hcs a) (mul_le_mul_left hck b)
        _ = _ := by rw [mul_add]


/-- Bounds for crossing components that connect all selected paths yield the
ambient coalescence bound at both subcube scales. -/
theorem IntegerCube.measure_not_coalesces_le_of_crossing_paths {d : ℕ}
    (hd : 0 < d) (Q : IntegerCube d) (s k : ℕ) (R : ℤ)
    (hR : 0 < R) (hsR : 2 * R + 1 ≤ (s : ℤ))
    (hks : k + 1 ≤ s) (hRk : R ≤ (k : ℤ) - 1) (hsQ : s ≤ Q.size)
    (large : (n : ℕ) → (Fin (n + 1) → Vertex d) → Prop)
    (hdiam : ∀ n γ, large n γ → pathDiameterAtLeast R n γ)
    (μ : Measure (Configuration d)) (a b : ℝ≥0∞)
    (ha : ∀ T : IntegerCube d, T.size = s →
      (↑T.vertices : Set (Vertex d)) ⊆ Q.vertices →
      μ {ω | ¬ HasCrossingComponentConnectingPaths ω (↑T.vertices)
        (fun i => ↑(T.lowerFace i)) (fun i => ↑(T.upperFace i))
        (pathDiameterAtLeast R)} ≤ a)
    (hb : ∀ T : IntegerCube d, T.size = k →
      (↑T.vertices : Set (Vertex d)) ⊆ Q.vertices →
      μ {ω | ¬ HasCrossingComponentConnectingPaths ω (↑T.vertices)
        (fun i => ↑(T.lowerFace i)) (fun i => ↑(T.upperFace i))
        (pathDiameterAtLeast R)} ≤ b) :
    μ {ω | ¬ LargePathsCoalesce ω (↑Q.vertices) large} ≤
      (Q.vertices.card : ℝ≥0∞) * (a + b) := by
  apply Q.measure_not_coalesces_le hd s k R hR hsR hks hRk hsQ large hdiam μ a b
  · intro T hTs hT
    calc
      _ ≤ μ {ω | ¬ HasCrossingComponentConnectingPaths ω (↑T.vertices)
          (fun i => ↑(T.lowerFace i)) (fun i => ↑(T.upperFace i))
          (pathDiameterAtLeast R)} := by
        apply measure_mono
        intro ω hω hgood
        exact hω hgood.crossing_and_coalescence.2
      _ ≤ a := ha T hTs hT
  · intro T hTk hT
    calc
      _ ≤ μ {ω | ¬ HasCrossingComponentConnectingPaths ω (↑T.vertices)
          (fun i => ↑(T.lowerFace i)) (fun i => ↑(T.upperFace i))
          (pathDiameterAtLeast R)} := by
        apply measure_mono
        intro ω hω hgood
        exact hω hgood.crossing_and_coalescence.1
      _ ≤ b := hb T hTk hT

end Rigidity.Percolation
