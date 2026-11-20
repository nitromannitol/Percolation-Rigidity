import Rigidity.Proofs.Percolation.PlanarMuSubadditiveError
import Rigidity.Proofs.Percolation.PlanarMuLowerMoments

/-!
# Exceptional edges of the subcube decomposition

The lattice edges of `U` leaving their subcube of scale `n` number at most `2 |U| / 3 ^ n`, and a
subcube of scale `n` is unresolved only if one of its vertices has a partition cube of side at
least `3 ^ (n + 1)`. Consequently the expected sum of sixth powers of partition sides over the
exceptional edges is at most `C |U| / 3 ^ n`, and over all edges at most `C |U|`.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped ENNReal Classical

namespace Rigidity.Percolation

variable {ω : Configuration 2}

/-- On the partition event, powers of partition sides are bounded by reach sums. -/
theorem ofReal_partSide_pow_le (hP : PlanarPartitionEvent ω) (x : Vertex 2) (m : ℕ) :
    ENNReal.ofReal (partSide ω x ^ (m + 1)) ≤ reachSum ω (m + 1) x := by
  have h0 : 0 ≤ partSide ω x := le_trans zero_le_one (one_le_partSide x)
  rw [ENNReal.ofReal_pow h0]
  exact (pow_le_pow_left₀ zero_le (ofReal_partSide_le hP x) _).trans (planarReach_pow_le ω x m)

/-- The lattice edges of `U` leaving their subcube of scale `n`. -/
noncomputable def subcubeCrossingEdges (U : TriadicCube 2) (n : ℕ) :
    Finset (Vertex 2 × Fin 2) :=
  (latticeEdgesIn U).filter fun k =>
    k.1 + unitVertex k.2 ∉ (scaleCube n k.1).toIntegerCube.vertices

theorem card_toIntegerCube_vertices_eq (V : TriadicCube 2) :
    ((V.toIntegerCube.vertices.card : ℕ) : ℝ) = (9 : ℝ) ^ V.scale := by
  rw [← volume_eq_card]
  rfl

/-- The number of subcubes of scale `n` times `9 ^ n` is the number of vertices of `U`. -/
theorem card_subcubesAt_mul {U : TriadicCube 2} {n : ℕ} (hn : n ≤ U.scale) :
    ((subcubesAt U n).card : ℝ) * (9 : ℝ) ^ n = U.volume := by
  have h := sum_scaleCube_eq hn (fun _ _ => (1 : ℝ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  rw [volume_eq_card, h, Finset.sum_congr rfl fun V hV => by
    rw [card_toIntegerCube_vertices_eq V, scale_of_mem_subcubesAt hV]]
  rw [Finset.sum_const, nsmul_eq_mul]

/-- **Crossing edges are few.** -/
theorem card_subcubeCrossingEdges_le {U : TriadicCube 2} {n : ℕ} (hn : n ≤ U.scale) :
    ((subcubeCrossingEdges U n).card : ℝ) * 3 ^ n ≤ 2 * U.volume := by
  have hface : ∀ V ∈ subcubesAt U n, ∀ i : Fin 2,
      ∑ x ∈ V.toIntegerCube.vertices,
        (if x + unitVertex i ∉ V.toIntegerCube.vertices then (1 : ℝ) else 0) ≤ (3 : ℝ) ^ n := by
    intro V hV i
    rw [Finset.sum_boole]
    have hsub : V.toIntegerCube.vertices.filter
        (fun x => x + unitVertex i ∉ V.toIntegerCube.vertices) ⊆
        V.toIntegerCube.upperFace i := by
      intro x hx
      obtain ⟨hxV, hxe⟩ := Finset.mem_filter.1 hx
      refine Finset.mem_filter.2 ⟨hxV, ?_⟩
      have h1 := ((IntegerCube.mem_vertices _ _).1 hxV i).2
      by_contra hne
      exact hxe (Finset.mem_filter.1 ((IntegerCube.mem_edgeStarts (R := V.toIntegerCube)
        (i := i)).2 ⟨hxV, by omega⟩)).2
    have hc := card_face_le V i true
    simp only [if_true] at hc
    have : ((V.toIntegerCube.vertices.filter
        (fun x => x + unitVertex i ∉ V.toIntegerCube.vertices)).card : ℝ) ≤
        (V.toIntegerCube.size : ℝ) := by
      exact_mod_cast (Finset.card_le_card hsub).trans hc
    calc _ ≤ (V.toIntegerCube.size : ℝ) := this
      _ = (3 : ℝ) ^ n := by
          change ((3 ^ V.scale : ℕ) : ℝ) = _
          rw [scale_of_mem_subcubesAt hV]
          push_cast
          rfl
  have hcount : ((subcubeCrossingEdges U n).card : ℝ) ≤
      ∑ i : Fin 2, ∑ V ∈ subcubesAt U n, ∑ x ∈ V.toIntegerCube.vertices,
        (if x + unitVertex i ∉ V.toIntegerCube.vertices then (1 : ℝ) else 0) := by
    rw [subcubeCrossingEdges, ← Finset.sum_boole]
    calc ∑ k ∈ latticeEdgesIn U,
          (if k.1 + unitVertex k.2 ∉ (scaleCube n k.1).toIntegerCube.vertices then (1 : ℝ)
            else 0)
        ≤ ∑ k ∈ U.toIntegerCube.vertices ×ˢ (Finset.univ : Finset (Fin 2)),
          (if k.1 + unitVertex k.2 ∉ (scaleCube n k.1).toIntegerCube.vertices then (1 : ℝ)
            else 0) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun _ _ _ => by split_ifs <;> norm_num
      _ = ∑ i : Fin 2, ∑ x ∈ U.toIntegerCube.vertices,
          (if x + unitVertex i ∉ (scaleCube n x).toIntegerCube.vertices then (1 : ℝ) else 0) := by
          rw [Finset.sum_product, Finset.sum_comm]
      _ = _ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          exact sum_scaleCube_eq hn (fun V x =>
            if x + unitVertex i ∉ V.toIntegerCube.vertices then (1 : ℝ) else 0)
  have hS := card_subcubesAt_mul (U := U) hn
  have h9 : (9 : ℝ) ^ n = 3 ^ n * 3 ^ n := by rw [← mul_pow]; norm_num
  calc ((subcubeCrossingEdges U n).card : ℝ) * 3 ^ n
      ≤ (∑ i : Fin 2, ∑ V ∈ subcubesAt U n, ∑ x ∈ V.toIntegerCube.vertices,
          (if x + unitVertex i ∉ V.toIntegerCube.vertices then (1 : ℝ) else 0)) * 3 ^ n := by
        gcongr
    _ ≤ (∑ _i : Fin 2, ∑ _V ∈ subcubesAt U n, (3 : ℝ) ^ n) * 3 ^ n := by
        gcongr with i _ V hV
        exact hface V hV i
    _ = 2 * U.volume := by
        rw [← hS, h9]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- An unresolved subcube contains a vertex with a large partition cube. -/
theorem indicator_unresolved_le {n : ℕ} (x : Vertex 2) :
    (if PlanarResolved ω (scaleCube n x) then (0 : ℝ) else 1) ≤
      ∑ z ∈ (scaleCube n x).toIntegerCube.vertices,
        (partSide ω z / 3 ^ (n + 1)) ^ 6 := by
  have hnn : ∀ z, 0 ≤ (partSide ω z / 3 ^ (n + 1)) ^ 6 := fun z => by
    have := one_le_partSide (ω := ω) z
    positivity
  split_ifs with hres
  · exact Finset.sum_nonneg fun z _ => hnn z
  · unfold PlanarResolved at hres
    push Not at hres
    obtain ⟨z, hz, hlt⟩ := hres
    have hzV : z ∈ (scaleCube n x).toIntegerCube.vertices :=
      ((scaleCube n x).mem_toIntegerCube_vertices z).2 hz
    have h1 : 1 ≤ (partSide ω z / 3 ^ (n + 1)) ^ 6 := by
      rw [scale_scaleCube] at hlt
      have hside : (3 : ℝ) ^ (n + 1) ≤ partSide ω z := by
        unfold partSide
        exact pow_le_pow_right₀ (by norm_num) hlt
      have : 1 ≤ partSide ω z / 3 ^ (n + 1) := by
        rw [le_div_iff₀ (by positivity)]
        linarith
      exact one_le_pow₀ this
    exact h1.trans (Finset.single_le_sum (fun z _ => hnn z) hzV)

end Rigidity.Percolation
