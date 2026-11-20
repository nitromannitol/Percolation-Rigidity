import Rigidity.Proofs.Percolation.PlanarCubeEnergy
import Rigidity.Percolation.IntegerCubeCoalescenceScales

/-!
# Elementary bounds on the planar energy quantities

`μ(U, q) ≤ 0 ≤ ν(U, p)`, both being compared with the zero function, and
`ν(U, p) ≤ (9 / 4) (|p₁| + |p₂|) ^ 2` by Young's inequality on each open edge (Armstrong and
Dario, Lemma 4.3, bound for `ν`).
-/

open LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped Classical

namespace Rigidity.Percolation

variable {ω : Configuration 2}

/-- `μ(U, q)` is at most the energy of any competitor. -/
theorem planarMu_le (hP : PlanarPartitionEvent ω) {U : TriadicCube 2} (hU : PlanarResolved ω U)
    (q : Fin 2 → ℝ) {w : ClusterFun ω U} (hw : w ∈ clusterHarmonic ω U) :
    planarMu ω U q ≤ (clusterForm ω U w w / 2 - coarsePairing ω U q w) / U.volume := by
  obtain ⟨u, hu, hmin⟩ := exists_clusterHarmonic_minimizer U (coarsePairing ω U q)
    (fun v hv => coarsePairing_eq_zero_of_clusterForm hP hU q hv)
  have hvol := U.volume_pos
  set f : clusterHarmonic ω U → ℝ := fun w =>
    (clusterForm ω U w w / 2 - coarsePairing ω U q w) / U.volume with hf
  have hμ : planarMu ω U q = ⨅ w, f w := rfl
  have hle : ∀ w, f ⟨u, hu⟩ ≤ f w :=
    fun w => div_le_div_of_nonneg_right ((hmin w.1 w.2).2) hvol.le
  have hfw : f ⟨w, hw⟩ = (clusterForm ω U w w / 2 - coarsePairing ω U q w) / U.volume := rfl
  rw [hμ, ← hfw]
  exact ciInf_le ⟨f ⟨u, hu⟩, by rintro _ ⟨v, rfl⟩; exact hle v⟩ _

/-- `ν(U, p)` is at least the value of any competitor. -/
theorem le_planarNu {U : TriadicCube 2} (p : Fin 2 → ℝ) {w : ClusterFun ω U}
    (hw : w ∈ clusterHarmonic ω U) :
    (fluxPairing ω U p w - clusterForm ω U w w / 2) / U.volume ≤ planarNu ω U p := by
  obtain ⟨v, hv, hmin⟩ := exists_clusterHarmonic_minimizer U (fluxPairing ω U p)
    (fun w hw => fluxPairing_eq_zero_of_clusterForm p hw)
  have hvol := U.volume_pos
  set f : clusterHarmonic ω U → ℝ := fun w =>
    (fluxPairing ω U p w - clusterForm ω U w w / 2) / U.volume with hf
  have hν : planarNu ω U p = ⨆ w, f w := rfl
  have hle : ∀ w, f w ≤ f ⟨v, hv⟩ := by
    intro w
    refine div_le_div_of_nonneg_right ?_ hvol.le
    linarith [(hmin w.1 w.2).2]
  have hfw : f ⟨w, hw⟩ = (fluxPairing ω U p w - clusterForm ω U w w / 2) / U.volume := rfl
  rw [hν, ← hfw]
  exact le_ciSup ⟨f ⟨v, hv⟩, by rintro _ ⟨v', rfl⟩; exact hle v'⟩ _

theorem zero_mem_clusterHarmonic {U : TriadicCube 2} : (0 : ClusterFun ω U) ∈ clusterHarmonic ω U :=
  (clusterHarmonic ω U).zero_mem

theorem planarMu_nonpos (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) (q : Fin 2 → ℝ) : planarMu ω U q ≤ 0 := by
  have h := planarMu_le hP hU q zero_mem_clusterHarmonic
  simpa using h

theorem planarNu_nonneg {U : TriadicCube 2} (p : Fin 2 → ℝ) : 0 ≤ planarNu ω U p := by
  have h := le_planarNu p (zero_mem_clusterHarmonic (ω := ω) (U := U))
  simpa using h

/-- A vertex has at most nine open neighbours in any finite set. -/
theorem card_filter_adj_le (S : Finset (Vertex 2)) (x : Vertex 2) :
    (S.filter fun y => (openGraph ω).Adj x y).card ≤ 9 := by
  set Box : Finset (Vertex 2) := Fintype.piFinset fun i => Finset.Icc (x i - 1) (x i + 1)
  have hsub : S.filter (fun y => (openGraph ω).Adj x y) ⊆ Box := by
    intro y hy
    have hadj := (Finset.mem_filter.1 hy).2
    rw [Fintype.mem_piFinset]
    intro i
    have h := Rigidity.Proofs.S3.abs_coord_sub_le_one_of_adj (openGraph_le ω hadj) i
    rw [abs_le] at h
    rw [Finset.mem_Icc]
    constructor <;> omega
  have hcard : Box.card = 9 := by
    simp only [Box, Fintype.card_piFinset, Int.card_Icc, Fin.prod_univ_two]
    have : ∀ z : ℤ, (z + 1 + 1 - (z - 1)).toNat = 3 := by
      intro z
      omega
    rw [this, this]
    norm_num
  exact (Finset.card_le_card hsub).trans hcard.le

/-- The cluster has at most `|U|` vertices. -/
theorem card_clusterVertices_le (U : TriadicCube 2) :
    ((clusterVertices ω U).card : ℝ) ≤ U.volume := by
  have h1 : (clusterVertices ω U).card ≤ U.toIntegerCube.vertices.card :=
    Finset.card_filter_le _ _
  have h2 : U.toIntegerCube.vertices.card = 9 ^ U.scale := by
    rw [IntegerCube.card_vertices]
    change (3 ^ U.scale) ^ 2 = 9 ^ U.scale
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  unfold TriadicCube.volume
  rw [h2] at h1
  exact_mod_cast h1

/-- **Upper bound for `ν`** (Armstrong and Dario, Lemma 4.3). -/
theorem planarNu_le {U : TriadicCube 2} (p : Fin 2 → ℝ) :
    planarNu ω U p ≤ 9 / 4 * (|p 0| + |p 1|) ^ 2 := by
  obtain ⟨v, -, -, hν⟩ := exists_planarNu_maximizer (ω := ω) (U := U) p
  rw [hν]
  have hvol := U.volume_pos
  set P := (|p 0| + |p 1|) with hP
  have hterm : ∀ x y : ↥(clusterVertices ω U), (openGraph ω).Adj x.1 y.1 →
      |∑ i, p i * ((y.1 i : ℝ) - x.1 i)| ≤ P := by
    intro x y hxy
    have h0 := Rigidity.Proofs.S3.abs_coord_sub_le_one_of_adj (openGraph_le ω hxy) 0
    have h1 := Rigidity.Proofs.S3.abs_coord_sub_le_one_of_adj (openGraph_le ω hxy) 1
    have h0' : |((y.1 0 : ℝ) - x.1 0)| ≤ 1 := by exact_mod_cast h0
    have h1' : |((y.1 1 : ℝ) - x.1 1)| ≤ 1 := by exact_mod_cast h1
    rw [Fin.sum_univ_two]
    calc |p 0 * ((y.1 0 : ℝ) - x.1 0) + p 1 * ((y.1 1 : ℝ) - x.1 1)|
        ≤ |p 0| * |((y.1 0 : ℝ) - x.1 0)| + |p 1| * |((y.1 1 : ℝ) - x.1 1)| := by
          rw [← abs_mul, ← abs_mul]
          exact abs_add_le _ _
      _ ≤ |p 0| * 1 + |p 1| * 1 := by gcongr
      _ = P := by ring
  have hpoint : ∀ x y : ↥(clusterVertices ω U),
      (if (openGraph ω).Adj x.1 y.1 then (∑ i, p i * ((y.1 i : ℝ) - x.1 i)) * (v y - v x)
        else 0) - clusterFormTerm ω v v x y / 2 ≤
      if (openGraph ω).Adj x.1 y.1 then P ^ 2 / 2 else 0 := by
    intro x y
    simp only [clusterFormTerm]
    split_ifs with hxy
    · have ha := hterm x y hxy
      have hsq : (∑ i, p i * ((y.1 i : ℝ) - x.1 i)) ^ 2 ≤ P ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) ha 2
      nlinarith [sq_nonneg ((∑ i, p i * ((y.1 i : ℝ) - x.1 i)) - (v y - v x))]
    · simp
  have hcount : ∑ x : ↥(clusterVertices ω U), ∑ y : ↥(clusterVertices ω U),
      (if (openGraph ω).Adj x.1 y.1 then P ^ 2 / 2 else 0) ≤
      9 * U.volume * (P ^ 2 / 2) := by
    have hrow : ∀ x : ↥(clusterVertices ω U), ∑ y : ↥(clusterVertices ω U),
        (if (openGraph ω).Adj x.1 y.1 then P ^ 2 / 2 else 0) ≤ 9 * (P ^ 2 / 2) := by
      intro x
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      gcongr
      have h := card_filter_adj_le (ω := ω) (clusterVertices ω U) x.1
      have hle : (Finset.univ.filter fun y : ↥(clusterVertices ω U) =>
          (openGraph ω).Adj x.1 y.1).card ≤
          ((clusterVertices ω U).filter fun y => (openGraph ω).Adj x.1 y).card := by
        rw [← Finset.card_map (Function.Embedding.subtype _)]
        apply Finset.card_le_card
        intro z hz
        simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
          Function.Embedding.subtype_apply] at hz
        obtain ⟨y, hy, rfl⟩ := hz
        exact Finset.mem_filter.2 ⟨y.2, hy⟩
      exact_mod_cast hle.trans h
    calc ∑ x : ↥(clusterVertices ω U), ∑ y : ↥(clusterVertices ω U),
          (if (openGraph ω).Adj x.1 y.1 then P ^ 2 / 2 else 0)
        ≤ ∑ _x : ↥(clusterVertices ω U), 9 * (P ^ 2 / 2) := Finset.sum_le_sum fun x _ => hrow x
      _ = ((clusterVertices ω U).card : ℝ) * (9 * (P ^ 2 / 2)) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_coe]
      _ ≤ U.volume * (9 * (P ^ 2 / 2)) := by
          gcongr
          exact card_clusterVertices_le U
      _ = 9 * U.volume * (P ^ 2 / 2) := by ring
  rw [div_le_iff₀ hvol, fluxPairing_apply, clusterForm_apply]
  have hsplit : (1 / 2 : ℝ) * (∑ x : ↥(clusterVertices ω U), ∑ y : ↥(clusterVertices ω U),
      if (openGraph ω).Adj x.1 y.1 then (∑ i, p i * ((y.1 i : ℝ) - x.1 i)) * (v y - v x)
        else 0) - (1 / 2 : ℝ) * (∑ x, ∑ y, clusterFormTerm ω v v x y) / 2 =
      (1 / 2 : ℝ) * ∑ x : ↥(clusterVertices ω U), ∑ y : ↥(clusterVertices ω U),
        ((if (openGraph ω).Adj x.1 y.1 then (∑ i, p i * ((y.1 i : ℝ) - x.1 i)) * (v y - v x)
          else 0) - clusterFormTerm ω v v x y / 2) := by
    rw [mul_div_assoc, ← mul_sub]
    congr 1
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]
  rw [hsplit]
  calc (1 / 2 : ℝ) * ∑ x : ↥(clusterVertices ω U), ∑ y : ↥(clusterVertices ω U),
        ((if (openGraph ω).Adj x.1 y.1 then (∑ i, p i * ((y.1 i : ℝ) - x.1 i)) * (v y - v x)
          else 0) - clusterFormTerm ω v v x y / 2)
      ≤ (1 / 2 : ℝ) * ∑ x : ↥(clusterVertices ω U), ∑ y : ↥(clusterVertices ω U),
          (if (openGraph ω).Adj x.1 y.1 then P ^ 2 / 2 else 0) := by
        gcongr with x _ y _
        exact hpoint x y
    _ ≤ (1 / 2 : ℝ) * (9 * U.volume * (P ^ 2 / 2)) := by gcongr
    _ = 9 / 4 * P ^ 2 * U.volume := by ring

end Rigidity.Percolation
