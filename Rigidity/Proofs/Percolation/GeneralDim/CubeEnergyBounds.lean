import Rigidity.Proofs.Percolation.GeneralDim.CubeEnergy

/-!
# Elementary bounds on the energy quantities of a triadic cube of `ℤ^d`

`μ(U, q) ≤ 0 ≤ ν(U, p)`, both being compared with the zero function, and
`ν(U, p) ≤ (3^d / 4) (∑_i |p_i|) ^ 2` by Young's inequality on each open edge, a vertex having at
most `3^d` open neighbours (Armstrong and Dario, Lemma 4.4, bound (4.13) for `ν`).
-/

open LatticeProb.Percolation Rigidity.External
open scoped Classical

namespace Rigidity.Percolation

variable {d : ℕ} {ω : Configuration d}

/-- `μ(U, q)` is at most the value of any competitor. -/
theorem cubeMu_le (hd : 0 < d) (hP : PartitionEvent ω) {U : TriadicCube d}
    (hU : PartitionResolved ω U) (q : Fin d → ℝ) {w : CubeFun ω U} (hw : w ∈ cubeHarmonic ω U) :
    cubeMu ω U q ≤ (cubeForm ω U w w / 2 - cubeCoarsePairing ω U q w) / U.latticeVolume := by
  obtain ⟨u, hu, hmin⟩ := exists_cubeHarmonic_minimizer U (cubeCoarsePairing ω U q)
    (fun v hv => cubeCoarsePairing_eq_zero_of_cubeForm hd hP hU q hv)
  have hvol := U.latticeVolume_pos
  set f : cubeHarmonic ω U → ℝ := fun w =>
    (cubeForm ω U w w / 2 - cubeCoarsePairing ω U q w) / U.latticeVolume with hf
  have hμ : cubeMu ω U q = ⨅ w, f w := rfl
  have hle : ∀ w, f ⟨u, hu⟩ ≤ f w :=
    fun w => div_le_div_of_nonneg_right ((hmin w.1 w.2).2) hvol.le
  have hfw : f ⟨w, hw⟩ =
      (cubeForm ω U w w / 2 - cubeCoarsePairing ω U q w) / U.latticeVolume := rfl
  rw [hμ, ← hfw]
  exact ciInf_le ⟨f ⟨u, hu⟩, by rintro _ ⟨v, rfl⟩; exact hle v⟩ _

/-- `ν(U, p)` is at least the value of any competitor. -/
theorem le_cubeNu {U : TriadicCube d} (p : Fin d → ℝ) {w : CubeFun ω U}
    (hw : w ∈ cubeHarmonic ω U) :
    (cubeFluxPairing ω U p w - cubeForm ω U w w / 2) / U.latticeVolume ≤ cubeNu ω U p := by
  obtain ⟨v, hv, hmin⟩ := exists_cubeHarmonic_minimizer U (cubeFluxPairing ω U p)
    (fun w hw => cubeFluxPairing_eq_zero_of_cubeForm p hw)
  have hvol := U.latticeVolume_pos
  set f : cubeHarmonic ω U → ℝ := fun w =>
    (cubeFluxPairing ω U p w - cubeForm ω U w w / 2) / U.latticeVolume with hf
  have hν : cubeNu ω U p = ⨆ w, f w := rfl
  have hle : ∀ w, f w ≤ f ⟨v, hv⟩ := by
    intro w
    refine div_le_div_of_nonneg_right ?_ hvol.le
    linarith [(hmin w.1 w.2).2]
  have hfw : f ⟨w, hw⟩ =
      (cubeFluxPairing ω U p w - cubeForm ω U w w / 2) / U.latticeVolume := rfl
  rw [hν, ← hfw]
  exact le_ciSup ⟨f ⟨v, hv⟩, by rintro _ ⟨v', rfl⟩; exact hle v'⟩ _

theorem zero_mem_cubeHarmonic {U : TriadicCube d} : (0 : CubeFun ω U) ∈ cubeHarmonic ω U :=
  (cubeHarmonic ω U).zero_mem

theorem cubeMu_nonpos (hd : 0 < d) (hP : PartitionEvent ω) {U : TriadicCube d}
    (hU : PartitionResolved ω U) (q : Fin d → ℝ) : cubeMu ω U q ≤ 0 := by
  have h := cubeMu_le hd hP hU q zero_mem_cubeHarmonic
  simpa using h

theorem cubeNu_nonneg {U : TriadicCube d} (p : Fin d → ℝ) : 0 ≤ cubeNu ω U p := by
  have h := le_cubeNu p (zero_mem_cubeHarmonic (ω := ω) (U := U))
  simpa using h

/-- A vertex has at most `3^d` open neighbours in any finite set. -/
theorem card_filter_openGraph_adj_le (S : Finset (Vertex d)) (x : Vertex d) :
    (S.filter fun y => (openGraph ω).Adj x y).card ≤ 3 ^ d := by
  set Box : Finset (Vertex d) := Fintype.piFinset fun i => Finset.Icc (x i - 1) (x i + 1)
  have hsub : S.filter (fun y => (openGraph ω).Adj x y) ⊆ Box := by
    intro y hy
    have hadj := (Finset.mem_filter.1 hy).2
    rw [Fintype.mem_piFinset]
    intro i
    have h := abs_sub_le_one_of_adj_lattice (openGraph_le ω hadj) i
    rw [abs_le] at h
    rw [Finset.mem_Icc]
    constructor <;> omega
  have hcard : Box.card = 3 ^ d := by
    simp only [Box, Fintype.card_piFinset, Int.card_Icc]
    have : ∀ z : ℤ, (z + 1 + 1 - (z - 1)).toNat = 3 := by
      intro z
      omega
    simp only [this, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact (Finset.card_le_card hsub).trans hcard.le

/-- The cluster has at most `|U|` vertices. -/
theorem card_crossingClusterVertices_le (U : TriadicCube d) :
    ((crossingClusterVertices ω U).card : ℝ) ≤ U.latticeVolume := by
  rw [← U.card_toIntegerCube_vertices]
  exact_mod_cast Finset.card_filter_le _ _

/-- An increment of an affine function across an open edge is at most `∑_i |p_i|`. -/
theorem abs_sum_mul_sub_le_of_adj {p : Fin d → ℝ} {x y : Vertex d}
    (hxy : (openGraph ω).Adj x y) :
    |∑ i, p i * ((y i : ℝ) - x i)| ≤ ∑ i, |p i| := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  have h := abs_sub_le_one_of_adj_lattice (openGraph_le ω hxy) i
  have h' : |((y i : ℝ) - x i)| ≤ 1 := by
    rw [abs_sub_comm]
    exact_mod_cast h
  rw [abs_mul]
  calc |p i| * |((y i : ℝ) - x i)| ≤ |p i| * 1 := by gcongr
    _ = |p i| := mul_one _

/-- **Upper bound for `ν`** (Armstrong and Dario, Lemma 4.4, (4.13)). -/
theorem cubeNu_le {U : TriadicCube d} (p : Fin d → ℝ) :
    cubeNu ω U p ≤ 3 ^ d / 4 * (∑ i, |p i|) ^ 2 := by
  obtain ⟨v, -, -, hν⟩ := exists_cubeNu_maximizer (ω := ω) (U := U) p
  rw [hν]
  have hvol := U.latticeVolume_pos
  set P := ∑ i, |p i| with hP
  have hpoint : ∀ x y : ↥(crossingClusterVertices ω U),
      (if (openGraph ω).Adj x.1 y.1 then (∑ i, p i * ((y.1 i : ℝ) - x.1 i)) * (v y - v x)
        else 0) - cubeFormTerm ω v v x y / 2 ≤
      if (openGraph ω).Adj x.1 y.1 then P ^ 2 / 2 else 0 := by
    intro x y
    simp only [cubeFormTerm]
    split_ifs with hxy
    · have ha := abs_sum_mul_sub_le_of_adj (p := p) hxy
      have hsq : (∑ i, p i * ((y.1 i : ℝ) - x.1 i)) ^ 2 ≤ P ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) ha 2
      nlinarith [sq_nonneg ((∑ i, p i * ((y.1 i : ℝ) - x.1 i)) - (v y - v x))]
    · simp
  have hcount : ∑ x : ↥(crossingClusterVertices ω U), ∑ y : ↥(crossingClusterVertices ω U),
      (if (openGraph ω).Adj x.1 y.1 then P ^ 2 / 2 else 0) ≤
      3 ^ d * U.latticeVolume * (P ^ 2 / 2) := by
    have hrow : ∀ x : ↥(crossingClusterVertices ω U), ∑ y : ↥(crossingClusterVertices ω U),
        (if (openGraph ω).Adj x.1 y.1 then P ^ 2 / 2 else 0) ≤ 3 ^ d * (P ^ 2 / 2) := by
      intro x
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      gcongr
      have h := card_filter_openGraph_adj_le (ω := ω) (crossingClusterVertices ω U) x.1
      have hle : (Finset.univ.filter fun y : ↥(crossingClusterVertices ω U) =>
          (openGraph ω).Adj x.1 y.1).card ≤
          ((crossingClusterVertices ω U).filter fun y => (openGraph ω).Adj x.1 y).card := by
        rw [← Finset.card_map (Function.Embedding.subtype _)]
        apply Finset.card_le_card
        intro z hz
        simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
          Function.Embedding.subtype_apply] at hz
        obtain ⟨y, hy, rfl⟩ := hz
        exact Finset.mem_filter.2 ⟨y.2, hy⟩
      exact_mod_cast hle.trans h
    calc ∑ x : ↥(crossingClusterVertices ω U), ∑ y : ↥(crossingClusterVertices ω U),
          (if (openGraph ω).Adj x.1 y.1 then P ^ 2 / 2 else 0)
        ≤ ∑ _x : ↥(crossingClusterVertices ω U), 3 ^ d * (P ^ 2 / 2) :=
          Finset.sum_le_sum fun x _ => hrow x
      _ = ((crossingClusterVertices ω U).card : ℝ) * (3 ^ d * (P ^ 2 / 2)) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_coe]
      _ ≤ U.latticeVolume * (3 ^ d * (P ^ 2 / 2)) := by
          gcongr
          exact card_crossingClusterVertices_le U
      _ = 3 ^ d * U.latticeVolume * (P ^ 2 / 2) := by ring
  rw [div_le_iff₀ hvol, cubeFluxPairing_apply, cubeForm_apply]
  have hsplit : (1 / 2 : ℝ) * (∑ x : ↥(crossingClusterVertices ω U),
      ∑ y : ↥(crossingClusterVertices ω U),
      if (openGraph ω).Adj x.1 y.1 then (∑ i, p i * ((y.1 i : ℝ) - x.1 i)) * (v y - v x)
        else 0) - (1 / 2 : ℝ) * (∑ x, ∑ y, cubeFormTerm ω v v x y) / 2 =
      (1 / 2 : ℝ) * ∑ x : ↥(crossingClusterVertices ω U), ∑ y : ↥(crossingClusterVertices ω U),
        ((if (openGraph ω).Adj x.1 y.1 then (∑ i, p i * ((y.1 i : ℝ) - x.1 i)) * (v y - v x)
          else 0) - cubeFormTerm ω v v x y / 2) := by
    rw [mul_div_assoc, ← mul_sub]
    congr 1
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]
  rw [hsplit]
  calc (1 / 2 : ℝ) * ∑ x : ↥(crossingClusterVertices ω U), ∑ y : ↥(crossingClusterVertices ω U),
        ((if (openGraph ω).Adj x.1 y.1 then (∑ i, p i * ((y.1 i : ℝ) - x.1 i)) * (v y - v x)
          else 0) - cubeFormTerm ω v v x y / 2)
      ≤ (1 / 2 : ℝ) * ∑ x : ↥(crossingClusterVertices ω U), ∑ y : ↥(crossingClusterVertices ω U),
          (if (openGraph ω).Adj x.1 y.1 then P ^ 2 / 2 else 0) := by
        gcongr with x _ y _
        exact hpoint x y
    _ ≤ (1 / 2 : ℝ) * (3 ^ d * U.latticeVolume * (P ^ 2 / 2)) := by gcongr
    _ = 3 ^ d / 4 * P ^ 2 * U.latticeVolume := by ring

end Rigidity.Percolation
