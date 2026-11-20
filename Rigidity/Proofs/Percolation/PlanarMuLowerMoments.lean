import Rigidity.Proofs.Percolation.PlanarMuLowerBound
import Rigidity.Proofs.Percolation.PlanarMuMoments

/-!
# Expected error in the lower bound for `-μ`

The boundary of a cube of side `L` has at most `4L` vertices counted once per face, and the side
of the partition cube of a vertex is at most the reach there. With the moment bound for the reach,

`E[(μ(U, q) + |q|² / 18)⁺; partition event, U resolved] ≤ C |q|₁² / √L`

uniformly in `U` (Armstrong and Dario, Lemma 4.7, (4.13) in expectation).
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped ENNReal Classical

namespace Rigidity.Percolation

variable {ω : Configuration 2}

/-- A face of an integer square has at most `L` vertices. -/
theorem card_face_le (U : TriadicCube 2) (i : Fin 2) (b : Bool) :
    (if b then U.toIntegerCube.upperFace i else U.toIntegerCube.lowerFace i).card ≤
      U.toIntegerCube.size := by
  set F := if b then U.toIntegerCube.upperFace i else U.toIntegerCube.lowerFace i with hF
  set j := i.rev
  have hcoord : ∀ l : Fin 2, l = i ∨ l = j := by
    intro l
    fin_cases i <;> fin_cases l <;> simp [j]
  have hconst : ∀ x' ∈ F, ∀ x'' ∈ F, x' i = x'' i := by
    intro x' hx' x'' hx''
    rw [hF] at hx' hx''
    split_ifs at hx' hx'' <;>
      · have h1 := (Finset.mem_filter.1 hx').2
        have h2 := (Finset.mem_filter.1 hx'').2
        omega
  have hinj : Set.InjOn (fun x' : Vertex 2 => x' j) ↑F := by
    intro x' hx' x'' hx'' h
    funext l
    rcases hcoord l with rfl | rfl
    · exact hconst x' hx' x'' hx''
    · exact h
  have hmaps : ∀ x' ∈ F, x' j ∈ Finset.Ico (U.toIntegerCube.corner j)
      (U.toIntegerCube.corner j + U.toIntegerCube.size) := by
    intro x' hx'
    have hv : x' ∈ U.toIntegerCube.vertices := by
      rw [hF] at hx'
      split_ifs at hx' <;> exact (Finset.mem_filter.1 hx').1
    rw [Finset.mem_Ico]
    exact (IntegerCube.mem_vertices _ _).1 hv j
  have := Finset.card_le_card_of_injOn (fun x' : Vertex 2 => x' j) hmaps hinj
  rw [Int.card_Ico] at this
  omega

/-- The boundary index has at most `4L` elements. -/
theorem card_boundaryIndex_le (U : TriadicCube 2) :
    ((boundaryIndex U).card : ℝ) ≤ 4 * (U.toIntegerCube.size : ℝ) := by
  have h := sum_boundaryIndex U (fun _ => (1 : ℝ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  rw [h]
  have hu := fun i => card_face_le U i true
  have hl := fun i => card_face_le U i false
  simp only [if_true, Bool.false_eq_true, if_false] at hu hl
  calc ∑ i, (((U.toIntegerCube.upperFace i).card : ℝ) + ((U.toIntegerCube.lowerFace i).card : ℝ))
      ≤ ∑ _i : Fin 2, ((U.toIntegerCube.size : ℝ) + (U.toIntegerCube.size : ℝ)) :=
        Finset.sum_le_sum fun i _ => add_le_add (by exact_mod_cast hu i) (by exact_mod_cast hl i)
    _ = 4 * (U.toIntegerCube.size : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- The side of the partition cube of a vertex is at most the reach there. -/
theorem ofReal_partSide_le (hP : PlanarPartitionEvent ω) (x : Vertex 2) :
    ENNReal.ofReal (partSide ω x) ≤ planarReach ω x := by
  have hx := (planarPartCube_spec hP x)
  have hx9 : x ∈ (↑(planarPartCube ω x).ninefold.vertices : Set (Vertex 2)) := by
    rw [TriadicCube.mem_ninefold]
    intro i
    have h1 := (planarPartCube ω x).abs_sub_center_le hx.1 i
    have h2 := (planarPartCube ω x).two_mul_ninefoldRadius
    have hpos : (1 : ℤ) ≤ 3 ^ (planarPartCube ω x).scale := one_le_pow₀ (by norm_num)
    omega
  unfold partSide planarReach
  rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
  exact le_iSup₂_of_le (planarPartCube ω x) ⟨hx.2, hx9⟩ le_rfl

/-- **Expected error in the lower bound for `-μ`.** -/
theorem exists_lintegral_planarMu_add_le {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (U : TriadicCube 2) (q : Fin 2 → ℝ),
      ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
          ENNReal.ofReal (planarMu ω U q + (q 0 ^ 2 + q 1 ^ 2) / 18) else 0)
          ∂(latticeBondLaw 2 p) ≤
        C * ENNReal.ofReal ((|q 0| + |q 1|) ^ 2 / Real.sqrt (U.toIntegerCube.size : ℝ)) := by
  obtain ⟨C₄, hC₄, hle⟩ := exists_lintegral_tsum_ninefold_le hpc 4
  refine ⟨648004 * C₄ + 1, by finiteness, fun U q => ?_⟩
  set L : ℝ := (U.toIntegerCube.size : ℝ) with hL
  have hL1 : 1 ≤ L := by
    rw [hL]
    exact_mod_cast (show 1 ≤ U.toIntegerCube.size from by
      change 1 ≤ 3 ^ U.scale
      exact Nat.one_le_pow _ _ (by norm_num))
  have hsqpos : 0 < Real.sqrt L := Real.sqrt_pos.2 (by linarith)
  set Q2 := (|q 0| + |q 1|) ^ 2 with hQ2
  have hQ2pos : 0 ≤ Q2 := sq_nonneg _
  set a : ℝ := Q2 * 162001 / (L * Real.sqrt L) with ha
  have ha0 : 0 ≤ a := by positivity
  set b : ℝ := Q2 / Real.sqrt L with hb
  have hb0 : 0 ≤ b := by positivity
  have hpoint : ∀ ω : Configuration 2, (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
      ENNReal.ofReal (planarMu ω U q + (q 0 ^ 2 + q 1 ^ 2) / 18) else 0) ≤
      ENNReal.ofReal a * ∑ k ∈ boundaryIndex U, reachSum ω 4 k.2.2 + ENNReal.ofReal b := by
    intro ω
    split_ifs with h
    · have hb' := planarMu_add_le h.1 h.2 q
      have hexp : (|q 0| + |q 1|) ^ 2 * (162001 * (∑ k ∈ boundaryIndex U,
          partSide ω k.2.2 ^ 4) / (L * Real.sqrt L) + 1 / Real.sqrt L) =
          a * ∑ k ∈ boundaryIndex U, partSide ω k.2.2 ^ 4 + b := by
        rw [ha, hb, hQ2]
        ring
      rw [hexp] at hb'
      refine (ENNReal.ofReal_le_ofReal hb').trans ?_
      rw [ENNReal.ofReal_add (by
        have : 0 ≤ ∑ k ∈ boundaryIndex U, partSide ω k.2.2 ^ 4 :=
          Finset.sum_nonneg fun k _ => by
            have := one_le_partSide (ω := ω) k.2.2
            positivity
        positivity) hb0]
      gcongr
      rw [ENNReal.ofReal_mul ha0, ENNReal.ofReal_sum_of_nonneg fun k _ => by
        have := one_le_partSide (ω := ω) k.2.2
        positivity]
      gcongr with k
      rw [ENNReal.ofReal_pow (by have := one_le_partSide (ω := ω) k.2.2; linarith)]
      exact (pow_le_pow_left₀ (zero_le) (ofReal_partSide_le h.1 k.2.2) 4).trans
        (planarReach_pow_le ω k.2.2 3)
    · exact zero_le
  calc ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
          ENNReal.ofReal (planarMu ω U q + (q 0 ^ 2 + q 1 ^ 2) / 18) else 0)
          ∂(latticeBondLaw 2 p)
      ≤ ∫⁻ ω, (ENNReal.ofReal a * ∑ k ∈ boundaryIndex U, reachSum ω 4 k.2.2 +
          ENNReal.ofReal b) ∂(latticeBondLaw 2 p) := lintegral_mono hpoint
    _ = ENNReal.ofReal a * ∑ k ∈ boundaryIndex U,
          ∫⁻ ω, reachSum ω 4 k.2.2 ∂(latticeBondLaw 2 p) + ENNReal.ofReal b := by
        rw [lintegral_add_right _ measurable_const, lintegral_const_mul _
          (Finset.measurable_sum _ fun k _ => measurable_reachSum 4 k.2.2),
          lintegral_finsetSum _ fun k _ => measurable_reachSum 4 k.2.2, lintegral_const,
          measure_univ, mul_one]
    _ ≤ ENNReal.ofReal a * ∑ _k ∈ boundaryIndex U, C₄ + ENNReal.ofReal b := by
        gcongr with k
        exact hle k.2.2
    _ ≤ (648004 * C₄ + 1) * ENNReal.ofReal b := by
        rw [Finset.sum_const, nsmul_eq_mul]
        have hcard : ((boundaryIndex U).card : ℝ≥0∞) ≤ ENNReal.ofReal (4 * L) := by
          rw [← ENNReal.ofReal_natCast]
          exact ENNReal.ofReal_le_ofReal (card_boundaryIndex_le U)
        have hab : ENNReal.ofReal a * ENNReal.ofReal (4 * L) ≤ 648004 * ENNReal.ofReal b := by
          rw [← ENNReal.ofReal_mul ha0, ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num)]
          apply ENNReal.ofReal_le_ofReal
          rw [ha, hb]
          have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ L by linarith)
          rw [show Q2 * 162001 / (L * Real.sqrt L) * (4 * L) = 648004 * (Q2 / Real.sqrt L) by
            field_simp
            ring]
        calc ENNReal.ofReal a * (((boundaryIndex U).card : ℝ≥0∞) * C₄) + ENNReal.ofReal b
            ≤ ENNReal.ofReal a * (ENNReal.ofReal (4 * L) * C₄) + ENNReal.ofReal b := by
              gcongr
          _ = ENNReal.ofReal a * ENNReal.ofReal (4 * L) * C₄ + ENNReal.ofReal b := by
              rw [mul_assoc]
          _ ≤ 648004 * ENNReal.ofReal b * C₄ + ENNReal.ofReal b := by
              gcongr
          _ = (648004 * C₄ + 1) * ENNReal.ofReal b := by ring

end Rigidity.Percolation
