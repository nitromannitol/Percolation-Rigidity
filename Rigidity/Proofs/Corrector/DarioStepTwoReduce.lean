import Rigidity.Proofs.Corrector.DarioStepTwoPaths
import Rigidity.Proofs.Corrector.DarioStepTwoSum
import PercolationClusterHomogenization.Proofs.Cluster.GeneralRestrictBadTail
import PercolationClusterHomogenization.Proofs.Cluster.MeyersPlanarBox

/-!
# The Step 2 sum through a partition carrying the Meyers estimate and the weight

The summation of estimate (2) runs over the partition of Armstrong and Dario, Proposition 2.1, for
the family of the triadic cubes whose children carry the Meyers estimate and on which the weight
`W` of the Step 2 sum (`stepTwoWeight`) is finite with `Σ_T W^q ≤ M |T|`, `q` the exponent
conjugate to `p = 1 + ε/2` (`weightGood`, `stepTwoGood`). When the maximal stopping cubes of this
family partition the lattice:

* `isCellScale_partScale`: their scales describe a partition into triadic cubes with comparable
  neighbours (`IsCellScale`), each cell carrying the Meyers estimate on its children and the bound
  of the weight;
* `flipSumTwo_le_of_partition`: almost surely
  `Σ_e T₂(e)² ≤ Σ_y Φ_{r²}(x, y)² K₀ (W(y) + 12 K pathWeight(y))`, with
  `pathWeight(y) = |R(y)| Σ_{z ∈ R(y)} c(z) N(z)`, `c(z) = (9^{n(z)})^{1 - 1/p}` for the scale
  `n(z)` of the cell of `z`: (4) (`ae_flipSumTwo_le`), the summation over the cells
  (`tsum_weight_energy_le`), the energy bound (`tsum_clusterOpenEnergy_le`) and the path count
  (`tsum_mul_edgeSq_le`).
-/

namespace Rigidity.Corrector

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.Proofs.Cluster
  Rigidity.External Rigidity.Poincare
open scoped Classical ENNReal InnerProductSpace

/-! ### The partition of a family of good cubes as a scale function -/

section Partition

variable {𝒢 : Set (TriadicCube 2)}
  (hpart : ∀ x : Vertex 2, ∃! Q : TriadicCube 2, x ∈ Q.vertices ∧ Q.IsMaximalStopping 𝒢)

/-- The cell of `x`: the maximal stopping cube containing it. -/
noncomputable def partCell (x : Vertex 2) : TriadicCube 2 := Classical.choose (hpart x).exists

/-- The scale of the cell of `x`. -/
noncomputable def partScale (x : Vertex 2) : ℕ := (partCell hpart x).scale

theorem partCell_spec (x : Vertex 2) :
    x ∈ (partCell hpart x).vertices ∧ (partCell hpart x).IsMaximalStopping 𝒢 :=
  Classical.choose_spec (hpart x).exists

theorem partCell_eq_of_mem {x y : Vertex 2} (h : y ∈ (partCell hpart x).vertices) :
    partCell hpart y = partCell hpart x :=
  (hpart y).unique (partCell_spec hpart y) ⟨h, (partCell_spec hpart x).2⟩

/-- The cell of `x` is the cube of its scale containing `x`. -/
theorem cube_partScale (x : Vertex 2) :
    cube (partScale hpart x) x = (partCell hpart x).toIntegerCube.vertices := by
  have hT : (⟨partScale hpart x, idx (partScale hpart x) x⟩ : TriadicCube 2) = partCell hpart x :=
    TriadicCube.eq_of_mem_of_scale_eq rfl (mem_triadicCube_idx_iff.2 (mem_cube_self _ x))
      (partCell_spec hpart x).1
  rw [cube_eq_toIntegerCube_vertices, hT]

theorem mem_cube_partScale_iff {x y : Vertex 2} :
    y ∈ cube (partScale hpart x) x ↔ y ∈ (partCell hpart x).vertices := by
  rw [cube_partScale, TriadicCube.mem_toIntegerCube_vertices]

/-- **The cells of a family of good cubes form a partition with comparable neighbours.** -/
theorem isCellScale_partScale : IsCellScale (partScale hpart) where
  eq_of_mem x y h := by
    unfold partScale
    rw [partCell_eq_of_mem hpart ((mem_cube_partScale_iff hpart).1 h)]
  le_of_near x y h :=
    ((partCell_spec hpart x).2.1.scales_close_of_near (partCell_spec hpart y).2.1
      (partCell_spec hpart x).1 (partCell_spec hpart y).1 h).1

/-- A cell belongs to the family. -/
theorem partCell_mem (x : Vertex 2) : partCell hpart x ∈ 𝒢 :=
  (partCell_spec hpart x).2.1.1 (TriadicCube.mem_influence_self _)

end Partition

/-! ### The good cubes for the Step 2 sum -/

section Good

variable {G : Set (Configuration 2)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2)

/-- The weight of the Step 2 sum is finite on `T` and `Σ_T W^q ≤ M |T|`. -/
def weightGood (κ : ℕ) (i : Fin 2) (q M : ℝ) (ω : Configuration 2) (T : TriadicCube 2) : Prop :=
  (∀ u ∈ T.toIntegerCube.vertices, stepTwoWeight hG hGv κ i ω u ≠ ∞) ∧
    ∑ u ∈ T.toIntegerCube.vertices, (stepTwoWeight hG hGv κ i ω u).toReal ^ q ≤
      M * T.toIntegerCube.vertices.card

/-- The good cubes of the summation of estimate (2): the children carry the Meyers estimate and
the weight is bounded on average. -/
def stepTwoGood (κ : ℕ) (i : Fin 2) (ε CM M : ℝ) (ω : Configuration 2) : Set (TriadicCube 2) :=
  {T | T ∈ GeneralDim.meyersGood ε CM ω ∧
    weightGood hG hGv κ i (Real.conjExponent (1 + ε / 2)) M ω T}

/-- **The weighted energy of the Step 2 sum through the cells** (deterministic): for a
partition into cells with comparable neighbours carrying the Meyers estimate on their children and
the bound `Σ_T W^q ≤ M |T|` of a weight `W = We.toReal` finite everywhere,
`Σ_u We(u) E_v(u) ≤ 12 K Σ_y Φ(y)² pathWeight(c)(y)`. -/
theorem tsum_weight_openEnergy_le {ω : Configuration 2} (hP : PlanarPartitionEvent ω) {r : ℝ}
    {x : Vertex 2} {j : Fin 2}
    (hS : Summable fun z => latticeHeat (r ^ 2) x z * (stepRegion ω z j).card)
    {n : Vertex 2 → ℕ} (hn : IsCellScale n) {ε CM M : ℝ} (hε : 0 < ε) (hCM : 0 ≤ CM)
    (hM : 0 ≤ M)
    (hMey : ∀ x' z, 1 ≤ n x' → z ∈ cube (n x') x' → GeneralDim.MeyersCube ε CM ω (n x' - 1) z)
    {We : Vertex 2 → ℝ≥0∞} (hfin : ∀ u, We u ≠ ∞)
    (hWM : ∀ x', ∑ u ∈ cube (n x') x', (We u).toReal ^ Real.conjExponent (1 + ε / 2) ≤
      M * (cube (n x') x').card) :
    ∑' u, We u * ENNReal.ofReal (openEnergy ω (clusterPot ω (coarseHeatField hP r x j)) u) ≤
      12 * ENNReal.ofReal (M ^ (1 / Real.conjExponent (1 + ε / 2)) + 48 * cellConst ε CM (9 * M)) *
        ∑' y, ENNReal.ofReal (latticeHeat (r ^ 2) x y ^ 2) *
          pathWeight (fun z => ((9 : ℝ) ^ n z) ^ (1 - 1 / (1 + ε / 2))) ω j y := by
  have hα0 : 0 ≤ 1 - 1 / (1 + ε / 2) := by
    have : 1 / (1 + ε / 2) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  have hc1 : ∀ z, 1 ≤ ((9 : ℝ) ^ n z) ^ (1 - 1 / (1 + ε / 2)) := fun z =>
    Real.one_le_rpow (one_le_pow₀ (by norm_num)) hα0
  have hv : ∀ z, ω ∈ infiniteComponentEvent z → openLaplacian ω
      (clusterPot ω (coarseHeatField hP r x j)) z = edgeDiv ω (coarseHeatField hP r x j) z :=
    fun z hz => openLaplacian_clusterPot _ hz
  have hcell := tsum_weight_energy_le hn hv hε hCM hMey (W := fun u => (We u).toReal)
    (fun u => ENNReal.toReal_nonneg) hM hWM
  have henergy := tsum_clusterOpenEnergy_le (ω := ω) (coarseHeatField hP r x j)
  have hpath := tsum_mul_edgeSq_le hP hS (fun z => zero_le_one.trans (hc1 z))
  have hΓ : ∑' z, ENNReal.ofReal (edgeSq (coarseHeatField hP r x j) z) ≤
      ∑' z, ENNReal.ofReal (((9 : ℝ) ^ n z) ^ (1 - 1 / (1 + ε / 2)) *
        edgeSq (coarseHeatField hP r x j) z) :=
    ENNReal.tsum_le_tsum fun z => ENNReal.ofReal_le_ofReal
      (le_mul_of_one_le_left (edgeSq_nonneg _ z) (hc1 z))
  have e1 : ∑' u, We u * ENNReal.ofReal (openEnergy ω (clusterPot ω (coarseHeatField hP r x j)) u) =
      ∑' u, ENNReal.ofReal ((We u).toReal *
        clusterOpenEnergy ω (clusterPot ω (coarseHeatField hP r x j)) u) := by
    refine tsum_congr fun u => ?_
    rw [openEnergy_clusterPot_eq, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (hfin u)]
  rw [e1]
  refine hcell.trans ?_
  calc _ ≤ ENNReal.ofReal (M ^ (1 / Real.conjExponent (1 + ε / 2)) + 48 * cellConst ε CM (9 * M)) *
        (2 * ∑' z, ENNReal.ofReal (((9 : ℝ) ^ n z) ^ (1 - 1 / (1 + ε / 2)) *
            edgeSq (coarseHeatField hP r x j) z) +
          ∑' z, ENNReal.ofReal (((9 : ℝ) ^ n z) ^ (1 - 1 / (1 + ε / 2)) *
            edgeSq (coarseHeatField hP r x j) z)) := by
        gcongr
        exact henergy.trans (by gcongr)
    _ = 3 * ENNReal.ofReal (M ^ (1 / Real.conjExponent (1 + ε / 2)) +
          48 * cellConst ε CM (9 * M)) *
        ∑' z, ENNReal.ofReal (((9 : ℝ) ^ n z) ^ (1 - 1 / (1 + ε / 2)) *
          edgeSq (coarseHeatField hP r x j) z) := by ring
    _ ≤ 3 * ENNReal.ofReal (M ^ (1 / Real.conjExponent (1 + ε / 2)) +
          48 * cellConst ε CM (9 * M)) *
        (4 * ∑' y, ENNReal.ofReal (latticeHeat (r ^ 2) x y ^ 2) *
          pathWeight (fun z => ((9 : ℝ) ^ n z) ^ (1 - 1 / (1 + ε / 2))) ω j y) := by gcongr
    _ = _ := by ring

/-- **The Step 2 sum through the partition of the good cubes.** -/
theorem flipSumTwo_le_of_partition {C₀ C : ℕ} (hC₀ : 2 ≤ C₀) (hres : ResamplePartitionBound C₀ C)
    {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGae : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G) {ε CM M : ℝ} (hε : 0 < ε) (hCM : 0 ≤ CM)
    (hM : 0 ≤ M) :
    ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ (i j : Fin 2) (r : ℝ), 0 < r → ∀ (x : Vertex 2)
      (hpart : ∀ z : Vertex 2, ∃! Q : TriadicCube 2, z ∈ Q.vertices ∧
        Q.IsMaximalStopping (stepTwoGood hG hGv (C₀ + 5 * C + 6) i ε CM M ω)),
      flipSumTwo hG hGv i j r x ω ≤ ∑' y, ENNReal.ofReal (latticeHeat (r ^ 2) x y ^ 2) *
        (ENNReal.ofReal (2 * 1297 ^ 4 * 46656) *
          (stepTwoWeight hG hGv (C₀ + 5 * C + 6) i ω y + 12 * ENNReal.ofReal
            (M ^ (1 / Real.conjExponent (1 + ε / 2)) + 48 * cellConst ε CM (9 * M)) *
            pathWeight (fun z => ((9 : ℝ) ^ partScale hpart z) ^ (1 - 1 / (1 + ε / 2)))
              ω j y)) := by
  filter_upwards [ae_flipSumTwo_le hG hGv hC₀ hres hpc hp1 hGae, ae_planarPartitionEvent hpc,
    ae_summable_heat_stepRegion hpc hp1] with ω hfs hP hS i j r hr x hpart
  have hS' : Summable fun z => latticeHeat (r ^ 2) x z * (stepRegion ω z j).card := by
    have := hS (edgeBond ((0 : Vertex 2), (0 : Fin 2)))
      (ω (edgeBond ((0 : Vertex 2), (0 : Fin 2)))) x j r hr
    rwa [setBond_self] at this
  have hfin : ∀ u, stepTwoWeight hG hGv (C₀ + 5 * C + 6) i ω u ≠ ∞ := fun u =>
    (partCell_mem hpart u).2.1 u
      ((TriadicCube.mem_toIntegerCube_vertices _ u).2 (partCell_spec hpart u).1)
  have hMey : ∀ x' z, 1 ≤ partScale hpart x' → z ∈ cube (partScale hpart x') x' →
      GeneralDim.MeyersCube ε CM ω (partScale hpart x' - 1) z := fun x' z h1 hz =>
    (partCell_mem hpart x').1 (partScale hpart x' - 1) (by unfold partScale at h1 ⊢; omega) z
      ((mem_cube_partScale_iff hpart).1 hz)
  have hWM : ∀ x', ∑ u ∈ cube (partScale hpart x') x',
      (stepTwoWeight hG hGv (C₀ + 5 * C + 6) i ω u).toReal ^ Real.conjExponent (1 + ε / 2) ≤
        M * (cube (partScale hpart x') x').card := fun x' => by
    rw [cube_partScale]
    exact (partCell_mem hpart x').2.2
  have hE := tsum_weight_openEnergy_le hP hS' (isCellScale_partScale hpart) hε hCM hM hMey hfin hWM
  refine (hfs i j r hr x hP).trans ?_
  calc ENNReal.ofReal (2 * 1297 ^ 4 * 46656) *
        (∑' u, stepTwoWeight hG hGv (C₀ + 5 * C + 6) i ω u *
            ENNReal.ofReal (openEnergy ω (clusterPot ω (coarseHeatField hP r x j)) u) +
          ∑' y, stepTwoWeight hG hGv (C₀ + 5 * C + 6) i ω y *
            ENNReal.ofReal (latticeHeat (r ^ 2) x y ^ 2))
      ≤ ENNReal.ofReal (2 * 1297 ^ 4 * 46656) *
        (12 * ENNReal.ofReal (M ^ (1 / Real.conjExponent (1 + ε / 2)) +
            48 * cellConst ε CM (9 * M)) *
          ∑' y, ENNReal.ofReal (latticeHeat (r ^ 2) x y ^ 2) *
            pathWeight (fun z => ((9 : ℝ) ^ partScale hpart z) ^ (1 - 1 / (1 + ε / 2))) ω j y +
          ∑' y, stepTwoWeight hG hGv (C₀ + 5 * C + 6) i ω y *
            ENNReal.ofReal (latticeHeat (r ^ 2) x y ^ 2)) := by gcongr
    _ = _ := by
        rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add, ← ENNReal.tsum_mul_left]
        refine tsum_congr fun y => ?_
        ring

end Good

end Rigidity.Corrector
