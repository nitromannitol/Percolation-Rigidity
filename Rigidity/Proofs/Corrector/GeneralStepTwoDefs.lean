import Rigidity.Proofs.Corrector.GeneralStepTwoPaths

/-!
# The weight and the good cubes of the Step 2 sum on `ℤᵈ`

The definitions of the summation of estimate (2) for the Step 2 sum of the proof of Lemma 3.3 of
Dario on `ℤᵈ` (from the planar files `DarioStepTwoSum` and `DarioStepTwoReduce`). For an oriented
edge `a = (x, i')` with endpoints `x, y`, let `m_a = max(s(x), s(y))` be the larger side of the
partition cubes of `ω` at its endpoints, `R_a = κ m_a`, `B_a = B(x, R_a)` and

`F_a = R_a^{7d} (Σ_{z ∈ B_a} G(z))²`,   `W(u) = Σ_a 1{u ∈ B_a} F_a`

(`stepTwoRadius`, `stepTwoBox`, `stepTwoFactor`, `stepTwoWeight`), with `G` the gradient bound of
the corrected plane (`planeGrad`); the power `7d` is the power `14` of dimension two. The good
cubes of the summation (`stepTwoGood`) carry the Meyers estimate on their children and the bound
`Σ_T W^q ≤ M |T|` (`weightGood`), `q` the exponent conjugate to `p = 1 + ε/2`. When the maximal
stopping cubes of a family partition the lattice, their scales describe a partition into triadic
cubes with comparable neighbours (`isCellScale_partScale`), and through such a partition carrying
the Meyers estimate and the weight bound (`tsum_weight_openEnergy_le`)

`Σ_u W(u) E_v(u) ≤ 6d K Σ_y Φ_{r²}(x, y)² pathWeight(y)`,

with `v` the potential of `P_ω γ_ω` on the infinite cluster, `γ_ω` the field of the anchor paths of
the partition weighted by the heat kernel, and `pathWeight(y) = |R(y)| Σ_{z ∈ R(y)} c(z) N(z)`,
`c(z) = (3^{d n(z)})^{1 - 1/p}` for the scale `n(z)` of the cell of `z`.
-/

namespace Rigidity.Corrector.GeneralDim

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.Proofs.Cluster
  Rigidity.External
open scoped Classical ENNReal InnerProductSpace
open Rigidity.Poincare.GeneralDim (zdHeat zdHeat_nonneg)

variable {d : ℕ}

/-- The radius `κ max(s(x), s(y))` attached to the oriented edge `a`. -/
noncomputable def stepTwoRadius (κ : ℕ) (ω : Configuration d) (a : LatticeEdge d) : ℕ :=
  κ * max (partSide ω a.1) (partSide ω (edgeHead a))

/-- The box `B(x, κ max(s(x), s(y)))` attached to the oriented edge `a`. -/
noncomputable def stepTwoBox (κ : ℕ) (ω : Configuration d) (a : LatticeEdge d) :
    Finset (Vertex d) :=
  LatticeProb.boxFinset a.1 (stepTwoRadius κ ω a)

theorem card_boxFinset_le_pow {x : Vertex d} {r R : ℕ} (hr : r ≤ R) (hR : 1 ≤ R) :
    ((LatticeProb.boxFinset x r).card : ℝ) ≤ 3 ^ d * (R : ℝ) ^ d := by
  rw [card_boxFinset_eq, ← mul_pow]
  push_cast
  have h1 : (r : ℝ) ≤ R := by exact_mod_cast hr
  have h2 : (1 : ℝ) ≤ R := by exact_mod_cast hR
  exact pow_le_pow_left₀ (by positivity) (by linarith) d

section Weight

variable [NeZero d] {G : Set (Configuration d)} (hG : MeasurableSet G)
  (hGv : G ⊆ correctorValidEvent d)

/-- The factor `F_a = R_a^{7d} (Σ_{z ∈ B_a} G(z))²`. -/
noncomputable def stepTwoFactor (κ : ℕ) (i : Fin d) (ω : Configuration d) (a : LatticeEdge d) :
    ℝ :=
  (stepTwoRadius κ ω a : ℝ) ^ (7 * d) * (∑ z ∈ stepTwoBox κ ω a, planeGrad hG hGv i ω z) ^ 2

/-- The weight `W(u) = Σ_a 1{u ∈ B_a} F_a`. -/
noncomputable def stepTwoWeight (κ : ℕ) (i : Fin d) (ω : Configuration d) (u : Vertex d) :
    ℝ≥0∞ :=
  ∑' a : LatticeEdge d, if u ∈ stepTwoBox κ ω a then
    ENNReal.ofReal (stepTwoFactor hG hGv κ i ω a) else 0

theorem stepTwoFactor_nonneg (κ : ℕ) (i : Fin d) (ω : Configuration d) (a : LatticeEdge d) :
    0 ≤ stepTwoFactor hG hGv κ i ω a := by
  unfold stepTwoFactor
  positivity

end Weight

/-! ### The partition of a family of good cubes as a scale function -/

section Partition

variable {𝒢 : Set (TriadicCube d)}
  (hpart : ∀ x : Vertex d, ∃! Q : TriadicCube d, x ∈ Q.vertices ∧ Q.IsMaximalStopping 𝒢)

/-- The cell of `x`: the maximal stopping cube containing it. -/
noncomputable def partCell (x : Vertex d) : TriadicCube d := Classical.choose (hpart x).exists

/-- The scale of the cell of `x`. -/
noncomputable def partScale (x : Vertex d) : ℕ := (partCell hpart x).scale

theorem partCell_spec (x : Vertex d) :
    x ∈ (partCell hpart x).vertices ∧ (partCell hpart x).IsMaximalStopping 𝒢 :=
  Classical.choose_spec (hpart x).exists

theorem partCell_eq_of_mem {x y : Vertex d} (h : y ∈ (partCell hpart x).vertices) :
    partCell hpart y = partCell hpart x :=
  (hpart y).unique (partCell_spec hpart y) ⟨h, (partCell_spec hpart x).2⟩

/-- The cell of `x` is the cube of its scale containing `x`. -/
theorem cube_partScale (x : Vertex d) :
    cube (partScale hpart x) x = (partCell hpart x).toIntegerCube.vertices := by
  have hT : (⟨partScale hpart x, idx (partScale hpart x) x⟩ : TriadicCube d) = partCell hpart x :=
    TriadicCube.eq_of_mem_of_scale_eq rfl (mem_triadicCube_idx_iff.2 (mem_cube_self _ x))
      (partCell_spec hpart x).1
  rw [cube_eq_toIntegerCube_vertices, hT]

theorem mem_cube_partScale_iff {x y : Vertex d} :
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
theorem partCell_mem (x : Vertex d) : partCell hpart x ∈ 𝒢 :=
  (partCell_spec hpart x).2.1.1 (TriadicCube.mem_influence_self _)

end Partition

/-! ### The good cubes for the Step 2 sum -/

section Good

variable [NeZero d] {G : Set (Configuration d)} (hG : MeasurableSet G)
  (hGv : G ⊆ correctorValidEvent d)

/-- The weight of the Step 2 sum is finite on `T` and `Σ_T W^q ≤ M |T|`. -/
def weightGood (κ : ℕ) (i : Fin d) (q M : ℝ) (ω : Configuration d) (T : TriadicCube d) : Prop :=
  (∀ u ∈ T.toIntegerCube.vertices, stepTwoWeight hG hGv κ i ω u ≠ ∞) ∧
    ∑ u ∈ T.toIntegerCube.vertices, (stepTwoWeight hG hGv κ i ω u).toReal ^ q ≤
      M * T.toIntegerCube.vertices.card

/-- The good cubes of the summation of estimate (2): the children carry the Meyers estimate and
the weight is bounded on average. -/
def stepTwoGood (κ : ℕ) (i : Fin d) (ε CM M : ℝ) (ω : Configuration d) : Set (TriadicCube d) :=
  {T | T ∈ GeneralDim.meyersGood ε CM ω ∧
    weightGood hG hGv κ i (Real.conjExponent (1 + ε / 2)) M ω T}

/-- **The weighted energy of the Step 2 sum through the cells** (deterministic): for a
partition into cells with comparable neighbours carrying the Meyers estimate on their children and
the bound `Σ_T W^q ≤ M |T|` of a weight `W = We.toReal` finite everywhere,
`Σ_u We(u) E_v(u) ≤ 6d K Σ_y Φ(y)² pathWeight(c)(y)`. -/
theorem tsum_weight_openEnergy_le [NeZero d] {ω : Configuration d} (hP : PartitionEvent ω) {r : ℝ}
    {x : Vertex d} {j : Fin d}
    (hS : Summable fun z => zdHeat d (r ^ 2) x z * (stepRegion ω z j).card)
    {n : Vertex d → ℕ} (hn : IsCellScale n) {ε CM M : ℝ} (hε : 0 < ε) (hCM : 0 ≤ CM)
    (hM : 0 ≤ M)
    (hMey : ∀ x' z, 1 ≤ n x' → z ∈ cube (n x') x' → GeneralDim.MeyersCube ε CM ω (n x' - 1) z)
    {We : Vertex d → ℝ≥0∞} (hfin : ∀ u, We u ≠ ∞)
    (hWM : ∀ x', ∑ u ∈ cube (n x') x', (We u).toReal ^ Real.conjExponent (1 + ε / 2) ≤
      M * (cube (n x') x').card) :
    ∑' u, We u * ENNReal.ofReal (openEnergy ω (clusterPot ω (coarseHeatField hP r x j)) u) ≤
      6 * d * ENNReal.ofReal (M ^ (1 / Real.conjExponent (1 + ε / 2)) +
        3 * 4 ^ d * cellConst ε CM (3 ^ d * M)) *
        ∑' y, ENNReal.ofReal (zdHeat d (r ^ 2) x y ^ 2) *
          pathWeight (fun z => (((3 : ℝ) ^ d) ^ n z) ^ (1 - 1 / (1 + ε / 2))) ω j y := by
  have hα0 : 0 ≤ 1 - 1 / (1 + ε / 2) := by
    have : 1 / (1 + ε / 2) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  have hc1 : ∀ z, 1 ≤ (((3 : ℝ) ^ d) ^ n z) ^ (1 - 1 / (1 + ε / 2)) := fun z =>
    Real.one_le_rpow (one_le_pow₀ (one_le_pow₀ (by norm_num))) hα0
  have hv : ∀ z, ω ∈ infiniteComponentEvent z → openLaplacian ω
      (clusterPot ω (coarseHeatField hP r x j)) z = edgeDiv ω (coarseHeatField hP r x j) z :=
    fun z hz => openLaplacian_clusterPot _ hz
  have hcell := tsum_weight_energy_le hn hv hε hCM hMey (W := fun u => (We u).toReal)
    (fun u => ENNReal.toReal_nonneg) hM hWM
  have henergy := tsum_clusterOpenEnergy_le (ω := ω) (coarseHeatField hP r x j)
  have hpath := tsum_mul_edgeSq_le hP hS (fun z => zero_le_one.trans (hc1 z))
  have hΓ : ∑' z, ENNReal.ofReal (edgeSq (coarseHeatField hP r x j) z) ≤
      ∑' z, ENNReal.ofReal ((((3 : ℝ) ^ d) ^ n z) ^ (1 - 1 / (1 + ε / 2)) *
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
  calc _ ≤ ENNReal.ofReal (M ^ (1 / Real.conjExponent (1 + ε / 2)) +
          3 * 4 ^ d * cellConst ε CM (3 ^ d * M)) *
        (2 * ∑' z, ENNReal.ofReal ((((3 : ℝ) ^ d) ^ n z) ^ (1 - 1 / (1 + ε / 2)) *
            edgeSq (coarseHeatField hP r x j) z) +
          ∑' z, ENNReal.ofReal ((((3 : ℝ) ^ d) ^ n z) ^ (1 - 1 / (1 + ε / 2)) *
            edgeSq (coarseHeatField hP r x j) z)) := by
        gcongr
        exact henergy.trans (by gcongr)
    _ = 3 * ENNReal.ofReal (M ^ (1 / Real.conjExponent (1 + ε / 2)) +
          3 * 4 ^ d * cellConst ε CM (3 ^ d * M)) *
        ∑' z, ENNReal.ofReal ((((3 : ℝ) ^ d) ^ n z) ^ (1 - 1 / (1 + ε / 2)) *
          edgeSq (coarseHeatField hP r x j) z) := by ring
    _ ≤ 3 * ENNReal.ofReal (M ^ (1 / Real.conjExponent (1 + ε / 2)) +
          3 * 4 ^ d * cellConst ε CM (3 ^ d * M)) *
        (2 * d * ∑' y, ENNReal.ofReal (zdHeat d (r ^ 2) x y ^ 2) *
          pathWeight (fun z => (((3 : ℝ) ^ d) ^ n z) ^ (1 - 1 / (1 + ε / 2))) ω j y) := by gcongr
    _ = _ := by ring

end Good

end Rigidity.Corrector.GeneralDim
