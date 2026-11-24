import Rigidity.Proofs.Corrector.DarioCellEnergy

/-!
# The source of the Step 2 sum through the heat weights

For the field `γ = Σ_y Φ_{r²}(x, y) pathField(p_{y,j})` of the anchor paths of the partition
(`coarseHeatField`), Dario's (3.27) bounds `|γ(z, i)|` by `Σ_y Φ(y) 1{z ∈ R(y)} |R(y)|`, with
`R(y) = stepRegion ω y j` the region of the path from the anchor of `y` to that of `y + e_j`
(`abs_coarseHeatField_apply_le`). With the Cauchy–Schwarz inequality against the weights
`1{z ∈ R(y)} |R(y)|`, of sum `N(z)` over `y` (`regionWeight`), this gives
`Γ(z) = Σ_i γ(z, i)² ≤ 4 N(z) Σ_y 1{z ∈ R(y)} |R(y)| Φ(y)²` (`ofReal_edgeSq_le`), and, for any
weight `c ≥ 0` on the vertices (`tsum_mul_edgeSq_le`),

`Σ_z c(z) Γ(z) ≤ 4 Σ_y Φ(y)² |R(y)| Σ_{z ∈ R(y)} c(z) N(z)`,

the path count of the summation of estimate (2): the source is a sum of square heat weights against
a weight built from the partition near `y`.
-/

namespace Rigidity.Corrector

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation Rigidity.Proofs.Cluster
open scoped Classical ENNReal InnerProductSpace

/-- `N(z) = Σ_y 1{z ∈ R(y)} |R(y)|`. -/
noncomputable def regionWeight (ω : Configuration 2) (j : Fin 2) (z : Vertex 2) : ℝ≥0∞ :=
  ∑' y, if z ∈ stepRegion ω y j then ((stepRegion ω y j).card : ℝ≥0∞) else 0

/-- `|R(y)| Σ_{z ∈ R(y)} c(z) N(z)`. -/
noncomputable def pathWeight (c : Vertex 2 → ℝ) (ω : Configuration 2) (j : Fin 2) (y : Vertex 2) :
    ℝ≥0∞ :=
  ((stepRegion ω y j).card : ℝ≥0∞) *
    ∑ z ∈ stepRegion ω y j, ENNReal.ofReal (c z) * regionWeight ω j z

/-- `x y ≤ x² + y²` in `ℝ≥0∞`. -/
theorem ennreal_mul_le_sq_add_sq (x y : ℝ≥0∞) : x * y ≤ x ^ 2 + y ^ 2 := by
  rcases le_total x y with h | h
  · calc x * y ≤ y * y := by gcongr
      _ = y ^ 2 := (sq y).symm
      _ ≤ x ^ 2 + y ^ 2 := le_add_self
  · calc x * y ≤ x * x := by gcongr
      _ = x ^ 2 := (sq x).symm
      _ ≤ x ^ 2 + y ^ 2 := le_self_add

/-- **The Cauchy–Schwarz inequality against weights**, in `ℝ≥0∞`:
`(Σ_y f(y) b(y))² ≤ 2 (Σ_y b(y)) (Σ_y b(y) f(y)²)`. -/
theorem sq_tsum_mul_le {ι : Type*} (f b : ι → ℝ≥0∞) :
    (∑' y, f y * b y) ^ 2 ≤ 2 * (∑' y, b y) * ∑' y, b y * f y ^ 2 := by
  rw [sq, ← ENNReal.tsum_mul_right]
  simp_rw [← ENNReal.tsum_mul_left]
  have hpt : ∀ y y', f y * b y * (f y' * b y') ≤
      b y' * (b y * f y ^ 2) + b y * (b y' * f y' ^ 2) := by
    intro y y'
    calc f y * b y * (f y' * b y') = (f y * f y') * (b y * b y') := by ring
      _ ≤ (f y ^ 2 + f y' ^ 2) * (b y * b y') := by gcongr; exact ennreal_mul_le_sq_add_sq _ _
      _ = _ := by ring
  refine (ENNReal.tsum_le_tsum fun y => ENNReal.tsum_le_tsum fun y' => hpt y y').trans
    (le_of_eq ?_)
  simp only [ENNReal.tsum_add]
  rw [ENNReal.tsum_comm (f := fun y y' => b y * (b y' * f y' ^ 2))]
  simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
  ring

/-- **The source at a vertex through the heat weights**:
`Γ(z) ≤ 4 N(z) Σ_y 1{z ∈ R(y)} |R(y)| Φ(y)²`. -/
theorem ofReal_edgeSq_le {ω : Configuration 2} (hP : PlanarPartitionEvent ω) {r : ℝ}
    {x : Vertex 2} {j : Fin 2}
    (hS : Summable fun z => latticeHeat (r ^ 2) x z * (stepRegion ω z j).card) (z : Vertex 2) :
    ENNReal.ofReal (edgeSq (coarseHeatField hP r x j) z) ≤
      4 * regionWeight ω j z * ∑' y, (if z ∈ stepRegion ω y j then
        ((stepRegion ω y j).card : ℝ≥0∞) else 0) * ENNReal.ofReal (latticeHeat (r ^ 2) x y ^ 2) := by
  set b : Vertex 2 → ℝ≥0∞ := fun y =>
    if z ∈ stepRegion ω y j then ((stepRegion ω y j).card : ℝ≥0∞) else 0 with hb
  set f : Vertex 2 → ℝ≥0∞ := fun y => ENNReal.ofReal (latticeHeat (r ^ 2) x y) with hf
  have hΦ0 : ∀ y, 0 ≤ latticeHeat (r ^ 2) x y := fun y => latticeHeat_nonneg (sq_nonneg r) x y
  have hk : ∀ i : Fin 2, ENNReal.ofReal (coarseHeatField hP r x j (z, i) ^ 2) ≤
      (∑' y, f y * b y) ^ 2 := by
    intro i
    have h := abs_coarseHeatField_apply_le hP hS (z, i)
    have hsum0 : ∀ y, 0 ≤ latticeHeat (r ^ 2) x y *
        (if z ∈ stepRegion ω y j then ((stepRegion ω y j).card : ℝ) else 0) := fun y =>
      mul_nonneg (hΦ0 y) (by split_ifs <;> positivity)
    have heq : ENNReal.ofReal (∑' y, latticeHeat (r ^ 2) x y *
        (if z ∈ stepRegion ω y j then ((stepRegion ω y j).card : ℝ) else 0)) =
        ∑' y, f y * b y := by
      by_cases hs : Summable fun y => latticeHeat (r ^ 2) x y *
          (if z ∈ stepRegion ω y j then ((stepRegion ω y j).card : ℝ) else 0)
      · rw [ENNReal.ofReal_tsum_of_nonneg hsum0 hs]
        refine tsum_congr fun y => ?_
        simp only [hf, hb]
        rw [ENNReal.ofReal_mul (hΦ0 y)]
        split_ifs <;> simp
      · exact absurd (hS.of_nonneg_of_le hsum0 fun y => by
          refine mul_le_mul_of_nonneg_left ?_ (hΦ0 y)
          split_ifs <;> simp) hs
    rw [← heq, ← ENNReal.ofReal_pow (tsum_nonneg hsum0)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  have hcs := sq_tsum_mul_le f b
  have hbf : ∑' y, b y * f y ^ 2 = ∑' y, b y * ENNReal.ofReal (latticeHeat (r ^ 2) x y ^ 2) := by
    refine tsum_congr fun y => ?_
    simp only [hf]
    rw [← ENNReal.ofReal_pow (hΦ0 y)]
  rw [hbf] at hcs
  unfold edgeSq
  rw [ENNReal.ofReal_sum_of_nonneg fun i _ => sq_nonneg _]
  calc ∑ i : Fin 2, ENNReal.ofReal (coarseHeatField hP r x j (z, i) ^ 2)
      ≤ ∑ _i : Fin 2, (∑' y, f y * b y) ^ 2 := Finset.sum_le_sum fun i _ => hk i
    _ = 2 * (∑' y, f y * b y) ^ 2 := by simp [two_mul]
    _ ≤ 2 * (2 * (∑' y, b y) * ∑' y, b y * ENNReal.ofReal (latticeHeat (r ^ 2) x y ^ 2)) := by
        gcongr
    _ = 4 * regionWeight ω j z * ∑' y, b y * ENNReal.ofReal (latticeHeat (r ^ 2) x y ^ 2) := by
        rw [show regionWeight ω j z = ∑' y, b y from rfl]; ring

/-- **The path count**: `Σ_z c(z) Γ(z) ≤ 4 Σ_y Φ(y)² |R(y)| Σ_{z ∈ R(y)} c(z) N(z)`. -/
theorem tsum_mul_edgeSq_le {ω : Configuration 2} (hP : PlanarPartitionEvent ω) {r : ℝ}
    {x : Vertex 2} {j : Fin 2}
    (hS : Summable fun z => latticeHeat (r ^ 2) x z * (stepRegion ω z j).card)
    {c : Vertex 2 → ℝ} (hc : ∀ z, 0 ≤ c z) :
    ∑' z, ENNReal.ofReal (c z * edgeSq (coarseHeatField hP r x j) z) ≤
      4 * ∑' y, ENNReal.ofReal (latticeHeat (r ^ 2) x y ^ 2) * pathWeight c ω j y := by
  have hpt : ∀ z, ENNReal.ofReal (c z * edgeSq (coarseHeatField hP r x j) z) ≤
      4 * ∑' y, ENNReal.ofReal (c z) * regionWeight ω j z *
        ((if z ∈ stepRegion ω y j then ((stepRegion ω y j).card : ℝ≥0∞) else 0) *
          ENNReal.ofReal (latticeHeat (r ^ 2) x y ^ 2)) := by
    intro z
    rw [ENNReal.ofReal_mul (hc z), ENNReal.tsum_mul_left]
    calc ENNReal.ofReal (c z) * ENNReal.ofReal (edgeSq (coarseHeatField hP r x j) z)
        ≤ ENNReal.ofReal (c z) * (4 * regionWeight ω j z * ∑' y, (if z ∈ stepRegion ω y j then
            ((stepRegion ω y j).card : ℝ≥0∞) else 0) *
              ENNReal.ofReal (latticeHeat (r ^ 2) x y ^ 2)) := by
          gcongr; exact ofReal_edgeSq_le hP hS z
      _ = _ := by ring
  refine (ENNReal.tsum_le_tsum hpt).trans ?_
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_comm]
  gcongr with y
  unfold pathWeight
  rw [Finset.mul_sum, Finset.mul_sum,
    tsum_eq_sum (s := stepRegion ω y j) fun z hz => by rw [if_neg hz]; simp]
  refine le_of_eq (Finset.sum_congr rfl fun z hz => ?_)
  rw [if_pos hz]
  ring

end Rigidity.Corrector
