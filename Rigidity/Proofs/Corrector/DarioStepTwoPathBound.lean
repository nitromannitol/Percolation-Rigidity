import Rigidity.Proofs.Corrector.DarioGrowthMomentsOps

/-!
# The path weight of the Step 2 sum under ball sums

On the planar partition event, with `σ` the size of the planar partition:

* `stepRegion_subset_supBox`: the anchor region of `z` lies in the box of radius `6σ(z)` around
  `z`;
* `regionWeight_le_weightMajorant`: the number `N(z)` of anchor regions through `z`, weighted by
  their sizes, is at most the majorant `Σ_a 1{|a - z| ≤ 12σ(a)} T₀(a)⁹` with `T₀(a)` the number of
  points within `10σ(a)` of `a`, since `81σ(a)² ≤ T₀(a)`;
* `pathWeight_le_ballSum`: the path weight `|R(y)| Σ_{z ∈ R(y)} c(z) N(z)` is at most
  `81σ(y)² Σ_{|z - y| ≤ 12σ(y)} c'(z) N'(z)` for any `c' ≥ c`;
* `planeGrad_le_of_lipschitz`: if the corrector increments at each vertex of the infinite cluster
  are at most `Λ`, the plane gradient bound is at most `1 + 4Λ`.
-/

namespace Rigidity.Corrector

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.Proofs.Cluster
  Rigidity.Proofs.Section5 Rigidity.Poincare Rigidity.External
open scoped Classical ENNReal

theorem abs_sub_le_of_mem_ninefold {Q : TriadicCube 2} {w x : Vertex 2}
    (hw : w ∈ Q.ninefold.vertices) (hx : x ∈ Q.vertices) (i : Fin 2) :
    |w i - x i| ≤ 5 * 3 ^ Q.scale := by
  have h1 := (TriadicCube.mem_ninefold.1 (Finset.mem_coe.2 hw)) i
  have h2 := hx i
  have hr := Q.two_mul_ninefoldRadius
  simp only [TriadicCube.side] at h2
  simp only [TriadicCube.center, TriadicCube.side] at h1
  rw [abs_le] at h1
  rw [abs_lt] at h2
  rw [abs_le]
  constructor <;> omega

/-- **The anchor region lies in the box of radius `6σ(z)`.** -/
theorem stepRegion_subset_supBox {ω : Configuration 2} (hP : PlanarPartitionEvent ω)
    (z : Vertex 2) (j : Fin 2) : stepRegion ω z j ⊆ supBox z (6 * planarSide ω z) := by
  intro w hw
  rw [mem_supBox]
  intro i
  rw [planarSide_eq hP]
  push_cast
  unfold stepRegion at hw
  split_ifs at hw with h
  · have := abs_sub_le_of_mem_ninefold hw (planarPartCube_spec hP z).1 i
    have h0 : (0 : ℤ) ≤ 3 ^ (planarPartCube ω z).scale := by positivity
    linarith
  · have h1 := abs_sub_le_of_mem_ninefold hw (planarPartCube_spec hP (z + LatticeProb.unit j)).1 i
    have h2 := (abs_sub_add_unit_le z j i).2
    have hlt : (planarPartCube ω (z + LatticeProb.unit j)).scale ≤ (planarPartCube ω z).scale := by
      omega
    have h3 : (3 : ℤ) ^ (planarPartCube ω (z + LatticeProb.unit j)).scale ≤
        3 ^ (planarPartCube ω z).scale := pow_le_pow_right₀ (by norm_num) hlt
    have h4 : (1 : ℤ) ≤ 3 ^ (planarPartCube ω (z + LatticeProb.unit j)).scale :=
      one_le_pow₀ (by norm_num)
    have := abs_sub_le (w i) ((z + LatticeProb.unit j) i) (z i)
    linarith

theorem regionWeight_le {ω : Configuration 2} (hP : PlanarPartitionEvent ω) (j : Fin 2)
    (z : Vertex 2) :
    regionWeight ω j z ≤ ∑' y, if z ∈ supBox y (6 * planarSide ω y) then
      ENNReal.ofReal (81 * TriadicCube.stoppingSize (planarGoodCubes ω) y ^ 2) else 0 := by
  unfold regionWeight
  refine ENNReal.tsum_le_tsum fun y => ?_
  split_ifs with h1 h2
  · rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (card_stepRegion_le hP y j)
  · exact absurd (stepRegion_subset_supBox hP y j h1) h2
  · positivity
  · exact le_rfl

/-- `81σ(y)²` is at most the number of points within `10σ(y)` of `y`. -/
theorem ballCount_le {ω : Configuration 2} (hP : PlanarPartitionEvent ω) (y : Vertex 2) :
    ENNReal.ofReal (81 * TriadicCube.stoppingSize (planarGoodCubes ω) y ^ 2) ≤
      stepOneBallSum (fun _ _ => 0) 10 y ω := by
  have hσ := stoppingSize_eq_planarSide hP y
  have hs1 : 1 ≤ planarSide ω y := by
    rw [planarSide_eq hP]; exact Nat.one_le_pow _ _ (by norm_num)
  have hs1' : (1 : ℝ) ≤ planarSide ω y := by exact_mod_cast hs1
  unfold stepOneBallSum
  calc ENNReal.ofReal (81 * TriadicCube.stoppingSize (planarGoodCubes ω) y ^ 2)
      ≤ ((supBox y (5 * planarSide ω y)).card : ℝ≥0∞) := by
        rw [← ENNReal.ofReal_natCast, card_supBox, hσ]
        refine ENNReal.ofReal_le_ofReal ?_
        push_cast
        nlinarith
    _ = ∑ w ∈ supBox y (5 * planarSide ω y),
          (if ‖latticeEuclideanEmbedding (w - y)‖ ≤
              10 * TriadicCube.stoppingSize (planarGoodCubes ω) y then
            ENNReal.ofReal (1 + (fun (_ : Vertex 2) (_ : Configuration 2) => (0 : ℝ)) w ω)
          else 0) := by
        rw [Finset.card_eq_sum_ones, Nat.cast_sum]
        refine Finset.sum_congr rfl fun w hw => ?_
        have h1 := norm_le_of_mem_supBox hw
        rw [if_pos (by rw [hσ]; push_cast at h1; linarith)]
        simp
    _ ≤ _ := ENNReal.sum_le_tsum _

/-- **The weighted number of anchor regions through `z` under the majorant.** -/
theorem regionWeight_le_weightMajorant {ω : Configuration 2} (hP : PlanarPartitionEvent ω)
    (j : Fin 2) (z : Vertex 2) :
    regionWeight ω j z ≤ weightMajorant (fun _ _ => 0) 12 10 z ω := by
  set g : LatticeEdge → ℝ≥0∞ := fun a =>
    if ‖latticeEuclideanEmbedding (a.1 - z)‖ ≤
        12 * TriadicCube.stoppingSize (planarGoodCubes ω) a.1 then
      stepOneBallSum (fun _ _ => 0) 10 a.1 ω ^ (9 : ℝ) else 0 with hg
  refine (regionWeight_le hP j z).trans ?_
  calc (∑' y, if z ∈ supBox y (6 * planarSide ω y) then
        ENNReal.ofReal (81 * TriadicCube.stoppingSize (planarGoodCubes ω) y ^ 2) else 0)
      ≤ ∑' y, ∑' k : Fin 2, g (y, k) := by
        refine ENNReal.tsum_le_tsum fun y => ?_
        split_ifs with h
        · have hc : ‖latticeEuclideanEmbedding (y - z)‖ ≤
              12 * TriadicCube.stoppingSize (planarGoodCubes ω) y := by
            have h1 := norm_le_of_mem_supBox h
            rw [norm_emb_sub_comm, stoppingSize_eq_planarSide hP]
            push_cast at h1
            linarith
          have hb1 : 1 ≤ stepOneBallSum (fun _ _ => 0) 10 y ω := by
            refine le_trans ?_ (ballCount_le hP y)
            rw [← ENNReal.ofReal_one]
            refine ENNReal.ofReal_le_ofReal ?_
            rw [stoppingSize_eq_planarSide hP]
            have : (1 : ℝ) ≤ planarSide ω y := by
              have := (planarSide_eq hP y) ▸ Nat.one_le_pow _ 3 (by norm_num)
              exact_mod_cast this
            nlinarith
          rw [tsum_fintype, Fin.sum_univ_two]
          simp only [hg, if_pos hc]
          calc ENNReal.ofReal (81 * TriadicCube.stoppingSize (planarGoodCubes ω) y ^ 2)
              ≤ stepOneBallSum (fun _ _ => 0) 10 y ω := ballCount_le hP y
            _ = stepOneBallSum (fun _ _ => 0) 10 y ω ^ (1 : ℝ) := (ENNReal.rpow_one _).symm
            _ ≤ stepOneBallSum (fun _ _ => 0) 10 y ω ^ (9 : ℝ) :=
                ENNReal.rpow_le_rpow_of_exponent_le hb1 (by norm_num)
            _ ≤ _ := le_add_right le_rfl
        · positivity
    _ = ∑' a : LatticeEdge, g a := (ENNReal.tsum_prod (f := fun v k => g (v, k))).symm
    _ = weightMajorant (fun _ _ => 0) 12 10 z ω := rfl

/-- **The path weight under a ball sum.** -/
theorem pathWeight_le_ballSum {ω : Configuration 2} (hP : PlanarPartitionEvent ω)
    {c : Vertex 2 → ℝ} {c' : Vertex 2 → ℝ≥0∞} (hc : ∀ z, ENNReal.ofReal (c z) ≤ c' z)
    (j : Fin 2) (y : Vertex 2) :
    pathWeight c ω j y ≤ ENNReal.ofReal (81 * TriadicCube.stoppingSize (planarGoodCubes ω) y ^ 2) *
      ∑' z, if ‖latticeEuclideanEmbedding (z - y)‖ ≤
          12 * TriadicCube.stoppingSize (planarGoodCubes ω) y then
        c' z * weightMajorant (fun _ _ => 0) 12 10 z ω else 0 := by
  unfold pathWeight
  refine mul_le_mul' ?_ ?_
  · rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (card_stepRegion_le hP y j)
  · calc ∑ z ∈ stepRegion ω y j, ENNReal.ofReal (c z) * regionWeight ω j z
        ≤ ∑ z ∈ stepRegion ω y j, (if ‖latticeEuclideanEmbedding (z - y)‖ ≤
            12 * TriadicCube.stoppingSize (planarGoodCubes ω) y then
          c' z * weightMajorant (fun _ _ => 0) 12 10 z ω else 0) :=
          Finset.sum_le_sum fun z hz => by
            have h1 := norm_le_of_mem_supBox (stepRegion_subset_supBox hP y j hz)
            rw [if_pos (by rw [stoppingSize_eq_planarSide hP]; push_cast at h1; linarith)]
            exact mul_le_mul' (hc z) (regionWeight_le_weightMajorant hP j z)
      _ ≤ _ := ENNReal.sum_le_tsum _

section Grad

variable {G : Set (Configuration 2)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2)

/-- **The plane gradient bound under a bound of the corrector increments.** -/
theorem planeGrad_le_of_lipschitz {ω : Configuration 2} {i : Fin 2} {Λ : Vertex 2 → ℝ}
    (hΛ0 : ∀ z, 0 ≤ Λ z)
    (hlip : ∀ x, ω ∈ infiniteComponentEvent x → ∀ y, (openGraph ω).Adj x y →
      |correctorDiff hG hGv (Pi.single i 1) ω x y| ≤ Λ x) (z : Vertex 2) :
    planeGrad hG hGv i ω z ≤ 1 + 4 * Λ z := by
  have key : ∀ y, (openGraph ω).Adj z y →
      |correctorDiff hG hGv (Pi.single i 1) ω z y| ≤ Λ z := by
    intro y hy
    by_cases hz : ω ∈ infiniteComponentEvent z
    · exact hlip z hz y hy
    · have hy' : ω ∉ infiniteComponentEvent y := fun h =>
        hz (mem_infiniteComponentEvent_of_adj hy.symm h)
      have : correctorDiff hG hGv (Pi.single i 1) ω z y = 0 := by
        unfold correctorDiff
        rw [dif_neg fun h => hy' h.2]
      rw [this, abs_zero]
      exact hΛ0 z
  have t : ∀ k : Fin 2, (if EdgeOpen ω (z, k) then
      |correctorDiff hG hGv (Pi.single i 1) ω z (z + LatticeProb.unit k)| else 0) ≤ Λ z := by
    intro k
    split_ifs with h
    · exact key (z + LatticeProb.unit k) h
    · exact hΛ0 z
  have t' : ∀ k : Fin 2, (if EdgeOpen ω (z - LatticeProb.unit k, k) then
      |correctorDiff hG hGv (Pi.single i 1) ω z (z - LatticeProb.unit k)| else 0) ≤ Λ z := by
    intro k
    split_ifs with h
    · have hadj : (openGraph ω).Adj z (z - LatticeProb.unit k) := by
        have : (openGraph ω).Adj (z - LatticeProb.unit k)
            (z - LatticeProb.unit k + LatticeProb.unit k) := h
        rw [sub_add_cancel] at this
        exact this.symm
      exact key _ hadj
    · exact hΛ0 z
  unfold planeGrad
  rw [Fin.sum_univ_two]
  linarith [t 0, t 1, t' 0, t' 1]

end Grad

end Rigidity.Corrector
