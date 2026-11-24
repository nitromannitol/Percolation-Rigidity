import Rigidity.Proofs.Corrector.DarioStepTwoWeightBound
import PercolationClusterHomogenization.Proofs.Percolation.PlanarNuLocal
import PercolationClusterHomogenization.Proofs.Percolation.PlanarNuStationarity

/-!
# The side of the planar partition capped at a scale

For a scale `n` and a vertex `v`, `capCube n v` is the triadic cube of scale `n` containing `v`,
and `cappedSide n ω v = 3^{scale}` is the side of the cube at `v` of the planar partition capped at
scale `n` (all cubes of scale at least `n` declared good). Then:

* `cappedSide_le`: it is at most `3ⁿ`;
* `planarSide_eq_cappedSide`: it is the side of the planar partition when the partition agrees
  with the capped partition on `capCube n v` (no `PlanarCappedDiscrepancy`);
* `cappedSide_eq_of_localBonds`, `measurable_cappedSide`: it depends only on the bonds inside the
  square of side `14 · 3ⁿ` around `capCube n v`, within `8 · 3ⁿ` of `v`
  (`planarLocalRegion_capCube_subset`), and is measurable;
* `measure_exists_planarCappedDiscrepancy_le`: the probability of a discrepancy at some vertex of a
  box of radius `r` is at most `(2r + 1)² C e^{-c 3ⁿ}`.

This is the finite-range version of the side in the weight of the Step 2 sum.
-/

namespace Rigidity.Corrector

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.Proofs.Cluster
  Rigidity.Proofs.Section5 Rigidity.Poincare Rigidity.External
open scoped Classical ENNReal

/-- The triadic cube of scale `n` containing `v`. -/
def capCube (n : ℕ) (v : Vertex 2) : TriadicCube 2 := ⟨n, idx n v⟩

theorem mem_capCube (n : ℕ) (v : Vertex 2) : v ∈ (capCube n v).vertices :=
  mem_triadicCube_idx_iff.2 (mem_cube_self n v)

/-- The side at `v` of the planar partition capped at scale `n`. -/
noncomputable def cappedSide (n : ℕ) (ω : Configuration 2) (v : Vertex 2) : ℕ :=
  3 ^ (TriadicCube.cappedCube (planarGoodCubes ω) n v).scale

theorem cappedSide_le (n : ℕ) (ω : Configuration 2) (v : Vertex 2) : cappedSide n ω v ≤ 3 ^ n :=
  Nat.pow_le_pow_right (by norm_num) (TriadicCube.scale_cappedCube_le _ _ _)

theorem one_le_cappedSide (n : ℕ) (ω : Configuration 2) (v : Vertex 2) : 1 ≤ cappedSide n ω v :=
  Nat.one_le_pow _ _ (by norm_num)

/-- **The capped side is the side** when the partition agrees with the capped partition. -/
theorem planarSide_eq_cappedSide {ω : Configuration 2} (hP : PlanarPartitionEvent ω) {n : ℕ}
    {v : Vertex 2} (h : ¬ PlanarCappedDiscrepancy ω (capCube n v)) :
    planarSide ω v = cappedSide n ω v := by
  rw [planarSide_eq hP, cappedSide, planarPartCube_eq_cappedCube ⟨hP, h⟩ (mem_capCube n v)]
  rfl

/-- **Locality of the capped side.** -/
theorem cappedSide_eq_of_localBonds {ω ω' : Configuration 2} {n : ℕ} {v : Vertex 2}
    (h : ∀ e ∈ localBonds (capCube n v).planarLocalRegion, ω e = ω' e) :
    cappedSide n ω' v = cappedSide n ω v := by
  have hd := planarLocalData_eq_of_localBonds h
  have hv : v ∈ (capCube n v).toIntegerCube.vertices :=
    ((capCube n v).mem_toIntegerCube_vertices v).2 (mem_capCube n v)
  have := congrArg (fun t : PlanarLocalDatum (capCube n v) => (t.1 ⟨v, hv⟩).1) hd
  simp only [planarLocalData] at this
  unfold cappedSide
  rw [show (capCube n v).scale = n from rfl] at this
  rw [this]

theorem measurable_cappedSide (n : ℕ) (v : Vertex 2) :
    Measurable fun ω => cappedSide n ω v :=
  measurable_of_fiber_const (fun ω => TriadicCube.cappedCube (planarGoodCubes ω) n v)
    (fun Q => measurableSet_cappedCube_eq n v Q) fun _ _ h => by
      simp only [cappedSide]
      rw [h]

/-- The local region of `capCube n v` lies within `8 · 3ⁿ` of `v`. -/
theorem planarLocalRegion_capCube_subset (n : ℕ) (v : Vertex 2) :
    (capCube n v).planarLocalRegion ⊆ ↑(supBox v (8 * 3 ^ n)) := by
  intro y hy
  rw [Finset.mem_coe, mem_supBox]
  intro i
  have h1 := hy i
  have h2 := (mem_capCube n v) i
  have hs : (capCube n v).side = 3 ^ n := rfl
  rw [hs] at h1 h2
  have hc : 2 * (v i - (3 : ℤ) ^ n * (capCube n v).index i) =
      2 * (v i - (capCube n v).center i) := rfl
  rw [hc, abs_mul] at h2
  have t := abs_sub_le (y i) ((capCube n v).center i) (v i)
  rw [abs_sub_comm ((capCube n v).center i) (v i)] at t
  push_cast
  simp only [abs_two] at h2
  have h3 : (0 : ℤ) ≤ 3 ^ n := by positivity
  linarith


/-- **The capped side is the side on a box, with high probability.** -/
theorem measure_exists_planarCappedDiscrepancy_le {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ) (u : Vertex 2) (r : ℕ),
      latticeBondLaw 2 p {ω | ∃ v ∈ supBox u r, PlanarCappedDiscrepancy ω (capCube n v)} ≤
        ((2 * r + 1) ^ 2 : ℕ) * (C * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ n))) := by
  obtain ⟨C, hC, c, hc, hD⟩ := exists_measure_planarCappedDiscrepancy_le hpc
  refine ⟨C, hC, c, hc, fun n u r => ?_⟩
  have e : {ω | ∃ v ∈ supBox u r, PlanarCappedDiscrepancy ω (capCube n v)} =
      ⋃ v ∈ supBox u r, {ω | PlanarCappedDiscrepancy ω (capCube n v)} := by
    ext ω; simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  rw [e]
  refine (measure_biUnion_finset_le _ _).trans ?_
  calc ∑ v ∈ supBox u r, latticeBondLaw 2 p {ω | PlanarCappedDiscrepancy ω (capCube n v)}
      ≤ ∑ _v ∈ supBox u r, C * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ n)) :=
        Finset.sum_le_sum fun v _ => hD (capCube n v)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, card_supBox]

end Rigidity.Corrector
