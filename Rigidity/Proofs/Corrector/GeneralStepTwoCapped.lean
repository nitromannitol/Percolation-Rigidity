import Rigidity.Proofs.Corrector.GeneralStepTwoWeight
import Rigidity.Proofs.Corrector.GeneralFlipResampling

/-!
# The side of the partition into good cubes of `ℤᵈ` capped at a scale

For a scale `n` and a vertex `v`, `capCube n v` is the triadic cube of scale `n` containing `v`,
and `cappedSide n ω v = 3^{scale}` is the side of the cube at `v` of the partition into good cubes
capped at scale `n` (all cubes of scale at least `n` declared good). Then:

* `cappedSide_le`: it is at most `3ⁿ`;
* `partSide_eq_cappedSide`: it is the side of the partition when the partition agrees with the
  capped partition on `capCube n v` (no `CubeCappedDiscrepancy`);
* `cappedSide_eq_of_localBonds`, `measurable_cappedSide`: it depends only on the bonds inside the
  cube of side `14 · 3ⁿ + 1` around `capCube n v` (`TriadicCube.localRegion`), within `8 · 3ⁿ` of
  `v` (`localRegion_capCube_subset`), and is measurable;
* `measure_exists_cappedDiscrepancy_le`: the probability of a discrepancy at some vertex of a box
  of radius `r` is at most `(2r + 1)ᵈ C e^{-c 3ⁿ}`.

The same holds for the configurations `ω^{e,0}` with one bond closed (`setBond e false ω`): the
capped side of `ω^{e,0}` is local (`cappedSide_setBond_eq_of_localBonds`) and measurable, almost
surely the partition of every `ω^{e,0}` exists (`ae_partitionEvent_setBond`), and since forcing a
bond closed changes probabilities by at most the factor `1/(1 - p)`
(`measure_preimage_setBond_false_le`, from `ofReal_bondWeight_mul_lintegral_setBond_le`), a
discrepancy of `ω^{e(v,k),0}` at some vertex `v` of a box of radius `r`, for any choice of bonds
`e(v, k)`, `k < d`, has probability at most `d (2r + 1)ᵈ C e^{-c 3ⁿ}/(1 - p)`
(`measure_exists_cappedDiscrepancy_setBond_le`).

This is the finite-range version of the side in the weight of the Step 2 sum. It ports the planar
file `DarioStepTwoCapped`: the planar partition is replaced by the partition into good cubes of
`ℤᵈ` (`TriadicCube.goodCubes`), its localization (Armstrong and Dario, Proposition 4.9) by
`exists_measure_cubeCappedDiscrepancy_le`, and the count `(2r + 1)²` of a box by `(2r + 1)ᵈ`.
-/

namespace Rigidity.Corrector.GeneralDim

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.Proofs.Cluster
  Rigidity.External
open Rigidity.Poincare.GeneralDim (supBox mem_supBox card_supBox)
open scoped Classical ENNReal

variable {d : ℕ}

/-- The triadic cube of scale `n` containing `v`. -/
def capCube (n : ℕ) (v : Vertex d) : TriadicCube d := ⟨n, idx n v⟩

theorem mem_capCube (n : ℕ) (v : Vertex d) : v ∈ (capCube n v).vertices :=
  mem_triadicCube_idx_iff.2 (mem_cube_self n v)

/-- The side at `v` of the partition into good cubes capped at scale `n`. -/
noncomputable def cappedSide (n : ℕ) (ω : Configuration d) (v : Vertex d) : ℕ :=
  3 ^ (TriadicCube.cappedCube (TriadicCube.goodCubes ω) n v).scale

theorem cappedSide_le (n : ℕ) (ω : Configuration d) (v : Vertex d) : cappedSide n ω v ≤ 3 ^ n :=
  Nat.pow_le_pow_right (by norm_num) (TriadicCube.scale_cappedCube_le _ _ _)

theorem one_le_cappedSide (n : ℕ) (ω : Configuration d) (v : Vertex d) : 1 ≤ cappedSide n ω v :=
  Nat.one_le_pow _ _ (by norm_num)

/-- **The capped side is the side** when the partition agrees with the capped partition. -/
theorem partSide_eq_cappedSide {ω : Configuration d} (hP : PartitionEvent ω) {n : ℕ}
    {v : Vertex d} (h : ¬ CubeCappedDiscrepancy ω (capCube n v)) :
    partSide ω v = cappedSide n ω v := by
  rw [partSide_eq hP, cappedSide, partitionCube_eq_cappedCube ⟨hP, h⟩ (mem_capCube n v)]
  rfl

/-- **Locality of the capped side.** -/
theorem cappedSide_eq_of_localBonds {ω ω' : Configuration d} {n : ℕ} {v : Vertex d}
    (h : ∀ e ∈ localBonds (capCube n v).localRegion, ω e = ω' e) :
    cappedSide n ω' v = cappedSide n ω v := by
  have := cappedCube_goodCubes_eq_of_localBonds (mem_capCube n v) h
  unfold cappedSide
  rw [show (capCube n v).scale = n from rfl] at this
  rw [this]

theorem measurable_cappedSide (n : ℕ) (v : Vertex d) :
    Measurable fun ω : Configuration d => cappedSide n ω v :=
  measurable_of_fiber_const (fun ω => TriadicCube.cappedCube (TriadicCube.goodCubes ω) n v)
    (fun Q => measurableSet_cappedCube_goodCubes_eq n v Q) fun _ _ h => by
      simp only [cappedSide]
      rw [h]

/-- The local region of `capCube n v` lies within `8 · 3ⁿ` of `v`. -/
theorem localRegion_capCube_subset (n : ℕ) (v : Vertex d) :
    (capCube n v).localRegion ⊆ ↑(supBox v (8 * 3 ^ n)) := by
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

/-- **The capped side is the side on a box, with high probability**: a discrepancy between the
partition and the partition capped at scale `n` at some vertex of a box of radius `r` has
probability at most `(2r + 1)ᵈ C e^{-c 3ⁿ}`. -/
theorem measure_exists_cappedDiscrepancy_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ) (u : Vertex d) (r : ℕ),
      latticeBondLaw d p {ω | ∃ v ∈ supBox u r, CubeCappedDiscrepancy ω (capCube n v)} ≤
        ((2 * r + 1) ^ d : ℕ) * (C * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ n))) := by
  obtain ⟨C, hC, c, hc, hD⟩ := exists_measure_cubeCappedDiscrepancy_le hd hpc
  refine ⟨C, hC, c, hc, fun n u r => ?_⟩
  have e : {ω | ∃ v ∈ supBox u r, CubeCappedDiscrepancy ω (capCube n v)} =
      ⋃ v ∈ supBox u r, {ω | CubeCappedDiscrepancy ω (capCube n v)} := by
    ext ω; simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  rw [e]
  refine (measure_biUnion_finset_le _ _).trans ?_
  calc ∑ v ∈ supBox u r, latticeBondLaw d p {ω | CubeCappedDiscrepancy ω (capCube n v)}
      ≤ ∑ _v ∈ supBox u r, C * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ n)) :=
        Finset.sum_le_sum fun v _ => hD (capCube n v)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, card_supBox]

/-! ### The configurations with one bond closed -/

/-- **Forcing a bond closed**: `P(ω^{e,0} ∈ S) ≤ P(S)/(1 - p)`. -/
theorem measure_preimage_setBond_false_le {p : unitInterval} (hp1 : (p : ℝ) < 1)
    {S : Set (Configuration d)} (hS : MeasurableSet S) (e : Bond d) :
    latticeBondLaw d p (setBond e false ⁻¹' S) ≤
      (ENNReal.ofReal (1 - p))⁻¹ * latticeBondLaw d p S := by
  have hq : (0 : ℝ) < 1 - p := by linarith
  have hq' : ENNReal.ofReal (1 - p) ≠ 0 := (ENNReal.ofReal_pos.2 hq).ne'
  have hflip := ofReal_bondWeight_mul_lintegral_setBond_le p
    (f := S.indicator fun _ => (1 : ℝ≥0∞)) (measurable_const.indicator hS) e false
  have hpre : (fun ω => S.indicator (fun _ => (1 : ℝ≥0∞)) (setBond e false ω)) =
      (setBond e false ⁻¹' S).indicator fun _ => 1 := by
    funext ω
    simp only [Set.indicator_apply, Set.mem_preimage]
  have hbw : bondWeight p false = 1 - p := by simp [bondWeight]
  rw [hpre, lintegral_indicator_const (hS.preimage (measurable_setBond e false)),
    lintegral_indicator_const hS, one_mul, one_mul, hbw] at hflip
  calc latticeBondLaw d p (setBond e false ⁻¹' S)
      = (ENNReal.ofReal (1 - p))⁻¹ *
          (ENNReal.ofReal (1 - p) * latticeBondLaw d p (setBond e false ⁻¹' S)) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hq' ENNReal.ofReal_ne_top, one_mul]
    _ ≤ _ := by gcongr

/-- Almost surely the partition into good cubes of every `ω^{e,b}` exists. -/
theorem ae_partitionEvent_setBond [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∀ᵐ ω ∂latticeBondLaw d p, ∀ (e : Bond d) (b : Bool), PartitionEvent (setBond e b ω) :=
  ae_setBond ((criticalProbability_nonneg d).trans_lt hpc) hp1 (ae_partitionEvent hd hpc)

/-- Configurations agreeing on a set of bonds still agree there after setting one bond. -/
theorem setBond_apply_eq_of_apply_eq {S : Set (Bond d)} {ω ω' : Configuration d}
    (h : ∀ e' ∈ S, ω e' = ω' e') (e : Bond d) (b : Bool) {e' : Bond d} (he' : e' ∈ S) :
    setBond e b ω e' = setBond e b ω' e' := by
  by_cases hee : e' = e
  · subst hee
    simp only [setBond, Function.update_self]
  · rw [setBond_apply_ne hee, setBond_apply_ne hee]
    exact h e' he'

/-- **Locality of the capped side of `ω^{e,b}`.** -/
theorem cappedSide_setBond_eq_of_localBonds {ω ω' : Configuration d} {n : ℕ} {v : Vertex d}
    (e : Bond d) (b : Bool) (h : ∀ e' ∈ localBonds (capCube n v).localRegion, ω e' = ω' e') :
    cappedSide n (setBond e b ω') v = cappedSide n (setBond e b ω) v :=
  cappedSide_eq_of_localBonds fun _ he' => setBond_apply_eq_of_apply_eq h e b he'

theorem measurable_cappedSide_setBond (n : ℕ) (v : Vertex d) (e : Bond d) (b : Bool) :
    Measurable fun ω : Configuration d => cappedSide n (setBond e b ω) v :=
  (measurable_cappedSide n v).comp (measurable_setBond e b)

/-- The capped side of `ω^{e,b}` is its side when its partition agrees with its capped
partition. -/
theorem partSide_setBond_eq_cappedSide {ω : Configuration d} {e : Bond d} {b : Bool}
    (hP : PartitionEvent (setBond e b ω)) {n : ℕ} {v : Vertex d}
    (h : ¬ CubeCappedDiscrepancy (setBond e b ω) (capCube n v)) :
    partSide (setBond e b ω) v = cappedSide n (setBond e b ω) v :=
  partSide_eq_cappedSide hP h

/-- **The capped sides of the configurations with one bond closed are their sides on a box, with
high probability**: for any bonds `e(v, k)`, `k < d`, a discrepancy of `ω^{e(v,k),0}` at some
vertex `v` of a box of radius `r` has probability at most `d (2r + 1)ᵈ C e^{-c 3ⁿ}/(1 - p)`. -/
theorem measure_exists_cappedDiscrepancy_setBond_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (E : LatticeEdge d → Bond d) (n : ℕ) (u : Vertex d) (r : ℕ),
        latticeBondLaw d p {ω | ∃ v ∈ supBox u r, ∃ k : Fin d,
            CubeCappedDiscrepancy (setBond (E (v, k)) false ω) (capCube n v)} ≤
          ((d * (2 * r + 1) ^ d : ℕ) : ℝ≥0∞) *
            (C * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ n) / (1 - p))) := by
  obtain ⟨C, hC, c, hc, hD⟩ := exists_measure_cubeCappedDiscrepancy_le hd hpc
  refine ⟨C, hC, c, hc, fun E n u r => ?_⟩
  have hq : (0 : ℝ) < 1 - p := by linarith
  have key : ∀ (e : Bond d) (V : TriadicCube d),
      latticeBondLaw d p {ω | CubeCappedDiscrepancy (setBond e false ω) V} ≤
        C * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ V.scale) / (1 - p)) := by
    intro e V
    refine (measure_preimage_setBond_false_le hp1 (measurableSet_cubeCappedDiscrepancy V) e).trans
      ?_
    calc (ENNReal.ofReal (1 - p))⁻¹ * latticeBondLaw d p {ω | CubeCappedDiscrepancy ω V}
        ≤ (ENNReal.ofReal (1 - p))⁻¹ *
            (C * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ V.scale))) := by
          gcongr
          exact hD V
      _ = _ := by
          rw [ENNReal.ofReal_div_of_pos hq, div_eq_mul_inv]
          ac_rfl
  have e : {ω | ∃ v ∈ supBox u r, ∃ k : Fin d,
      CubeCappedDiscrepancy (setBond (E (v, k)) false ω) (capCube n v)} =
      ⋃ v ∈ supBox u r, ⋃ k : Fin d,
        {ω | CubeCappedDiscrepancy (setBond (E (v, k)) false ω) (capCube n v)} := by
    ext ω; simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  rw [e]
  refine (measure_biUnion_finset_le _ _).trans ?_
  calc ∑ v ∈ supBox u r, latticeBondLaw d p (⋃ k : Fin d,
        {ω | CubeCappedDiscrepancy (setBond (E (v, k)) false ω) (capCube n v)})
      ≤ ∑ v ∈ supBox u r, ∑ k : Fin d, latticeBondLaw d p
          {ω | CubeCappedDiscrepancy (setBond (E (v, k)) false ω) (capCube n v)} :=
        Finset.sum_le_sum fun v _ => measure_iUnion_fintype_le _ _
    _ ≤ ∑ _v ∈ supBox u r, ∑ _k : Fin d,
          C * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ n) / (1 - p)) :=
        Finset.sum_le_sum fun v _ => Finset.sum_le_sum fun k _ => key (E (v, k)) (capCube n v)
    _ = _ := by
        rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin, card_supBox,
          nsmul_eq_mul, nsmul_eq_mul]
        push_cast
        ring

end Rigidity.Corrector.GeneralDim
