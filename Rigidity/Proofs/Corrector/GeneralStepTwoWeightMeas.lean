import Rigidity.Proofs.Corrector.GeneralStepTwoDefs

/-!
# Measurability of the weight and of the good cubes of the Step 2 sum on `ℤᵈ`

The radius of the box of an edge is a measurable integer (`measurable_stepTwoRadius`), the plane
gradient bound at a vertex is measurable (`measurable_planeGrad`), hence so is the weight of the
Step 2 sum at every vertex (`measurable_stepTwoWeight`), and the events that a triadic cube carries
the weight bound (`measurableSet_weightGood`) or is a good cube of the summation of estimate (2)
(`measurableSet_mem_stepTwoGood`) are measurable.

This is the planar file `DarioStepTwoWeightMeas` on `ℤᵈ`: the side of the planar partition is
replaced by the side `partSide` of the partition into good cubes of `ℤᵈ`, the radius of an edge
also uses the side of the partition of the configuration with the bond of the edge closed
(`setBond`), the boxes of the edges are the boxes `LatticeProb.boxFinset`, the power `14` of the
factor is `7d`, and the Meyers estimate of the good cubes is the one on `ℤᵈ`.
-/

namespace Rigidity.Corrector.GeneralDim

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.Proofs.Cluster
  Rigidity.External
open scoped Classical ENNReal

variable {d : ℕ}

theorem measurable_nat_comp {β : Type*} [MeasurableSpace β] {f : Configuration d → ℕ}
    (hf : Measurable f) {g : ℕ → Configuration d → β} (hg : ∀ n, Measurable (g n)) :
    Measurable fun ω => g (f ω) ω := by
  have h : Measurable fun q : Configuration d × ℕ => g q.2 q.1 :=
    measurable_from_prod_countable_left fun n => hg n
  exact h.comp (measurable_id.prodMk hf)

/-- The radius `κ max(s(x), s(y), s♭(x))` of the box of an edge is measurable. -/
theorem measurable_stepTwoRadius (κ : ℕ) (a : LatticeEdge d) :
    Measurable fun ω => stepTwoRadius κ ω a := by
  unfold stepTwoRadius
  refine measurable_nat_comp (measurable_partSide a.1)
    (g := fun n ω => κ * max (max n (partSide ω (edgeHead a)))
      (partSide (setBond (edgeBond a) false ω) a.1)) fun n => ?_
  refine measurable_nat_comp (measurable_partSide (edgeHead a))
    (g := fun m ω => κ * max (max n m) (partSide (setBond (edgeBond a) false ω) a.1))
    fun m => ?_
  exact measurable_nat_comp ((measurable_partSide a.1).comp (measurable_setBond (edgeBond a) false))
    (g := fun l _ => κ * max (max n m) l) fun _ => measurable_const

section Grad

variable {G : Set (Configuration d)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent d)

/-- The plane gradient bound at a vertex is measurable. -/
theorem measurable_planeGrad (i : Fin d) (z : Vertex d) :
    Measurable fun ω => planeGrad hG hGv i ω z := by
  unfold planeGrad
  refine measurable_const.add (Finset.measurable_sum _ fun k _ => Measurable.add ?_ ?_)
  · exact Measurable.ite (measurableSet_openGraph_adj _ _)
      (continuous_abs.measurable.comp (measurable_correctorDiff hG hGv _ _ _)) measurable_const
  · exact Measurable.ite (measurableSet_openGraph_adj _ _)
      (continuous_abs.measurable.comp (measurable_correctorDiff hG hGv _ _ _)) measurable_const

/-- The weight of the Step 2 sum at a vertex is measurable. -/
theorem measurable_stepTwoWeight (κ : ℕ) (i : Fin d) (u : Vertex d) :
    Measurable fun ω => stepTwoWeight hG hGv κ i ω u := by
  unfold stepTwoWeight
  refine Measurable.tsum fun a => ?_
  unfold stepTwoFactor stepTwoBox
  exact measurable_nat_comp (measurable_stepTwoRadius κ a)
    (g := fun n ω => if u ∈ LatticeProb.boxFinset a.1 n then ENNReal.ofReal ((n : ℝ) ^ (7 * d) *
      (∑ z ∈ LatticeProb.boxFinset a.1 n, planeGrad hG hGv i ω z) ^ 2) else 0)
    fun n => Measurable.ite (MeasurableSet.const _)
      ((measurable_const.mul ((Finset.measurable_sum _ fun z _ =>
        measurable_planeGrad hG hGv i z).pow_const 2)).ennreal_ofReal) measurable_const

/-- The event that a triadic cube carries the weight bound is measurable. -/
theorem measurableSet_weightGood (κ : ℕ) (i : Fin d) (q M : ℝ) (T : TriadicCube d) :
    MeasurableSet {ω | weightGood hG hGv κ i q M ω T} := by
  unfold weightGood
  rw [Set.setOf_and]
  refine MeasurableSet.inter ?_ (measurableSet_le (Finset.measurable_sum _ fun u _ =>
    (measurable_stepTwoWeight hG hGv κ i u).ennreal_toReal.pow_const q) measurable_const)
  have e : {ω | ∀ u ∈ T.toIntegerCube.vertices, stepTwoWeight hG hGv κ i ω u ≠ ∞} =
      ⋂ u ∈ T.toIntegerCube.vertices, (fun ω => stepTwoWeight hG hGv κ i ω u) ⁻¹' {∞}ᶜ := by
    ext ω
    simp
  rw [e]
  exact Finset.measurableSet_biInter _ fun u _ =>
    measurable_stepTwoWeight hG hGv κ i u (measurableSet_singleton ∞).compl

/-- **The event that a triadic cube is a good cube of the summation of estimate (2) is
measurable.** -/
theorem measurableSet_mem_stepTwoGood (κ : ℕ) (i : Fin d) (ε CM M : ℝ) (T : TriadicCube d) :
    MeasurableSet {ω | T ∈ stepTwoGood hG hGv κ i ε CM M ω} :=
  (GeneralDim.measurableSet_mem_meyersGood ε CM T).inter
    (measurableSet_weightGood hG hGv κ i _ M T)

end Grad

end Rigidity.Corrector.GeneralDim
