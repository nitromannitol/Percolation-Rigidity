import Rigidity.Proofs.Corrector.DarioStepTwoBlocks

/-!
# Measurability of the weight and of the good cubes of the Step 2 sum

The radius of the box of an edge is a measurable integer (`measurable_stepTwoRadius`), the plane
gradient bound at a vertex is measurable (`measurable_planeGrad`), hence so is the weight of the
Step 2 sum at every vertex (`measurable_stepTwoWeight`), and the events that a triadic cube carries
the weight bound (`measurableSet_weightGood`) or is a good cube of the summation of estimate (2)
(`measurableSet_mem_stepTwoGood`) are measurable.
-/

namespace Rigidity.Corrector

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.Proofs.Cluster
  Rigidity.Proofs.Section5 Rigidity.Poincare Rigidity.External
open scoped Classical ENNReal

theorem measurable_nat_comp {β : Type*} [MeasurableSpace β] {f : Configuration 2 → ℕ}
    (hf : Measurable f) {g : ℕ → Configuration 2 → β} (hg : ∀ n, Measurable (g n)) :
    Measurable fun ω => g (f ω) ω := by
  have h : Measurable fun q : Configuration 2 × ℕ => g q.2 q.1 :=
    measurable_from_prod_countable_left fun n => hg n
  exact h.comp (measurable_id.prodMk hf)

theorem measurable_stepTwoRadius (κ : ℕ) (a : LatticeEdge) :
    Measurable fun ω => stepTwoRadius κ ω a := by
  unfold stepTwoRadius
  refine measurable_nat_comp (measurable_planarSide a.1)
    (g := fun n ω => κ * max n (planarSide ω (edgeHead a))) fun n => ?_
  exact measurable_nat_comp (measurable_planarSide (edgeHead a)) (g := fun m _ => κ * max n m)
    fun _ => measurable_const

section Grad

variable {G : Set (Configuration 2)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2)

theorem measurable_planeGrad (i : Fin 2) (z : Vertex 2) :
    Measurable fun ω => planeGrad hG hGv i ω z := by
  unfold planeGrad
  refine measurable_const.add (Finset.measurable_sum _ fun k _ => Measurable.add ?_ ?_)
  · exact Measurable.ite (measurableSet_openGraph_adj _ _)
      (continuous_abs.measurable.comp (measurable_correctorDiff hG hGv _ _ _)) measurable_const
  · exact Measurable.ite (measurableSet_openGraph_adj _ _)
      (continuous_abs.measurable.comp (measurable_correctorDiff hG hGv _ _ _)) measurable_const

theorem measurable_stepTwoWeight (κ : ℕ) (i : Fin 2) (u : Vertex 2) :
    Measurable fun ω => stepTwoWeight hG hGv κ i ω u := by
  unfold stepTwoWeight
  refine Measurable.tsum fun a => ?_
  unfold stepTwoFactor stepTwoBox
  exact measurable_nat_comp (measurable_stepTwoRadius κ a)
    (g := fun n ω => if u ∈ supBox a.1 n then ENNReal.ofReal ((n : ℝ) ^ 14 *
      (∑ z ∈ supBox a.1 n, planeGrad hG hGv i ω z) ^ 2) else 0)
    fun n => Measurable.ite (MeasurableSet.const _)
      ((measurable_const.mul ((Finset.measurable_sum _ fun z _ =>
        measurable_planeGrad hG hGv i z).pow_const 2)).ennreal_ofReal) measurable_const

theorem measurableSet_weightGood (κ : ℕ) (i : Fin 2) (q M : ℝ) (T : TriadicCube 2) :
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

theorem measurableSet_mem_stepTwoGood (κ : ℕ) (i : Fin 2) (ε CM M : ℝ) (T : TriadicCube 2) :
    MeasurableSet {ω | T ∈ stepTwoGood hG hGv κ i ε CM M ω} :=
  (GeneralDim.measurableSet_mem_meyersGood ε CM T).inter
    (measurableSet_weightGood hG hGv κ i _ M T)

end Grad

end Rigidity.Corrector
