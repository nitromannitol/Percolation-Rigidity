import Rigidity.Proofs.Percolation.LatticeModelComparison
import Mathlib.Probability.Distributions.Bernoulli

/-!
# Comparison of bond percolation laws

The Boolean product law on lattice bonds maps to the set-valued Bernoulli bond law in every
finite dimension. The construction follows `LatticeProb/Probability/Percolation/EdgeCrossing.lean`
and `DualDecayRectangle.lean` at Lattice-Probability revision `a6fae9f9`.
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

namespace Rigidity.Percolation

open LatticeProb.Percolation _root_.Percolation.Literature

variable {V : Type*} (G : SimpleGraph V) (p : unitInterval)

/-- Restrict an ambient bond configuration to the graph edges. -/
def restrictEdges (ω : BondConfig V) (e : G.edgeSet) : Prop := e.val ∈ ω

/-- Extend an edge configuration by closing all nonedges. -/
def extendEdges (η : G.edgeSet → Prop) : BondConfig V :=
  {e | ∃ h : e ∈ G.edgeSet, η ⟨e, h⟩}

/-- Edge restriction is measurable. -/
theorem measurable_restrictEdges : Measurable (restrictEdges G) := by
  change Measurable (fun ω (e : G.edgeSet) => e.val ∈ ω)
  fun_prop

/-- The restriction of the ambient law is the independent edge product law. -/
theorem edge_product_law :
    (bondPercolation G p).map (restrictEdges G) =
      Measure.infinitePi (fun _ : G.edgeSet => bernoulliMeasure True False p) := by
  rw [bondPercolation, setBernoulli_eq_map, Measure.map_map]
  · convert (Measure.infinitePi_map_restrict' (μ := fun i : Sym2 V =>
      bernoulliMeasure (i ∈ G.edgeSet) False p) (I := G.edgeSet)) using 1
    · rfl
    · congr 1
      funext e
      simp only [e.property]
  · exact measurable_restrictEdges G
  · fun_prop

/-- Almost surely, the ambient bond configuration contains no nonedges. -/
theorem edge_support_ae [Countable V] :
    ∀ᵐ ω ∂bondPercolation G p, ω ∩ G.edgeSet = ω := by
  filter_upwards [setBernoulli_ae_subset (u := G.edgeSet) (p := p)] with ω hω
  exact Set.inter_eq_self_of_subset_left hω

/-- Restriction and extension discard exactly the nonedges. -/
theorem extend_restrictEdges (ω : BondConfig V) :
    extendEdges G (restrictEdges G ω) = ω ∩ G.edgeSet := by
  ext e
  simp [extendEdges, restrictEdges, and_comm]

/-- Extension by closed nonedges is measurable. -/
theorem measurable_extendEdges : Measurable (extendEdges G) := by
  apply measurable_set_iff.mpr
  intro e
  change Measurable (fun η => e ∈ extendEdges G η)
  by_cases he : e ∈ G.edgeSet
  · have h : (fun η => e ∈ extendEdges G η) = (fun η => η ⟨e, he⟩) := by
      funext η
      simp [extendEdges, he]
    rw [h]
    exact measurable_pi_apply (⟨e, he⟩ : G.edgeSet)
  · have h : (fun η => e ∈ extendEdges G η) = (fun _ => False) := by
      funext η
      simp [extendEdges, he]
    rw [h]
    exact measurable_const

variable (d : ℕ)

/-- Read a Boolean bond configuration as an edge-indexed proposition. -/
def toEdgeConfig (ω : Configuration d) (e : (LatticeModels.zdGraph d).edgeSet) : Prop :=
  ω ((bondEquiv d).symm e) = true

/-- The Boolean product law becomes the independent product law on lattice edges. -/
theorem map_bool_product :
    (latticeBondLaw d p).map (toEdgeConfig d) =
      Measure.infinitePi (fun _ : (LatticeModels.zdGraph d).edgeSet =>
        bernoulliMeasure True False p) := by
  have hm : Measurable (fun b : Bool => b = true) := by fun_prop
  rw [latticeBondLaw, show toEdgeConfig d = (fun f e => f ((bondEquiv d).symm e)) ∘
      (fun ω b => ω b = true) by rfl,
    ← Measure.map_map (by fun_prop) (by fun_prop),
    Measure.infinitePi_map_pi _ (fun _ => hm)]
  have hmap : (bernoulliMeasure true false p).map (fun b : Bool => b = true) =
      bernoulliMeasure True False p := by
    rw [map_bernoulliMeasure' _ _ hm p]
    congr 1 <;> apply propext <;> decide
  rw [show (fun _ : Bond d => (bernoulliMeasure true false p).map (fun b : Bool => b = true)) =
        (fun _ : Bond d => bernoulliMeasure True False p) by funext; exact hmap]
  exact Measure.map_infinitePi_infinitePi_of_inj (bondEquiv d).symm.injective

/-- The canonical Boolean law pushes forward to the ambient bond law. -/
theorem map_latticeBondLaw :
    (latticeBondLaw d p).map
      (extendEdges (LatticeModels.zdGraph d) ∘ toEdgeConfig d) =
        bondPercolation (LatticeModels.zdGraph d) p := by
  rw [← Measure.map_map (measurable_extendEdges _) (by unfold toEdgeConfig; fun_prop)]
  rw [map_bool_product, ← edge_product_law,
    Measure.map_map (measurable_extendEdges _) (measurable_restrictEdges _)]
  calc
    _ = (bondPercolation (LatticeModels.zdGraph d) p).map id := by
      apply Measure.map_congr
      filter_upwards [edge_support_ae (LatticeModels.zdGraph d) p] with ω hω
      exact (extend_restrictEdges _ ω).trans hω
    _ = _ := Measure.map_id

end Rigidity.Percolation
