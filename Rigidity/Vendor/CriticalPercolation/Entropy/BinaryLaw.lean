/- Adapted from OpenAI's math repository (https://github.com/openai/math), commit 4eaee875,
   file lean/OAI/Probability/CriticalPercolation/Entropy/BinaryLaw.lean, Apache License 2.0;
   changes: the module path is Rigidity.Vendor.CriticalPercolation.Entropy.BinaryLaw in place of OAI.Probability.CriticalPercolation.Entropy.BinaryLaw, and the module paths of local imports are changed in the same way; the import of OAI.Probability.CriticalPercolation.Exploration.SequentialExposure, OAI.Probability.CriticalPercolation.Entropy.BinaryInterpolation, OAI.Probability.CriticalPercolation.Exploration.ReachableIncidenceImp (not copied here) is replaced by the imports of the copied modules it reaches,
   namely Rigidity.Vendor.CriticalPercolation.Model, Rigidity.Vendor.CriticalPercolation.GraphGeometry.Link, Rigidity.Vendor.CriticalPercolation.Exploration.ClosedFresh, Rigidity.Vendor.CriticalPercolation.GraphGeometry.VertexBall, Rigidity.Vendor.CriticalPercolation.Clusters.ClusterObject, Rigidity.Vendor.CriticalPercolation.ProductMeasure.Density;
   the unused declarations `interval`, `interval_bounds`, `nextIndex`, `nextIndex_bounds`, `anchors`, `anchorSet`, `anchors_length`, `anchorSet_step`, `endpoint_mem`, `parentPredicate_congr`, `side_record`, `density`, `density_nonneg`, `density_record`, `density_normalized`, `base_left_mem`, `root_bound`, `reachable_record`, `cluster_record`, `seed`, `endpointEvent_record`, `seed_record`, `seed_normalized`, `seed_nonneg`, `endpoint_density_normalized`, `kernel_parent_exists`, `density_step_support` (they need modules not copied here) are omitted and `BinaryInterpolation`, a namespace of modules not copied here, is removed from `open` commands; a module docstring is added; in proofs, `dite_eq_left` is replaced by `dif_pos`; statements of the declarations kept are unchanged. -/
import Mathlib
import Rigidity.Vendor.CriticalPercolation.Model
import Rigidity.Vendor.CriticalPercolation.GraphGeometry.Link
import Rigidity.Vendor.CriticalPercolation.Exploration.ClosedFresh
import Rigidity.Vendor.CriticalPercolation.GraphGeometry.VertexBall
import Rigidity.Vendor.CriticalPercolation.Clusters.ClusterObject
import Rigidity.Vendor.CriticalPercolation.ProductMeasure.Density

/-!
# Binary Law

Results on binary law for Bernoulli percolation on bond graphs.
-/

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph

universe uE

def History (E : Type uE) : ℕ → Type uE
  | 0 => PUnit
  | n+1 => History E n × Bool × Option E

instance historyFintype {E : Type*} [Fintype E] : (n : ℕ) → Fintype (History E n)
  | 0 => inferInstanceAs (Fintype PUnit)
  | n+1 => by
    letI := historyFintype (E := E) n
    exact inferInstanceAs (Fintype (History E n × Bool × Option E))










noncomputable def firstIndex (P : ℕ → Prop) : ℕ :=
  if h : ∃ j, P j then Nat.find h else 0

lemma firstIndex_spec {P : ℕ → Prop} (h : ∃ j, P j) : P (firstIndex P) := by
  rw [firstIndex,dif_pos h]
  exact Nat.find_spec h

lemma firstIndex_le {P : ℕ → Prop} {j : ℕ} (hj : P j) : firstIndex P ≤ j := by
  rw [firstIndex,dif_pos ⟨j,hj⟩]
  exact Nat.find_min' _ hj

variable {V E : Type*} (G : BondGraph V E)

def parentPredicate (L : List (V × Bool)) (a : V) (ω : Set E) (m : Option E) (j : ℕ) : Prop :=
  ∃ z, L[j]? = some z ∧ match m with
    | none => (G.openGraph ω).Reachable a z.1
    | some e => ∃ v ∈ G.ends e, (G.openGraph ω).Reachable z.1 v

noncomputable def parent (L : List (V × Bool)) (a : V) (ω : Set E) (m : Option E) : ℕ :=
  firstIndex (parentPredicate G L a ω m)

noncomputable def side (L : List (V × Bool)) (a : V) (ω : Set E) (m : Option E) : Bool :=
  ((L[parent G L a ω m]?).getD (a,true)).2



section Density
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (r₀ : (E → Prop) → ℝ)





end Density





section Seed
variable [Fintype V] [Fintype E]

def endpointEvent (u v : V) (s : ℕ) (ω : Set E) : Prop :=
  ¬ (G.openGraph ω).Reachable u v ∧
    s ≤ (G.cluster ω u).toFinset.card ∧ s ≤ (G.cluster ω v).toFinset.card






end Seed

section ExactLaw
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]



omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
lemma parent_lt_of_exists (L : List (V × Bool)) (a : V) (ω : Set E) (m : Option E)
    (h : ∃ j, parentPredicate G L a ω m j) : parent G L a ω m < L.length := by
  obtain ⟨z,hz,-⟩ := firstIndex_spec h
  exact (List.getElem?_eq_some_iff.mp hz).1


end ExactLaw

end CriticalPercolation.BinaryLaw
end
end

end OAI
