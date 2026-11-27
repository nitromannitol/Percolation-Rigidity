import Mathlib

/-!
# Lipschitz rigidity on the supercritical percolation cluster, with no literature input: comparator challenge

Mathlib-only comparator challenge for Theorem 1.1 (label `theorem:lipschitz`) of *Rigidity of
harmonic functions on the supercritical percolation cluster* (Ahmed Bou-Rabee, William Cooperman
and Paul Dario), in the form whose only hypotheses are the regime `2 ≤ d`, `p_c(d) < p < 1`.  The
library's statement is `Rigidity.Assembly.Unconditional.lipschitz` in
`Rigidity/Proofs/Assembly/Unconditional.lean`; the seven cited results that
`RigidityAudit/Lipschitz/Challenge.lean` takes as hypotheses (supercritical uniqueness, the
corrected planes and their quantitative sublinearity, the regularity of order zero, the Green column
and its homogenization, and well-connected cubes) are proved in the library.

**The result.**  Let `d ≥ 2` and `p_c(d) < p < 1`, and let `𝒞_∞` be the infinite cluster of
Bernoulli bond percolation of parameter `p` on `ℤ^d`.  Almost surely the infinite cluster exists and
is unique, and every function `u` on `𝒞_∞` that is harmonic (`componentLaplacian u = 0` at every
vertex) and Lipschitz for the graph distance of `𝒞_∞` is constant.  The Laplacian and the Lipschitz
property are those of `RigidityAudit/Lipschitz/Challenge.lean`.

This file imports only `Mathlib`: no repository module and no dependency.  Its vocabulary is that of
`RigidityAudit/Lipschitz/Challenge.lean` without the seven cited results and without the
definitions that only they use; the solution uses `RigidityAudit/Lipschitz/SolutionBasic.lean`.
The sole intentional `sorry` is the proof of the final theorem.
-/

open MeasureTheory Filter

namespace Rigidity
namespace StatementAudit
namespace Lipschitz

-- VOCABULARY-BEGIN
noncomputable section

/-! ## The lattice (`LatticeProb/Site.lean`) -/

/-- A site of the lattice `ℤ^d`. -/
abbrev Site (d : ℕ) : Type := Fin d → ℤ

/-- The unit vector in direction `i`. -/
def unit {d : ℕ} (i : Fin d) : Site d := Pi.single i 1

/-- A unit vector is not zero. -/
theorem unit_ne_zero {d : ℕ} (i : Fin d) : unit i ≠ 0 := by
  intro h
  have := congrFun h i
  simp [unit, Pi.single_eq_same] at this

/-- The nearest-neighbour lattice on `ℤ^d`. -/
def lattice (d : ℕ) : SimpleGraph (Site d) where
  Adj x y := ∃ i : Fin d, y = x + unit i ∨ x = y + unit i
  symm := ⟨fun _ _ h => h.imp fun _ hi => hi.symm⟩
  loopless := ⟨fun x h => by
    obtain ⟨i, hi | hi⟩ := h
    · exact unit_ne_zero i (by have := congrArg (· - x) hi; simpa using this.symm)
    · exact unit_ne_zero i (by have := congrArg (· - x) hi; simpa using this.symm)⟩

/-! ## Bernoulli bond percolation
(`LatticeProb/Prob/Percolation/LatticeBondModel.lean`, `LatticeBondProbability.lean`) -/

section BondModel

open ProbabilityTheory

variable {d : ℕ}

/-- Integer-coordinate vertices of the lattice. -/
abbrev Vertex (d : ℕ) := Fin d → ℤ

/-- Unordered nearest-neighbor bonds, with the literal ℓ¹-distance-one carrier. -/
abbrev Bond (d : ℕ) :=
  {e : Sym2 (Vertex d) // ∃ x y : Vertex d,
    e = s(x, y) ∧ (∑ i, |x i - y i|) = 1}

/-- A deterministic assignment of open or closed status to every genuine lattice bond. -/
abbrev Configuration (d : ℕ) := Bond d → Bool

/-- The nearest-neighbor graph already supplied by the lattice library. -/
abbrev nearestNeighborGraph (d : ℕ) := lattice d

/-- Adjacent vertices are at `ℓ¹` distance one. -/
theorem l1Dist_eq_one_of_adj {x y : Vertex d} (h : (nearestNeighborGraph d).Adj x y) :
    (∑ i, |x i - y i|) = 1 := by
  obtain ⟨i, rfl | rfl⟩ := h <;> simp [unit, Pi.single_apply, apply_ite abs]

/-- The bond determined by adjacent vertices; no endpoint ordering is chosen. -/
def bondOfAdjacent {x y : Vertex d} (h : (nearestNeighborGraph d).Adj x y) : Bond d :=
  ⟨s(x, y), x, y, rfl, l1Dist_eq_one_of_adj h⟩

/-- Reversing the endpoint presentation does not change its bond. -/
theorem bondOfAdjacent_symm {x y : Vertex d} (h : (nearestNeighborGraph d).Adj x y) :
    bondOfAdjacent h.symm = bondOfAdjacent h := by
  apply Subtype.ext
  exact Sym2.eq_swap

/-- The canonical product Bernoulli law on genuine nearest-neighbor bonds. -/
noncomputable def latticeBondLaw (d : ℕ) (p : unitInterval) : Measure (Configuration d) :=
  Measure.infinitePi (fun _ : Bond d => bernoulliMeasure true false p)

end BondModel

/-! ## The open graph and its components (`LatticeProb/Prob/Percolation/LatticeBondGraph.lean`) -/

section BondGraph

variable {d : ℕ}

/-- The graph retaining exactly the bonds assigned `true` by the configuration. -/
def openGraph (ω : Configuration d) : SimpleGraph (Vertex d) where
  Adj x y := ∃ h : (nearestNeighborGraph d).Adj x y, ω (bondOfAdjacent h) = true
  symm := ⟨fun _ _ ⟨h, ho⟩ => ⟨h.symm, by rw [bondOfAdjacent_symm]; exact ho⟩⟩
  loopless := ⟨fun _ ⟨h, _⟩ => h.ne rfl⟩

/-- Every open neighbor set is finite: it lies among the `2d` lattice neighbors. -/
theorem openGraph_neighborSet_finite (ω : Configuration d) (x : Vertex d) :
    ((openGraph ω).neighborSet x).Finite := by
  refine (Set.finite_range (fun q : Fin d × Bool =>
    if q.2 then x + unit q.1 else x - unit q.1)).subset ?_
  rintro y ⟨⟨i, hi | hi⟩, -⟩
  · exact ⟨(i, true), by simp [hi]⟩
  · exact ⟨(i, false), by simp [hi]⟩

/-- Every open neighbor set is a finite subset of the lattice neighbor set. -/
noncomputable instance openGraphLocallyFinite (ω : Configuration d) :
    (openGraph ω).LocallyFinite :=
  fun x => Set.Finite.fintype (openGraph_neighborSet_finite ω x)

/-- Actual connected components of the configuration's open graph. -/
abbrev OpenComponent (ω : Configuration d) := (openGraph ω).ConnectedComponent

/-- Existence and uniqueness of an infinite open component, without a chosen carrier. -/
def HasUniqueInfiniteOpenComponent (ω : Configuration d) : Prop :=
  ∃! C : OpenComponent ω, C.supp.Infinite

/-- The graph on the actual vertices of an open connected component. -/
abbrev componentGraph {ω : Configuration d} (C : OpenComponent ω) := C.toSimpleGraph

/-- Inclusion of component neighbors into the open graph's neighbors is injective. -/
def componentNeighborEmbedding {ω : Configuration d} (C : OpenComponent ω) (x : C) :
    (componentGraph C).neighborSet x ↪ (openGraph ω).neighborSet x.val where
  toFun y := ⟨y.val.val, y.property⟩
  inj' := by
    intro y z h
    have hv : y.val.val = z.val.val :=
      congrArg (fun t : (openGraph ω).neighborSet x.val => t.val) h
    exact Subtype.ext (Subtype.ext hv)

/-- Component graphs inherit local finiteness through inclusion of their neighbors. -/
noncomputable instance componentGraphLocallyFinite {ω : Configuration d} (C : OpenComponent ω) :
    (componentGraph C).LocallyFinite := fun x =>
  Fintype.ofInjective (componentNeighborEmbedding C x) (componentNeighborEmbedding C x).injective

/-- The source Laplacian on a component uses functions on its actual vertex subtype. -/
noncomputable def componentLaplacian {ω : Configuration d} (C : OpenComponent ω)
    (u : C → ℝ) (x : C) : ℝ :=
  ∑ y ∈ (componentGraph C).neighborFinset x, (u y - u x)

end BondGraph

/-! ## The critical probability and the unique infinite cluster
(`LatticeBondInfiniteEvent.lean`, `LatticeBondCritical.lean`, `LatticeUniqueCluster.lean`,
`LatticeUniqueClusterEvent.lean`, `LatticeClusterLipschitz.lean`) -/

section Cluster

variable {d : ℕ}

/-- The actual component of `x` has infinitely many vertices. -/
def infiniteComponentEvent (x : Vertex d) : Set (Configuration d) :=
  {ω | ((openGraph ω).connectedComponentMk x).supp.Infinite}

/-- The probability that the actual open component of the origin is infinite. -/
noncomputable def theta (d : ℕ) (p : unitInterval) : ℝ :=
  (latticeBondLaw d p).real (infiniteComponentEvent 0)

/-- The critical probability is literally the real infimum of positive-theta parameters. -/
noncomputable def criticalProbability (d : ℕ) [NeZero d] : ℝ :=
  sInf {q : ℝ | ∃ p : unitInterval, (p : ℝ) = q ∧ 0 < theta d p}

variable {ω : Configuration d}

/-- The unique infinite actual component, with no value on configurations lacking uniqueness. -/
noncomputable def uniqueInfiniteComponent (h : HasUniqueInfiniteOpenComponent ω) :
    OpenComponent ω := h.exists.choose

/-- Source Lipschitzness: one nonnegative finite real constant bounds all graph differences. -/
def ComponentLipschitz (C : OpenComponent ω) (u : C → ℝ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ x y : C, |u x - u y| ≤ K * ((componentGraph C).dist x y : ℝ)

end Cluster

end
-- VOCABULARY-END

/-! ## The theorem -/

/-- **Theorem 1.1** (`theorem:lipschitz`): for `d ≥ 2` and `p_c(d) < p < 1`, almost surely the
infinite cluster exists and is unique, and every function `u` on it that is harmonic
(`componentLaplacian u = 0` at every vertex) and Lipschitz for the graph distance of the cluster is
constant.  The regime is the only hypothesis. -/
theorem lipschitz_unconditional (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∀ᵐ ω ∂latticeBondLaw d p,
      ∃ h : HasUniqueInfiniteOpenComponent ω,
        ∀ u : uniqueInfiniteComponent h → ℝ,
          (∀ x, componentLaplacian (uniqueInfiniteComponent h) u x = 0) →
          ComponentLipschitz (uniqueInfiniteComponent h) u →
          ∃ c : ℝ, ∀ x, u x = c
:= by
  sorry

end Lipschitz
end StatementAudit
end Rigidity
