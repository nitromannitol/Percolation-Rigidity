import Mathlib

/-!
# Fast decay of harmonic functions on the planar percolation cluster, with no literature input: comparator challenge

Mathlib-only comparator challenge for Theorem 1.3 (label `theorem:fast-decay`) of *Rigidity of
harmonic functions on the supercritical percolation cluster* (Ahmed Bou-Rabee, William Cooperman
and Paul Dario), in the form whose only hypothesis is the regime `p_c(2) < p < 1`.  The library's
statement is `Rigidity.Assembly.Unconditional.fast_decay` in
`Rigidity/Proofs/Assembly/Unconditional.lean`, equal to
`Rigidity.Assembly.ProvedFluxWeakNorm.fast_decay_holds`; the eleven cited results that
`RigidityAudit/FastDecay/Challenge.lean` takes as hypotheses are proved in the library.

**The result.**  Consider supercritical bond percolation on `ℤ²` with parameter
`p_c(2) < p < 1`.  Almost surely the infinite open cluster `𝒞_∞` exists and is unique, and for
every finitely supported `f : ℤ² → ℤ` and every `u : 𝒞_∞ → ℝ` with `-Δu = f` on `𝒞_∞` and
`lim sup_{R → ∞} R · sup_{𝒞_∞ ∩ (B_R \ B_{R/2})} |u| = 0`, the function `u` has finite support.
The conclusion is `FastDecayStmt` of `RigidityAudit/FastDecay/Challenge.lean`.

This file imports only `Mathlib`: no repository module and no dependency.  Its vocabulary is that
of `RigidityAudit/FastDecay/Challenge.lean` without the eleven cited results and without the
definitions that only they use; the solution uses `RigidityAudit/FastDecay/SolutionBasic.lean`.
The sole intentional `sorry` is the proof of the final theorem.
-/

namespace Rigidity
namespace StatementAudit
namespace FastDecay

-- VOCABULARY-BEGIN
/-! ## Vertices, bonds and configurations (`LatticeProb/Prob/Percolation/LatticeBondModel.lean`) -/

section

open scoped BigOperators

variable {d : ℕ}

/-- Integer-coordinate vertices of the lattice. -/
abbrev Vertex (d : ℕ) := Fin d → ℤ

/-- Unordered nearest-neighbor bonds, with the literal ℓ¹-distance-one carrier. -/
abbrev Bond (d : ℕ) :=
  {e : Sym2 (Vertex d) // ∃ x y : Vertex d,
    e = s(x, y) ∧ (∑ i, |x i - y i|) = 1}

/-- A deterministic assignment of open or closed status to every genuine lattice bond. -/
abbrev Configuration (d : ℕ) := Bond d → Bool

end

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

/-! ## Nearest-neighbour bonds (`LatticeProb/Prob/Percolation/LatticeBondModel.lean`) -/

section

open scoped BigOperators

variable {d : ℕ}

/-- The nearest-neighbor graph already supplied by the lattice library. -/
abbrev nearestNeighborGraph (d : ℕ) := lattice d

/-- Adjacent vertices are at `ℓ¹` distance one (a proof ingredient of `bondOfAdjacent`). -/
theorem nearestNeighborGraph_adj_l1 {x y : Vertex d} (h : (nearestNeighborGraph d).Adj x y) :
    (∑ i, |x i - y i|) = 1 := by
  obtain ⟨i, rfl | rfl⟩ := h <;>
    simp [unit, Pi.single_apply, apply_ite abs]

/-- The bond determined by adjacent vertices; no endpoint ordering is chosen. -/
def bondOfAdjacent {x y : Vertex d} (h : (nearestNeighborGraph d).Adj x y) : Bond d :=
  ⟨s(x, y), x, y, rfl, nearestNeighborGraph_adj_l1 h⟩

/-- Reversing the endpoint presentation does not change its bond. -/
theorem bondOfAdjacent_symm {x y : Vertex d} (h : (nearestNeighborGraph d).Adj x y) :
    bondOfAdjacent h.symm = bondOfAdjacent h := by
  apply Subtype.ext
  exact Sym2.eq_swap

end

/-! ## The open graph (`LatticeProb/Prob/Percolation/LatticeBondGraph.lean`) -/

section

open scoped BigOperators

variable {d : ℕ}

/-- The graph retaining exactly the bonds assigned `true` by the configuration. -/
def openGraph (ω : Configuration d) : SimpleGraph (Vertex d) where
  Adj x y := ∃ h : (nearestNeighborGraph d).Adj x y, ω (bondOfAdjacent h) = true
  symm := ⟨fun _ _ ⟨h, ho⟩ => ⟨h.symm, by rw [bondOfAdjacent_symm]; exact ho⟩⟩
  loopless := ⟨fun _ ⟨h, _⟩ => h.ne rfl⟩

end

/-! ## The percolation probability (`LatticeProb/Prob/Percolation/LatticeBondInfiniteEvent.lean`,
`LatticeBondProbability.lean`, `LatticeBondCritical.lean`) -/

section

open MeasureTheory ProbabilityTheory

variable {d : ℕ}

/-- The actual component of `x` has infinitely many vertices. -/
def infiniteComponentEvent (x : Vertex d) : Set (Configuration d) :=
  {ω | ((openGraph ω).connectedComponentMk x).supp.Infinite}

/-- The canonical product Bernoulli law on genuine nearest-neighbor bonds. -/
noncomputable def latticeBondLaw (d : ℕ) (p : unitInterval) : Measure (Configuration d) :=
  Measure.infinitePi (fun _ : Bond d => bernoulliMeasure true false p)

/-- The probability that the actual open component of the origin is infinite. -/
noncomputable def theta (d : ℕ) (p : unitInterval) : ℝ :=
  (latticeBondLaw d p).real (infiniteComponentEvent 0)

end

/-- The critical probability is literally the real infimum of positive-theta parameters. -/
noncomputable def criticalProbability (d : ℕ) [NeZero d] : ℝ :=
  sInf {q : ℝ | ∃ p : unitInterval, (p : ℝ) = q ∧ 0 < theta d p}

/-! ## Open clusters and their Laplacian (`LatticeProb/Prob/Percolation/LatticeBondGraph.lean`) -/

section

open scoped BigOperators

variable {d : ℕ}

/-- Actual connected components of the configuration's open graph. -/
abbrev OpenComponent (ω : Configuration d) := (openGraph ω).ConnectedComponent

/-- Existence and uniqueness of an infinite open component, without a chosen carrier. -/
def HasUniqueInfiniteOpenComponent (ω : Configuration d) : Prop :=
  ∃! C : OpenComponent ω, C.supp.Infinite

/-- The graph on the actual vertices of an open connected component. -/
abbrev componentGraph {ω : Configuration d} (C : OpenComponent ω) := C.toSimpleGraph

/-- Open neighbours are among the `2d` lattice neighbours `x ± unit i` (a proof ingredient of
`openGraphLocallyFinite`). -/
theorem openGraph_neighborSet_finite (ω : Configuration d) (x : Vertex d) :
    ((openGraph ω).neighborSet x).Finite := by
  refine (Set.finite_range (fun q : Fin d × Bool =>
    if q.2 then x + unit q.1 else x - unit q.1)).subset ?_
  rintro y ⟨⟨i, h | h⟩, _⟩
  · exact ⟨(i, true), by simp [h]⟩
  · exact ⟨(i, false), by simp [h]⟩

/-- Every open neighbor set is a finite subset of the lattice neighbor set. -/
noncomputable instance openGraphLocallyFinite (ω : Configuration d) :
    (openGraph ω).LocallyFinite :=
  fun x => Set.Finite.fintype (openGraph_neighborSet_finite ω x)

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

end

/-! ## Euclidean balls of a cluster (`LatticeProb/Prob/Percolation/LatticeClusterBall.lean`) -/

noncomputable section

variable {d : ℕ}

/-- The coordinatewise integer inclusion into Euclidean space, with its Euclidean metric. -/
def latticeEuclideanEmbedding : Vertex d ↪ EuclideanSpace ℝ (Fin d) where
  toFun x := WithLp.toLp 2 (fun i => (x i : ℝ))
  inj' := by
    intro x y h
    funext i
    have hi := congrArg (fun v : EuclideanSpace ℝ (Fin d) => v i) h
    change (x i : ℝ) = (y i : ℝ) at hi
    exact_mod_cast hi

end

/-! ## The infinite cluster (`LatticeProb/Prob/Percolation/LatticeUniqueCluster.lean`,
`LatticeUniqueClusterEvent.lean`) -/

section

variable {d : ℕ} {ω : Configuration d}

/-- The unique infinite actual component, with no value on configurations lacking uniqueness. -/
noncomputable def uniqueInfiniteComponent (h : HasUniqueInfiniteOpenComponent ω) :
    OpenComponent ω := h.exists.choose

end

/-! ## The statement of Theorem 1.3 (`Rigidity/Draft/Section5Statements.lean`) -/

section

open MeasureTheory Classical Filter Topology

/-- The Euclidean norm `|x|₂`. -/
noncomputable def eucl (x : Vertex 2) : ℝ := ‖latticeEuclideanEmbedding x‖

/-- Theorem 1.3 (d = 2): almost surely, for every finitely supported `f : ℤ² → ℤ` and every
`u : 𝒞_∞ → ℝ` with `-Δu = f` and `lim sup_R R sup_{B_R \ B_{R/2}} |u| = 0`, `u` has finite
support. -/
def FastDecayStmt (p : unitInterval) : Prop :=
  ∀ᵐ ω ∂latticeBondLaw 2 p, ∃ h : HasUniqueInfiniteOpenComponent ω,
    ∀ f : Vertex 2 → ℤ, (Function.support f).Finite →
    ∀ u : uniqueInfiniteComponent h → ℝ,
      (∀ x, -componentLaplacian (uniqueInfiniteComponent h) u x = f x.val) →
      (∀ ε : ℝ, 0 < ε → ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R → ∀ x : uniqueInfiniteComponent h,
        R / 2 ≤ eucl x.val → eucl x.val < R → R * |u x| ≤ ε) →
      (Function.support u).Finite

end
-- VOCABULARY-END

/-! ## The theorem -/

/-- **Theorem 1.3** (`theorem:fast-decay`, fast decay, `d = 2`): for `p_c(2) < p < 1`, almost
surely the infinite cluster `𝒞_∞` exists and is unique, and for every finitely supported
`f : ℤ² → ℤ`, every `u : 𝒞_∞ → ℝ` with `-Δu = f` and
`lim sup_R R sup_{𝒞_∞ ∩ (B_R \ B_{R/2})} |u| = 0` has finite support.  The regime is the only
hypothesis. -/
theorem fast_decay_unconditional (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    FastDecayStmt p := by
  sorry

end FastDecay
end StatementAudit
end Rigidity
