import Mathlib

/-!
# Integer-valued harmonic functions of linear growth on the percolation cluster, with no literature input: comparator challenge

Mathlib-only comparator challenge for Theorem 1.2 (label `theorem:integer-valued-linear-growth`)
of *Rigidity of harmonic functions on the supercritical percolation cluster* (Ahmed Bou-Rabee,
William Cooperman and Paul Dario), in the form whose only hypotheses are the regime `2 ≤ d`,
`p_c(d) < p < 1`.  The library's statement is
`Rigidity.Assembly.WithProvedInputs.integer_valued_linear_growth` in
`Rigidity/Proofs/Assembly/ProvedInputs.lean`, applied to the proved first-order corrector input
`Rigidity.Proofs.Regularity.GeneralDim.supercriticalBondCorrectorInput_holds`; the two cited
results that `RigidityAudit/IntegerLinearGrowth/Challenge.lean` takes as hypotheses (supercritical
uniqueness and the first-order correctors) are proved in the library.

**The result.**  Let `d ≥ 2` and `p_c(d) < p < 1`, and let `𝒞_∞` be the infinite cluster of
Bernoulli bond percolation of parameter `p` on `ℤ^d`.  Almost surely the infinite cluster exists
and is unique, and every function `u : 𝒞_∞ → ℝ` that is harmonic on `𝒞_∞` (for the graph
Laplacian of the cluster), integer-valued, and of at most linear growth (`u(x) = O(|x|)`) is a
constant integer `a ∈ ℤ`.

This file imports only `Mathlib`: no repository module and no dependency.  Its vocabulary is that
of `RigidityAudit/IntegerLinearGrowth/Challenge.lean` without the two cited results and the
definitions that only they use; the solution uses
`RigidityAudit/IntegerLinearGrowth/SolutionBasic.lean`.  The sole intentional `sorry` is the proof
of the final theorem.
-/

namespace Rigidity
namespace StatementAudit
namespace IntegerLinearGrowth

-- VOCABULARY-BEGIN
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

/-! ## Bonds and configurations (`LatticeProb/Prob/Percolation/LatticeBondModel.lean`) -/

section BondModel

variable {d : ℕ}

/-- Integer-coordinate vertices of the lattice. -/
abbrev Vertex (d : ℕ) := Fin d → ℤ

/-- Unordered nearest-neighbour bonds: unordered pairs of vertices at `ℓ¹` distance one. -/
abbrev Bond (d : ℕ) :=
  {e : Sym2 (Vertex d) // ∃ x y : Vertex d,
    e = s(x, y) ∧ (∑ i, |x i - y i|) = 1}

/-- A bond configuration: every bond is open (`true`) or closed (`false`). -/
abbrev Configuration (d : ℕ) := Bond d → Bool

/-- The nearest-neighbour graph of `ℤ^d`. -/
abbrev nearestNeighborGraph (d : ℕ) := lattice d

/-- Nearest neighbours are at `ℓ¹` distance one. -/
theorem l1Dist_eq_one_of_adj {x y : Vertex d} (h : (nearestNeighborGraph d).Adj x y) :
    (∑ i, |x i - y i|) = 1 := by
  obtain ⟨i, rfl | rfl⟩ := h <;> simp [unit, Pi.single_apply, apply_ite abs]

/-- The bond joining two nearest neighbours. -/
def bondOfAdjacent {x y : Vertex d} (h : (nearestNeighborGraph d).Adj x y) : Bond d :=
  ⟨s(x, y), x, y, rfl, l1Dist_eq_one_of_adj h⟩

/-- Reversing the endpoints does not change the bond. -/
theorem bondOfAdjacent_symm {x y : Vertex d} (h : (nearestNeighborGraph d).Adj x y) :
    bondOfAdjacent h.symm = bondOfAdjacent h := by
  apply Subtype.ext
  exact Sym2.eq_swap

end BondModel

/-! ## The open graph and its clusters (`LatticeProb/Prob/Percolation/LatticeBondGraph.lean`) -/

section BondGraph

variable {d : ℕ}

/-- The graph of the open bonds of a configuration. -/
def openGraph (ω : Configuration d) : SimpleGraph (Vertex d) where
  Adj x y := ∃ h : (nearestNeighborGraph d).Adj x y, ω (bondOfAdjacent h) = true
  symm := ⟨fun _ _ ⟨h, ho⟩ => ⟨h.symm, by rw [bondOfAdjacent_symm]; exact ho⟩⟩
  loopless := ⟨fun _ ⟨h, _⟩ => h.ne rfl⟩

/-- The open graph is locally finite: the open neighbours of `x` are among its `2d` lattice
neighbours. -/
noncomputable instance openGraphLocallyFinite (ω : Configuration d) :
    (openGraph ω).LocallyFinite :=
  fun x => Set.Finite.fintype
    ((Set.finite_iUnion fun i : Fin d =>
      ({x + unit i, x - unit i} : Set (Vertex d)).toFinite).subset
      (fun y hy => by
        obtain ⟨⟨i, hi | hi⟩, -⟩ := hy
        · exact Set.mem_iUnion.mpr ⟨i, Or.inl hi⟩
        · exact Set.mem_iUnion.mpr ⟨i, Or.inr (show y = x - unit i by rw [hi]; abel)⟩))

/-- The connected components of the open graph (the open clusters). -/
abbrev OpenComponent (ω : Configuration d) := (openGraph ω).ConnectedComponent

/-- There is exactly one infinite open cluster. -/
def HasUniqueInfiniteOpenComponent (ω : Configuration d) : Prop :=
  ∃! C : OpenComponent ω, C.supp.Infinite

/-- The graph of an open cluster, on its vertices. -/
abbrev componentGraph {ω : Configuration d} (C : OpenComponent ω) := C.toSimpleGraph

/-- The neighbours of `x` in a cluster are neighbours of `x` in the open graph. -/
def componentNeighborEmbedding {ω : Configuration d} (C : OpenComponent ω) (x : C) :
    (componentGraph C).neighborSet x ↪ (openGraph ω).neighborSet x.val where
  toFun y := ⟨y.val.val, y.property⟩
  inj' := by
    intro y z h
    have hv : y.val.val = z.val.val :=
      congrArg (fun t : (openGraph ω).neighborSet x.val => t.val) h
    exact Subtype.ext (Subtype.ext hv)

/-- The graph of a cluster is locally finite. -/
noncomputable instance componentGraphLocallyFinite {ω : Configuration d} (C : OpenComponent ω) :
    (componentGraph C).LocallyFinite := fun x =>
  Fintype.ofInjective (componentNeighborEmbedding C x) (componentNeighborEmbedding C x).injective

/-- The graph Laplacian of a cluster: `Δu(x) = Σ_{y ∼ x} (u(y) - u(x))`. -/
noncomputable def componentLaplacian {ω : Configuration d} (C : OpenComponent ω)
    (u : C → ℝ) (x : C) : ℝ :=
  ∑ y ∈ (componentGraph C).neighborFinset x, (u y - u x)

end BondGraph

/-! ## The percolation law (`LatticeProb/Prob/Percolation/LatticeBondProbability.lean`,
`LatticeBondInfiniteEvent.lean`, `LatticeBondCritical.lean`) -/

section BondLaw

open MeasureTheory ProbabilityTheory

variable {d : ℕ}

/-- Bernoulli bond percolation of parameter `p`: the bonds are independent, each open with
probability `p`. -/
noncomputable def latticeBondLaw (d : ℕ) (p : unitInterval) : Measure (Configuration d) :=
  Measure.infinitePi (fun _ : Bond d => bernoulliMeasure true false p)

/-- The event that the open cluster of `x` is infinite. -/
def infiniteComponentEvent (x : Vertex d) : Set (Configuration d) :=
  {ω | ((openGraph ω).connectedComponentMk x).supp.Infinite}

/-- The percolation probability `θ(p)`: the probability that the open cluster of the origin is
infinite. -/
noncomputable def theta (d : ℕ) (p : unitInterval) : ℝ :=
  (latticeBondLaw d p).real (infiniteComponentEvent 0)

end BondLaw

/-- The critical probability `p_c(d) = inf {p : θ(p) > 0}`. -/
noncomputable def criticalProbability (d : ℕ) [NeZero d] : ℝ :=
  sInf {q : ℝ | ∃ p : unitInterval, (p : ℝ) = q ∧ 0 < theta d p}

/-! ## The infinite cluster (`LatticeProb/Prob/Percolation/LatticeUniqueCluster.lean`,
`LatticeUniqueClusterEvent.lean`) -/

section UniqueCluster

variable {d : ℕ} {ω : Configuration d}

/-- The infinite cluster `𝒞_∞`, on a configuration with a unique infinite open cluster. -/
noncomputable def uniqueInfiniteComponent (h : HasUniqueInfiniteOpenComponent ω) :
    OpenComponent ω := h.exists.choose

end UniqueCluster

/-! ## Linear growth (`LatticeProb/Prob/Percolation/LatticeLinearGrowth.lean`) -/

noncomputable section LinearGrowth

open Filter Asymptotics

variable {d : ℕ} {ω : Configuration d}

/-- `u` grows at most linearly on the cluster: `u(x) = O(|x|₁)` as `x → ∞` in the cluster. -/
def componentPointwiseLinearGrowth (C : OpenComponent ω) (u : C → ℝ) : Prop :=
  u =O[cofinite] (fun x : C => ∑ i : Fin d, |(x.val i : ℝ)|)

end LinearGrowth
-- VOCABULARY-END

/-! ## The theorem -/

open MeasureTheory

/-- **Theorem 1.2** (`theorem:integer-valued-linear-growth`): for `d ≥ 2` and `p_c(d) < p < 1`,
almost surely the infinite cluster `𝒞_∞` exists and is unique, and every harmonic, integer-valued
function `u : 𝒞_∞ → ℝ` of at most linear growth is a constant integer.  The regime is the only
hypothesis. -/
theorem integer_valued_linear_growth_unconditional (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∀ᵐ ω ∂latticeBondLaw d p,
      ∃ h : HasUniqueInfiniteOpenComponent ω,
        ∀ u : uniqueInfiniteComponent h → ℝ,
          (∀ x : uniqueInfiniteComponent h,
            componentLaplacian (uniqueInfiniteComponent h) u x = 0) →
          (∀ x : uniqueInfiniteComponent h, ∃ z : ℤ, u x = (z : ℝ)) →
          componentPointwiseLinearGrowth (uniqueInfiniteComponent h) u →
          ∃ a : ℤ, ∀ x : uniqueInfiniteComponent h, u x = (a : ℝ)
:= by
  sorry

end IntegerLinearGrowth
end StatementAudit
end Rigidity
