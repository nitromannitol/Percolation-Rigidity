import Mathlib

/-!
# Slow mixing of the sandpile chain on the percolation cluster, with no literature input: comparator challenge

Mathlib-only comparator challenge for Theorem 6.5 (label `theorem:slow-mixing-percolation`) of
*Rigidity of harmonic functions on the supercritical percolation cluster* (Ahmed Bou-Rabee,
William Cooperman and Paul Dario), in the form whose only hypotheses are the regime `2 ≤ d`,
`p_c(d) < p < 1`.  The library's statement is `Rigidity.Assembly.Unconditional.slow_mixing` in
`Rigidity/Proofs/Assembly/Unconditional.lean`; the three cited results that
`RigidityAudit/SlowMixing/Challenge.lean` takes as hypotheses (supercritical uniqueness,
well-connected cubes and the smoothing parameter of Micciancio and Regev) are proved in the library.

**The result.**  Let `d ≥ 2` and `p_c(d) < p < 1`, and let `𝒞_∞` be the infinite cluster of
Bernoulli bond percolation of parameter `p` on `ℤ^d`.  There are constants `c, C > 0` such that,
almost surely, the infinite cluster exists and is unique, and for every `ε > 0` and every large
`n`: some largest open cluster `V` of the cube `Q_n` lies in `𝒞_∞`; and for every largest open
cluster `V` of `Q_n` that lies in `𝒞_∞` and meets the boundary of `Q_n`, the sandpile Markov
chain on `V` satisfies `‖P^t - U‖₂² ≤ ε` for every `t ≥ C n^d log n` and `‖P^t - U‖₂² ≥ ε` for
every `t ≤ c n^d log n`.  The chain and the distance are those of
`RigidityAudit/SlowMixing/Challenge.lean`.

This file imports only `Mathlib`: no repository module and no dependency.  Its vocabulary is that
of `RigidityAudit/SlowMixing/Challenge.lean` without the three cited results; the solution uses
`RigidityAudit/SlowMixing/SolutionBasic.lean`.  The sole intentional `sorry` is the proof of the
final theorem.
-/

namespace Rigidity
namespace StatementAudit
namespace SlowMixing

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

/-! ## The open graph (`LatticeProb/Prob/Percolation/LatticeBondGraph.lean`) -/

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

open MeasureTheory in
/-- The event that there is exactly one infinite open cluster. -/
def uniqueInfiniteComponentEvent (d : ℕ) : Set (Configuration d) :=
  {ω | HasUniqueInfiniteOpenComponent ω}

end UniqueCluster

/-! ## The sandpile chain on a cluster of the cube (`Rigidity/Draft/Section6Statements.lean`) -/

section Sandpile

open MeasureTheory Classical Filter

variable {d : ℕ}

/-- The cube `Q_n = {x : |x|_∞ ≤ n}`. -/
def cube (d : ℕ) (n : ℕ) : Set (Vertex d) := {x | ∀ i, |x i| ≤ (n : ℤ)}

/-- The open edges with both endpoints in `Q_n`. -/
def boxOpenGraph (ω : Configuration d) (n : ℕ) : SimpleGraph (Vertex d) where
  Adj x y := (openGraph ω).Adj x y ∧ x ∈ cube d n ∧ y ∈ cube d n
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => (openGraph ω).loopless.irrefl _ h.1⟩

/-- The open cluster of `x ∈ Q_n` inside `Q_n`. -/
def boxCluster (ω : Configuration d) (n : ℕ) (x : Vertex d) : Set (Vertex d) :=
  {y | (boxOpenGraph ω n).Reachable x y}

/-- `V` is a largest open cluster of `Q_n`. -/
def IsLargestBoxCluster (ω : Configuration d) (n : ℕ) (V : Finset (Vertex d)) : Prop :=
  (∃ x ∈ cube d n, (V : Set (Vertex d)) = boxCluster ω n x) ∧
    ∀ x ∈ cube d n, (boxCluster ω n x).ncard ≤ V.card

/-- The toppling Laplacian of `V`: `(Δ_V f)(x) = deg(x) f(x) - Σ_{y ∈ V, y ∼ x} f(y)`, with `deg`
the number of open edges at `x`. -/
noncomputable def toppling (ω : Configuration d) (V : Finset (Vertex d)) :
    (V → ℤ) →+ (V → ℤ) where
  toFun f x := ((openGraph ω).degree x.val : ℤ) * f x -
    ∑ y : V, if (openGraph ω).Adj x.val y.val then f y else 0
  map_zero' := by ext; simp
  map_add' f g := by
    ext x
    have : (∑ y : V, if (openGraph ω).Adj x.val y.val then f y + g y else 0) =
        (∑ y : V, if (openGraph ω).Adj x.val y.val then f y else 0) +
          ∑ y : V, if (openGraph ω).Adj x.val y.val then g y else 0 := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun y _ => by split_ifs <;> simp
    simp only [Pi.add_apply, this]
    ring

/-- The sandpile group `ℤ^V / Δ_V ℤ^V`. -/
abbrev SandpileGroup (ω : Configuration d) (V : Finset (Vertex d)) :=
  (V → ℤ) ⧸ (toppling ω V).range

/-- The law of the chain after `t` steps, started from the saturated sandpile `deg - 1`: the
proportion of the `|V|^t` sequences of chip sites `x₁, …, x_t` that lead to the class `g`. -/
noncomputable def chainLaw (ω : Configuration d) (V : Finset (Vertex d)) (t : ℕ)
    (g : SandpileGroup ω V) : ℝ :=
  ((Finset.univ.filter (fun w : Fin t → V =>
      (QuotientAddGroup.mk (fun x : V => ((openGraph ω).degree x.val : ℤ) - 1) +
        ∑ k, QuotientAddGroup.mk (Pi.single (w k) 1) : SandpileGroup ω V) = g)).card : ℝ) /
    (V.card : ℝ) ^ t

/-- `‖P^t - U‖₂² = |𝒢| Σ_g |P^t(g) - 1/|𝒢||²`. -/
noncomputable def l2DistSq (ω : Configuration d) (V : Finset (Vertex d)) (t : ℕ) : ℝ :=
  (Nat.card (SandpileGroup ω V) : ℝ) *
    ∑ᶠ g : SandpileGroup ω V,
      (chainLaw ω V t g - 1 / (Nat.card (SandpileGroup ω V) : ℝ)) ^ 2

end Sandpile
-- VOCABULARY-END

/-! ## The theorem -/

open MeasureTheory Classical Filter

/-- **Theorem 6.5** (`theorem:slow-mixing-percolation`): for `d ≥ 2` and `p_c(d) < p < 1` there
are `c, C > 0` such that, almost surely, the infinite cluster `𝒞_∞` exists and is unique, and for
every `ε > 0` and every large `n`, some largest open cluster `V` of `Q_n` lies in `𝒞_∞`, and for
every such `V` meeting the boundary of `Q_n` the sandpile chain on `V` satisfies
`‖P^t - U‖₂² ≤ ε` for `t ≥ C n^d log n` and `‖P^t - U‖₂² ≥ ε` for `t ≤ c n^d log n`.  The
regime is the only hypothesis. -/
theorem slow_mixing_unconditional (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᵐ ω ∂latticeBondLaw d p,
      ∃ h : HasUniqueInfiniteOpenComponent ω, ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
        (∃ V : Finset (Vertex d), IsLargestBoxCluster ω n V ∧
          ∀ x ∈ V, x ∈ (uniqueInfiniteComponent h).supp) ∧
        ∀ V : Finset (Vertex d), IsLargestBoxCluster ω n V →
          (∀ x ∈ V, x ∈ (uniqueInfiniteComponent h).supp) → (∃ x ∈ V, ∃ i, |x i| = (n : ℤ)) →
          (∀ t : ℕ, C * (n : ℝ) ^ d * Real.log n ≤ t → l2DistSq ω V t ≤ ε) ∧
          (∀ t : ℕ, (t : ℝ) ≤ c * (n : ℝ) ^ d * Real.log n → ε ≤ l2DistSq ω V t)
:= by
  sorry

end SlowMixing
end StatementAudit
end Rigidity
