import Mathlib

/-!
# Slow mixing of the sandpile chain on the percolation cluster: comparator challenge

Mathlib-only comparator challenge for Theorem 6.5 (label `theorem:slow-mixing-percolation`) of
*Rigidity of harmonic functions on the supercritical percolation cluster* (Ahmed Bou-Rabee,
William Cooperman and Paul Dario).  The library's statement is
`Rigidity.Assembly.Main.slowMixing` in `Rigidity/Proofs/Assembly/Main.lean`.

**The result.**  Let `d ≥ 2` and `p_c(d) < p < 1`, and let `𝒞_∞` be the infinite cluster of
Bernoulli bond percolation of parameter `p` on `ℤ^d`.  There are constants `c, C > 0` such that,
almost surely, the infinite cluster exists and is unique, and for every `ε > 0` and every large
`n`: some largest open cluster `V` of the cube `Q_n` lies in `𝒞_∞`; and for every largest open
cluster `V` of `Q_n` that lies in `𝒞_∞` and meets the boundary of `Q_n`, the sandpile Markov
chain on `V` satisfies `‖P^t - U‖₂² ≤ ε` for every `t ≥ C n^d log n` and `‖P^t - U‖₂² ≥ ε` for
every `t ≤ c n^d log n`.

The chain is the random walk on the sandpile group `ℤ^V / Δ_V ℤ^V` of `V`, started at the class of
the saturated sandpile `deg - 1`, whose steps are uniform over the classes of the unit chips
`1_x`, `x ∈ V`; here `deg x` is the number of open edges at `x`, and the toppling Laplacian `Δ_V`
moves one chip along each open edge, chips leaving `V` being lost.  `P^t` is the law of the chain
after `t` steps, `U` the uniform law on the group `𝒢`, and
`‖P^t - U‖₂² = |𝒢| ∑_g (P^t(g) - 1/|𝒢|)²`.  Ties for the largest cluster are covered by
quantifying over every largest cluster.

This file imports only `Mathlib`: no repository module and no dependency.  It rebuilds from
Mathlib primitives every definition needed to read the theorem.

* The lattice `Site d = Fin d → ℤ`, its unit vectors and nearest-neighbour graph `lattice d`.
* Bernoulli bond percolation: the bonds `Bond d`, the configurations `Configuration d`, the open
  graph `openGraph`, its components `OpenComponent`, the product law `latticeBondLaw`, the
  percolation probability `theta`, the critical probability `criticalProbability`, the event
  `HasUniqueInfiniteOpenComponent` and the infinite cluster `uniqueInfiniteComponent`.
* The cube `cube d n`, its largest open clusters `IsLargestBoxCluster`, the toppling Laplacian
  `toppling`, the sandpile group `SandpileGroup`, the law of the chain `chainLaw` and the distance
  `l2DistSq`.
* The three cited results the theorem takes as explicit hypotheses, each a `Prop`:
  - `SupercriticalBondUniqueness`: `0 < p_c(d) < 1` for `d ≥ 2`, and the infinite cluster exists
    and is unique almost surely for `p_c(d) < p < 1` (G. Grimmett, *Percolation*, 2nd ed., 1999,
    Theorems 1.10 and 8.1);
  - `WellConnectedInput`: a cube of radius `N` is well-connected outside an event of probability
    at most `C exp(-c N^s)` (A. Pisztora, Probab. Theory Related Fields 104 (1996), Theorem 3.2;
    M. D. Penrose and A. Pisztora, Adv. Appl. Probab. 28 (1996), Theorem 5; as recalled in
    P. Antal and A. Pisztora, Ann. Probab. 24 (1996), equation (2.24));
  - `MicciancioRegevSmoothing`: the bound `η_ε(Λ) ≤ √(log(2k(1 + 1/ε))/π) · λ_k(Λ)` on the
    smoothing parameter of a lattice of rank `k` (D. Micciancio and O. Regev, SIAM J. Comput. 37
    (2007), Lemma 3.3).

The definitions are statement-level copies of the library's, token for token; a proof field
inside a definition may be proved differently, which does not change the definition up to
proof irrelevance.  The sole intentional `sorry` is the proof of the final theorem.

The vocabulary between `VOCABULARY-BEGIN` and `VOCABULARY-END` is copied verbatim into
`SolutionBasic.lean`; the two must stay byte-identical so that the comparator's
constant-by-constant closure check passes.
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

/-! ## Cited result: supercritical uniqueness
(`LatticeProb/External/SupercriticalBondUniquenessInput.lean`) -/

/-- **Grimmett, *Percolation* (2nd ed., 1999), Theorems 1.10 and 8.1** (literature input).  For
`d ≥ 2`, `0 < p_c(d) < 1`; for `p_c(d) < p < 1`, almost surely there is exactly one infinite
open cluster. -/
def SupercriticalBondUniqueness : Prop :=
  (∀ (d : ℕ) [NeZero d], 2 ≤ d →
    0 < criticalProbability d ∧ criticalProbability d < 1) ∧
  (∀ (d : ℕ) [NeZero d], 2 ≤ d → ∀ p : unitInterval,
    criticalProbability d < (p : ℝ) → (p : ℝ) < 1 →
      latticeBondLaw d p (uniqueInfiniteComponentEvent d) = 1)

/-! ## Cited result: well-connected cubes (`Rigidity/External/WellConnected.lean`) -/

section WellConnected

open MeasureTheory Classical

variable {d : ℕ}

/-- The cube `x + Q_r`. -/
def cubeAt (x : Vertex d) (r : ℕ) : Set (Vertex d) := {y | ∀ i, |y i - x i| ≤ (r : ℤ)}

/-- The open edges with both endpoints in `B`. -/
def openIn (ω : Configuration d) (B : Set (Vertex d)) : SimpleGraph (Vertex d) where
  Adj y z := (openGraph ω).Adj y z ∧ y ∈ B ∧ z ∈ B
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => (openGraph ω).loopless.irrefl _ h.1⟩

/-- `V` is a largest open cluster of the finite set `B`. -/
def IsLargestClusterIn (ω : Configuration d) (B V : Set (Vertex d)) : Prop :=
  (∃ x ∈ B, V = {y | (openIn ω B).Reachable x y}) ∧
    ∀ x ∈ B, {y | (openIn ω B).Reachable x y}.ncard ≤ V.ncard

/-- `V` meets both faces of `z + Q_r` in every coordinate direction. -/
def CrossesCube (z : Vertex d) (r : ℕ) (V : Set (Vertex d)) : Prop :=
  ∀ i : Fin d, (∃ y ∈ V, y i = z i - r) ∧ (∃ y ∈ V, y i = z i + r)

/-- `z + Q_r` is crossing: a largest open cluster of it crosses it. -/
def IsCrossingCube (ω : Configuration d) (z : Vertex d) (r : ℕ) : Prop :=
  ∃ V, IsLargestClusterIn ω (cubeAt z r) V ∧ CrossesCube z r V

/-- `z + Q_M` is a good subcube: it is crossed by a largest open cluster to which every open path
of length at least `M/100` in the cube is connected inside the cube. -/
def IsGoodSubcube (ω : Configuration d) (z : Vertex d) (M : ℕ) : Prop :=
  ∃ V, IsLargestClusterIn ω (cubeAt z M) V ∧ CrossesCube z M V ∧
    ∀ (n : ℕ) (γ : Fin (n + 1) → Vertex d), Function.Injective γ →
      (∀ i : Fin n, (openIn ω (cubeAt z M)).Adj (γ i.castSucc) (γ i.succ)) →
      (M : ℝ) / 100 ≤ n → ∃ y ∈ V, (openIn ω (cubeAt z M)).Reachable (γ 0) y

/-- `x + Q_R` is well-connected: `R^{1/(10d)²} ≤ R/100`, the cube is crossing, and every cube of
radius `M ∈ [R^{1/(10d)²}/2, R/10]` meeting it is a good subcube. -/
def IsWellConnected (ω : Configuration d) (x : Vertex d) (R : ℕ) : Prop :=
  (R : ℝ) ^ (1 / (10 * (d : ℝ)) ^ 2) ≤ R / 100 ∧ IsCrossingCube ω x R ∧
    ∀ (z : Vertex d) (M : ℕ), (R : ℝ) ^ (1 / (10 * (d : ℝ)) ^ 2) / 2 ≤ M → (M : ℝ) ≤ R / 10 →
      (cubeAt z M ∩ cubeAt x R).Nonempty → IsGoodSubcube ω z M

/-- **Pisztora (1996), Theorem 3.2; Penrose and Pisztora (1996), Theorem 5** (literature input;
Proposition 2.3 of the paper).  For `d ≥ 2` and `p_c(d) < p < 1` there are `c, C > 0` and
`s > 0` such that every cube `x + Q_N` is well-connected outside an event of probability at most
`C exp(-c N^s)`. -/
def WellConnectedInput : Prop :=
  ∀ (d : ℕ) [NeZero d], 2 ≤ d → ∀ p : unitInterval,
    criticalProbability d < (p : ℝ) → (p : ℝ) < 1 →
    ∃ c C s : ℝ, 0 < c ∧ 0 < C ∧ 0 < s ∧ ∀ (x : Vertex d) (N : ℕ),
      latticeBondLaw d p {ω | ¬ IsWellConnected ω x N} ≤
        ENNReal.ofReal (C * Real.exp (-(c * (N : ℝ) ^ s)))

end WellConnected

/-! ## Cited result: the smoothing parameter (`Rigidity/External/SmoothingParameter.lean`) -/

/-- The dual of the lattice generated over `ℤ` by `b`: the vectors of the real span of `b` whose
inner product with every `b i` is an integer. -/
def dualLattice {N k : ℕ} (b : Fin k → EuclideanSpace ℝ (Fin N)) :
    Set (EuclideanSpace ℝ (Fin N)) :=
  {y | y ∈ Submodule.span ℝ (Set.range b) ∧ ∀ i, ∃ z : ℤ, inner ℝ y (b i) = z}

/-- **Micciancio and Regev (2007), Lemma 3.3** (literature input).  For the lattice generated by
`k` linearly independent vectors of length at most `r`, the Gaussian sum
`∑_{y ∈ Λ* ∖ 0} exp(-π s² ‖y‖²)` over its nonzero dual vectors is at most `ε` once
`s ≥ √(log(2k(1 + 1/ε))/π) · r`. -/
def MicciancioRegevSmoothing : Prop :=
  ∀ (N k : ℕ) (b : Fin k → EuclideanSpace ℝ (Fin N)), LinearIndependent ℝ b →
    ∀ r : ℝ, (∀ i, ‖b i‖ ≤ r) → ∀ ε : ℝ, 0 < ε → ∀ s : ℝ,
      Real.sqrt (Real.log (2 * k * (1 + 1 / ε)) / Real.pi) * r ≤ s →
      Summable (fun y : {y // y ∈ dualLattice b ∧ y ≠ 0} =>
          Real.exp (-(Real.pi * s ^ 2 * ‖(y : EuclideanSpace ℝ (Fin N))‖ ^ 2))) ∧
        ∑' y : {y // y ∈ dualLattice b ∧ y ≠ 0},
          Real.exp (-(Real.pi * s ^ 2 * ‖(y : EuclideanSpace ℝ (Fin N))‖ ^ 2)) ≤ ε

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
`‖P^t - U‖₂² ≤ ε` for `t ≥ C n^d log n` and `‖P^t - U‖₂² ≥ ε` for `t ≤ c n^d log n`.  The three
cited results enter as explicit hypotheses. -/
theorem slow_mixing (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : SupercriticalBondUniqueness)
    (hW : WellConnectedInput)
    (hMR : MicciancioRegevSmoothing) :
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
