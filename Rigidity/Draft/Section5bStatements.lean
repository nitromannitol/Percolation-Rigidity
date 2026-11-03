import Rigidity.Draft.Section5Statements
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Convex.Segment
import Mathlib.Topology.Connected.Basic

/-! Statements of the numbered results of Section 5.3.1-5.3.2 (unbounded level sets and
large biconnected components of the potential, d = 2).

These results live in the standing context of Sections 5.3-5.4: the event `Σ f = 0`,
`|supp u_f| = ∞`, on which `u_f` decays to zero. They are stated for every `u` with `-Δu = f` on
`𝒞_∞` and `u → 0` at infinity (the potential normalized at infinity, see `Section5Statements`)
whose support is infinite. Graph notions (paths, connected and biconnected sets, components) are
those of `𝒞_∞` restricted to the set in question; "disjoint" paths are vertex-disjoint; `Q_r` is
the cube of radius `r`.

Convention: like every `...Stmt` of the draft, the statements below omit the paper's standing
assumption `p_c(d) < p < 1` (corrected draft L66, L231); the composed theorems in
`Rigidity/Proofs/Assembly` carry it as hypotheses (`criticalProbability 2 < p`, `p < 1`, or the
part of it they use). Read alone, outside that regime, a statement may be false. -/

open MeasureTheory LatticeProb.Percolation Classical Filter Topology

namespace Rigidity.Section5

variable {ω : Configuration 2}

/-- The potential normalized at infinity: `-Δu = f` on `𝒞_∞` and `u(x) → 0`. -/
def IsDecayingPotential (C : OpenComponent ω) (f : Vertex 2 → ℤ) (u : C → ℝ) : Prop :=
  (∀ x, -componentLaplacian C u x = f x.val) ∧ Tendsto u cofinite (𝓝 0)

/-- The level set `L_a = {x ∈ 𝒞_∞ : u(x) = a}`. -/
def levelSet {C : OpenComponent ω} (u : C → ℝ) (a : ℝ) : Set C := {x | u x = a}

/-- The cube `Q_r = {x : |x|_∞ ≤ r}`. -/
def cube (r : ℕ) : Set (Vertex 2) := {x | ∀ i, |x i| ≤ (r : ℤ)}

/-- `x` and `y` are joined by a path of `𝒞_∞` inside `S`. -/
def JoinedIn (C : OpenComponent ω) (S : Set C) (x y : C) : Prop :=
  ∃ hx : x ∈ S, ∃ hy : y ∈ S, ((componentGraph C).induce S).Reachable ⟨x, hx⟩ ⟨y, hy⟩

/-- `T` is a connected component of `S`. -/
def IsComponentOf (C : OpenComponent ω) (S T : Set C) : Prop :=
  ∃ x ∈ S, T = {y | JoinedIn C S x y}

/-- `S` is connected. -/
def IsConnectedSet (C : OpenComponent ω) (S : Set C) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, JoinedIn C S x y

/-- `S` is biconnected: connected, and connected after removing any one of its vertices. -/
def IsBiconnected (C : OpenComponent ω) (S : Set C) : Prop :=
  IsConnectedSet C S ∧ ∀ x ∈ S, IsConnectedSet C (S \ {x})

/-- An infinite path of `𝒞_∞` inside `S`. -/
def IsInfinitePathIn (C : OpenComponent ω) (S : Set C) (γ : ℕ → C) : Prop :=
  Function.Injective γ ∧ (∀ n, (componentGraph C).Adj (γ n) (γ (n + 1))) ∧ ∀ n, γ n ∈ S

/-- `S` contains `k` disjoint infinite paths. -/
def HasDisjointInfinitePaths (C : OpenComponent ω) (S : Set C) (k : ℕ) : Prop :=
  ∃ γ : Fin k → ℕ → C, (∀ j, IsInfinitePathIn C S (γ j)) ∧
    ∀ j j', j ≠ j' → Disjoint (Set.range (γ j)) (Set.range (γ j'))

/-- There are `k` disjoint paths of `𝒞_∞` connecting `S` to infinity. -/
def HasDisjointPathsToInfinity (C : OpenComponent ω) (S : Set C) (k : ℕ) : Prop :=
  ∃ γ : Fin k → ℕ → C, (∀ j, IsInfinitePathIn C Set.univ (γ j) ∧ γ j 0 ∈ S) ∧
    ∀ j j', j ≠ j' → Disjoint (Set.range (γ j)) (Set.range (γ j'))

/-- Proposition 5.12: a connected component of `L_0` contains at most `|supp f| + 2` disjoint
infinite paths. -/
def InfiniteDisjointPathsStmt (p : unitInterval) (f : Vertex 2 → ℤ) : Prop :=
  (Function.support f).Finite →
  ∀ᵐ ω ∂latticeBondLaw 2 p, ∃ h : HasUniqueInfiniteOpenComponent ω,
    ∀ u, IsDecayingPotential (uniqueInfiniteComponent h) f u → (Function.support u).Infinite →
    ∀ S, IsComponentOf _ (levelSet u 0) S →
      ¬ HasDisjointInfinitePaths _ S ((Function.support f).ncard + 3)

/-- The point `x` of `ℤ²` as a complex number. -/
def toComplex (x : Vertex 2) : ℂ := ⟨x 0, x 1⟩

/-- The winding number around the origin of the closed lattice path `γ 0, γ 1, …, γ n, γ 0`
avoiding the origin: the sum of the angle increments `arg (γ(i+1) / γ(i)) ∈ (-π, π]` over `2π`. -/
noncomputable def windingNumber {n : ℕ} (γ : Fin (n + 1) → Vertex 2) : ℝ :=
  (∑ i : Fin (n + 1), Complex.arg (toComplex (γ (i + 1)) / toComplex (γ i))) / (2 * Real.pi)

/-- Lemma 5.14: almost surely there is a scale `M` such that for every `R ≥ M` the cluster
contains a loop in `Q_{2R} \ Q_R` with nonzero winding number around the origin. -/
def LoopsAroundAnnuliStmt (p : unitInterval) : Prop :=
  ∀ᵐ ω ∂latticeBondLaw 2 p, ∃ h : HasUniqueInfiniteOpenComponent ω, ∃ M : ℕ, ∀ R : ℕ, M ≤ R →
    ∃ n : ℕ, ∃ γ : Fin (n + 1) → uniqueInfiniteComponent h,
      (∀ i, (componentGraph _).Adj (γ i) (γ (i + 1))) ∧
      (∀ i, (γ i).val ∈ cube (2 * R) \ cube R) ∧ windingNumber (fun i => (γ i).val) ≠ 0

/-- The outer boundary `∂Ω` of `Ω` in `𝒞_∞`. -/
def outerBoundary (C : OpenComponent ω) (Ω : Set C) : Set C :=
  {x | x ∉ Ω ∧ ∃ y ∈ Ω, (componentGraph C).Adj x y}

/-- Lemma 5.16 (strong maximum principle in two dimensions): if `g` is bounded on `𝒞_∞` and
harmonic on an infinite `Ω ≠ 𝒞_∞`, then `g ≤ M` on `∂Ω` implies `g ≤ M` on `Ω`. -/
def StrongMaxPrincipleStmt (p : unitInterval) : Prop :=
  ∀ᵐ ω ∂latticeBondLaw 2 p, ∃ h : HasUniqueInfiniteOpenComponent ω,
    ∀ Ω : Set (uniqueInfiniteComponent h), Ω.Infinite → Ω ≠ Set.univ →
    ∀ g : uniqueInfiniteComponent h → ℝ, (∃ B, ∀ x, |g x| ≤ B) →
      (∀ x ∈ Ω, componentLaplacian _ g x = 0) →
    ∀ M : ℝ, (∀ x ∈ outerBoundary _ Ω, g x ≤ M) → ∀ x ∈ Ω, g x ≤ M

/-- Lemma 5.17: every connected component of `{u > a}` meets the support of `f` (a pole). -/
def PolesSuperLevelSetsStmt (p : unitInterval) (f : Vertex 2 → ℤ) : Prop :=
  (Function.support f).Finite →
  ∀ᵐ ω ∂latticeBondLaw 2 p, ∃ h : HasUniqueInfiniteOpenComponent ω,
    ∀ u, IsDecayingPotential (uniqueInfiniteComponent h) f u → (Function.support u).Infinite →
    ∀ a : ℝ, ∀ T, IsComponentOf _ {x | a < u x} T → ∃ y ∈ T, f y.val ≠ 0

/-- Lemma 5.18: if `supp f ⊆ Q_R` and `R' > R`, a path of `𝒞_∞` from `Q_R` to the complement of
`Q_{R'}` avoids the zero set of `u`. -/
def LongNonzeroPathsStmt (p : unitInterval) (f : Vertex 2 → ℤ) : Prop :=
  (Function.support f).Finite →
  ∀ᵐ ω ∂latticeBondLaw 2 p, ∃ h : HasUniqueInfiniteOpenComponent ω,
    ∀ u, IsDecayingPotential (uniqueInfiniteComponent h) f u →
    ∀ R : ℕ, 0 < R → (∀ x, f x ≠ 0 → x ∈ cube R) → ∀ R' : ℕ, R < R' →
      (Function.support u).Infinite →
      ∃ n : ℕ, ∃ γ : Fin (n + 1) → uniqueInfiniteComponent h,
        (∀ i : Fin n, (componentGraph _).Adj (γ i.castSucc) (γ i.succ)) ∧
        (γ 0).val ∈ cube R ∧ (γ (Fin.last n)).val ∉ cube R' ∧ ∀ i, u (γ i) ≠ 0

/-- The trace in `ℝ²` of a bi-infinite lattice path: the union of its unit segments. -/
def pathTrace {C : OpenComponent ω} (γ : ℤ → C) : Set (EuclideanSpace ℝ (Fin 2)) :=
  ⋃ n : ℤ, segment ℝ (latticeEuclideanEmbedding (γ n).val)
    (latticeEuclideanEmbedding (γ (n + 1)).val)

/-- Lemma 5.19: almost surely, `supp u` infinite excludes a bi-infinite path `γ ⊆ L_0` such that
the cluster points of one connected component of `ℝ² \ γ` all lie in `L_0`. -/
def NoThickPathsStmt (p : unitInterval) (f : Vertex 2 → ℤ) : Prop :=
  (Function.support f).Finite →
  ∀ᵐ ω ∂latticeBondLaw 2 p, ∃ h : HasUniqueInfiniteOpenComponent ω,
    ∀ u, IsDecayingPotential (uniqueInfiniteComponent h) f u →
      ¬ ((Function.support u).Infinite ∧
        ∃ γ : ℤ → uniqueInfiniteComponent h, Function.Injective γ ∧
          (∀ n, (componentGraph _).Adj (γ n) (γ (n + 1))) ∧ (∀ n, u (γ n) = 0) ∧
          ∃ z ∉ pathTrace γ, ∀ x : uniqueInfiniteComponent h,
            latticeEuclideanEmbedding x.val ∈ connectedComponentIn (pathTrace γ)ᶜ z → u x = 0)

/-- `T` is a connected component of `A ⊆ ℤ²` for the nearest-neighbour lattice. -/
def IsLatticeComponentOf (A T : Set (Vertex 2)) : Prop :=
  ∃ x ∈ A, T = {y | ∃ hx : x ∈ A, ∃ hy : y ∈ A,
    ((nearestNeighborGraph 2).induce A).Reachable ⟨x, hx⟩ ⟨y, hy⟩}

/-- Proposition 5.20: there is `C_f ∈ ℕ`, depending only on `f`, with `supp f ⊆ Q_{C_f/2}` and
such that for every `a` and every biconnected `S ⊆ L_a` whose complement in `ℤ²` has no finite
connected component meeting `supp f`, at most `C_f` disjoint paths connect `S` to infinity. -/
def BoundarySizeStmt (p : unitInterval) (f : Vertex 2 → ℤ) : Prop :=
  (Function.support f).Finite →
  ∃ Cf : ℕ, (∀ x, f x ≠ 0 → x ∈ cube (Cf / 2)) ∧
  ∀ᵐ ω ∂latticeBondLaw 2 p, ∃ h : HasUniqueInfiniteOpenComponent ω,
    ∀ u, IsDecayingPotential (uniqueInfiniteComponent h) f u → (Function.support u).Infinite →
    ∀ a : ℝ, ∀ S : Set (uniqueInfiniteComponent h), S ⊆ levelSet u a → IsBiconnected _ S →
      (∀ T, IsLatticeComponentOf (Subtype.val '' S)ᶜ T → T.Finite → ∀ x ∈ T, f x = 0) →
      ¬ HasDisjointPathsToInfinity _ S (Cf + 1)

end Rigidity.Section5
