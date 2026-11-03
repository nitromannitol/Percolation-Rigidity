import LatticeProb.Prob.Percolation.LatticeBondCritical
import LatticeProb.Prob.Percolation.LatticeUniqueCluster
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Statement of Theorem 6.5 (slow mixing of the sandpile Markov chain on the cluster).

* The chain is stated as the random walk on the sandpile group `ℤ^V / Δ_V ℤ^V` of the largest
  cluster `V = 𝒞_*(Q_n)`, started at the class of the saturated sandpile `deg - 1`, with steps
  uniform over the classes of the unit chips `1_x`, `x ∈ V`. This is how Section 6.1 describes
  the chain (a random walk on the group of recurrent sandpiles), and the norm `‖·‖₂` of the theorem
  is defined there for measures on that group; the identification of the recurrent sandpiles with
  the group is Dhar's theorem. `Δ_V` is the Laplacian of the chain's toppling rule: a site of `V`
  loses `deg_{𝒞_∞}` chips and sends one along each open edge, chips leaving `V` being lost.
* The paper restricts to the event `𝒞_*(Q_n) ⊂ 𝒞_∞ ∩ Q_n` and `∂Q_n ∩ 𝒞_*(Q_n) ≠ ∅`. The
  statement asserts that, almost surely, for every large `n` some largest cluster `V` of `Q_n` lies
  in `𝒞_∞` (Proposition 2.3 with Borel-Cantelli), and the
  bounds are stated for every such `V` that meets `∂Q_n` (implied by `V ⊂ 𝒞_∞`, `V ≠ ∅`). Ties for
  the largest cluster, broken "in a deterministic fashion" in the paper, are covered by quantifying
  over every largest cluster.
* `Q_n` is the cube of radius `n`, as in the notation section.
* The proof's eigenvalue `1 - 2/m` of the gadget of Figure 8 is `1 - 4/m` (the multiplicative
  harmonic function equals `-1` at two sites); the constants of the theorem absorb this.
* Convention: like every `...Stmt` of the draft, `SlowMixingStmt` omits the standing assumption
  `p_c(d) < p < 1` (and `2 ≤ d`) of the paper (corrected draft L66, L231); the composed theorem
  (`Rigidity.Assembly.slowMixing`) carries it as hypotheses `hpc`, `hp1`. Read alone, outside
  that regime, the statement may be false. -/

open MeasureTheory LatticeProb.Percolation Classical Filter

namespace Rigidity.Section6

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

/-- `V` is a largest open cluster of `Q_n`: `V = 𝒞_*(Q_n)` for some tie-breaking. -/
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
proportion of the `|V|^t` sequences of chip sites `x₁, …, x_t` that end in the class `g`. -/
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

/-- Theorem 6.5: there are `c, C > 0` such that almost surely, for every `ε > 0` and every large
`n`, some largest open cluster `V` of `Q_n` lies in `𝒞_∞`, and for every such `V` meeting `∂Q_n`,
`‖P^t - U‖₂² ≤ ε` for `t ≥ C n^d log n` and `‖P^t - U‖₂² ≥ ε` for `t ≤ c n^d log n`. -/
def SlowMixingStmt (d : ℕ) [NeZero d] (p : unitInterval) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᵐ ω ∂latticeBondLaw d p,
    ∃ h : HasUniqueInfiniteOpenComponent ω, ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      (∃ V : Finset (Vertex d), IsLargestBoxCluster ω n V ∧
        ∀ x ∈ V, x ∈ (uniqueInfiniteComponent h).supp) ∧
      ∀ V : Finset (Vertex d), IsLargestBoxCluster ω n V →
        (∀ x ∈ V, x ∈ (uniqueInfiniteComponent h).supp) → (∃ x ∈ V, ∃ i, |x i| = (n : ℤ)) →
        (∀ t : ℕ, C * (n : ℝ) ^ d * Real.log n ≤ t → l2DistSq ω V t ≤ ε) ∧
        (∀ t : ℕ, (t : ℝ) ≤ c * (n : ℝ) ^ d * Real.log n → ε ≤ l2DistSq ω V t)

end Rigidity.Section6
