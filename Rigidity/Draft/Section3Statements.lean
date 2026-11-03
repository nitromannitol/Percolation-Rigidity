import LatticeProb.Prob.Percolation.LatticeClusterLipschitz
import LatticeProb.Prob.Percolation.CorrectedPlaneCharacterization
import LatticeProb.Prob.Percolation.GreenColumn
import LatticeProb.Prob.Percolation.LatticeUniqueCluster

/-! Statements of the numbered results of Section 3 (Lipschitz harmonic functions). The cited
literature inputs that each proof uses are added as explicit hypotheses of the final theorems;
these definitions are the statements themselves.

* Convention: the statements (`…Stmt`) omit the regime `p_c(d) < p < 1`; the composed theorems
  (`Rigidity/Proofs/Assembly`) carry it as hypotheses `criticalProbability d < p` and `p < 1`.
* "With positive probability", for an event that quantifies over corrected planes (not shown
  measurable), is stated in the inner-measure form of Section 5c: the event contains a measurable
  event of positive probability (Proposition 3.2). -/

open MeasureTheory LatticeProb.Percolation Classical

namespace Rigidity.Section3

variable {d : ℕ}

/-- The first coordinate direction `e₁`, as a slope. -/
def slopeE1 (d : ℕ) [NeZero d] : Fin d → ℝ := Pi.single 0 1

/-- `u` is `L`-Lipschitz for the graph distance of the component. -/
def IsLipschitzWith {ω : Configuration d} (C : OpenComponent ω) (L : ℝ) (u : C → ℝ) : Prop :=
  ∀ x y : C, |u x - u y| ≤ L * ((componentGraph C).dist x y : ℝ)

/-- `|∇u(0)|`, the `ℓ¹` norm of the vector of differences `u(0) - u(e_i)` over the open edges
`(0, e_i)`, for a component that contains the origin. -/
noncomputable def originGradientNorm {ω : Configuration d} (C : OpenComponent ω)
    (ho : (0 : Vertex d) ∈ C.supp) (u : C → ℝ) : ℝ :=
  ∑ i : Fin d,
    if hi : (openGraph ω).Adj 0 (LatticeProb.unit i) then
      |u ⟨0, ho⟩ - u ⟨LatticeProb.unit i, C.mem_supp_of_adj_mem_supp ho hi⟩|
    else 0

/-- A function on a component, extended by zero to every vertex of the lattice. -/
noncomputable def extend {ω : Configuration d} (C : OpenComponent ω) (u : C → ℝ) :
    Vertex d → ℝ :=
  fun z => if h : z ∈ C.supp then u ⟨z, h⟩ else 0

/-- The configuration in which the bonds of `B` are closed. -/
def closeBonds (B : Finset (Bond d)) (ω : Configuration d) : Configuration d :=
  fun e => if e ∈ B then false else ω e

/-- Theorem 1.1: almost surely, every Lipschitz harmonic function on the infinite cluster is
constant. -/
def LipschitzStmt (d : ℕ) [NeZero d] (p : unitInterval) : Prop :=
  ∀ᵐ ω ∂latticeBondLaw d p,
    ∃ h : HasUniqueInfiniteOpenComponent ω,
      ∀ u : uniqueInfiniteComponent h → ℝ,
        (∀ x, componentLaplacian (uniqueInfiniteComponent h) u x = 0) →
        ComponentLipschitz (uniqueInfiniteComponent h) u →
        ∃ c : ℝ, ∀ x, u x = c

/-- Lemma 3.1: if, with positive probability, there is a non-constant Lipschitz harmonic function
on the infinite cluster, then for a deterministic `L > 0` the corrected plane of slope `e₁` is
almost surely `L`-Lipschitz. -/
def ReductionToSlopeE1Stmt (d : ℕ) [NeZero d] (p : unitInterval) : Prop :=
  latticeBondLaw d p {ω | ∃ h : HasUniqueInfiniteOpenComponent ω,
      ∃ u : uniqueInfiniteComponent h → ℝ,
        (∀ x, componentLaplacian (uniqueInfiniteComponent h) u x = 0) ∧
        ComponentLipschitz (uniqueInfiniteComponent h) u ∧ ∃ x y, u x ≠ u y} ≠ 0 →
  ∃ L : ℝ, 0 < L ∧ ∀ᵐ ω ∂latticeBondLaw d p, ∃ h : HasUniqueInfiniteOpenComponent ω,
    ∀ u, IsCorrectedPlane (uniqueInfiniteComponent h) (slopeE1 d) u →
      IsLipschitzWith (uniqueInfiniteComponent h) L u

/-- Proposition 3.2: for every `L ≥ 1`, with positive probability the origin is in the infinite
cluster and `|∇ℓ_{e₁}(0)| > L`; consequently `ℓ_{e₁}` is not `L`-Lipschitz with positive
probability. Both events quantify over corrected planes; "with positive probability" is the
inner-measure form (each contains a measurable event of positive probability), as Lemma 5.25 uses
it (the outer-measure form `latticeBondLaw d p {…} ≠ 0` is weaker). -/
def NotLipschitzStmt (d : ℕ) [NeZero d] (p : unitInterval) : Prop :=
  ∀ L : ℝ, 1 ≤ L →
    (∃ A ⊆ {ω | ∃ h : HasUniqueInfiniteOpenComponent ω,
        ∃ ho : (0 : Vertex d) ∈ (uniqueInfiniteComponent h).supp,
        ∃ u, IsCorrectedPlane (uniqueInfiniteComponent h) (slopeE1 d) u ∧
          L < originGradientNorm (uniqueInfiniteComponent h) ho u},
      MeasurableSet A ∧ 0 < latticeBondLaw d p A) ∧
    (∃ A ⊆ {ω | ∃ h : HasUniqueInfiniteOpenComponent ω,
        ∃ u, IsCorrectedPlane (uniqueInfiniteComponent h) (slopeE1 d) u ∧
          ¬ IsLipschitzWith (uniqueInfiniteComponent h) L u},
      MeasurableSet A ∧ 0 < latticeBondLaw d p A)

/-- The summand of Lemma 3.3 for a removed edge `{x, y}`, where `g x z` is the Green function at
`z` with pole `x`: its mixed gradient along `(a, b)` and `(x, y)` times `w y - w x`. It is
symmetric in `x` and `y`. -/
noncomputable def compareSummand (g : Vertex d → Vertex d → ℝ) (w : Vertex d → ℝ)
    (a b : Vertex d) : Sym2 (Vertex d) → ℝ :=
  Sym2.lift ⟨fun x y => ((g x a - g y a) - (g x b - g y b)) * (w y - w x),
    fun x y => by ring⟩

/-- Lemma 3.3: almost surely, for every finite set `B` of edges of the infinite cluster whose
removal does not disconnect it, the corrected planes of every slope are well-defined (up to an
additive constant) on the cluster and on the cluster without `B`, and their gradients differ by
the sum over `B` of the mixed gradient of the cluster's Green function. -/
def CompareDifferentPlanesStmt (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval) : Prop :=
  ∀ᵐ ω ∂latticeBondLaw d p, ∃ h : HasUniqueInfiniteOpenComponent ω,
    ∀ B : Finset (Bond d),
      (∀ e ∈ B, ω e = true ∧ ∀ z ∈ (e : Sym2 (Vertex d)), z ∈ (uniqueInfiniteComponent h).supp) →
      (∀ x ∈ (uniqueInfiniteComponent h).supp, ∀ y ∈ (uniqueInfiniteComponent h).supp,
        (openGraph (closeBonds B ω)).Reachable x y) →
      ∃ h' : HasUniqueInfiniteOpenComponent (closeBonds B ω),
        (uniqueInfiniteComponent h').supp = (uniqueInfiniteComponent h).supp ∧
        (∃ G : uniqueInfiniteComponent h → uniqueInfiniteComponent h → ℝ,
          ∀ y, IsGreenColumn d hd (uniqueInfiniteComponent h) y (G y)) ∧
        ∀ q : Fin d → ℝ,
          (∃ u, IsCorrectedPlane (uniqueInfiniteComponent h) q u) ∧
          (∀ u v, IsCorrectedPlane (uniqueInfiniteComponent h) q u →
            IsCorrectedPlane (uniqueInfiniteComponent h) q v → ∃ c : ℝ, ∀ x, u x = v x + c) ∧
          (∃ u', IsCorrectedPlane (uniqueInfiniteComponent h') q u') ∧
          (∀ u' v', IsCorrectedPlane (uniqueInfiniteComponent h') q u' →
            IsCorrectedPlane (uniqueInfiniteComponent h') q v' → ∃ c : ℝ, ∀ x, u' x = v' x + c) ∧
          ∀ u u', IsCorrectedPlane (uniqueInfiniteComponent h) q u →
            IsCorrectedPlane (uniqueInfiniteComponent h') q u' →
            ∀ G : uniqueInfiniteComponent h → uniqueInfiniteComponent h → ℝ,
              (∀ y, IsGreenColumn d hd (uniqueInfiniteComponent h) y (G y)) →
              ∀ a b : uniqueInfiniteComponent h,
                (componentGraph (uniqueInfiniteComponent h)).Adj a b →
                (u a - u b) - (extend _ u' a.val - extend _ u' b.val) =
                  ∑ e ∈ B, compareSummand
                    (fun x z => extend _ (fun y => if hx : x ∈ (uniqueInfiniteComponent h).supp
                      then G ⟨x, hx⟩ y else 0) z)
                    (extend _ u') a.val b.val e.val

end Rigidity.Section3
