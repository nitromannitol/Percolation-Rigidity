import Rigidity.Draft.Section5bStatements

/-! # Section 5: shared step propositions
Definitions only; the proofs live in `Rigidity/Proofs/Section5/`. -/

open MeasureTheory LatticeProb.Percolation Classical Filter Topology

namespace Rigidity.Steps.Section5

open Rigidity.Section5

/-- Almost surely the infinite open cluster exists and is unique. -/
def UniqueClusterAe (p : unitInterval) : Prop :=
  ∀ᵐ ω ∂latticeBondLaw 2 p, HasUniqueInfiniteOpenComponent ω

/-- The planar Green function `Ḡ(x) = -log |x|₂ / (2πκ)` at a lattice point (`Real.log 0 = 0`). -/
noncomputable def greenLog (κ : {a : ℝ // 0 < a}) (x : Vertex 2) : ℝ :=
  -Real.log (eucl x) / (2 * Real.pi * κ.val)

/-- Almost surely a Green family of the cluster exists. -/
def GreenFamilyExists (p : unitInterval) : Prop :=
  ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω,
    ∃ G, IsGreenFamily (uniqueInfiniteComponent h) G

/-- Potential asymptotics (Dario-Gu Thm 2, d = 2): `u_f - (Σ f) Ḡ` converges at infinity, to a
limit independent of the Green family. -/
def PotentialAsymptotic (p : unitInterval) : Prop :=
  ∃ κ : {a : ℝ // 0 < a}, ∀ f : Vertex 2 → ℤ, (Function.support f).Finite →
    ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω, ∃ L : ℝ,
      ∀ G, IsGreenFamily (uniqueInfiniteComponent h) G →
        Tendsto (fun x => potential (uniqueInfiniteComponent h) G f x -
          (mass (uniqueInfiniteComponent h) f : ℝ) * greenLog κ x.val) cofinite (𝓝 L)

/-- The potential normalized at infinity ([C3], [C13], [C14]): for `Σ f = 0`, `u_f` converges at
infinity, to a limit independent of the Green family. -/
def PotentialLimit (p : unitInterval) : Prop :=
  ∀ f : Vertex 2 → ℤ, (Function.support f).Finite →
    ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω,
      mass (uniqueInfiniteComponent h) f = 0 → ∃ L : ℝ,
        ∀ G, IsGreenFamily (uniqueInfiniteComponent h) G →
          Tendsto (potential (uniqueInfiniteComponent h) G f) cofinite (𝓝 L)

/-- Liouville, order zero: almost surely, harmonic functions of sublinear growth are constant. -/
def SublinearLiouville (p : unitInterval) : Prop :=
  ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω,
    ∀ v : uniqueInfiniteComponent h → ℝ, (∀ x, componentLaplacian _ v x = 0) →
      (∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ x : uniqueInfiniteComponent h,
        R ≤ eucl x.val → |v x| ≤ ε * eucl x.val) →
      ∃ c : ℝ, ∀ x, v x = c

/-- Finite maximum principle on an infinite open component: a function harmonic on a finite set
`Ω` is bounded on `Ω` by any upper bound on its outer boundary. -/
def FiniteMaxPrinciple : Prop :=
  ∀ (ω : Configuration 2) (C : OpenComponent ω), (Set.univ : Set C).Infinite →
    ∀ Ω : Set C, Ω.Finite → ∀ g : C → ℝ, (∀ x ∈ Ω, componentLaplacian C g x = 0) →
      ∀ M : ℝ, (∀ x ∈ outerBoundary C Ω, g x ≤ M) → ∀ x ∈ Ω, g x ≤ M

/-- The Green potential solves `-Δ u_f = f` on the component. -/
def PotentialLaplacian : Prop :=
  ∀ (ω : Configuration 2) (C : OpenComponent ω) (G : C → C → ℝ), IsGreenFamily C G →
    ∀ f : Vertex 2 → ℤ, (Function.support f).Finite →
      ∀ x, -componentLaplacian C (potential C G f) x = f x.val

end Rigidity.Steps.Section5
