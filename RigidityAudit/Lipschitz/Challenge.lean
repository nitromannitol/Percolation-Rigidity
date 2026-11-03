import Mathlib

/-!
# Lipschitz rigidity on the supercritical percolation cluster: comparator challenge

Mathlib-only comparator challenge for Theorem 1.1 (label `theorem:lipschitz`) of *Rigidity of
harmonic functions on the supercritical percolation cluster* (Ahmed Bou-Rabee, William Cooperman,
Paul Dario): for `d ≥ 2` and `p_c(d) < p < 1`, almost surely every Lipschitz harmonic function on
the infinite cluster of Bernoulli bond percolation on `ℤ^d` is constant.  The library's statement is
`Rigidity.Assembly.Main.lipschitz` in `Rigidity/Proofs/Assembly/Main.lean`.

This file imports only `Mathlib`: no repository module and no dependency.  It rebuilds from
Mathlib primitives every definition needed to read the theorem.

* The lattice `Site d = Fin d → ℤ`, its unit vectors and the nearest-neighbour graph `lattice d`
  (the `lattice-probability` dependency).
* Bernoulli bond percolation: the bonds `Bond d`, the configurations `Configuration d`, the
  product law `latticeBondLaw d p`, the open graph `openGraph ω`, its components, the critical
  probability `criticalProbability d`, and the unique infinite component
  `uniqueInfiniteComponent h`.
* Analysis on a component: the graph Laplacian `componentLaplacian`, Lipschitz functions
  `ComponentLipschitz`, Euclidean balls `componentEuclideanBall`, the normalized `L²` average
  `componentBallL2`, the spaces `harmonicGrowthSpace C k` of harmonic functions of growth
  `o(R^(k+1))`, the corrected planes `IsCorrectedPlane`, the continuum Green function
  `continuumGreen` and the Green column `IsGreenColumn`; and the well-connected cubes
  `IsWellConnected`.
* The seven cited results the theorem takes as explicit hypotheses, each a `Prop`:
  `SupercriticalBondUniqueness` (`0 < p_c(d) < 1`, existence and uniqueness of the infinite
  cluster; Grimmett, *Percolation*, Theorems 1.10 and 8.1),
  `SupercriticalBondCorrectorInput` (existence and uniqueness of the corrected planes and the
  classification of `𝒜₁`; Armstrong-Dario, Theorem 2 and (1.22), Dario-Gu, Proposition 2.12),
  `CorrectorQuantitativeInput` (quantitative sublinearity of the correctors; Armstrong-Dario
  (1.22), Dario-Gu, Proposition 2.12), `ArmstrongDarioOrderZero` (large-scale `C^{0,1}`
  regularity of order zero; Armstrong-Dario, Theorem 2), `SupercriticalBondGreenColumnExistence`
  and `SupercriticalBondGreenQuantitative` (the Green function of the infinite cluster and its
  homogenization; Dario-Gu), and `WellConnectedInput` (well-connected cubes; Pisztora,
  Penrose-Pisztora, Antal-Pisztora).

The definitions are statement-level copies of the repository's, token for token.  Where the
repository's proof of a side condition (finiteness of a neighbourhood, closure of a submodule)
uses repository lemmas, the copy proves it from Mathlib; the definitions themselves are unchanged.
The one helper the repository keeps private, `componentNeighborEmbedding`, is public here.  The
sole intentional `sorry` is the proof of the final theorem.

The vocabulary between `VOCABULARY-BEGIN` and `VOCABULARY-END` is copied verbatim into
`SolutionBasic.lean`; the two must stay byte-identical so that the comparator's
constant-by-constant closure check passes.
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

/-- The event of existence and uniqueness of an infinite actual open component. -/
def uniqueInfiniteComponentEvent (d : ℕ) : Set (Configuration d) :=
  {ω | HasUniqueInfiniteOpenComponent ω}

variable {ω : Configuration d}

/-- The unique infinite actual component, with no value on configurations lacking uniqueness. -/
noncomputable def uniqueInfiniteComponent (h : HasUniqueInfiniteOpenComponent ω) :
    OpenComponent ω := h.exists.choose

/-- Source Lipschitzness: one nonnegative finite real constant bounds all graph differences. -/
def ComponentLipschitz (C : OpenComponent ω) (u : C → ℝ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ x y : C, |u x - u y| ≤ K * ((componentGraph C).dist x y : ℝ)

end Cluster

/-! ## Euclidean balls and the normalized `L²` average
(`LatticeClusterBall.lean`, `LatticeClusterL2.lean`) -/

section Balls

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

/-- An ambient open Euclidean ball contains only finitely many lattice vertices. -/
theorem finite_latticeEuclideanBall (z : Vertex d) (r : ℝ) :
    {x : Vertex d | dist (latticeEuclideanEmbedding x)
      (latticeEuclideanEmbedding z) < r}.Finite := by
  have hbox := Set.Finite.pi' (fun i : Fin d =>
    Set.finite_Icc (z i - ⌈r⌉) (z i + ⌈r⌉))
  apply hbox.subset
  intro x hx i
  have hi := PiLp.norm_apply_le
    (latticeEuclideanEmbedding x - latticeEuclideanEmbedding z) i
  change |(x i : ℝ) - (z i : ℝ)| ≤
    ‖latticeEuclideanEmbedding x - latticeEuclideanEmbedding z‖ at hi
  have hb : |(x i : ℝ) - (z i : ℝ)| ≤ (⌈r⌉ : ℝ) :=
    (hi.trans_lt (show ‖latticeEuclideanEmbedding x -
      latticeEuclideanEmbedding z‖ < r from hx)).le.trans (Int.le_ceil r)
  obtain ⟨hl, hu⟩ := abs_le.mp hb
  constructor
  · exact_mod_cast (by linarith : (z i : ℝ) - (⌈r⌉ : ℝ) ≤ (x i : ℝ))
  · exact_mod_cast (by linarith : (x i : ℝ) ≤ (z i : ℝ) + (⌈r⌉ : ℝ))

/-- The finite component-vertex carrier of an open Euclidean ball. -/
theorem finite_componentEuclideanBall {ω : Configuration d} (C : OpenComponent ω)
    (z : Vertex d) (r : ℝ) :
    {x : C | dist (latticeEuclideanEmbedding x.val)
      (latticeEuclideanEmbedding z) < r}.Finite :=
  (finite_latticeEuclideanBall z r).preimage Subtype.val_injective.injOn

/-- The literal intersection of a component with an open Euclidean ball, on its vertex subtype. -/
def componentEuclideanBall {ω : Configuration d} (C : OpenComponent ω)
    (z : Vertex d) (r : ℝ) : Finset C :=
  (finite_componentEuclideanBall C z r).toFinset

variable {ω : Configuration d}

/-- The source normalized L² expression on the literal finite component ball. -/
def componentBallL2 (C : OpenComponent ω) (z : Vertex d) (r : ℝ) (u : C → ℝ) : ℝ :=
  Real.sqrt ((∑ x ∈ componentEuclideanBall C z r, (u x) ^ 2) /
    ((componentEuclideanBall C z r).card : ℝ))

/-- The normalized sum is a finite Euclidean norm with its cardinality factor. -/
theorem componentBallL2_eq_norm_div (C : OpenComponent ω) (z : Vertex d) (r : ℝ)
    (u : C → ℝ) :
    componentBallL2 C z r u =
      ‖(WithLp.toLp 2 (fun x : componentEuclideanBall C z r => u x) :
        EuclideanSpace ℝ (componentEuclideanBall C z r))‖ /
        Real.sqrt ((componentEuclideanBall C z r).card : ℝ) := by
  classical
  rw [componentBallL2, Real.sqrt_div (Finset.sum_nonneg (fun x _ => sq_nonneg (u x))),
    EuclideanSpace.norm_eq]
  simp only [Real.norm_eq_abs, sq_abs]
  congr 2
  exact (Finset.sum_coe_sort (componentEuclideanBall C z r) (fun x => (u x) ^ 2)).symm

/-- Minkowski's inequality for the normalized `L²` average. -/
theorem componentBallL2_add_le (C : OpenComponent ω) (z : Vertex d) (r : ℝ)
    (u v : C → ℝ) :
    componentBallL2 C z r (u + v) ≤
      componentBallL2 C z r u + componentBallL2 C z r v := by
  classical
  rw [componentBallL2_eq_norm_div, componentBallL2_eq_norm_div,
    componentBallL2_eq_norm_div, ← add_div]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  exact norm_add_le
    (WithLp.toLp 2 (fun x : componentEuclideanBall C z r => u x))
    (WithLp.toLp 2 (fun x : componentEuclideanBall C z r => v x))

/-- Scalar multiplication scales the normalized `L²` average by the absolute scalar. -/
theorem componentBallL2_smul (C : OpenComponent ω) (z : Vertex d) (r a : ℝ)
    (u : C → ℝ) :
    componentBallL2 C z r (a • u) = |a| * componentBallL2 C z r u := by
  classical
  rw [componentBallL2_eq_norm_div, componentBallL2_eq_norm_div, ← mul_div_assoc]
  congr 1
  exact norm_smul a
    (WithLp.toLp 2 (fun x : componentEuclideanBall C z r => u x))

end Balls

/-! ## Harmonic functions of controlled growth and corrected planes
(`LatticeHarmonicGrowth.lean`, `CorrectedPlaneCharacterization.lean`) -/

section Growth

variable {d : ℕ} {ω : Configuration d}

/-- The literal normalized L² growth condition at all real radii tending to infinity. -/
def componentL2Subpolynomial (C : OpenComponent ω) (k : ℕ) (u : C → ℝ) : Prop :=
  Tendsto (fun R : ℝ => (R ^ (k + 1))⁻¹ * componentBallL2 C 0 R u) atTop (nhds 0)

/-- On nonnegative radii the scaled normalized `L²` average is nonnegative. -/
theorem componentL2_scaled_nonneg (C : OpenComponent ω) (k : ℕ) (u : C → ℝ)
    {R : ℝ} (hR : 0 ≤ R) :
    0 ≤ (R ^ (k + 1))⁻¹ * componentBallL2 C 0 R u :=
  mul_nonneg (inv_nonneg.mpr (pow_nonneg hR _)) (Real.sqrt_nonneg _)

/-- The zero function satisfies the growth condition. -/
theorem componentL2Subpolynomial_zero (C : OpenComponent ω) (k : ℕ) :
    componentL2Subpolynomial C k 0 := by
  simp [componentL2Subpolynomial, componentBallL2]

/-- The growth condition is closed under addition. -/
theorem componentL2Subpolynomial_add (C : OpenComponent ω) (k : ℕ)
    {u v : C → ℝ} (hu : componentL2Subpolynomial C k u)
    (hv : componentL2Subpolynomial C k v) : componentL2Subpolynomial C k (u + v) := by
  apply squeeze_zero'
  · exact eventually_atTop.mpr ⟨0, fun R hR => componentL2_scaled_nonneg C k _ hR⟩
  · refine eventually_atTop.mpr ⟨0, fun R hR => ?_⟩
    calc
      (R ^ (k + 1))⁻¹ * componentBallL2 C 0 R (u + v) ≤
          (R ^ (k + 1))⁻¹ * (componentBallL2 C 0 R u + componentBallL2 C 0 R v) :=
        mul_le_mul_of_nonneg_left (componentBallL2_add_le C 0 R u v)
          (inv_nonneg.mpr (pow_nonneg hR _))
      _ = (R ^ (k + 1))⁻¹ * componentBallL2 C 0 R u +
          (R ^ (k + 1))⁻¹ * componentBallL2 C 0 R v := mul_add _ _ _
  · simpa only [add_zero] using hu.add hv

/-- The growth condition is closed under scalar multiplication. -/
theorem componentL2Subpolynomial_smul (C : OpenComponent ω) (k : ℕ)
    {u : C → ℝ} (hu : componentL2Subpolynomial C k u) (a : ℝ) :
    componentL2Subpolynomial C k (a • u) := by
  have h := hu.const_mul |a|
  simp only [mul_zero] at h
  exact h.congr (fun R => by rw [componentBallL2_smul]; ring)

/-- The component Laplacian is additive. -/
theorem componentLaplacian_add (C : OpenComponent ω) (u v : C → ℝ) (x : C) :
    componentLaplacian C (u + v) x = componentLaplacian C u x + componentLaplacian C v x := by
  simp only [componentLaplacian, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- The component Laplacian commutes with scalar multiplication. -/
theorem componentLaplacian_smul (C : OpenComponent ω) (a : ℝ) (u : C → ℝ) (x : C) :
    componentLaplacian C (a • u) x = a * componentLaplacian C u x := by
  simp only [componentLaplacian, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- Source A_k on an actual open component, with literal exponent k+1 and averaged L². -/
def harmonicGrowthSpace (C : OpenComponent ω) (k : ℕ) : Submodule ℝ (C → ℝ) where
  carrier := {u | (∀ x, componentLaplacian C u x = 0) ∧ componentL2Subpolynomial C k u}
  zero_mem' := ⟨fun x => by simp [componentLaplacian], componentL2Subpolynomial_zero C k⟩
  add_mem' := by
    rintro u v ⟨hu, hgu⟩ ⟨hv, hgv⟩
    exact ⟨fun x => by rw [componentLaplacian_add, hu, hv, add_zero],
      componentL2Subpolynomial_add C k hgu hgv⟩
  smul_mem' := by
    rintro a u ⟨hu, hgu⟩
    exact ⟨fun x => by rw [componentLaplacian_smul, hu, mul_zero],
      componentL2Subpolynomial_smul C k hgu a⟩

/-- The literal Euclidean affine linear part restricted to component vertices. -/
def componentSlope (C : OpenComponent ω) (p : Fin d → ℝ) (x : C) : ℝ :=
  ∑ i, p i * (x.val i : ℝ)

/-- Uniform sublinear error from a prescribed slope on actual open Euclidean balls. -/
def componentSlopeAsymptotics (C : OpenComponent ω) (p : Fin d → ℝ)
    (u : C → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
    ∀ x ∈ componentEuclideanBall C 0 R, |u x - componentSlope C p x| ≤ ε * R

/-- A source corrected plane is harmonic in A₁ and has the stated slope at infinity.
Uniqueness modulo constants is a separate literature assertion, absent from this predicate. -/
def IsCorrectedPlane (C : OpenComponent ω) (p : Fin d → ℝ) (u : C → ℝ) : Prop :=
  u ∈ harmonicGrowthSpace C 1 ∧ componentSlopeAsymptotics C p u

end Growth

/-! ## The Green function (`ContinuumGreen.lean`, `GreenColumn.lean`) -/

section Green

open scoped Classical

/-- The continuum Green function with positive scalar conductivity, on punctured space. -/
def continuumGreen (d : ℕ) (_hd : 2 ≤ d) (κ : {a : ℝ // 0 < a})
    (z : {x : EuclideanSpace ℝ (Fin d) // x ≠ 0}) : ℝ :=
  if d = 2 then
    -Real.log ‖z.val‖ / (2 * Real.pi * κ.val)
  else
    (Real.Gamma ((d : ℝ) / 2 - 1) /
      (4 * Real.rpow Real.pi ((d : ℝ) / 2) * κ.val)) *
        Real.rpow ‖z.val‖ (2 - (d : ℝ))

/-- The Green column characterized by its unit-neighbor Laplacian and its
normalization at Euclidean infinity. -/
def IsGreenColumn (d : ℕ) (_hd : 2 ≤ d) {ω : Configuration d}
    (C : OpenComponent ω) (y : C) (g : C → ℝ) : Prop :=
  (∀ x : C, -componentLaplacian C g x = if x = y then 1 else 0) ∧
  (d = 2 → g y = 0 ∧
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
      ∀ x : C, R ≤ ‖latticeEuclideanEmbedding x.val‖ →
        |g x| ≤ ε * ‖latticeEuclideanEmbedding x.val‖) ∧
  (3 ≤ d → ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
    ∀ x : C, R ≤ ‖latticeEuclideanEmbedding x.val‖ → |g x| ≤ ε)

end Green

/-! ## Well-connected cubes (`Rigidity/External/WellConnected.lean`) -/

section WellConnected

open Classical

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

/-- `V` meets both faces of `z + Q_r` in every coordinate direction, so (being a cluster of the
cube) it joins each pair of opposite faces by a path inside the cube. -/
def CrossesCube (z : Vertex d) (r : ℕ) (V : Set (Vertex d)) : Prop :=
  ∀ i : Fin d, (∃ y ∈ V, y i = z i - r) ∧ (∃ y ∈ V, y i = z i + r)

/-- `z + Q_r` is crossing: a largest cluster `𝒞_*` of it crosses it. -/
def IsCrossingCube (ω : Configuration d) (z : Vertex d) (r : ℕ) : Prop :=
  ∃ V, IsLargestClusterIn ω (cubeAt z r) V ∧ CrossesCube z r V

/-- `z + Q_M` is crossing, by a largest cluster `𝒞_*` to which every open path of length at least
`M/100` in the cube is connected inside the cube. -/
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

end WellConnected

/-! ## The cited results taken as hypotheses

`LatticeProb/External/` and `Rigidity/External/`. -/

/-- The classical critical bounds and supercritical unique-component probability,
with the literal canonical law, critical value, and existence-and-uniqueness event. -/
def SupercriticalBondUniqueness : Prop :=
  (∀ (d : ℕ) [NeZero d], 2 ≤ d →
    0 < criticalProbability d ∧ criticalProbability d < 1) ∧
  (∀ (d : ℕ) [NeZero d], 2 ≤ d → ∀ p : unitInterval,
    criticalProbability d < (p : ℝ) → (p : ℝ) < 1 →
      latticeBondLaw d p (uniqueInfiniteComponentEvent d) = 1)

/-- Almost surely, each slope has a unique normalized harmonic plane, and every A₁
function has a unique slope. Normalization uses an actual component vertex. The uniform
sublinear error is the qualitative consequence of the cited oscillation estimate; no
stochastic moment estimate or gradient estimate is included in this proposition. -/
def SupercriticalBondCorrectorInput : Prop :=
  ∀ (d : ℕ) [NeZero d], 2 ≤ d → ∀ p : unitInterval,
    criticalProbability d < (p : ℝ) → (p : ℝ) < 1 →
    ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω,
      (∀ q : Fin d → ℝ, ∀ o : uniqueInfiniteComponent h,
        ∃! u : uniqueInfiniteComponent h → ℝ,
          IsCorrectedPlane (uniqueInfiniteComponent h) q u ∧ u o = 0) ∧
      (∀ u : uniqueInfiniteComponent h → ℝ,
        u ∈ harmonicGrowthSpace (uniqueInfiniteComponent h) 1 →
        ∃! q : Fin d → ℝ, IsCorrectedPlane (uniqueInfiniteComponent h) q u)

section Quantitative

open Classical

/-- `X ≤ O_s(θ)` for the bond law of parameter `p`. -/
def IsOsBond (d : ℕ) (p : unitInterval) (X : Configuration d → ℝ) (s θ : ℝ) : Prop :=
  Integrable (fun ω => Real.exp (Real.rpow (max (X ω / θ) 0) s)) (latticeBondLaw d p) ∧
  (∫ ω, Real.exp (Real.rpow (max (X ω / θ) 0) s) ∂latticeBondLaw d p) ≤ 2

/-- **Theorem 2.5, quantitative sublinearity and Lipschitz bound** (literature input). For every
`α > 0` there are `s, C > 0` and, for every vertex `x`, a minimal scale `M ≤ O_s(C)` such that for
every `r ≥ M`, every slope `p` and every corrected plane `ℓ_p`, with `χ_p = ℓ_p - p·x`,
`osc_{𝒞_∞ ∩ B_r(x)} χ_p + ‖∇χ_p‖_{L^∞(𝒞_∞ ∩ B_r(x))} ≤ C |p| r^α`. -/
def CorrectorQuantitativeInput : Prop :=
  ∀ (d : ℕ) [NeZero d], 2 ≤ d → ∀ p : unitInterval,
    criticalProbability d < (p : ℝ) → (p : ℝ) < 1 →
    ∀ α : ℝ, 0 < α → ∃ s C : ℝ, 0 < s ∧ 0 < C ∧ ∀ x : Vertex d,
      ∃ M : Configuration d → ℝ, Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧ IsOsBond d p M s C ∧
      ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω,
        ∀ (q : Fin d → ℝ) (ℓ : uniqueInfiniteComponent h → ℝ),
          IsCorrectedPlane (uniqueInfiniteComponent h) q ℓ →
        ∀ r : ℝ, M ω ≤ r →
        ∀ a b a' b' : uniqueInfiniteComponent h,
          ‖latticeEuclideanEmbedding a.val - latticeEuclideanEmbedding x‖ < r →
          ‖latticeEuclideanEmbedding b.val - latticeEuclideanEmbedding x‖ < r →
          ‖latticeEuclideanEmbedding a'.val - latticeEuclideanEmbedding x‖ < r →
          ‖latticeEuclideanEmbedding b'.val - latticeEuclideanEmbedding x‖ < r →
          (componentGraph (uniqueInfiniteComponent h)).Adj a' b' →
          |(ℓ a - ∑ i, q i * a.val i) - (ℓ b - ∑ i, q i * b.val i)| +
              |(ℓ a' - ∑ i, q i * a'.val i) - (ℓ b' - ∑ i, q i * b'.val i)|
            ≤ C * (∑ i, |q i|) * r ^ α

end Quantitative

/-- Order-zero specialization of Armstrong–Dario, Theorem 2, for iid zero-one bonds. -/
def ArmstrongDarioOrderZero : Prop :=
  ∀ (d : ℕ) [NeZero d] (_hd : 2 ≤ d) (p : unitInterval),
    criticalProbability d < (p : ℝ) → (p : ℝ) < 1 →
    ∃ (s θ C : ℝ), 0 < s ∧ 0 < θ ∧ 0 < C ∧
      ∃ X : Configuration d → ℝ,
        Measurable X ∧ (∀ ω, 0 ≤ X ω) ∧
        Integrable (fun ω => Real.exp (Real.rpow (X ω / θ) s)) (latticeBondLaw d p) ∧
        (∫ ω, Real.exp (Real.rpow (X ω / θ) s) ∂latticeBondLaw d p) ≤ 2 ∧
        ∀ᵐ ω ∂latticeBondLaw d p,
          ∃ _h : HasUniqueInfiniteOpenComponent ω,
            ∀ h' : HasUniqueInfiniteOpenComponent ω,
              FiniteDimensional ℝ (harmonicGrowthSpace (uniqueInfiniteComponent h') 0) ∧
              Module.finrank ℝ (harmonicGrowthSpace (uniqueInfiniteComponent h') 0) = 1 ∧
              ∀ (R : ℝ), 2 * X ω ≤ R →
                ∀ u : uniqueInfiniteComponent h' → ℝ,
                  (∀ x ∈ componentEuclideanBall (uniqueInfiniteComponent h') 0 R,
                    (∀ y : uniqueInfiniteComponent h',
                      (componentGraph (uniqueInfiniteComponent h')).Adj x y →
                        y ∈ componentEuclideanBall (uniqueInfiniteComponent h') 0 R) →
                    componentLaplacian (uniqueInfiniteComponent h') u x = 0) →
                  ∃ φ : uniqueInfiniteComponent h' → ℝ,
                    φ ∈ harmonicGrowthSpace (uniqueInfiniteComponent h') 0 ∧
                    ∀ r : ℝ, X ω ≤ r → r ≤ R / 2 →
                      componentBallL2 (uniqueInfiniteComponent h') 0 r (u - φ) ≤
                        C * (r / R) * componentBallL2 (uniqueInfiniteComponent h') 0 R u

/-- Existence and uniqueness of the infinite-cluster Green column for each
fixed lattice pole, as described by Dario and Gu around equation (1.8). -/
def SupercriticalBondGreenColumnExistence : Prop :=
  ∀ (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval),
    criticalProbability d < (p : ℝ) → (p : ℝ) < 1 →
    ∀ y : Vertex d, ∀ᵐ ω ∂latticeBondLaw d p,
      ∀ h : HasUniqueInfiniteOpenComponent ω,
        ∀ hy : y ∈ (uniqueInfiniteComponent h).supp,
          ∃! g : uniqueInfiniteComponent h → ℝ,
            IsGreenColumn d hd (uniqueInfiniteComponent h) ⟨y, hy⟩ g

section GreenQuantitative

open scoped ENNReal Classical

/-- The value estimates for the infinite-cluster Green function of Dario and Gu,
with an existential positive conductivity. -/
def SupercriticalBondGreenQuantitative : Prop :=
  ∀ (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval),
    criticalProbability d < (p : ℝ) → (p : ℝ) < 1 →
    ∃ κ : ℝ, ∃ hκ : 0 < κ,
      (d = 2 →
        ∃ K : Vertex d → Configuration d → ℝ,
          (∀ y, Measurable (K y)) ∧
          ∀ δ : ℝ, 0 < δ → ∃ C s : ℝ, 0 < C ∧ 0 < s ∧
            ∀ y : Vertex d,
              (∀ R : ℝ, 0 ≤ R →
                latticeBondLaw d p {ω | R ≤ |K y ω|} ≤
                  ENNReal.ofReal (C * Real.exp (-Real.rpow R s / C))) ∧
              ∃ M : Configuration d → ℝ,
                Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧
                (∀ R : ℝ, 0 ≤ R →
                  latticeBondLaw d p {ω | R ≤ M ω} ≤
                    ENNReal.ofReal (C * Real.exp (-Real.rpow R s / C))) ∧
                ∀ᵐ ω ∂latticeBondLaw d p,
                  ∀ h : HasUniqueInfiniteOpenComponent ω,
                    ∀ hy : y ∈ (uniqueInfiniteComponent h).supp,
                      ∀ g : uniqueInfiniteComponent h → ℝ,
                        IsGreenColumn d hd (uniqueInfiniteComponent h) ⟨y, hy⟩ g →
                        (∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
                          ∀ x : uniqueInfiniteComponent h,
                            ∀ z : {v : EuclideanSpace ℝ (Fin d) // v ≠ 0},
                              z.val = latticeEuclideanEmbedding x.val -
                                latticeEuclideanEmbedding y →
                              R ≤ ‖latticeEuclideanEmbedding x.val‖ →
                              |g x - continuumGreen d hd ⟨κ, hκ⟩ z - K y ω| ≤ ε) ∧
                        ∀ x : uniqueInfiniteComponent h,
                          ∀ z : {v : EuclideanSpace ℝ (Fin d) // v ≠ 0},
                            z.val = latticeEuclideanEmbedding x.val -
                              latticeEuclideanEmbedding y →
                            M ω ≤ ‖z.val‖ →
                            |g x - continuumGreen d hd ⟨κ, hκ⟩ z - K y ω| ≤
                              C / Real.rpow ‖z.val‖ (1 - δ)) ∧
      (3 ≤ d →
        ∀ δ : ℝ, 0 < δ → ∃ C s : ℝ, 0 < C ∧ 0 < s ∧
          ∀ y : Vertex d, ∃ M : Configuration d → ℝ,
            Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧
            (∀ R : ℝ, 0 ≤ R →
              latticeBondLaw d p {ω | R ≤ M ω} ≤
                ENNReal.ofReal (C * Real.exp (-Real.rpow R s / C))) ∧
            ∀ᵐ ω ∂latticeBondLaw d p,
              ∀ h : HasUniqueInfiniteOpenComponent ω,
                ∀ hy : y ∈ (uniqueInfiniteComponent h).supp,
                  ∀ g : uniqueInfiniteComponent h → ℝ,
                    IsGreenColumn d hd (uniqueInfiniteComponent h) ⟨y, hy⟩ g →
                    ∀ x : uniqueInfiniteComponent h,
                      ∀ z : {v : EuclideanSpace ℝ (Fin d) // v ≠ 0},
                        z.val = latticeEuclideanEmbedding x.val -
                          latticeEuclideanEmbedding y →
                        M ω ≤ ‖z.val‖ →
                        |g x - continuumGreen d hd ⟨κ, hκ⟩ z| ≤
                          C / (Real.rpow ‖z.val‖ (1 - δ) *
                            ‖z.val‖ ^ (d - 2)))

end GreenQuantitative

section WellConnectedInput

open Classical

/-- **Proposition 2.3** (literature input). For `d ≥ 2` and `p_c(d) < p < 1` there are
`c, C > 0` and `s > 0` such that every cube `x + Q_N` is well-connected outside an event of
probability at most `C exp(-c N^s)`. -/
def WellConnectedInput : Prop :=
  ∀ (d : ℕ) [NeZero d], 2 ≤ d → ∀ p : unitInterval,
    criticalProbability d < (p : ℝ) → (p : ℝ) < 1 →
    ∃ c C s : ℝ, 0 < c ∧ 0 < C ∧ 0 < s ∧ ∀ (x : Vertex d) (N : ℕ),
      latticeBondLaw d p {ω | ¬ IsWellConnected ω x N} ≤
        ENNReal.ofReal (C * Real.exp (-(c * (N : ℝ) ^ s)))

end WellConnectedInput

end
-- VOCABULARY-END

/-! ## The theorem -/

/-- **Theorem 1.1** (`theorem:lipschitz`): for `d ≥ 2` and `p_c(d) < p < 1`, almost surely the
infinite cluster exists and is unique, and every function `u` on it that is harmonic
(`componentLaplacian u = 0` at every vertex) and Lipschitz for the graph distance of the cluster is
constant.  The seven cited results enter as explicit hypotheses. -/
theorem lipschitz (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : SupercriticalBondUniqueness)
    (hCorr : SupercriticalBondCorrectorInput)
    (hCQ : CorrectorQuantitativeInput)
    (hAD : ArmstrongDarioOrderZero)
    (hE : SupercriticalBondGreenColumnExistence)
    (hGQ : SupercriticalBondGreenQuantitative)
    (hW : WellConnectedInput) :
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
