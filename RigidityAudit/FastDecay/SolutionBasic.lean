import Mathlib

/-!
# Statement-level audit vocabulary for the `FastDecay` comparator

Verbatim copy of the vocabulary block of `RigidityAudit/FastDecay/Challenge.lean` (between
`VOCABULARY-BEGIN` and `VOCABULARY-END`), Mathlib-only; a mechanical copy, not hand-edited.  The
two blocks must stay byte-identical so that the comparator's constant-by-constant closure check
passes.
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

/-- Only finitely many lattice points lie in an open Euclidean ball. -/
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

end

/-! ## The normalized `L²` norm on a ball (`LatticeProb/Prob/Percolation/LatticeClusterL2.lean`) -/

noncomputable section

open scoped BigOperators

variable {d : ℕ} {ω : Configuration d}

/-- The source normalized L² expression on the literal finite component ball. -/
def componentBallL2 (C : OpenComponent ω) (z : Vertex d) (r : ℝ) (u : C → ℝ) : ℝ :=
  Real.sqrt ((∑ x ∈ componentEuclideanBall C z r, (u x) ^ 2) /
    ((componentEuclideanBall C z r).card : ℝ))

/-- Minkowski's inequality for the normalized `L²` norm (a proof ingredient of
`harmonicGrowthSpace`). -/
theorem componentBallL2_add_le (C : OpenComponent ω) (z : Vertex d) (r : ℝ) (u v : C → ℝ) :
    componentBallL2 C z r (u + v) ≤ componentBallL2 C z r u + componentBallL2 C z r v := by
  set s := componentEuclideanBall C z r
  have hn : (0 : ℝ) ≤ (s.card : ℝ) := Nat.cast_nonneg _
  have hA : 0 ≤ ∑ x ∈ s, u x ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hB : 0 ≤ ∑ x ∈ s, v x ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt s u v
  have hsq : ∑ x ∈ s, (u + v) x ^ 2 ≤
      (Real.sqrt (∑ x ∈ s, u x ^ 2) + Real.sqrt (∑ x ∈ s, v x ^ 2)) ^ 2 := by
    have h1 : ∑ x ∈ s, (u + v) x ^ 2 =
        ∑ x ∈ s, u x ^ 2 + 2 * ∑ x ∈ s, u x * v x + ∑ x ∈ s, v x ^ 2 := by
      simp only [Pi.add_apply, add_sq, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
    rw [h1, add_sq, Real.sq_sqrt hA, Real.sq_sqrt hB]
    nlinarith
  have hroot : Real.sqrt (∑ x ∈ s, (u + v) x ^ 2) ≤
      Real.sqrt (∑ x ∈ s, u x ^ 2) + Real.sqrt (∑ x ∈ s, v x ^ 2) := by
    calc Real.sqrt (∑ x ∈ s, (u + v) x ^ 2)
        ≤ Real.sqrt ((Real.sqrt (∑ x ∈ s, u x ^ 2) + Real.sqrt (∑ x ∈ s, v x ^ 2)) ^ 2) :=
          Real.sqrt_le_sqrt hsq
      _ = Real.sqrt (∑ x ∈ s, u x ^ 2) + Real.sqrt (∑ x ∈ s, v x ^ 2) :=
          Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  simp only [componentBallL2]
  rw [Real.sqrt_div' _ hn, Real.sqrt_div' _ hn, Real.sqrt_div' _ hn, ← add_div]
  exact div_le_div_of_nonneg_right hroot (Real.sqrt_nonneg _)

/-- Homogeneity of the normalized `L²` norm (a proof ingredient of `harmonicGrowthSpace`). -/
theorem componentBallL2_smul (C : OpenComponent ω) (z : Vertex d) (r : ℝ) (a : ℝ)
    (u : C → ℝ) : componentBallL2 C z r (a • u) = |a| * componentBallL2 C z r u := by
  simp only [componentBallL2, Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum,
    mul_div_assoc]
  rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs]

end

/-! ## Harmonic functions of polynomial growth
(`LatticeProb/Prob/Percolation/LatticeHarmonicGrowth.lean`) -/

noncomputable section

open Filter

open scoped BigOperators

variable {d : ℕ} {ω : Configuration d}

/-- The literal normalized L² growth condition at all real radii tending to infinity. -/
def componentL2Subpolynomial (C : OpenComponent ω) (k : ℕ) (u : C → ℝ) : Prop :=
  Tendsto (fun R : ℝ => (R ^ (k + 1))⁻¹ * componentBallL2 C 0 R u) atTop (nhds 0)

/-- Source A_k on an actual open component, with literal exponent k+1 and averaged L². -/
def harmonicGrowthSpace (C : OpenComponent ω) (k : ℕ) : Submodule ℝ (C → ℝ) where
  carrier := {u | (∀ x, componentLaplacian C u x = 0) ∧ componentL2Subpolynomial C k u}
  zero_mem' := by
    refine ⟨fun x => by simp [componentLaplacian], ?_⟩
    simp only [componentL2Subpolynomial, componentBallL2, Pi.zero_apply]
    simp
  add_mem' := by
    rintro u v ⟨hu, hgu⟩ ⟨hv, hgv⟩
    refine ⟨fun x => ?_, ?_⟩
    · have h : ∀ y : C, (u + v) y - (u + v) x = (u y - u x) + (v y - v x) := fun y => by
        simp only [Pi.add_apply]; ring
      simp only [componentLaplacian, h, Finset.sum_add_distrib]
      simp only [componentLaplacian] at hu hv
      rw [hu x, hv x, add_zero]
    · apply squeeze_zero' (g := fun R : ℝ => (R ^ (k + 1))⁻¹ * componentBallL2 C 0 R u +
        (R ^ (k + 1))⁻¹ * componentBallL2 C 0 R v)
      · exact eventually_atTop.mpr ⟨0, fun R hR =>
          mul_nonneg (inv_nonneg.mpr (pow_nonneg hR _)) (Real.sqrt_nonneg _)⟩
      · refine eventually_atTop.mpr ⟨0, fun R hR => ?_⟩
        rw [← mul_add]
        exact mul_le_mul_of_nonneg_left (componentBallL2_add_le C 0 R u v)
          (inv_nonneg.mpr (pow_nonneg hR _))
      · simpa only [add_zero] using hgu.add hgv
  smul_mem' := by
    rintro a u ⟨hu, hgu⟩
    refine ⟨fun x => ?_, ?_⟩
    · simp only [componentLaplacian] at hu
      simp only [componentLaplacian, Pi.smul_apply, smul_eq_mul, ← mul_sub, ← Finset.mul_sum,
        hu x, mul_zero]
    · have h := hgu.const_mul |a|
      simp only [mul_zero] at h
      exact h.congr (fun R => by
        simp only [componentBallL2_smul]; ring)

end

/-! ## The infinite cluster (`LatticeProb/Prob/Percolation/LatticeUniqueCluster.lean`,
`LatticeUniqueClusterEvent.lean`) -/

section

variable {d : ℕ} {ω : Configuration d}

/-- The unique infinite actual component, with no value on configurations lacking uniqueness. -/
noncomputable def uniqueInfiniteComponent (h : HasUniqueInfiniteOpenComponent ω) :
    OpenComponent ω := h.exists.choose

/-- The event of existence and uniqueness of an infinite actual open component. -/
def uniqueInfiniteComponentEvent (d : ℕ) : Set (Configuration d) :=
  {ω | HasUniqueInfiniteOpenComponent ω}

end

/-! ## Green functions (`LatticeProb/Prob/Percolation/GreenColumn.lean`,
`ContinuumGreen.lean`) -/

noncomputable section

open scoped Classical

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

/-- The continuum Green function with positive scalar conductivity, on punctured space. -/
def continuumGreen (d : ℕ) (_hd : 2 ≤ d) (κ : {a : ℝ // 0 < a})
    (z : {x : EuclideanSpace ℝ (Fin d) // x ≠ 0}) : ℝ :=
  if d = 2 then
    -Real.log ‖z.val‖ / (2 * Real.pi * κ.val)
  else
    (Real.Gamma ((d : ℝ) / 2 - 1) /
      (4 * Real.rpow Real.pi ((d : ℝ) / 2) * κ.val)) *
        Real.rpow ‖z.val‖ (2 - (d : ℝ))

end

/-! ## Corrected planes (`LatticeProb/Prob/Percolation/CorrectedPlaneCharacterization.lean`) -/

noncomputable section

open scoped BigOperators

variable {d : ℕ} {ω : Configuration d}

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

end

/-! ## Cited results on the lattice (`LatticeProb/External/`) -/

section

/-- The classical critical bounds and supercritical unique-component probability,
with the literal canonical law, critical value, and existence-and-uniqueness event
(Grimmett, *Percolation*). -/
def SupercriticalBondUniqueness : Prop :=
  (∀ (d : ℕ) [NeZero d], 2 ≤ d →
    0 < criticalProbability d ∧ criticalProbability d < 1) ∧
  (∀ (d : ℕ) [NeZero d], 2 ≤ d → ∀ p : unitInterval,
    criticalProbability d < (p : ℝ) → (p : ℝ) < 1 →
      latticeBondLaw d p (uniqueInfiniteComponentEvent d) = 1)

end

section

open MeasureTheory

/-- Almost surely, each slope has a unique normalized harmonic plane, and every A₁
function has a unique slope. Normalization uses an actual component vertex. The uniform
sublinear error is the qualitative consequence of the cited oscillation estimate
(Armstrong–Dario, arXiv:1609.09431v2, Theorem 2 and (1.22); Dario–Gu, arXiv:1909.10439v4,
Proposition 2.12). -/
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

end

section

open MeasureTheory

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

end

/-! ## Cited results on the cluster (`Rigidity/External/CorrectorQuantitative.lean`,
`ArmstrongDarioRegularity.lean`, `ClusterDensity.lean`) -/

section

open MeasureTheory Classical

/-- `X ≤ O_s(θ)` for the bond law of parameter `p`. -/
def IsOsBond (d : ℕ) (p : unitInterval) (X : Configuration d → ℝ) (s θ : ℝ) : Prop :=
  Integrable (fun ω => Real.exp (Real.rpow (max (X ω / θ) 0) s)) (latticeBondLaw d p) ∧
  (∫ ω, Real.exp (Real.rpow (max (X ω / θ) 0) s) ∂latticeBondLaw d p) ≤ 2

/-- **Theorem 2.5, quantitative sublinearity and Lipschitz bound** (literature input;
Armstrong–Dario, Comm. Pure Appl. Math. 71 (2018), eq. (1.22); Dario–Gu, Ann. Probab. 49 (2021),
Proposition 2.12). For every `α > 0` there are
`s, C > 0` and, for every vertex `x`, a minimal scale `M ≤ O_s(C)` such that for every `r ≥ M`,
every slope `p` and every corrected plane `ℓ_p`, with `χ_p = ℓ_p - p·x`,
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

end

section

open MeasureTheory

/-- **Theorem 2.4 (iii) at `k = 1`, at the origin** (Armstrong–Dario 2018, Theorem 2(iii),
arXiv:1609.09431v2; literature input). There are `s, C₀ > 0` and a nonnegative random variable
`𝒳 ≤ O_s(C₀)`, and a constant `C`, such that for every `R ≥ 2𝒳` and every `u` harmonic in
`𝒞_∞ ∩ B_R` there is `φ ∈ 𝒜₁(𝒞_∞)` with
`‖u - φ‖_{L̲²(𝒞_∞ ∩ B_r)} ≤ C (r/R)² ‖u‖_{L̲²(𝒞_∞ ∩ B_R)}` for every `r ∈ [𝒳, R/2]`. -/
def ArmstrongDarioOrderOneOrigin : Prop :=
  ∀ (d : ℕ) [NeZero d], 2 ≤ d → ∀ p : unitInterval,
    criticalProbability d < (p : ℝ) → (p : ℝ) < 1 →
    ∃ s C₀ : ℝ, 0 < s ∧ 0 < C₀ ∧
      ∃ X : Configuration d → ℝ, Measurable X ∧ (∀ ω, 0 ≤ X ω) ∧ IsOsBond d p X s C₀ ∧
      ∃ C : ℝ, ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω,
        ∀ R : ℝ, 2 * X ω ≤ R → ∀ u : uniqueInfiniteComponent h → ℝ,
          (∀ z ∈ componentEuclideanBall (uniqueInfiniteComponent h) 0 R,
            (∀ w, (componentGraph (uniqueInfiniteComponent h)).Adj z w →
              w ∈ componentEuclideanBall (uniqueInfiniteComponent h) 0 R) →
            componentLaplacian (uniqueInfiniteComponent h) u z = 0) →
          ∃ φ ∈ harmonicGrowthSpace (uniqueInfiniteComponent h) 1,
            ∀ r : ℝ, X ω ≤ r → r ≤ R / 2 →
              componentBallL2 (uniqueInfiniteComponent h) 0 r (u - φ) ≤
                C * (r / R) ^ 2 * componentBallL2 (uniqueInfiniteComponent h) 0 R u

/-- The triadic cube `□_m(3^m k) = ℤ^d ∩ (3^m k + (-3^m/2, 3^m/2)^d)` of size `3^m`, `k ∈ ℤ^d`. -/
def triadicCube (d m : ℕ) (k : Vertex d) : Set (Vertex d) :=
  {y | ∀ i, |(y i : ℝ) - 3 ^ m * (k i : ℝ)| < 3 ^ m / 2}

/-- The number of vertices of `Q` whose open cluster is infinite: `|𝒞_∞ ∩ Q|` when the infinite
open cluster `𝒞_∞` exists and is unique. -/
noncomputable def infiniteClusterCount {d : ℕ} (Q : Set (Vertex d)) (ω : Configuration d) : ℕ :=
  {y ∈ Q | ω ∈ infiniteComponentEvent y}.ncard

/-- **Concentration of the density of the infinite cluster** (literature input; Dario–Gu,
arXiv:1909.10439v4, Proposition A.1): "There exists a positive constant `C(d,𝔭) < ∞` such that for
any triadic cube `□ ∈ 𝒯` of size `3^m`, one has an estimate
`| |𝒞_∞ ∩ □| / |□| - θ(𝔭) | ≤ 𝒪_{2(d-1)/(3d²+2d-1)}(C 3^{-dm/2})`."
Bond percolation, `d ≥ 2`, `p_c(d) < p < 1`. -/
def ClusterDensityConcentrationInput : Prop :=
  ∀ (d : ℕ) [NeZero d], 2 ≤ d → ∀ p : unitInterval,
    criticalProbability d < (p : ℝ) → (p : ℝ) < 1 →
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (k : Vertex d),
      IsOsBond d p
        (fun ω => |(infiniteClusterCount (triadicCube d m k) ω : ℝ) /
          ((triadicCube d m k).ncard : ℝ) - theta d p|)
        (2 * ((d : ℝ) - 1) / (3 * (d : ℝ) ^ 2 + 2 * (d : ℝ) - 1))
        (C * (3 : ℝ) ^ (-((d : ℝ) * (m : ℝ)) / 2))

end

/-! ## Well-connected cubes (`Rigidity/External/WellConnected.lean`) -/

section

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

/-- **Proposition 2.3** (literature input; Pisztora, Penrose–Pisztora). For `d ≥ 2` and
`p_c(d) < p < 1` there are `c, C > 0` and `s > 0` such that every cube `x + Q_N` is
well-connected outside an event of probability at most `C exp(-c N^s)`. -/
def WellConnectedInput : Prop :=
  ∀ (d : ℕ) [NeZero d], 2 ≤ d → ∀ p : unitInterval,
    criticalProbability d < (p : ℝ) → (p : ℝ) < 1 →
    ∃ c C s : ℝ, 0 < c ∧ 0 < C ∧ 0 < s ∧ ∀ (x : Vertex d) (N : ℕ),
      latticeBondLaw d p {ω | ¬ IsWellConnected ω x N} ≤
        ENNReal.ofReal (C * Real.exp (-(c * (N : ℝ) ^ s)))

end

/-! ## Crossings of rectangles and the Jordan curve theorem (`Rigidity/External/KestenCrossing.lean`,
`JordanCurve.lean`) -/

section

open MeasureTheory

/-- The rectangle `x + R`, where `R` is `[0, m]` in direction `i` and `[0, n]` in the other one. -/
def crossingRectangle (x : Vertex 2) (m n : ℕ) (i : Fin 2) : Set (Vertex 2) :=
  {y | ∀ j, x j ≤ y j ∧ y j ≤ x j + (if j = i then (m : ℤ) else n)}

/-- An open path inside `x + R` joins its two faces orthogonal to direction `i`. -/
def HasOpenCrossing (ω : Configuration 2) (x : Vertex 2) (m n : ℕ) (i : Fin 2) : Prop :=
  ∃ (y z : Vertex 2) (hy : y ∈ crossingRectangle x m n i) (hz : z ∈ crossingRectangle x m n i),
    y i = x i ∧ z i = x i + m ∧
      ((openGraph ω).induce (crossingRectangle x m n i)).Reachable ⟨y, hy⟩ ⟨z, hz⟩

/-- **Kesten, Theorem 11.1** (literature input; *Percolation Theory for Mathematicians*). -/
def KestenRectangleCrossing : Prop :=
  ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) →
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (x : Vertex 2) (m n : ℕ) (i : Fin 2),
      latticeBondLaw 2 p {ω | ¬ HasOpenCrossing ω x m n i} ≤
        ENNReal.ofReal (C * (m + 1) * Real.exp (-(c * n)))

/-- The unit sphere `S²` of `ℝ³`. -/
abbrev S2 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

/-- **Jordan curve theorem on `S²`** (literature input). -/
def JordanCurveTheoremSphere : Prop :=
  ∀ (q : S2) (β : Path q q), Set.InjOn β (Set.Ico 0 1) →
    ∃ U V : Set S2, IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧ Disjoint U V ∧
      U ∪ V = (Set.range β)ᶜ ∧ frontier U = Set.range β ∧ frontier V = Set.range β

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

end FastDecay
end StatementAudit
end Rigidity
