import Mathlib

/-!
# Statement-level audit vocabulary for the `IntegerLinearGrowth` comparator

Verbatim copy of the vocabulary block of
`RigidityAudit/IntegerLinearGrowth/Challenge.lean` (between `VOCABULARY-BEGIN` and
`VOCABULARY-END`), Mathlib-only; a mechanical copy, not hand-edited.  The two
blocks must stay byte-identical so that the comparator's constant-by-constant
closure check passes.
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

/-! ## Linear growth (`LatticeProb/Prob/Percolation/LatticeLinearGrowth.lean`) -/

noncomputable section LinearGrowth

open Filter Asymptotics

variable {d : ℕ} {ω : Configuration d}

/-- `u` grows at most linearly on the cluster: `u(x) = O(|x|₁)` as `x → ∞` in the cluster. -/
def componentPointwiseLinearGrowth (C : OpenComponent ω) (u : C → ℝ) : Prop :=
  u =O[cofinite] (fun x : C => ∑ i : Fin d, |(x.val i : ℝ)|)

end LinearGrowth

/-! ## Euclidean balls in a cluster (`LatticeProb/Prob/Percolation/LatticeClusterBall.lean`) -/

noncomputable section ClusterBall

variable {d : ℕ}

/-- The embedding of `ℤ^d` into the Euclidean space `ℝ^d`. -/
def latticeEuclideanEmbedding : Vertex d ↪ EuclideanSpace ℝ (Fin d) where
  toFun x := WithLp.toLp 2 (fun i => (x i : ℝ))
  inj' := by
    intro x y h
    funext i
    have hi := congrArg (fun v : EuclideanSpace ℝ (Fin d) => v i) h
    change (x i : ℝ) = (y i : ℝ) at hi
    exact_mod_cast hi

/-- An open Euclidean ball contains finitely many lattice vertices. -/
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

/-- An open Euclidean ball contains finitely many vertices of a cluster. -/
theorem finite_componentEuclideanBall {ω : Configuration d} (C : OpenComponent ω)
    (z : Vertex d) (r : ℝ) :
    {x : C | dist (latticeEuclideanEmbedding x.val)
      (latticeEuclideanEmbedding z) < r}.Finite :=
  (finite_latticeEuclideanBall z r).preimage Subtype.val_injective.injOn

/-- The vertices of the cluster `C` in the open Euclidean ball of center `z` and radius `r`. -/
def componentEuclideanBall {ω : Configuration d} (C : OpenComponent ω)
    (z : Vertex d) (r : ℝ) : Finset C :=
  (finite_componentEuclideanBall C z r).toFinset

end ClusterBall

/-! ## The averaged `L²` norm on a ball (`LatticeProb/Prob/Percolation/LatticeClusterL2.lean`) -/

noncomputable section ClusterL2

variable {d : ℕ} {ω : Configuration d}

/-- The averaged `L²` norm `‖u‖_{L̲²(B_r(z) ∩ C)}` of `u` on the vertices of the cluster `C` in a
Euclidean ball. -/
def componentBallL2 (C : OpenComponent ω) (z : Vertex d) (r : ℝ) (u : C → ℝ) : ℝ :=
  Real.sqrt ((∑ x ∈ componentEuclideanBall C z r, (u x) ^ 2) /
    ((componentEuclideanBall C z r).card : ℝ))

/-- The averaged `L²` norm is nonnegative. -/
theorem componentBallL2_nonneg (C : OpenComponent ω) (z : Vertex d) (r : ℝ)
    (u : C → ℝ) : 0 ≤ componentBallL2 C z r u :=
  Real.sqrt_nonneg _

/-- The averaged `L²` norm as a Euclidean norm divided by the square root of the volume. -/
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

/-- The triangle inequality for the averaged `L²` norm. -/
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

/-- The averaged `L²` norm is absolutely homogeneous. -/
theorem componentBallL2_smul (C : OpenComponent ω) (z : Vertex d) (r a : ℝ)
    (u : C → ℝ) :
    componentBallL2 C z r (a • u) = |a| * componentBallL2 C z r u := by
  classical
  rw [componentBallL2_eq_norm_div, componentBallL2_eq_norm_div, ← mul_div_assoc]
  congr 1
  exact norm_smul a
    (WithLp.toLp 2 (fun x : componentEuclideanBall C z r => u x))

end ClusterL2

/-! ## Harmonic functions of controlled growth
(`LatticeProb/Prob/Percolation/LatticeHarmonicGrowth.lean`) -/

noncomputable section HarmonicGrowth

open Filter

variable {d : ℕ} {ω : Configuration d}

/-- `‖u‖_{L̲²(B_R)} = o(R^{k+1})` as `R → ∞`, for the balls centred at the origin. -/
def componentL2Subpolynomial (C : OpenComponent ω) (k : ℕ) (u : C → ℝ) : Prop :=
  Tendsto (fun R : ℝ => (R ^ (k + 1))⁻¹ * componentBallL2 C 0 R u) atTop (nhds 0)

/-- The zero function has subpolynomial growth. -/
theorem componentL2Subpolynomial_zero (C : OpenComponent ω) (k : ℕ) :
    componentL2Subpolynomial C k 0 := by
  have h : ∀ R : ℝ, componentBallL2 C 0 R 0 = 0 := fun R => by
    simp [componentBallL2]
  simp only [componentL2Subpolynomial, h, mul_zero]
  exact tendsto_const_nhds

/-- Subpolynomial growth is closed under addition. -/
theorem componentL2Subpolynomial_add (C : OpenComponent ω) (k : ℕ)
    {u v : C → ℝ} (hu : componentL2Subpolynomial C k u)
    (hv : componentL2Subpolynomial C k v) : componentL2Subpolynomial C k (u + v) := by
  apply squeeze_zero'
  · exact eventually_atTop.mpr ⟨0, fun R hR =>
      mul_nonneg (inv_nonneg.mpr (pow_nonneg hR _)) (componentBallL2_nonneg C 0 R _)⟩
  · refine eventually_atTop.mpr ⟨0, fun R hR => ?_⟩
    calc
      (R ^ (k + 1))⁻¹ * componentBallL2 C 0 R (u + v) ≤
          (R ^ (k + 1))⁻¹ * (componentBallL2 C 0 R u + componentBallL2 C 0 R v) :=
        mul_le_mul_of_nonneg_left (componentBallL2_add_le C 0 R u v)
          (inv_nonneg.mpr (pow_nonneg hR _))
      _ = (R ^ (k + 1))⁻¹ * componentBallL2 C 0 R u +
          (R ^ (k + 1))⁻¹ * componentBallL2 C 0 R v := mul_add _ _ _
  · simpa only [add_zero] using hu.add hv

/-- Subpolynomial growth is closed under scalar multiplication. -/
theorem componentL2Subpolynomial_smul (C : OpenComponent ω) (k : ℕ)
    {u : C → ℝ} (hu : componentL2Subpolynomial C k u) (a : ℝ) :
    componentL2Subpolynomial C k (a • u) := by
  have h := hu.const_mul |a|
  simp only [mul_zero] at h
  exact h.congr (fun R => by rw [componentBallL2_smul]; ring)

/-- The Laplacian of a sum is the sum of the Laplacians. -/
theorem componentLaplacian_add (C : OpenComponent ω) (u v : C → ℝ) (x : C) :
    componentLaplacian C (u + v) x = componentLaplacian C u x + componentLaplacian C v x := by
  simp only [componentLaplacian, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- The Laplacian commutes with scalar multiplication. -/
theorem componentLaplacian_smul (C : OpenComponent ω) (a : ℝ) (u : C → ℝ) (x : C) :
    componentLaplacian C (a • u) x = a * componentLaplacian C u x := by
  simp only [componentLaplacian, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- The space `𝒜_k` of the harmonic functions `u` on the cluster `C` with
`‖u‖_{L̲²(B_R)} = o(R^{k+1})`. -/
def harmonicGrowthSpace (C : OpenComponent ω) (k : ℕ) : Submodule ℝ (C → ℝ) where
  carrier := {u | (∀ x, componentLaplacian C u x = 0) ∧ componentL2Subpolynomial C k u}
  zero_mem' := by
    constructor
    · intro x
      simp [componentLaplacian]
    · exact componentL2Subpolynomial_zero C k
  add_mem' := by
    rintro u v ⟨hu, hgu⟩ ⟨hv, hgv⟩
    constructor
    · intro x
      rw [componentLaplacian_add, hu x, hv x, add_zero]
    · exact componentL2Subpolynomial_add C k hgu hgv
  smul_mem' := by
    rintro a u ⟨hu, hgu⟩
    constructor
    · intro x
      rw [componentLaplacian_smul, hu x, mul_zero]
    · exact componentL2Subpolynomial_smul C k hgu a

end HarmonicGrowth

/-! ## Corrected planes (`LatticeProb/Prob/Percolation/CorrectedPlaneCharacterization.lean`) -/

noncomputable section CorrectedPlane

variable {d : ℕ} {ω : Configuration d}

/-- The linear function `x ↦ p · x` on the cluster. -/
def componentSlope (C : OpenComponent ω) (p : Fin d → ℝ) (x : C) : ℝ :=
  ∑ i, p i * (x.val i : ℝ)

/-- `u` is within `o(R)` of `x ↦ p · x`, uniformly on the balls of radius `R` centred at the
origin. -/
def componentSlopeAsymptotics (C : OpenComponent ω) (p : Fin d → ℝ)
    (u : C → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
    ∀ x ∈ componentEuclideanBall C 0 R, |u x - componentSlope C p x| ≤ ε * R

/-- `u` is a corrected plane of slope `p`: an element of `𝒜₁` asymptotic to `x ↦ p · x`. -/
def IsCorrectedPlane (C : OpenComponent ω) (p : Fin d → ℝ) (u : C → ℝ) : Prop :=
  u ∈ harmonicGrowthSpace C 1 ∧ componentSlopeAsymptotics C p u

end CorrectedPlane

/-! ## Cited result: the first-order correctors
(`LatticeProb/External/SupercriticalBondCorrectorInput.lean`) -/

section CorrectorInput

open MeasureTheory

/-- **Armstrong and Dario (2018), Theorem 2 and (1.22); Dario and Gu (2021), Proposition 2.12**
(literature input).  For `d ≥ 2` and `p_c(d) < p < 1`, almost surely, on the infinite cluster:
for every slope `q` and every vertex `o` there is exactly one corrected plane of slope `q`
vanishing at `o`, and every element of `𝒜₁` is a corrected plane of exactly one slope. -/
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

end CorrectorInput
-- VOCABULARY-END

end IntegerLinearGrowth
end StatementAudit
end Rigidity
