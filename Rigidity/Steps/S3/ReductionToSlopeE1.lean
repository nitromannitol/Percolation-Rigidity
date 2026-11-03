import Rigidity.Draft.Section3Statements

/-!
# Lemma 3.1: the steps of the reduction to the slope `e₁`

Lemma 3.1 (paper L801-860 of the corrected draft) is carved into five steps, stated with the set
of slopes `q` whose corrected planes `ℓ_q` are `L`-Lipschitz on the unique infinite cluster.

* `step:3.1-zero-one`: the event `E_L` (a nonconstant `L`-Lipschitz harmonic function exists) has
  probability `0` or `1`.
* `step:lip-in-A1`: almost surely a nonconstant `L`-Lipschitz harmonic function lies in `A₁`,
  hence is a corrected plane of a nonzero slope plus a constant.
* `step:3.1-closed-slopes`: almost surely `q ↦ ℓ_q(x) - ℓ_q(y)` is linear, so the set of
  `L`-Lipschitz slopes is closed and Lipschitz constants add under linear combinations of slopes.
* `step:3.1-deterministic-slope`: a deterministic nonzero slope is almost surely `L`-Lipschitz.
* `step:3.1-reflection`: the dihedral symmetry of the lattice and of the bond law.

The reduction makes the union bound over integer `L`, and replaces the formula
`ℓ_{2 p̄₁ e₁} = ℓ_{p̄} + ℓ_{T₂ ⋯ T_d p̄}` by zeroing the coordinates other than the first one at a
time, `(q + T_j q)/2`, after a coordinate transposition that makes the first coordinate nonzero
(the "without loss of generality `p̄₁ > 0`" of the paper).
-/

namespace Rigidity.Steps.S3

open MeasureTheory LatticeProb.Percolation Rigidity.Section3

variable {d : ℕ}

/-- The slopes `q` whose corrected planes `ℓ_q` on the unique infinite cluster of `ω` are all
`L`-Lipschitz for the graph distance of the cluster; empty off the unique-cluster event. -/
def lipschitzSlopeSet (ω : Configuration d) (L : ℝ) : Set (Fin d → ℝ) :=
  {q | ∃ h : HasUniqueInfiniteOpenComponent ω,
    ∀ u, IsCorrectedPlane (uniqueInfiniteComponent h) q u →
      IsLipschitzWith (uniqueInfiniteComponent h) L u}

/-- The event `E_L`: the unique infinite cluster carries a nonconstant harmonic function which is
`L`-Lipschitz. -/
def lipschitzHarmonicEvent (d : ℕ) (L : ℝ) : Set (Configuration d) :=
  {ω | ∃ h : HasUniqueInfiniteOpenComponent ω, ∃ u : uniqueInfiniteComponent h → ℝ,
    (∀ x, componentLaplacian (uniqueInfiniteComponent h) u x = 0) ∧
    IsLipschitzWith (uniqueInfiniteComponent h) L u ∧ ∃ x y, u x ≠ u y}

/-- The reflection `T_j` of a slope: its `j`-th coordinate changes sign. -/
def reflectSlope (j : Fin d) (q : Fin d → ℝ) : Fin d → ℝ :=
  Function.update q j (-q j)

/-- Step `step:3.1-zero-one` (paper L817-819): the event `E_L` is translation invariant, so by
the ergodicity of Bernoulli percolation it has probability `0` or `1`. -/
def ZeroOneStep (d : ℕ) [NeZero d] (p : unitInterval) : Prop :=
  ∀ L : ℝ, latticeBondLaw d p (lipschitzHarmonicEvent d L) = 0 ∨
    ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ lipschitzHarmonicEvent d L

/-- Step `step:lip-in-A1` (paper L808, L820-824): almost surely, a nonconstant `L`-Lipschitz
harmonic function on the cluster lies in `A₁`, so (Theorem 2.5) it is the corrected plane of a
slope `q` plus a constant, with `q ≠ 0`; hence every corrected plane of slope `q` is
`L`-Lipschitz. -/
def LipschitzMemA1Step (d : ℕ) [NeZero d] (p : unitInterval) : Prop :=
  ∀ᵐ ω ∂latticeBondLaw d p, ∀ (h : HasUniqueInfiniteOpenComponent ω) (L : ℝ)
    (u : uniqueInfiniteComponent h → ℝ),
    (∀ x, componentLaplacian (uniqueInfiniteComponent h) u x = 0) →
    IsLipschitzWith (uniqueInfiniteComponent h) L u → (∃ x y, u x ≠ u y) →
    ∃ q ≠ 0, q ∈ lipschitzSlopeSet ω L

/-- Step `step:3.1-closed-slopes` (paper L825-827): almost surely, for all vertices `x, y` of the
cluster the map `q ↦ ℓ_q(x) - ℓ_q(y)` is well-defined and linear; hence the set of slopes whose
corrected plane is `L`-Lipschitz is closed, and `ℓ_{a q + b q'}` is `(|a| L + |b| L')`-Lipschitz
when `ℓ_q` is `L`-Lipschitz and `ℓ_{q'}` is `L'`-Lipschitz. -/
def ClosedSlopesStep (d : ℕ) [NeZero d] (p : unitInterval) : Prop :=
  ∀ᵐ ω ∂latticeBondLaw d p, ∀ L : ℝ, IsClosed (lipschitzSlopeSet ω L) ∧
    ∀ (L' a b : ℝ) (q q' : Fin d → ℝ), q ∈ lipschitzSlopeSet ω L →
      q' ∈ lipschitzSlopeSet ω L' → a • q + b • q' ∈ lipschitzSlopeSet ω (|a| * L + |b| * L')

/-- Step `step:3.1-deterministic-slope` (paper L829-838): if almost surely the set of
`L`-Lipschitz slopes is closed and contains a nonzero slope, then its translation-invariant
selection (the argsup `p̄` of the paper) is deterministic: a fixed nonzero slope has an
`L`-Lipschitz corrected plane almost surely. -/
def DeterministicSlopeStep (d : ℕ) [NeZero d] (p : unitInterval) : Prop :=
  ∀ L : ℝ, (∀ᵐ ω ∂latticeBondLaw d p, IsClosed (lipschitzSlopeSet ω L)) →
    (∀ᵐ ω ∂latticeBondLaw d p, ∃ q ≠ 0, q ∈ lipschitzSlopeSet ω L) →
    ∃ q ≠ 0, ∀ᵐ ω ∂latticeBondLaw d p, q ∈ lipschitzSlopeSet ω L

/-- Step `step:3.1-reflection` (paper L841-859): by the dihedral symmetry of `ℤ^d` and of
Bernoulli percolation, and the covariance of corrected planes under it, if the corrected plane of
slope `q` is almost surely `L`-Lipschitz, then so are those of the reflected slopes `T_j q` and of
the slopes with two coordinates exchanged. -/
def ReflectionStep (d : ℕ) [NeZero d] (p : unitInterval) : Prop :=
  ∀ (L : ℝ) (q : Fin d → ℝ), (∀ᵐ ω ∂latticeBondLaw d p, q ∈ lipschitzSlopeSet ω L) →
    (∀ j, ∀ᵐ ω ∂latticeBondLaw d p, reflectSlope j q ∈ lipschitzSlopeSet ω L) ∧
    ∀ i j, ∀ᵐ ω ∂latticeBondLaw d p, q ∘ Equiv.swap i j ∈ lipschitzSlopeSet ω L

/-- A Lipschitz bound persists under a larger constant. -/
theorem isLipschitzWith_mono {ω : Configuration d} {C : OpenComponent ω} {L L' : ℝ}
    {u : C → ℝ} (hu : IsLipschitzWith C L u) (hL : L ≤ L') : IsLipschitzWith C L' u :=
  fun x y => (hu x y).trans (mul_le_mul_of_nonneg_right hL (Nat.cast_nonneg _))

/-- The union bound over integers: if nonconstant Lipschitz harmonic functions exist with
positive probability, then so does the event `E_{n+1}` for some integer `n`. -/
theorem exists_lipschitzHarmonicEvent_ne_zero [NeZero d] {p : unitInterval}
    (hN : latticeBondLaw d p {ω | ∃ h : HasUniqueInfiniteOpenComponent ω,
      ∃ u : uniqueInfiniteComponent h → ℝ,
        (∀ x, componentLaplacian (uniqueInfiniteComponent h) u x = 0) ∧
        ComponentLipschitz (uniqueInfiniteComponent h) u ∧ ∃ x y, u x ≠ u y} ≠ 0) :
    ∃ n : ℕ, latticeBondLaw d p (lipschitzHarmonicEvent d ((n : ℝ) + 1)) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  refine hN (measure_mono_null ?_ (measure_iUnion_null hcon))
  rintro ω ⟨h, u, hharm, ⟨K, -, hK⟩, hnc⟩
  refine Set.mem_iUnion.2 ⟨⌈K⌉₊, h, u, hharm, isLipschitzWith_mono hK ?_, hnc⟩
  linarith [Nat.le_ceil K]

/-- A slope with its coordinates in `s` set to zero. -/
def zeroSlope (s : Finset (Fin d)) (q : Fin d → ℝ) : Fin d → ℝ :=
  fun i => if i ∈ s then 0 else q i

/-- Averaging a slope with its reflection `T_j` sets its `j`-th coordinate to zero. -/
theorem half_add_half_reflectSlope_zeroSlope (j : Fin d) (s : Finset (Fin d))
    (q : Fin d → ℝ) :
    (1 / 2 : ℝ) • zeroSlope s q + (1 / 2 : ℝ) • reflectSlope j (zeroSlope s q) =
      zeroSlope (insert j s) q := by
  funext i
  by_cases hij : i = j
  · subst hij
    simp [reflectSlope, zeroSlope]
  · simp only [reflectSlope, zeroSlope, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Function.update_of_ne hij, Finset.mem_insert, hij, false_or]
    split_ifs <;> ring

/-- Zeroing every coordinate but the first leaves a multiple of `e₁`. -/
theorem zeroSlope_erase_zero [NeZero d] (q : Fin d → ℝ) :
    zeroSlope (Finset.univ.erase 0) q = q 0 • slopeE1 d := by
  funext i
  by_cases hi : i = 0
  · subst hi
    simp [zeroSlope, slopeE1]
  · simp [zeroSlope, slopeE1, hi]

/-- Lemma 3.1 follows from its five steps. -/
theorem reductionToSlopeE1_of_steps [NeZero d] {p : unitInterval}
    (h01 : ZeroOneStep d p) (hA1 : LipschitzMemA1Step d p) (hclosed : ClosedSlopesStep d p)
    (hdet : DeterministicSlopeStep d p) (hrefl : ReflectionStep d p) :
    ReductionToSlopeE1Stmt d p := by
  intro hN
  obtain ⟨n, hn⟩ := exists_lipschitzHarmonicEvent_ne_zero hN
  set L : ℝ := (n : ℝ) + 1 with hL
  have hL0 : 0 < L := by positivity
  have hE : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ lipschitzHarmonicEvent d L :=
    (h01 L).resolve_left hn
  have hex : ∀ᵐ ω ∂latticeBondLaw d p, ∃ q ≠ 0, q ∈ lipschitzSlopeSet ω L := by
    filter_upwards [hE, hA1] with ω ⟨h, u, hharm, hlip, hnc⟩ hω
    exact hω h L u hharm hlip hnc
  obtain ⟨q, hq0, hq⟩ := hdet L (hclosed.mono fun ω hω => (hω L).1) hex
  obtain ⟨j, hj⟩ : ∃ j, q j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hq0 (funext hcon)
  set r : Fin d → ℝ := q ∘ Equiv.swap 0 j with hr_def
  have hr : ∀ᵐ ω ∂latticeBondLaw d p, r ∈ lipschitzSlopeSet ω L := (hrefl L q hq).2 0 j
  have hr0 : r 0 ≠ 0 := by
    simpa [hr_def, Equiv.swap_apply_left] using hj
  have hzero : ∀ s : Finset (Fin d),
      ∀ᵐ ω ∂latticeBondLaw d p, zeroSlope s r ∈ lipschitzSlopeSet ω L := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [show zeroSlope ∅ r = r from funext fun i => by simp [zeroSlope]]
      exact hr
    | insert i s _ ih =>
      filter_upwards [ih, (hrefl L _ ih).1 i, hclosed] with ω h1 h2 hω
      have hmem := (hω L).2 L (1 / 2) (1 / 2) _ _ h1 h2
      rwa [half_add_half_reflectSlope_zeroSlope,
        show |(1 / 2 : ℝ)| * L + |(1 / 2 : ℝ)| * L = L by
          rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]; ring] at hmem
  refine ⟨|r 0|⁻¹ * L, by positivity, ?_⟩
  filter_upwards [hzero (Finset.univ.erase 0), hclosed] with ω h1 hω
  have hmem := (hω L).2 L (r 0)⁻¹ 0 _ _ h1 h1
  rw [zeroSlope_erase_zero, smul_smul, inv_mul_cancel₀ hr0, one_smul, zero_smul, add_zero,
    abs_inv, abs_zero, zero_mul, add_zero] at hmem
  exact hmem

end Rigidity.Steps.S3
