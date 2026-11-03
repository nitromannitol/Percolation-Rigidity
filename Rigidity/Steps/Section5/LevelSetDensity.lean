import Rigidity.Steps.Section5.GoodEventDensity
import Rigidity.Proofs.Section5.PotentialLaplacian

/-!
# Proposition 5.11: sensitive sites and the printed conclusion

Shared definitions for Proposition 5.11 (`prop:level-set-of-harmonic-function`, corrected draft
L1732-1738, proof L2423-2429):

* `sensitiveSites C u ℓ C₀`: the sites within `ℓ¹`-distance `C₀` of an edge of `𝒞_∞` on which
  `∇u ≠ 0` and `∇ℓ ≠ 0`; the counting step `step:5.11-count` charges each sensitive edge of
  `B_{2^k}` by at most `(2C₀ + 1)²` such sites.
* `LevelSetDensityAt p f q`: the conclusion of Proposition 5.11 at the slope `q` as printed, with
  an upper limit (`lim sup`, for infinitely many `k`). The draft `LevelSetDensityStmt` states the
  lower limit (`∀ᶠ k`, `LevelSetDensityEventuallyAt`, [C29]), which Step 3 of Proposition 5.7
  consumes and which implies the printed form (`levelSetDensityAt_of_eventually`).
* Finiteness of the cube and of the truncated triangle, used by the counting.

The proof of Proposition 5.11 in the draft form: at the slope `e₁` from the draft Lemma 5.27
(`Rigidity/Steps/Section5/LevelSetDensityEventual.lean`, `levelSetDensityEventuallyAt_e1_of_steps`);
at every slope `q ≠ 0` from Lemma 5.27 at slope `q` (`Rigidity/Steps/Section5/GeneralSlope.lean`,
[C30]). The potential `u_f - lim u_f` is a decaying potential by `potentialLaplacian`.

Issues in the printed proof.
* Slope. Proposition 5.11 is stated for a fixed slope `p ≠ 0` [C19], while Lemma 5.27, its
  good events `G_2`, `G_3` and the end of the printed proof (L2428) only treat `∇ℓ_{e₁}`; the map
  `Θ` of L2426 into the edges with `∇ℓ_p ≠ 0` is not constructed for `p ≠ ±e₁`. The remark L2370
  ("symmetry arguments ensure that this assumption can be made without loss of generality")
  covers the lattice directions at most. The proof is rerun at slope `q` in `GeneralSlope.lean`
  ([C30], gap G7).
* Constants. `GoodEventDensityStmt` (Lemma 5.26) holds for `C_χ ≥ 1` and `K ≥ K₀(C_χ, C_f, R, c₁)`,
  while `LargeGradientSensitiveStmt` (Lemma 5.27) chooses its own `C_χ` and `K₀`, with no relation
  to these; the two drafted statements do not compose (the paper uses one `K₀` for both). The proof
  uses the two steps of Lemma 5.26 that hold for all parameters (`TriangleDensityStep`,
  `GoodEventTranslationStep`) directly.
-/

open MeasureTheory Filter Topology LatticeProb.Percolation

namespace Rigidity.Steps.Section5

open Rigidity.Section5

variable {ω : Configuration 2}

/-- The sites `x₀ ∈ ℤ²` within `ℓ¹`-distance `C₀` of an oriented edge `(a, b)` of the component
on which `∇u ≠ 0` and `∇ℓ ≠ 0`. -/
def sensitiveSites (C : OpenComponent ω) (u ℓ : C → ℝ) (C₀ : ℝ) : Set (Vertex 2) :=
  {x₀ | ∃ a b : C, (componentGraph C).Adj a b ∧ l1 (a.val - x₀) ≤ C₀ ∧ ℓ a ≠ ℓ b ∧ u a ≠ u b}

/-- The conclusion of Proposition 5.11 for the slope `q` as printed, with an upper limit (`lim sup`);
the draft statement has the lower limit ([C29], `LevelSetDensityEventuallyAt`, which implies this
form: `levelSetDensityAt_of_eventually`). -/
def LevelSetDensityAt (p : unitInterval) (f : Vertex 2 → ℤ) (q : Fin 2 → ℝ) : Prop :=
  ∀ᵐ ω ∂latticeBondLaw 2 p, ∃ h : HasUniqueInfiniteOpenComponent ω,
    mass (uniqueInfiniteComponent h) f = 0 →
    ∀ G, IsGreenFamily (uniqueInfiniteComponent h) G →
    ∀ ℓ, IsCorrectedPlane (uniqueInfiniteComponent h) q ℓ →
    ∀ L : ℝ, Tendsto (potential _ G f) cofinite (𝓝 L) →
      (Function.support (fun x => potential _ G f x - L)).Infinite →
      ∃ c : ℝ, 0 < c ∧ ∀ K : ℕ, ∃ k : ℕ, K ≤ k ∧
        c ≤ ((activeEdges _ (potential _ G f) ℓ (2 ^ k)).ncard : ℝ) / (Real.pi * 4 ^ k)

theorem cube_finite (L : ℕ) : (cube L).Finite := by
  refine (Set.finite_Icc (fun _ : Fin 2 => -(L : ℤ)) (fun _ => (L : ℤ))).subset ?_
  intro y hy
  exact ⟨fun i => (abs_le.1 (hy i)).1, fun i => (abs_le.1 (hy i)).2⟩

theorem triangle_subset_cube (L : ℕ) : triangle L ⊆ cube L := by
  rintro y ⟨h1, h0⟩ i
  have h0' : 0 ≤ y 0 := (abs_nonneg _).trans h1
  fin_cases i
  · simpa [abs_of_nonneg h0'] using h0
  · exact h1.trans h0

/-- The sites of the triangles `T_L` with first coordinate below `M` form a finite set. -/
theorem triangleBelow_finite (M : ℝ) : {y : Vertex 2 | |y 1| ≤ y 0 ∧ (y 0 : ℝ) < M}.Finite := by
  refine (cube_finite ⌈M⌉₊).subset ?_
  rintro y ⟨h1, h0⟩
  have hm : y 0 ≤ (⌈M⌉₊ : ℤ) := by
    have : (y 0 : ℝ) ≤ ((⌈M⌉₊ : ℤ) : ℝ) := by
      push_cast
      exact h0.le.trans (Nat.le_ceil M)
    exact_mod_cast this
  exact triangle_subset_cube ⌈M⌉₊ ⟨h1, hm⟩

end Rigidity.Steps.Section5
