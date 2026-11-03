import Rigidity.Steps.Section5.GradientTrichotomy
import Rigidity.Steps.Section5.LargeGradientSensitive
import Rigidity.Proofs.Section5.SensitiveEdgeCount
import Rigidity.Proofs.Section5.GoodEventBasics

/-!
# Proposition 5.11 in `lim inf` form at the slope `e₁`

Step 3 of Proposition 5.7 (corrected draft L1833-1836) needs Proposition 5.11
(`prop:level-set-of-harmonic-function`, L1732-1738, proof L2423-2429) with `lim inf` in place of
`lim sup`: almost surely the density of the edges of `B_{2^k}` with `∇u_f ≠ 0` and `∇ℓ ≠ 0` is at
least `c > 0` for all large `k` (`LevelSetDensityEventuallyAt`, stated in
`Rigidity/Steps/Section5/GradientTrichotomy.lean`; see the issues listed there). The proof of
Proposition 5.11 gives this form at the slope `e₁`, which is the slope its proof treats:

* the ergodic theorem on the triangles (`TriangleDensityStep`) gives a limit
  `L⁻² |{y ∈ T_L : τ_{-y} ω ∈ A}| → P[A]`, hence at least `(P[A] / 2) L²` sensitive sites in `Q_L`
  for all large `L` (`sensitiveSiteDensityEventually_e1_of_goodEvent`), not only for infinitely
  many `L`;
* the counting of `step:5.11-count` holds with `∀ᶠ` in place of `∃ᶠ`
  (`sensitiveEdgeCountEventuallyStep`): for `k ≥ 3` take `L = 2^{k-3}`, so that `B_{2^k} ⊇` the
  edges charged by `Q_L` and `|B_{2^k}| = π 4^k = 64 π L²`.

The conclusion is drawn from the draft Lemma 5.27 (`levelSetDensityEventuallyAt_e1_of_steps`,
from `LargeGradientSensitiveStmt`, with the universal `G_1` [C31] and the direction-free `G_3`
[C32]); the translation covariance of the good event is `goodEventTranslationStep`.
-/

open MeasureTheory Filter Topology LatticeProb.Percolation

namespace Rigidity.Steps.Section5

open Rigidity.Section5 Rigidity.Proofs.Section5

variable {ω : Configuration 2}

/-! ### Counting with `∀ᶠ` -/

/-- `step:5.11-count` with `∀ᶠ` in place of `∃ᶠ`: if, for all large `L`, at least `c L²` sites of
the cube `Q_L` lie within `ℓ¹`-distance `C₀` of an edge on which `∇u ≠ 0` and `∇ℓ ≠ 0`, then
`|B_{2^k}|⁻¹ |{e ∈ E(B_{2^k}) : ∇u(e) ≠ 0, ∇ℓ(e) ≠ 0}|` is bounded below for all large `k`. -/
def SensitiveEdgeCountEventuallyStep : Prop :=
  ∀ (ω : Configuration 2) (C : OpenComponent ω) (u ℓ : C → ℝ) (C₀ c : ℝ), 0 < c →
    (∀ᶠ L : ℕ in atTop, c * (L : ℝ) ^ 2 ≤ ((cube L ∩ sensitiveSites C u ℓ C₀).ncard : ℝ)) →
    ∃ c' : ℝ, 0 < c' ∧ ∀ᶠ k : ℕ in atTop,
      c' ≤ ((activeEdges C u ℓ (2 ^ k)).ncard : ℝ) / (Real.pi * 4 ^ k)

/-- `step:5.11-count` with `∀ᶠ` (deterministic): with `N = ⌈C₀⌉` and `L = 2^{k-3}`, the bound
`c L² ≤ |Q_L ∩ S| ≤ |Q_N| |{e ∈ E(B_{2^k}) : ∇u(e) ≠ 0, ∇ℓ(e) ≠ 0}|` and `π 4^k = 64 π L²` give
the density `c / (64 π |Q_N|)` for all large `k`. -/
theorem sensitiveEdgeCountEventuallyStep : SensitiveEdgeCountEventuallyStep := by
  intro ω C u ℓ C₀ c hc hev
  set N := ⌈C₀⌉₊
  have hn : 0 < (cube N).ncard :=
    (Set.ncard_pos (cube_finite N)).2 ⟨0, fun i => by simp⟩
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.1 hev
  refine ⟨c / (64 * Real.pi * (cube N).ncard), by positivity,
    eventually_atTop.2 ⟨L₀ + N + 4, fun k hk => ?_⟩⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
  have hjL : j < 2 ^ j := Nat.lt_two_pow_self
  have hcount := hL₀ (2 ^ j) (by omega)
  have hNL : (N + 1 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by exact_mod_cast (show N + 1 ≤ 2 ^ j by omega)
  have h8 : (2 : ℝ) ^ (j + 3) = 8 * ((2 ^ j : ℕ) : ℝ) := by push_cast; ring
  have hr : 2 * ((2 ^ j : ℕ) : ℝ) + N + 1 < (2 : ℝ) ^ (j + 3) := by
    rw [h8]
    have : (0 : ℝ) ≤ N := N.cast_nonneg
    linarith
  have hcnt := ncard_cube_inter_sensitiveSites_le C u ℓ (Nat.le_ceil C₀) hr
  have hS : ((cube (2 ^ j) ∩ sensitiveSites C u ℓ C₀).ncard : ℝ) ≤
      ((activeEdges C u ℓ ((2 : ℝ) ^ (j + 3))).ncard : ℝ) * (cube N).ncard := by
    exact_mod_cast hcnt
  have h4k : (4 : ℝ) ^ (j + 3) = 64 * ((2 ^ j : ℕ) : ℝ) ^ 2 := by
    calc (4 : ℝ) ^ (j + 3) = ((2 : ℝ) ^ (j + 3)) ^ 2 := by
          rw [← pow_mul, mul_comm, pow_mul]; norm_num
      _ = 64 * ((2 ^ j : ℕ) : ℝ) ^ 2 := by rw [h8]; ring
  rw [div_le_div_iff₀ (by positivity) (by positivity), h4k]
  calc c * (Real.pi * (64 * ((2 ^ j : ℕ) : ℝ) ^ 2))
      = 64 * Real.pi * (c * ((2 ^ j : ℕ) : ℝ) ^ 2) := by ring
    _ ≤ 64 * Real.pi *
          (((activeEdges C u ℓ ((2 : ℝ) ^ (j + 3))).ncard : ℝ) * (cube N).ncard) :=
        mul_le_mul_of_nonneg_left (hcount.trans hS) (by positivity)
    _ = ((activeEdges C u ℓ (2 ^ (j + 3))).ncard : ℝ) * (64 * Real.pi * (cube N).ncard) := by
        ring

/-! ### Density of sensitive sites for all large `L` -/

/-- Positive density of sensitive sites for the corrected plane of slope `q`, for all large `L`:
there are `c > 0` and `C₀` such that, almost surely, for every decaying potential `u` of `f` with
infinite support and every corrected plane `ℓ_q`, for all large `L` at least `c L²` sites of `Q_L`
lie within `ℓ¹`-distance `C₀` of an edge of `𝒞_∞` on which `∇u ≠ 0` and `∇ℓ_q ≠ 0`. -/
def SensitiveSiteDensityEventually (p : unitInterval) (f : Vertex 2 → ℤ) (q : Fin 2 → ℝ) :
    Prop :=
  ∃ c C₀ : ℝ, 0 < c ∧ ∀ᵐ ω ∂latticeBondLaw 2 p, ∃ h : HasUniqueInfiniteOpenComponent ω,
    ∀ u, IsDecayingPotential (uniqueInfiniteComponent h) f u → (Function.support u).Infinite →
    ∀ ℓ, IsCorrectedPlane (uniqueInfiniteComponent h) q ℓ →
      ∀ᶠ L : ℕ in atTop, c * (L : ℝ) ^ 2 ≤
        ((cube L ∩ sensitiveSites (uniqueInfiniteComponent h) u ℓ C₀).ncard : ℝ)

/-- The density of sensitive sites for the slope `e₁` for all large `L`, from a family of good
events `G(x)` with `τ_{-x} ω ∈ G(0) → ω ∈ G(x)`, a null-measurable `A ⊆ G(0)` with `P[A] > 0`, the
ergodic theorem on the triangles, and the conclusion of Lemma 5.27 (ii) for `G`. The limit
`P[A]` of `L⁻² |{y ∈ T_L : τ_{-y} ω ∈ A}|` exceeds `3 P[A] / 4` for all large `L`. -/
theorem sensitiveSiteDensityEventually_e1_of_goodEvent {p : unitInterval} {f : Vertex 2 → ℤ}
    (G : Vertex 2 → Set (Configuration 2))
    (hT : ∀ (y : Vertex 2) (ω : Configuration 2), configurationTranslation (-y) ω ∈ G 0 → ω ∈ G y)
    (hD : TriangleDensityStep p) {A : Set (Configuration 2)} (hAG : A ⊆ G 0)
    (hAm : NullMeasurableSet A (latticeBondLaw 2 p)) (hApos : 0 < latticeBondLaw 2 p A)
    {C₀ : ℝ}
    (hae : ∀ᵐ ω ∂latticeBondLaw 2 p, ∃ h : HasUniqueInfiniteOpenComponent ω, ∃ M : ℝ,
      ∀ u, IsDecayingPotential (uniqueInfiniteComponent h) f u → (Function.support u).Infinite →
      ∀ ℓ, IsCorrectedPlane (uniqueInfiniteComponent h) (Pi.single 0 1) ℓ →
      ∀ x₀ : Vertex 2, |x₀ 1| ≤ x₀ 0 → M ≤ x₀ 0 → ω ∈ G x₀ →
        ∃ a b : uniqueInfiniteComponent h, (componentGraph _).Adj a b ∧
          l1 (a.val - x₀) ≤ C₀ ∧ ℓ a ≠ ℓ b ∧ u a ≠ u b) :
    SensitiveSiteDensityEventually p f (Pi.single 0 1) := by
  set P := (latticeBondLaw 2 p A).toReal with hP
  have hPpos : 0 < P := ENNReal.toReal_pos hApos.ne' (measure_ne_top _ _)
  refine ⟨P / 2, C₀, by positivity, ?_⟩
  filter_upwards [hae, hD A hAm] with ω hω hdens
  obtain ⟨h, M, hM⟩ := hω
  refine ⟨h, fun u hu hsu ℓ hℓ => ?_⟩
  set S := sensitiveSites (uniqueInfiniteComponent h) u ℓ C₀
  set B : Set (Vertex 2) := {y | |y 1| ≤ y 0 ∧ (y 0 : ℝ) < M}
  have hcard : ∀ L : ℕ,
      ({y | y ∈ triangle L ∧ configurationTranslation (-y) ω ∈ A}.ncard : ℝ) ≤
        ((cube L ∩ S).ncard : ℝ) + B.ncard := by
    intro L
    have hsub :
        {y | y ∈ triangle L ∧ configurationTranslation (-y) ω ∈ A} ⊆ (cube L ∩ S) ∪ B := by
      rintro y ⟨hyT, hyA⟩
      by_cases hyM : M ≤ (y 0 : ℝ)
      · exact Or.inl ⟨triangle_subset_cube L hyT,
          hM u hu hsu ℓ hℓ y hyT.1 hyM (hT y ω (hAG hyA))⟩
      · exact Or.inr ⟨hyT.1, not_le.1 hyM⟩
    have hfin : ((cube L ∩ S) ∪ B).Finite :=
      ((cube_finite L).subset Set.inter_subset_left).union (triangleBelow_finite M)
    exact_mod_cast (Set.ncard_le_ncard hsub hfin).trans (Set.ncard_union_le _ _)
  have h1 := hdens.eventually (lt_mem_nhds (show 3 * P / 4 < P by linarith))
  filter_upwards [h1, eventually_ge_atTop (⌈4 * B.ncard / P⌉₊ + 1)] with L hL1 hL2
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast (show 1 ≤ L by omega)
  have hLb : 4 * (B.ncard : ℝ) / P ≤ L :=
    (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈4 * (B.ncard : ℝ) / P⌉₊ ≤ L by omega))
  rw [div_le_iff₀ hPpos] at hLb
  rw [lt_div_iff₀ (by positivity)] at hL1
  have hLL : (L : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith
  have := hcard L
  nlinarith

/-- Proposition 5.11 in `lim inf` form for a slope `q`, from the density of sensitive sites for `q`
for all large `L` and `step:5.11-count` with `∀ᶠ`, applied to the decaying potential
`u_f - lim u_f`. -/
theorem levelSetDensityEventuallyAt_of_sensitiveSiteDensityEventually {p : unitInterval}
    {f : Vertex 2 → ℤ} {q : Fin 2 → ℝ} (hf : (Function.support f).Finite)
    (hq : SensitiveSiteDensityEventually p f q) : LevelSetDensityEventuallyAt p f q := by
  obtain ⟨c, C₀, hc, hae⟩ := hq
  filter_upwards [hae] with ω hω
  obtain ⟨h, hω⟩ := hω
  refine ⟨h, ?_⟩
  intro _ Gr hG ℓ hℓ L hL hsupp
  set u : uniqueInfiniteComponent h → ℝ := fun x => potential _ Gr f x - L with hu_def
  have hu : IsDecayingPotential (uniqueInfiniteComponent h) f u := by
    refine ⟨fun x => ?_, ?_⟩
    · have hlap : componentLaplacian _ u x = componentLaplacian _ (potential _ Gr f) x := by
        simp only [componentLaplacian, u, sub_sub_sub_cancel_right]
      rw [hlap]
      exact Rigidity.Proofs.Section5.potentialLaplacian ω _ Gr hG f hf x
    · simpa [u] using hL.sub_const L
  obtain ⟨c', hc', hk⟩ := sensitiveEdgeCountEventuallyStep ω _ u ℓ C₀ c hc (hω u hu hsupp ℓ hℓ)
  have hact : ∀ r : ℝ, activeEdges _ u ℓ r = activeEdges _ (potential _ Gr f) ℓ r := by
    intro r
    ext e
    simp only [activeEdges, Set.mem_setOf_eq, u, ne_eq, sub_left_inj]
  exact ⟨c', hc', by simpa only [hact] using hk⟩

/-! ### The draft good event -/

/-- Proposition 5.11 in `lim inf` form for the slope `e₁`, from the draft Lemma 5.27
(`LargeGradientSensitiveStmt`) and the ergodic theorem on the triangles (`TriangleDensityStep`);
the translation covariance of `G` is `goodEventTranslationStep`. -/
theorem levelSetDensityEventuallyAt_e1_of_steps {p : unitInterval} {f : Vertex 2 → ℤ}
    (hf : (Function.support f).Finite) (hD : TriangleDensityStep p)
    (h527 : LargeGradientSensitiveStmt p f) : LevelSetDensityEventuallyAt p f (Pi.single 0 1) := by
  obtain ⟨Cf, R, c₁, Cχ, K₀, C₀, ⟨A, hAG, hAm, hApos⟩, hae⟩ := h527 hf
  exact levelSetDensityEventuallyAt_of_sensitiveSiteDensityEventually hf
    (sensitiveSiteDensityEventually_e1_of_goodEvent (fun x => eventG Cf R c₁ x Cχ K₀)
      (fun y ω hω => (goodEventTranslationStep Cf R c₁ Cχ K₀ y ω).2 hω) hD hAG
      hAm.nullMeasurableSet hApos hae)

end Rigidity.Steps.Section5
