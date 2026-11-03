import Rigidity.Steps.Section5.LevelSetDensityEventual
import Rigidity.Steps.S3.NotLipschitzInner
import Rigidity.Proofs.Section5.TriangleDensity
import Rigidity.Proofs.Section5.ThirdGoodEvent
import Rigidity.Proofs.Section5.SecondGoodEvent
import Rigidity.Proofs.Section5.CorrectedPlaneMinimalScale
import Rigidity.Proofs.Section5.ExplorationBlocks
import Rigidity.Proofs.Section5.RootBlock
import Rigidity.Proofs.Section5.LeafSensitive
import Rigidity.Proofs.Section5.FluxBalance
import Rigidity.Proofs.Section5.FluxGrowth
import Rigidity.Proofs.Section5.GreedyExploration
import Rigidity.Proofs.Section5.ExplorationAssembly
import Rigidity.Proofs.Section5.InfiniteBranches
import Rigidity.Proofs.Section5.LeafExit
import Rigidity.Proofs.Section5.LeafSeparator
import Rigidity.Proofs.Section5.NoK33Minor
import LatticeProb.Prob.Percolation.CorrectedPlaneAlgebra

/-!
# Proposition 5.11 for a general slope: the good events and Lemmas 5.25-5.28 at slope `q`

Proposition 5.11 (`prop:level-set-of-harmonic-function`, corrected draft L1732-1738, proof
L2423-2429) is stated for every slope `q ≠ 0` and in `lim inf` form ([C29], [C30]); the printed
proof treats the corrected plane `ℓ_{e₁}` only (good events L2342-2371, Lemma 5.27 L2413-2419,
end of the proof L2428). This file runs the proof at a general slope `q`; the composed
Propositions 5.11 and 5.7 for every `q ≠ 0` are `Rigidity.Assembly.levelSetDensity` and
`Rigidity.Assembly.gradientTrichotomy` (`Rigidity/Proofs/Assembly/Section5GeneralSlope.lean`).

**Good events at slope `q`.** For a slope `q`, a constant `Λ` and a lattice direction `v`:
`G_2^q(x, K)` (`eventG2At`): `osc_{Q_{R'}(x) ∩ 𝒞_∞} ℓ_q ≤ Λ R'` for every `R' ≥ K`;
`G_3^{q,v}(x, C_χ)` (`eventG3At`): `(x, x + v)` is an edge of `𝒞_∞` with
`ℓ_q(x + v) - ℓ_q(x) ≥ C_χ`; `G^{q,v} = G_1 ∩ G_2^q ∩ G_3^{q,v}` (`eventGAt`), with the universal
first good event of the draft ([C31]). For `q = e₁`, `Λ = 4` these are the draft `G_2` and, for
`v = e₁`, the printed edge event (`eventG2At_e1`, `eventG3At_e1`, `eventGAt_e1`); the draft `G_3`
is direction-free ([C32]).

**Lemma 5.27 at slope `q`** (`LargeGradientSensitiveAtStmt`): the triangle `x₁ ≥ |x₂|` is replaced
by the cone `κ |x₀|₁ ≤ q · x₀` (every `κ > 0`) and `M ≤ x₀,₁` by `M ≤ |x₀|₁`; for `q = e₁` and
`κ = 1/2` the cone is the triangle.

**The reduction.** `levelSetDensityEventuallyAt_of_largeGradientSensitiveAt` and
`levelSetDensity_of_largeGradientSensitiveAt` derive Proposition 5.11 (`lim inf` form at slope
`q`, and the draft `LevelSetDensityStmt`) from Lemma 5.27 at every slope `q ≠ 0`. Lemma 5.26 at
slope `q` needs no cone: since `-ℓ_q` is a corrected plane of slope `-q` with the same sensitive
sites, `q₀ ≥ 0` may be assumed, and one of the rectangles `[0, n) × [n, 2n)` (`q₁ > 0`),
`[n, 2n) × [0, n)` (`q₁ = 0`), `[0, n) × [-2n, -n)` (`q₁ < 0`), `n = ⌊L/2⌋`, lies in
`Q_L ∩ {κ |x|₁ ≤ q · x, |x|₁ ≥ n}`; the ergodic theorem on anchored rectangles
(`ae_tendsto_upperRect`, `ae_tendsto_lowerRect`) gives the density `P[A]` on it.

**Lemmas 5.25-5.28 at slope `q`.**
* Slope-free, carry over verbatim: `ExplorationBlockStep`, `FluxGrowthStep`,
  `GreedyExplorationStep`, `ExplorationAssemblyStep`, `TerminationWindowStep` (they do not mention
  the slope), the first good event and its bound (Prop 5.24, Lemma 5.25), and the translation
  covariance (`eventGAt_translation`).
* Verbatim with `ℓ_q` for `ℓ_{e₁}` (their proofs use only `Δ ℓ = 0`): the harmonic versions
  `RootBlockHarmonicStep`, `LeafSensitiveHarmonicStep`, `FluxBalanceHarmonicStep`,
  `LeafExitHarmonicStep` and Lemma 5.28 for every initial edge (`FiniteBranchesHarmonicStmt`,
  `finiteBranchesHarmonic_of_steps`).
* Slope geometry, same proof: `CorrectedPlaneMinimalScaleAtStep` (Theorem 2.5 at slope `q` on the
  cone `κ |x|₁ ≤ q · x`, and the half-line `L_-` replaced by a lattice half-line along which
  `q · x → -∞`) and `ExplorationHolesRayStep` (a lattice half-line through `Q_r`). The glue
  (`largeGradientSensitiveAt_of_steps`) uses `G_2^q` with `Λ = 4 |q|₁ + 1`
  (`secondGoodEventAtStep`, Theorem 2.5 at slope `q`), which only changes `C_χ`.
* The third good event. The proof of Lemma 5.27 uses the edge `(x₀, x₁)` only as an edge across
  which `ℓ` increases by `C_χ` ([C32]). `P[G_3^{q,v}(0, C_χ)] > 0` for some lattice unit vector `v`
  follows from the unsigned bound `P[0 ∈ 𝒞_∞, |∇ℓ_q(0)| > L] > 0` for all `L` (pigeonhole on the
  edges `(0, ±e_i)` and stationarity), with the uniqueness of `ℓ_q` up to constants
  (`exists_eventG3At_of_notLipschitzAt`); Lemma 5.25 at slope `q` is `goodEventPositiveAt_of_steps`.
* Proposition 3.2 at slope `q` (`NotLipschitzAtStep p q`) is proved for every `q ≠ 0` from
  Proposition 3.2 at `e₁` by the reflection identity of Lemma 3.1 (`Rigidity.Steps.S3.notLipschitzAt`,
  `Rigidity/Steps/S3/NotLipschitzAt.lean`; [C30]); the combination
  `ℓ_q = q₁ ℓ_{e₁} + q₂ ℓ_{e₂}` alone would not transfer the lower bound (the two gradients may
  cancel).

`levelSetDensity_of_notLipschitzAt` composes these: the draft `LevelSetDensityStmt p f` from
`NotLipschitzAtStep p q` for every `q ≠ 0`, Lemma 5.16, Props 5.12, 5.20, 5.24, Theorem 2.5 and the
external inputs.
-/

open MeasureTheory Filter Topology LatticeProb.Percolation

namespace Rigidity.Steps.Section5

open Rigidity.Section5 Rigidity.Proofs.Section5

/-! ### The good events at slope `q` -/

/-- The value `q · x` of the affine plane of slope `q` at `x`. -/
def slopeDot (q : Fin 2 → ℝ) (x : Vertex 2) : ℝ := q 0 * (x 0 : ℝ) + q 1 * (x 1 : ℝ)

/-- The second good event at slope `q` with constant `Λ`: for every `R' ≥ K`, the oscillation of
every corrected plane `ℓ_q` on `Q_{R'}(x) ∩ 𝒞_∞` is at most `Λ R'`. -/
def eventG2At (q : Fin 2 → ℝ) (Λ : ℝ) (x : Vertex 2) (K : ℝ) : Set (Configuration 2) :=
  {ω | ∃ h : HasUniqueInfiniteOpenComponent ω, ∀ ℓ,
    IsCorrectedPlane (uniqueInfiniteComponent h) q ℓ →
    ∀ R' : ℕ, K ≤ R' → ∀ y z : uniqueInfiniteComponent h, y.val ∈ cubeAt x R' →
      z.val ∈ cubeAt x R' → ℓ y - ℓ z ≤ Λ * R'}

/-- The third good event at slope `q` in direction `v`: `(x, x + v)` is an edge of `𝒞_∞` across
which every corrected plane `ℓ_q` increases by at least `C_χ`. -/
def eventG3At (q : Fin 2 → ℝ) (v x : Vertex 2) (Cχ : ℝ) : Set (Configuration 2) :=
  {ω | ∃ h : HasUniqueInfiniteOpenComponent ω, ∃ hx : x ∈ (uniqueInfiniteComponent h).supp,
    ∃ hx' : x + v ∈ (uniqueInfiniteComponent h).supp,
      (componentGraph _).Adj ⟨x, hx⟩ ⟨x + v, hx'⟩ ∧
      ∀ ℓ, IsCorrectedPlane (uniqueInfiniteComponent h) q ℓ →
        Cχ ≤ ℓ ⟨x + v, hx'⟩ - ℓ ⟨x, hx⟩}

/-- The good event at slope `q` in direction `v`: `G_1^∀(x, K) ∩ G_2^q(x, K) ∩ G_3^{q,v}(x, C_χ)`. -/
def eventGAt (Cf : ℕ) (R c₁ : ℝ) (q : Fin 2 → ℝ) (Λ : ℝ) (v x : Vertex 2) (Cχ K : ℝ) :
    Set (Configuration 2) :=
  eventG1 Cf R c₁ x K ∩ eventG2At q Λ x K ∩ eventG3At q v x Cχ

theorem eventG2At_e1 (x : Vertex 2) (K : ℝ) : eventG2At (Pi.single 0 1) 4 x K = eventG2 x K :=
  rfl

theorem eventG3At_e1 (x : Vertex 2) (Cχ : ℝ) :
    eventG3At (Pi.single 0 1) e1 x Cχ = eventG3Edge x Cχ :=
  rfl

theorem eventGAt_e1 (Cf : ℕ) (R c₁ : ℝ) (x : Vertex 2) (Cχ K : ℝ) :
    eventGAt Cf R c₁ (Pi.single 0 1) 4 e1 x Cχ K =
      eventG1 Cf R c₁ x K ∩ eventG2 x K ∩ eventG3Edge x Cχ :=
  rfl

/-- Lemma 5.27 at slope `q` (direction `v` of `G_3` free): there are parameters with
`P[G^{q,v}(0, C_χ, K₀)] > 0` and, for every `κ > 0`, almost surely a scale `M` such that for every
`x₀` with `κ |x₀|₁ ≤ q · x₀` and `|x₀|₁ ≥ M` at which `G^{q,v}(x₀, C_χ, K₀)` holds, some edge of
`𝒞_∞` within `C₀` of `x₀` has `∇ℓ_q ≠ 0` and `∇u ≠ 0`. -/
def LargeGradientSensitiveAtStmt (p : unitInterval) (f : Vertex 2 → ℤ) (q : Fin 2 → ℝ) : Prop :=
  (Function.support f).Finite →
  ∃ (Cf : ℕ) (R c₁ Λ Cχ K₀ C₀ : ℝ) (v : Vertex 2),
    (∃ A ⊆ eventGAt Cf R c₁ q Λ v 0 Cχ K₀, MeasurableSet A ∧ 0 < latticeBondLaw 2 p A) ∧
    ∀ κ : ℝ, 0 < κ → ∀ᵐ ω ∂latticeBondLaw 2 p, ∃ h : HasUniqueInfiniteOpenComponent ω,
      ∃ M : ℝ, ∀ u, IsDecayingPotential (uniqueInfiniteComponent h) f u →
        (Function.support u).Infinite →
      ∀ ℓ, IsCorrectedPlane (uniqueInfiniteComponent h) q ℓ →
      ∀ x₀ : Vertex 2, κ * l1 x₀ ≤ slopeDot q x₀ → M ≤ l1 x₀ →
        ω ∈ eventGAt Cf R c₁ q Λ v x₀ Cχ K₀ →
        ∃ a b : uniqueInfiniteComponent h, (componentGraph _).Adj a b ∧
          l1 (a.val - x₀) ≤ C₀ ∧ ℓ a ≠ ℓ b ∧ u a ≠ u b

/-! ### Translation covariance -/

section Translation

variable {ω : Configuration 2} {Cf : ℕ} {R c₁ Λ Cχ K : ℝ} {q : Fin 2 → ℝ}

/-- The second good event at slope `q` moves with the environment. -/
theorem eventG2At_translation (z : Vertex 2) {x : Vertex 2} (hω : ω ∈ eventG2At q Λ x K) :
    configurationTranslation z ω ∈ eventG2At q Λ (x + z) K := by
  obtain ⟨h, hG⟩ := hω
  have h' := (hasUniqueInfiniteOpenComponent_translation_iff z ω).mpr h
  have hC : openComponentTranslation z ω (uniqueInfiniteComponent h) =
      uniqueInfiniteComponent h' := openComponentTranslation_uniqueInfiniteComponent z h
  refine ⟨h', ?_⟩
  rw [← hC]
  intro ℓ hℓ R' hR' a b ha hb
  have := hG _ (isCorrectedPlane_comp_translation z hℓ) R' hR'
    ((openComponentTranslationIso z _).symm a) ((openComponentTranslationIso z _).symm b)
    (by rwa [openComponentTranslationIso_symm_val, sub_mem_cubeAt_iff])
    (by rwa [openComponentTranslationIso_symm_val, sub_mem_cubeAt_iff])
  simpa only [RelIso.apply_symm_apply] using this

/-- The third good event at slope `q` in direction `v` moves with the environment. -/
theorem eventG3At_translation (z : Vertex 2) {v x : Vertex 2} (hω : ω ∈ eventG3At q v x Cχ) :
    configurationTranslation z ω ∈ eventG3At q v (x + z) Cχ := by
  obtain ⟨h, hx, hx1, hadj, hG⟩ := hω
  have h' := (hasUniqueInfiniteOpenComponent_translation_iff z ω).mpr h
  have hC : openComponentTranslation z ω (uniqueInfiniteComponent h) =
      uniqueInfiniteComponent h' := openComponentTranslation_uniqueInfiniteComponent z h
  refine ⟨h', ?_⟩
  rw [← hC]
  set C := uniqueInfiniteComponent h
  set φ := openComponentTranslationIso z C
  have hxz : x + z ∈ (openComponentTranslation z ω C).supp :=
    (add_mem_openComponentTranslation_supp z C x).mpr hx
  have hxz1 : x + z + v ∈ (openComponentTranslation z ω C).supp := by
    rw [add_right_comm]
    exact (add_mem_openComponentTranslation_supp z C _).mpr hx1
  have e0 : (⟨x + z, hxz⟩ : openComponentTranslation z ω C) = φ ⟨x, hx⟩ := rfl
  have e1' : (⟨x + z + v, hxz1⟩ : openComponentTranslation z ω C) = φ ⟨x + v, hx1⟩ :=
    Subtype.ext (show x + z + v = x + v + z from add_right_comm _ _ _)
  refine ⟨hxz, hxz1, ?_, fun ℓ hℓ => ?_⟩
  · rw [e0, e1']
    exact φ.map_adj_iff.mpr hadj
  · rw [e0, e1']
    exact hG _ (isCorrectedPlane_comp_translation z hℓ)

/-- The good event at slope `q` moves with the environment. -/
theorem eventGAt_translation (z : Vertex 2) {v x : Vertex 2}
    (hω : ω ∈ eventGAt Cf R c₁ q Λ v x Cχ K) :
    configurationTranslation z ω ∈ eventGAt Cf R c₁ q Λ v (x + z) Cχ K :=
  ⟨⟨eventG1_translation z hω.1.1, eventG2At_translation z hω.1.2⟩,
    eventG3At_translation z hω.2⟩

/-- `τ_{-x} ω ∈ G^{q,v}(0, C_χ, K)` implies `ω ∈ G^{q,v}(x, C_χ, K)`. -/
theorem mem_eventGAt_of_translation {v x : Vertex 2}
    (hω : configurationTranslation (-x) ω ∈ eventGAt Cf R c₁ q Λ v 0 Cχ K) :
    ω ∈ eventGAt Cf R c₁ q Λ v x Cχ K := by
  have := eventGAt_translation x hω
  rwa [configurationTranslation_add, add_neg_cancel, configurationTranslation_zero,
    zero_add] at this

end Translation

/-! ### Lemma 5.26 at slope `q`: densities on rectangles -/

/-- Splitting a rectangle along the second coordinate. -/
theorem sum_rect_split_snd (g : Vertex 2 → ℝ) (a₀ a₁ : ℤ) {b₀ b₁ b₂ : ℤ} (h₁ : b₀ ≤ b₁)
    (h₂ : b₁ ≤ b₂) :
    ∑ x ∈ rect a₀ a₁ b₀ b₂, g x = ∑ x ∈ rect a₀ a₁ b₀ b₁, g x + ∑ x ∈ rect a₀ a₁ b₁ b₂, g x := by
  rw [← Finset.sum_union (Finset.disjoint_left.mpr fun x hx hx' => by
    rw [mem_rect] at hx hx'
    omega)]
  congr 1
  ext x
  simp only [Finset.mem_union, mem_rect]
  omega

/-- The half scale `n = ⌊L/2⌋` tends to infinity. -/
theorem tendsto_half : Tendsto (fun L : ℕ => L / 2) atTop atTop :=
  tendsto_atTop_atTop.2 fun b => ⟨2 * b, fun a ha => by omega⟩

/-- A region of `Q_L` adapted to the slope `q`: its points `y` satisfy `κ |y|₁ ≤ q · y` and
`|y|₁ ≥ ⌊L/2⌋`, and for every measurable `A`, almost surely the number of its points `y` with
`τ_{-y} ω ∈ A`, divided by `⌊L/2⌋²`, tends to `P[A]`. -/
def IsSlopeRegion (p : unitInterval) (q : Fin 2 → ℝ) (κ : ℝ) (D : ℕ → Finset (Vertex 2)) :
    Prop :=
  (∀ L, ∀ y ∈ D L, y ∈ cube L) ∧ (∀ L, ∀ y ∈ D L, ((L / 2 : ℕ) : ℝ) ≤ l1 y) ∧
    (∀ L, ∀ y ∈ D L, κ * l1 y ≤ slopeDot q y) ∧
    ∀ A : Set (Configuration 2), MeasurableSet A → ∀ᵐ ω ∂latticeBondLaw 2 p,
      Tendsto (fun L => (∑ y ∈ D L, seenFrom A ω y) / ((L / 2 : ℕ) : ℝ) ^ 2) atTop
        (𝓝 (latticeBondLaw 2 p A).toReal)


theorem l1_eq (y : Vertex 2) : l1 y = |(y 0 : ℝ)| + |(y 1 : ℝ)| := by
  simp [l1, Fin.sum_univ_two]

/-- The density on `D L` when `big L` is the disjoint union of `small L` and `D L`. -/
theorem ae_tendsto_of_union {p : unitInterval} {A : Set (Configuration 2)}
    {D big small : ℕ → Finset (Vertex 2)} {a b : ℝ}
    (hU : ∀ L, big L = small L ∪ D L) (hdisj : ∀ L, Disjoint (small L) (D L))
    (hbig : ∀ᵐ ω ∂latticeBondLaw 2 p, Tendsto (fun L =>
      (∑ x ∈ big L, seenFrom A ω x) / ((L / 2 : ℕ) : ℝ) ^ 2) atTop (𝓝 a))
    (hsmall : ∀ᵐ ω ∂latticeBondLaw 2 p, Tendsto (fun L =>
      (∑ x ∈ small L, seenFrom A ω x) / ((L / 2 : ℕ) : ℝ) ^ 2) atTop (𝓝 b)) :
    ∀ᵐ ω ∂latticeBondLaw 2 p, Tendsto (fun L =>
      (∑ x ∈ D L, seenFrom A ω x) / ((L / 2 : ℕ) : ℝ) ^ 2) atTop (𝓝 (a - b)) := by
  filter_upwards [hbig, hsmall] with ω h1 h2
  refine (h1.sub h2).congr fun L => ?_
  rw [hU, Finset.sum_union (hdisj L)]
  ring

/-- For `q₀ ≥ 0` and `q ≠ 0` there is a region adapted to `q`. -/
theorem exists_isSlopeRegion (p : unitInterval) {q : Fin 2 → ℝ} (hq : q ≠ 0) (hq0 : 0 ≤ q 0) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ D : ℕ → Finset (Vertex 2), IsSlopeRegion p q κ D := by
  have hn := tendsto_half
  rcases lt_trichotomy (q 1) 0 with hq1 | hq1 | hq1
  · -- `q₁ < 0`: the rectangle `[0, n) × [-2n, -n)`
    refine ⟨-q 1 / 2, by linarith, fun L => rect 0 (L / 2 : ℕ) (-(2 * ((L / 2 : ℕ) : ℤ)))
      (-((L / 2 : ℕ) : ℤ)), fun L y hy => ?_, fun L y hy => ?_, fun L y hy => ?_, fun A hA => ?_⟩
    · rw [mem_rect] at hy
      exact Fin.forall_fin_two.2 ⟨abs_le.2 ⟨by omega, by omega⟩, abs_le.2 ⟨by omega, by omega⟩⟩
    · rw [mem_rect] at hy
      have h0 : (0 : ℝ) ≤ (y 0 : ℝ) := by exact_mod_cast hy.1.1
      have h1 : (y 1 : ℝ) + ((L / 2 : ℕ) : ℝ) < 0 := by
        have : y 1 + ((L / 2 : ℕ) : ℤ) < 0 := by omega
        have := (Int.cast_lt (R := ℝ)).2 this
        push_cast at this
        exact this
      rw [l1_eq, abs_of_nonneg h0, abs_of_neg (by linarith [Nat.cast_nonneg (α := ℝ) (L / 2)])]
      linarith
    · rw [mem_rect] at hy
      have h0 : (0 : ℝ) ≤ (y 0 : ℝ) := by exact_mod_cast hy.1.1
      have h01 : (y 0 : ℝ) + (y 1 : ℝ) ≤ 0 := by
        have : y 0 + y 1 ≤ 0 := by omega
        exact_mod_cast this
      have h1 : (y 1 : ℝ) < 0 := by exact_mod_cast (by omega : y 1 < 0)
      rw [l1_eq, abs_of_nonneg h0, abs_of_neg h1, slopeDot]
      nlinarith [mul_nonneg hq0 h0]
    · have h := ae_tendsto_of_union (D := fun L => rect 0 (L / 2 : ℕ)
        (-(2 * ((L / 2 : ℕ) : ℤ))) (-((L / 2 : ℕ) : ℤ))) (fun L => ?_) (fun L => ?_)
        (ae_tendsto_lowerRect (p := p) hA hn 1 2) (ae_tendsto_lowerRect (p := p) hA hn 1 1)
      · convert h using 3
        push_cast
        ring_nf
      · ext x
        simp only [Finset.mem_union, mem_rect, Nat.cast_one, Nat.cast_ofNat, one_mul]
        omega
      · refine Finset.disjoint_left.2 fun x hx hx' => ?_
        rw [mem_rect] at hx hx'
        omega
  · -- `q₁ = 0`, `q₀ > 0`: the rectangle `[n, 2n) × [0, n)`
    have hq0' : 0 < q 0 := by
      refine lt_of_le_of_ne hq0 fun h => hq (funext fun i => ?_)
      fin_cases i
      · exact h.symm
      · exact hq1
    refine ⟨q 0 / 2, by linarith, fun L => rect (L / 2 : ℕ) (2 * ((L / 2 : ℕ) : ℤ)) 0
      (L / 2 : ℕ), fun L y hy => ?_, fun L y hy => ?_, fun L y hy => ?_, fun A hA => ?_⟩
    · rw [mem_rect] at hy
      exact Fin.forall_fin_two.2 ⟨abs_le.2 ⟨by omega, by omega⟩, abs_le.2 ⟨by omega, by omega⟩⟩
    · rw [mem_rect] at hy
      have h0 : ((L / 2 : ℕ) : ℝ) ≤ (y 0 : ℝ) := by
        have := (Int.cast_le (R := ℝ)).2 hy.1.1
        push_cast at this
        exact this
      have h1 : (0 : ℝ) ≤ (y 1 : ℝ) := by exact_mod_cast hy.2.1
      rw [l1_eq, abs_of_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) (L / 2)]),
        abs_of_nonneg h1]
      linarith
    · rw [mem_rect] at hy
      have h1 : (0 : ℝ) ≤ (y 1 : ℝ) := by exact_mod_cast hy.2.1
      have h10 : (y 1 : ℝ) ≤ (y 0 : ℝ) := by
        have : y 1 ≤ y 0 := by omega
        exact_mod_cast this
      rw [l1_eq, abs_of_nonneg (by linarith), abs_of_nonneg h1, slopeDot, hq1]
      nlinarith
    · have h := ae_tendsto_of_union (D := fun L => rect (L / 2 : ℕ) (2 * ((L / 2 : ℕ) : ℤ)) 0
        (L / 2 : ℕ)) (fun L => ?_) (fun L => ?_)
        (ae_tendsto_upperRect (p := p) hA hn 2 1) (ae_tendsto_upperRect (p := p) hA hn 1 1)
      · convert h using 3
        push_cast
        ring_nf
      · ext x
        simp only [Finset.mem_union, mem_rect, Nat.cast_one, Nat.cast_ofNat, one_mul]
        omega
      · refine Finset.disjoint_left.2 fun x hx hx' => ?_
        rw [mem_rect] at hx hx'
        omega
  · -- `q₁ > 0`: the rectangle `[0, n) × [n, 2n)`
    refine ⟨q 1 / 2, by linarith, fun L => rect 0 (L / 2 : ℕ) (L / 2 : ℕ)
      (2 * ((L / 2 : ℕ) : ℤ)), fun L y hy => ?_, fun L y hy => ?_, fun L y hy => ?_,
      fun A hA => ?_⟩
    · rw [mem_rect] at hy
      exact Fin.forall_fin_two.2 ⟨abs_le.2 ⟨by omega, by omega⟩, abs_le.2 ⟨by omega, by omega⟩⟩
    · rw [mem_rect] at hy
      have h0 : (0 : ℝ) ≤ (y 0 : ℝ) := by exact_mod_cast hy.1.1
      have h1 : ((L / 2 : ℕ) : ℝ) ≤ (y 1 : ℝ) := by
        have := (Int.cast_le (R := ℝ)).2 hy.2.1
        push_cast at this
        exact this
      rw [l1_eq, abs_of_nonneg h0, abs_of_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) (L / 2)])]
      linarith
    · rw [mem_rect] at hy
      have h0 : (0 : ℝ) ≤ (y 0 : ℝ) := by exact_mod_cast hy.1.1
      have h01 : (y 0 : ℝ) ≤ (y 1 : ℝ) := by
        have : y 0 ≤ y 1 := by omega
        exact_mod_cast this
      rw [l1_eq, abs_of_nonneg h0, abs_of_nonneg (by linarith), slopeDot]
      nlinarith [mul_nonneg hq0 h0]
    · have h := ae_tendsto_of_union (D := fun L => rect 0 (L / 2 : ℕ) (L / 2 : ℕ)
        (2 * ((L / 2 : ℕ) : ℤ))) (fun L => ?_) (fun L => ?_)
        (ae_tendsto_upperRect (p := p) hA hn 1 2) (ae_tendsto_upperRect (p := p) hA hn 1 1)
      · convert h using 3
        push_cast
        ring_nf
      · ext x
        simp only [Finset.mem_union, mem_rect, Nat.cast_one, Nat.cast_ofNat, one_mul]
        omega
      · refine Finset.disjoint_left.2 fun x hx hx' => ?_
        rw [mem_rect] at hx hx'
        omega

/-! ### The reduction -/

/-- The density of sensitive sites at slope `q` for all large `L`, from good events `G(x)` with
`τ_{-x} ω ∈ G(0) → ω ∈ G(x)`, a measurable `A ⊆ G(0)` with `P[A] > 0`, a region adapted to `q`,
and Lemma 5.27 (ii) at slope `q` on the cone `κ |x|₁ ≤ q · x`. -/
theorem sensitiveSiteDensityEventually_of_slopeRegion {p : unitInterval} {f : Vertex 2 → ℤ}
    {q : Fin 2 → ℝ} {κ : ℝ} {D : ℕ → Finset (Vertex 2)} (hD : IsSlopeRegion p q κ D)
    (G : Vertex 2 → Set (Configuration 2))
    (hT : ∀ (y : Vertex 2) (ω : Configuration 2), configurationTranslation (-y) ω ∈ G 0 → ω ∈ G y)
    {A : Set (Configuration 2)} (hAG : A ⊆ G 0) (hAm : MeasurableSet A)
    (hApos : 0 < latticeBondLaw 2 p A) {C₀ : ℝ}
    (hae : ∀ᵐ ω ∂latticeBondLaw 2 p, ∃ h : HasUniqueInfiniteOpenComponent ω, ∃ M : ℝ,
      ∀ u, IsDecayingPotential (uniqueInfiniteComponent h) f u → (Function.support u).Infinite →
      ∀ ℓ, IsCorrectedPlane (uniqueInfiniteComponent h) q ℓ →
      ∀ x₀ : Vertex 2, κ * l1 x₀ ≤ slopeDot q x₀ → M ≤ l1 x₀ → ω ∈ G x₀ →
        ∃ a b : uniqueInfiniteComponent h, (componentGraph _).Adj a b ∧
          l1 (a.val - x₀) ≤ C₀ ∧ ℓ a ≠ ℓ b ∧ u a ≠ u b) :
    SensitiveSiteDensityEventually p f q := by
  classical
  obtain ⟨hDc, hDl, hDκ, hDd⟩ := hD
  set P := (latticeBondLaw 2 p A).toReal with hP
  have hPpos : 0 < P := ENNReal.toReal_pos hApos.ne' (measure_ne_top _ _)
  refine ⟨P / 32, C₀, by positivity, ?_⟩
  filter_upwards [hae, hDd A hAm] with ω hω hdens
  obtain ⟨h, M, hM⟩ := hω
  refine ⟨h, fun u hu hsu ℓ hℓ => ?_⟩
  set S := sensitiveSites (uniqueInfiniteComponent h) u ℓ C₀
  have hcount : ∀ L : ℕ, M ≤ ((L / 2 : ℕ) : ℝ) →
      (∑ y ∈ D L, seenFrom A ω y) ≤ ((cube L ∩ S).ncard : ℝ) := by
    intro L hL
    have hle : ∀ y ∈ D L, seenFrom A ω y ≤ if y ∈ cube L ∩ S then (1 : ℝ) else 0 := by
      intro y hy
      by_cases hyA : configurationTranslation (-y) ω ∈ A
      · have hyS : y ∈ cube L ∩ S := ⟨hDc L y hy, hM u hu hsu ℓ hℓ y (hDκ L y hy)
          (hL.trans (hDl L y hy)) (hT y ω (hAG hyA))⟩
        simp [seenFrom, hyA, hyS]
      · have h0 : seenFrom A ω y = 0 := by simp [seenFrom, hyA]
        rw [h0]
        split_ifs <;> norm_num
    refine (Finset.sum_le_sum hle).trans ?_
    rw [Finset.sum_boole]
    have hsub : (((D L).filter fun y => y ∈ cube L ∩ S : Finset (Vertex 2)) : Set (Vertex 2)) ⊆
        cube L ∩ S := fun y hy => (Finset.mem_filter.1 (Finset.mem_coe.1 hy)).2
    have := Set.ncard_le_ncard hsub ((cube_finite L).subset Set.inter_subset_left)
    rw [Set.ncard_coe_finset] at this
    exact_mod_cast this
  have h1 := hdens.eventually (lt_mem_nhds (show 3 * P / 4 < P by linarith))
  have hM' : ∀ᶠ L : ℕ in atTop, M ≤ ((L / 2 : ℕ) : ℝ) :=
    (tendsto_natCast_atTop_atTop.comp tendsto_half).eventually_ge_atTop M
  filter_upwards [h1, hM', eventually_ge_atTop 2] with L hL1 hL2 hL3
  have hn : (0 : ℝ) < ((L / 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < L / 2)
  have h4 : (L : ℝ) ≤ 4 * ((L / 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : L ≤ 4 * (L / 2))
  have h16 : (L : ℝ) ^ 2 ≤ 16 * ((L / 2 : ℕ) : ℝ) ^ 2 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) L]
  rw [lt_div_iff₀ (by positivity)] at hL1
  have := hcount L hL2
  nlinarith [mul_le_mul_of_nonneg_left h16 hPpos.le]

/-- The sensitive sites of `ℓ` and `-ℓ` agree. -/
theorem sensitiveSites_neg {ω : Configuration 2} (C : OpenComponent ω) (u ℓ : C → ℝ) (C₀ : ℝ) :
    sensitiveSites C u (-ℓ) C₀ = sensitiveSites C u ℓ C₀ := by
  ext x₀
  simp only [sensitiveSites, Set.mem_setOf_eq, Pi.neg_apply, ne_eq, neg_inj]

/-- The density of sensitive sites at slope `-q` gives it at slope `q` (`-ℓ_q` is a corrected
plane of slope `-q`). -/
theorem sensitiveSiteDensityEventually_of_neg {p : unitInterval} {f : Vertex 2 → ℤ}
    {q : Fin 2 → ℝ} (h : SensitiveSiteDensityEventually p f (-q)) :
    SensitiveSiteDensityEventually p f q := by
  obtain ⟨c, C₀, hc, hae⟩ := h
  refine ⟨c, C₀, hc, ?_⟩
  filter_upwards [hae] with ω hω
  obtain ⟨h, hω⟩ := hω
  refine ⟨h, fun u hu hsu ℓ hℓ => ?_⟩
  simpa only [sensitiveSites_neg] using hω u hu hsu (-ℓ) (isCorrectedPlane_neg _ hℓ)

/-- The density of sensitive sites at a slope `q ≠ 0` with `q₀ ≥ 0` from Lemma 5.27 at slope `q`. -/
theorem sensitiveSiteDensityEventually_of_largeGradientSensitiveAt {p : unitInterval}
    {f : Vertex 2 → ℤ} {q : Fin 2 → ℝ} (hf : (Function.support f).Finite) (hq : q ≠ 0)
    (hq0 : 0 ≤ q 0) (h527 : LargeGradientSensitiveAtStmt p f q) :
    SensitiveSiteDensityEventually p f q := by
  obtain ⟨Cf, R, c₁, Λ, Cχ, K₀, C₀, v, ⟨A, hAG, hAm, hApos⟩, hae⟩ := h527 hf
  obtain ⟨κ, hκ, D, hD⟩ := exists_isSlopeRegion p hq hq0
  exact sensitiveSiteDensityEventually_of_slopeRegion hD
    (fun x => eventGAt Cf R c₁ q Λ v x Cχ K₀) (fun _ _ hω => mem_eventGAt_of_translation hω)
    hAG hAm hApos (hae κ hκ)

/-- The density of sensitive sites at every slope `q ≠ 0` from Lemma 5.27 at every slope. -/
theorem sensitiveSiteDensityEventually_of_slopeSteps {p : unitInterval} {f : Vertex 2 → ℤ}
    (hf : (Function.support f).Finite)
    (h527 : ∀ q : Fin 2 → ℝ, q ≠ 0 → LargeGradientSensitiveAtStmt p f q) {q : Fin 2 → ℝ}
    (hq : q ≠ 0) : SensitiveSiteDensityEventually p f q := by
  by_cases hq0 : 0 ≤ q 0
  · exact sensitiveSiteDensityEventually_of_largeGradientSensitiveAt hf hq hq0 (h527 q hq)
  · have hnq : -q ≠ 0 := neg_ne_zero.2 hq
    have hnq0 : 0 ≤ (-q) 0 := by
      rw [Pi.neg_apply]
      linarith [not_le.1 hq0]
    exact sensitiveSiteDensityEventually_of_neg
      (by simpa only [neg_neg] using
        sensitiveSiteDensityEventually_of_largeGradientSensitiveAt hf hnq hnq0 (h527 (-q) hnq))

/-- Proposition 5.11 in `lim inf` form at every slope `q ≠ 0`, from Lemma 5.27 at every slope. -/
theorem levelSetDensityEventuallyAt_of_largeGradientSensitiveAt {p : unitInterval}
    {f : Vertex 2 → ℤ} (hf : (Function.support f).Finite)
    (h527 : ∀ q : Fin 2 → ℝ, q ≠ 0 → LargeGradientSensitiveAtStmt p f q) {q : Fin 2 → ℝ}
    (hq : q ≠ 0) : LevelSetDensityEventuallyAt p f q :=
  levelSetDensityEventuallyAt_of_sensitiveSiteDensityEventually hf
    (sensitiveSiteDensityEventually_of_slopeSteps hf h527 hq)

/-- Proposition 5.11 (`LevelSetDensityStmt`) from Lemma 5.27 at every slope `q ≠ 0`. -/
theorem levelSetDensity_of_largeGradientSensitiveAt {p : unitInterval} {f : Vertex 2 → ℤ}
    (h527 : ∀ q : Fin 2 → ℝ, q ≠ 0 → LargeGradientSensitiveAtStmt p f q) :
    LevelSetDensityStmt p f :=
  levelSetDensityStmt_iff.2 fun hf _ hq =>
    levelSetDensityEventuallyAt_of_largeGradientSensitiveAt hf h527 hq

/-! ### Lemma 5.25 at slope `q`: the statement

The third good event of the draft is direction-free ([C32]); at slope `q` its edge is
`(x, x + v)` for a lattice unit vector `v` chosen once (`eventG3At`). -/

open Rigidity.External in
/-- Lemma 5.25 at slope `q` with a free direction: some lattice unit vector `v` such that, for
every `C_χ ≥ 1` and parameters `R, c₁` satisfying the bound of Proposition 5.24, the good event
`G^{q,v}(0, C_χ, K)` (universal `G_1`, constant `Λ` in `G_2`) contains a measurable event of
positive probability for all large `K`. -/
def GoodEventPositiveAtStmt (p : unitInterval) (q : Fin 2 → ℝ) (Λ : ℝ) : Prop :=
  ∃ v : Vertex 2, l1 v = 1 ∧ ∀ Cχ : ℝ, 1 ≤ Cχ → ∀ (Cf : ℕ) (R c₁ : ℝ), LongPathBound p Cf R c₁ →
    ∃ K₀ : ℝ, ∀ K : ℝ, K₀ ≤ K → ∃ A ⊆ eventGAt Cf R c₁ q Λ v 0 Cχ K,
      MeasurableSet A ∧ 0 < latticeBondLaw 2 p A

/-! ### Lemma 5.25 at slope `q`: the third good event in a free direction

From the unsigned Proposition 3.2 at slope `q` (`NotLipschitzAtStep`), some lattice direction `v`
has `P[G_3^{q,v}(0, C_χ)] > 0` for every `C_χ ≥ 1` (`exists_eventG3At_of_notLipschitzAt`). -/

section ThirdGoodEvent

open LatticeProb.External Classical

/-- For every `L ≥ 1`, with positive outer probability `(0, v)` is an edge of `𝒞_∞` across which
some corrected plane of slope `q` increases by more than `L` (`HorizontalIncrementStep` is
`q = e₁`, `v = e₁`). -/
def DirectedIncrementStep (p : unitInterval) (q : Fin 2 → ℝ) (v : Vertex 2) : Prop :=
  ∀ L : ℝ, 1 ≤ L →
    latticeBondLaw 2 p {ω | ∃ h : HasUniqueInfiniteOpenComponent ω,
      ∃ ho : (0 : Vertex 2) ∈ (uniqueInfiniteComponent h).supp,
      ∃ he : v ∈ (uniqueInfiniteComponent h).supp,
        (componentGraph _).Adj ⟨0, ho⟩ ⟨v, he⟩ ∧
        ∃ u, IsCorrectedPlane (uniqueInfiniteComponent h) q u ∧ L < u ⟨v, he⟩ - u ⟨0, ho⟩} ≠ 0

/-- Proposition 3.2 at slope `q` (unsigned): the first conjunct of `NotLipschitzStmt 2 p` with
`e₁` replaced by `q`. -/
def NotLipschitzAtStep (p : unitInterval) (q : Fin 2 → ℝ) : Prop :=
  ∀ L : ℝ, 1 ≤ L →
    latticeBondLaw 2 p {ω | ∃ h : HasUniqueInfiniteOpenComponent ω,
        ∃ ho : (0 : Vertex 2) ∈ (uniqueInfiniteComponent h).supp,
        ∃ u, IsCorrectedPlane (uniqueInfiniteComponent h) q u ∧
          L < Rigidity.Section3.originGradientNorm (uniqueInfiniteComponent h) ho u} ≠ 0

/-- **T1.** Proposition 3.2 gives its slope-`e₁` instance. -/
theorem notLipschitzAtStep_e1 {p : unitInterval} (h : Rigidity.Section3.NotLipschitzStmt 2 p) :
    NotLipschitzAtStep p (Pi.single 0 1) :=
  fun _ hL => h.originGradient_ne_zero hL

/-! ### Increments across an edge, and their translation covariance -/

section Increment

variable {ω : Configuration 2}

/-- The vertices `x` and `y` lie in the infinite cluster, are adjacent in it, and some corrected
plane of slope `q` increases by more than `L` from `x` to `y`. -/
def incrementEvent (q : Fin 2 → ℝ) (x y : Vertex 2) (L : ℝ) : Set (Configuration 2) :=
  {ω | ∃ h : HasUniqueInfiniteOpenComponent ω, ∃ hx : x ∈ (uniqueInfiniteComponent h).supp,
    ∃ hy : y ∈ (uniqueInfiniteComponent h).supp,
      (componentGraph _).Adj ⟨x, hx⟩ ⟨y, hy⟩ ∧
      ∃ u, IsCorrectedPlane (uniqueInfiniteComponent h) q u ∧ L < u ⟨y, hy⟩ - u ⟨x, hx⟩}

theorem directedIncrementStep_iff {p : unitInterval} {q : Fin 2 → ℝ} {v : Vertex 2} :
    DirectedIncrementStep p q v ↔
      ∀ L : ℝ, 1 ≤ L → latticeBondLaw 2 p (incrementEvent q 0 v L) ≠ 0 :=
  Iff.rfl

theorem incrementEvent_mono (q : Fin 2 → ℝ) (x y : Vertex 2) {L L' : ℝ} (hLL : L ≤ L') :
    incrementEvent q x y L' ⊆ incrementEvent q x y L := by
  rintro ω ⟨h, hx, hy, hadj, u, hu, hlt⟩
  exact ⟨h, hx, hy, hadj, u, hu, lt_of_le_of_lt hLL hlt⟩

/-- The event `incrementEvent` moves with the environment. -/
theorem incrementEvent_translation (z : Vertex 2) {q : Fin 2 → ℝ} {x y : Vertex 2} {L : ℝ}
    (hω : ω ∈ incrementEvent q x y L) :
    configurationTranslation z ω ∈ incrementEvent q (x + z) (y + z) L := by
  obtain ⟨h, hx, hy, hadj, u, hu, hlt⟩ := hω
  have h' := (hasUniqueInfiniteOpenComponent_translation_iff z ω).mpr h
  have hC : openComponentTranslation z ω (uniqueInfiniteComponent h) =
      uniqueInfiniteComponent h' := openComponentTranslation_uniqueInfiniteComponent z h
  refine ⟨h', ?_⟩
  rw [← hC]
  set φ := openComponentTranslationIso z (uniqueInfiniteComponent h)
  have hxz : x + z ∈ (openComponentTranslation z ω (uniqueInfiniteComponent h)).supp :=
    (add_mem_openComponentTranslation_supp z _ x).mpr hx
  have hyz : y + z ∈ (openComponentTranslation z ω (uniqueInfiniteComponent h)).supp :=
    (add_mem_openComponentTranslation_supp z _ y).mpr hy
  have e0 : (⟨x + z, hxz⟩ : openComponentTranslation z ω (uniqueInfiniteComponent h)) =
      φ ⟨x, hx⟩ := rfl
  have e1' : (⟨y + z, hyz⟩ : openComponentTranslation z ω (uniqueInfiniteComponent h)) =
      φ ⟨y, hy⟩ := rfl
  refine ⟨hxz, hyz, by rw [e0, e1']; exact φ.map_adj_iff.mpr hadj,
    fun w => u (φ.symm w), (isCorrectedPlane_translation_iff z _ _ u).mpr hu, ?_⟩
  rw [e0, e1']
  simpa only [RelIso.symm_apply_apply] using hlt

/-- A null event has null preimages under the lattice translations (outer measure). -/
theorem latticeBondLaw_preimage_translation_null_at {p : unitInterval} {A : Set (Configuration 2)}
    (hA : latticeBondLaw 2 p A = 0) (z : Vertex 2) :
    latticeBondLaw 2 p (configurationTranslation z ⁻¹' A) = 0 := by
  have hτ := measurePreserving_configurationTranslation p z
  refine measure_mono_null
    (Set.preimage_mono (subset_toMeasurable (latticeBondLaw 2 p) A)) ?_
  rw [hτ.measure_preimage (measurableSet_toMeasurable _ A).nullMeasurableSet,
    measure_toMeasurable]
  exact hA

end Increment

/-! ### T2: a direction with large increments -/

/-- The four lattice directions `±e_i`: `(i, true) ↦ e_i`, `(i, false) ↦ -e_i`. -/
def latticeDirection (s : Fin 2 × Bool) : Vertex 2 := cond s.2 (LatticeProb.unit s.1) (-LatticeProb.unit s.1)

theorem l1_dir (s : Fin 2 × Bool) : l1 (latticeDirection s) = 1 := by
  obtain ⟨i, b⟩ := s
  fin_cases i <;> cases b <;>
    simp [l1, latticeDirection, LatticeProb.unit, Fin.sum_univ_two, Pi.single_apply]

/-- For every `L ≥ 1` some direction `±e_i` has an increment event of positive probability. -/
theorem exists_dir_incrementEvent_ne_zero {p : unitInterval} {q : Fin 2 → ℝ}
    (hN : NotLipschitzAtStep p q) {L : ℝ} (hL : 1 ≤ L) :
    ∃ s : Fin 2 × Bool, latticeBondLaw 2 p (incrementEvent q 0 (latticeDirection s) L) ≠ 0 := by
  by_contra hcon
  have h0 : ∀ s : Fin 2 × Bool, latticeBondLaw 2 p (incrementEvent q 0 (latticeDirection s) L) = 0 :=
    fun s => by_contra fun h => hcon ⟨s, h⟩
  refine hN (2 * L) (by linarith) (measure_mono_null ?_ (measure_union_null
    (measure_iUnion_null fun i : Fin 2 => h0 (i, true))
    (measure_iUnion_null fun i : Fin 2 =>
      latticeBondLaw_preimage_translation_null_at (h0 (i, false)) (-LatticeProb.unit i))))
  rintro ω ⟨h, ho, u, hu, hlt⟩
  unfold Rigidity.Section3.originGradientNorm at hlt
  obtain ⟨i, -, hi⟩ := Finset.exists_lt_of_sum_lt (s := (Finset.univ : Finset (Fin 2)))
    (f := fun _ => L) (lt_of_eq_of_lt (by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; norm_num) hlt)
  split_ifs at hi with hadj
  · have hy := (uniqueInfiniteComponent h).mem_supp_of_adj_mem_supp ho hadj
    have hA : (componentGraph (uniqueInfiniteComponent h)).Adj ⟨0, ho⟩
        ⟨LatticeProb.unit i, hy⟩ := ((uniqueInfiniteComponent h).toSimpleGraph_adj ho hy).2 hadj
    rcases lt_abs.mp hi with hi | hi
    · refine Or.inr (Set.mem_iUnion.mpr ⟨i, ?_⟩)
      have hmem : ω ∈ incrementEvent q (LatticeProb.unit i) 0 L :=
        ⟨h, hy, ho, hA.symm, u, hu, by linarith⟩
      have := incrementEvent_translation (-LatticeProb.unit i) hmem
      rwa [add_neg_cancel, zero_add] at this
    · have hlt' : L < u ⟨LatticeProb.unit i, hy⟩ - u ⟨0, ho⟩ := by linarith
      exact Or.inl (Set.mem_iUnion.mpr ⟨i, h, ho, hy, hA, u, hu, hlt'⟩)
  · linarith

/-- **T2.** An unsigned gradient lower bound at slope `q` gives a lattice direction `v` with
`|v|₁ = 1` along which the increments are large with positive probability. -/
theorem exists_directedIncrementStep {p : unitInterval} {q : Fin 2 → ℝ}
    (hN : NotLipschitzAtStep p q) :
    ∃ v : Vertex 2, l1 v = 1 ∧ DirectedIncrementStep p q v := by
  choose f hf using fun n : ℕ =>
    exists_dir_incrementEvent_ne_zero hN (L := (n : ℝ) + 1) (by linarith [n.cast_nonneg (α := ℝ)])
  obtain ⟨s, hs⟩ := Finite.exists_infinite_fiber f
  refine ⟨latticeDirection s, l1_dir s, fun L hL => ?_⟩
  obtain ⟨n, hn, hlt⟩ := (Set.infinite_coe_iff.mp hs).exists_gt ⌈L⌉₊
  have hfn : f n = s := hn
  have hLn : L ≤ (n : ℝ) + 1 := by
    have h1 : L ≤ (⌈L⌉₊ : ℝ) := Nat.le_ceil L
    have h2 : (⌈L⌉₊ : ℝ) ≤ n := by exact_mod_cast hlt.le
    linarith
  have hfn' := hf n
  rw [hfn] at hfn'
  exact fun h0 => hfn' (measure_mono_null (incrementEvent_mono q 0 (latticeDirection s) hLn) h0)

/-! ### T3: positive probability inside the third good event -/

/-- **T3.** The proof of `thirdGoodEventStep_of_horizontalIncrement` with the direction `e₁`
replaced by `v` and the slope by `q`. -/
theorem exists_measurableSet_eventG3At (hU : SupercriticalBondCorrectorInput) {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) {q : Fin 2 → ℝ} {v : Vertex 2}
    (hH : DirectedIncrementStep p q v) (Cχ : ℝ) (hCχ : 1 ≤ Cχ) :
    ∃ A ⊆ eventG3At q v 0 Cχ, MeasurableSet A ∧ 0 < latticeBondLaw 2 p A := by
  set μ := latticeBondLaw 2 p
  have hbad := ae_iff.mp (hU 2 le_rfl p hpc hp1)
  set N := toMeasurable μ {ω | ¬ ∀ h : HasUniqueInfiniteOpenComponent ω,
      (∀ q : Fin 2 → ℝ, ∀ o : uniqueInfiniteComponent h,
        ∃! u : uniqueInfiniteComponent h → ℝ,
          IsCorrectedPlane (uniqueInfiniteComponent h) q u ∧ u o = 0) ∧
      (∀ u : uniqueInfiniteComponent h → ℝ,
        u ∈ harmonicGrowthSpace (uniqueInfiniteComponent h) 1 →
        ∃! q : Fin 2 → ℝ, IsCorrectedPlane (uniqueInfiniteComponent h) q u)} with hN
  have hN0 : μ N = 0 := by rw [hN, measure_toMeasurable]; exact hbad
  set G := Nᶜ ∩ uniqueInfiniteComponentEvent 2
  have hGm : MeasurableSet G :=
    (measurableSet_toMeasurable _ _).compl.inter (measurableSet_uniqueInfiniteComponentEvent 2)
  have hvalid : G ⊆ correctorValidEvent 2 := by
    intro ω hω
    by_contra hn
    exact hω.1 (subset_toMeasurable _ _ fun hP => hn ⟨hω.2, by simpa using hP⟩)
  obtain ⟨F, hFm, hF⟩ := exists_measurable_rooted_plane_on_valid_set G hGm hvalid 0
  have hB : MeasurableSet (G ∩ infiniteComponentEvent 0) :=
    hGm.inter (measurableSet_infiniteComponentEvent 0)
  set T : Set ↥(G ∩ infiniteComponentEvent 0) :=
    {z | (openGraph z.val).Adj 0 v ∧ Cχ ≤ F (z, q) v}
  have hT : MeasurableSet T := by
    refine (measurable_subtype_coe (measurableSet_openGraph_adj 0 v)).inter ?_
    exact measurableSet_le measurable_const
      ((measurable_pi_apply v).comp (hFm.comp (measurable_id.prodMk measurable_const)))
  refine ⟨Subtype.val '' T, ?_, hB.subtype_image hT, ?_⟩
  · rintro _ ⟨z, ⟨hadj, hval⟩, rfl⟩
    have h := (hvalid z.2.1).1
    have ho : (0 : Vertex 2) ∈ (uniqueInfiniteComponent h).supp :=
      (mem_uniqueInfiniteComponent_iff h 0).mpr z.2.2
    have he : v ∈ (uniqueInfiniteComponent h).supp :=
      (uniqueInfiniteComponent h).mem_supp_of_adj_mem_supp ho hadj
    have he' : (0 : Vertex 2) + v ∈ (uniqueInfiniteComponent h).supp := by
      rw [zero_add]; exact he
    refine ⟨h, ho, he', ((uniqueInfiniteComponent h).toSimpleGraph_adj ho he').2
      (by rw [zero_add]; exact hadj), fun ℓ hℓ => ?_⟩
    rw [rootedPlane_eq hF z h ho hℓ he] at hval
    have h0e : ℓ ⟨(0 : Vertex 2) + v, he'⟩ = ℓ ⟨v, he⟩ :=
      congrArg ℓ (Subtype.ext (zero_add v))
    rw [h0e]
    exact hval
  · have hS := hH Cχ hCχ
    refine pos_iff_ne_zero.mpr fun hA => hS (measure_mono_null ?_ (measure_union_null hA hN0))
    rintro ω ⟨h, ho, he, hadj, u, hu, hlt⟩
    by_cases hωN : ω ∈ N
    · exact Or.inr hωN
    · refine Or.inl ⟨⟨ω, ⟨hωN, h⟩, (mem_uniqueInfiniteComponent_iff h 0).mp ho⟩, ⟨?_, ?_⟩, rfl⟩
      · exact ((uniqueInfiniteComponent h).toSimpleGraph_adj ho he).1 hadj
      · rw [rootedPlane_eq hF _ h ho hu he]
        exact hlt.le

/-! ### T4 -/

/-- **T4.** From an unsigned gradient lower bound at slope `q`, there is a lattice direction `v`
with `|v|₁ = 1` such that for every `C_χ ≥ 1` the third good event `G_3^{q,v}(0, C_χ)` contains
a measurable event of positive probability. -/
theorem exists_eventG3At_of_notLipschitzAt (hU : SupercriticalBondCorrectorInput)
    {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    {q : Fin 2 → ℝ} (hN : NotLipschitzAtStep p q) :
    ∃ v : Vertex 2, l1 v = 1 ∧ ∀ Cχ : ℝ, 1 ≤ Cχ →
      ∃ A ⊆ eventG3At q v 0 Cχ, MeasurableSet A ∧ 0 < latticeBondLaw 2 p A := by
  obtain ⟨v, hv, hD⟩ := exists_directedIncrementStep hN
  exact ⟨v, hv, fun Cχ hCχ => exists_measurableSet_eventG3At hU hpc hp1 hD Cχ hCχ⟩

end ThirdGoodEvent

/-! ### Lemma 5.25 at slope `q` with a free direction -/

/-- Lemma 5.25 at slope `q` with a free direction, from the third good event in a free direction,
a bound on the failure of `G_2^q` (Theorem 2.5 at slope `q`) and Proposition 5.24: remove from
`A₃ ⊆ G_3^{q,v}(0, C_χ)` measurable covers of the failures of `G_1^∀` and `G_2^q`. -/
theorem goodEventPositiveAt_of_steps {p : unitInterval} {q : Fin 2 → ℝ} {Λ : ℝ}
    (h3 : ∃ v : Vertex 2, l1 v = 1 ∧ ∀ Cχ : ℝ, 1 ≤ Cχ →
      ∃ A ⊆ eventG3At q v 0 Cχ, MeasurableSet A ∧ 0 < latticeBondLaw 2 p A)
    (h2 : ∃ C c s : ℝ, 0 < C ∧ 0 < c ∧ 0 < s ∧ ∀ K : ℝ, 1 ≤ K →
      latticeBondLaw 2 p (eventG2At q Λ 0 K)ᶜ ≤ ENNReal.ofReal (C * Real.exp (-(c * K ^ s)))) :
    GoodEventPositiveAtStmt p q Λ := by
  obtain ⟨v, hv, h3⟩ := h3
  obtain ⟨C, c, s, hC, hc, hs, h2⟩ := h2
  refine ⟨v, hv, fun Cχ hCχ Cf R c₁ hLP => ?_⟩
  obtain ⟨A₃, hA₃G, hA₃m, hA₃pos⟩ := h3 Cχ hCχ
  obtain ⟨C', c', hC', hc', hbad⟩ := hLP
  set μ := latticeBondLaw 2 p
  have hPpos : 0 < (μ A₃).toReal := ENNReal.toReal_pos hA₃pos.ne' (measure_ne_top _ _)
  have e1 : Tendsto (fun K : ℝ => Real.exp (-(c' * K))) atTop (𝓝 0) := by
    have := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hc')
    simpa [Function.comp_def] using this
  have e2 : Tendsto (fun K : ℝ => Real.exp (-(c * K ^ s))) atTop (𝓝 0) := by
    have := Real.tendsto_exp_neg_atTop_nhds_zero.comp ((tendsto_rpow_atTop hs).const_mul_atTop hc)
    simpa [Function.comp_def] using this
  have hlim : Tendsto (fun K : ℝ => C' * Real.exp (-(c' * K)) + C * Real.exp (-(c * K ^ s)))
      atTop (𝓝 0) := by
    simpa using (e1.const_mul C').add (e2.const_mul C)
  obtain ⟨K₁, hK₁⟩ := (hlim.eventually (gt_mem_nhds hPpos)).exists_forall_of_atTop
  refine ⟨max K₁ 1, fun K hK => ?_⟩
  have hK1 : 1 ≤ K := (le_max_right _ _).trans hK
  set T := toMeasurable μ (badPathEvent Cf R c₁ K) ∪ toMeasurable μ (eventG2At q Λ 0 K)ᶜ
  refine ⟨A₃ \ T, ?_, hA₃m.diff ((measurableSet_toMeasurable _ _).union
    (measurableSet_toMeasurable _ _)), ?_⟩
  · rintro ω ⟨hωA, hωT⟩
    have hω3 := hA₃G hωA
    have hω3' := hω3
    obtain ⟨h1, -⟩ := hω3'
    refine ⟨⟨⟨h1, fun n γ hγ h0 hKγ => ?_⟩, ?_⟩, hω3⟩
    · by_contra hcon
      replace hcon := not_le.1 hcon
      exact hωT (Or.inl (subset_toMeasurable _ _
        ⟨h1, n, γ, hγ, h0, by simpa using hKγ, by simpa using hcon.le⟩))
    · by_contra hn
      exact hωT (Or.inr (subset_toMeasurable _ _ hn))
  · have hTle : μ T ≤
        ENNReal.ofReal (C' * Real.exp (-(c' * K)) + C * Real.exp (-(c * K ^ s))) := by
      refine (measure_union_le _ _).trans ?_
      rw [measure_toMeasurable, measure_toMeasurable,
        ENNReal.ofReal_add (by positivity) (by positivity)]
      exact add_le_add (hbad K hK1) (h2 K hK1)
    have hTlt : μ T < μ A₃ := by
      refine hTle.trans_lt ?_
      rw [ENNReal.ofReal_lt_iff_lt_toReal (by positivity) (measure_ne_top _ _)]
      exact hK₁ K ((le_max_left _ _).trans hK)
    exact (tsub_pos_of_lt hTlt).trans_le le_measure_sdiff

/-! ### Lemma 5.27 at slope `q`: the slope-dependent steps

The steps of `LargeGradientSensitive.lean` and `FiniteBranches.lean` that assume a corrected plane
of slope `e₁` use only `Δℓ = 0` (`hℓ.1.1`); their harmonic versions assume `ℓ ∈ 𝒜₁` (the first
conjunct of `IsCorrectedPlane C q ℓ` for every `q`). The minimal scale and the holes step use the
cone `κ |x|₁ ≤ q · x` and a lattice half-line `{k w}` along which `q · x` decreases. -/

/-- The lattice half-line `{k w : k ∈ ℕ}` (`L_-` for `w = -e₁`). -/
def latticeRay (w : Vertex 2) : Set (Vertex 2) := {y | ∃ k : ℕ, y = (k : ℤ) • w}

open Rigidity.External in
/-- step:5.27-Mh at slope `q` (eq. `def-Mh`, L2457-2462): from Theorem 2.5 at slope `q`, for every
cone `κ |x|₁ ≤ q · x` and every lattice direction `w` with `q · w < 0`, almost surely a scale `M`
beyond which every corrected plane `ℓ_q` on the cone exceeds `ℓ_q` on `𝒞_∞ ∩ (Q_r ∪ {k w})`. -/
def CorrectedPlaneMinimalScaleAtStep : Prop :=
  CorrectorQuantitativeInput → ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) →
    (p : ℝ) < 1 → ∀ (q : Fin 2 → ℝ) (w : Vertex 2), slopeDot q w < 0 → ∀ κ : ℝ, 0 < κ →
    ∀ r : ℕ, ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω,
      ∃ M : ℝ, ∀ ℓ, IsCorrectedPlane (uniqueInfiniteComponent h) q ℓ →
        ∀ x y : uniqueInfiniteComponent h, κ * l1 x.val ≤ slopeDot q x.val → M ≤ l1 x.val →
          (y.val ∈ cube r ∨ y.val ∈ latticeRay w) → ℓ y < ℓ x

/-- `ExplorationHolesStep` with `L_-` replaced by a lattice half-line `{k w}`, `|w|₁ = 1`. -/
def ExplorationHolesRayStep : Prop :=
  ∀ w : Vertex 2, l1 w = 1 →
  ∀ (ω : Configuration 2) (C : OpenComponent ω) (f : Vertex 2 → ℤ) (r : ℕ) (u ℓ : C → ℝ)
    (x₀ x₁ : C), (∀ x, f x ≠ 0 → x ∈ cube r) → ℓ x₀ < ℓ x₁ →
    (∀ y : C, (y.val ∈ cube r ∨ y.val ∈ latticeRay w) → ℓ y < ℓ x₀) →
    ∀ S ⊆ explorationSet C u ℓ x₀ x₁, ∀ T, IsLatticeComponentOf (Subtype.val '' S)ᶜ T →
      T.Finite → ∀ x ∈ T, f x = 0

/-- `RootBlockStep` for `ℓ ∈ 𝒜₁` (every slope). -/
def RootBlockHarmonicStep : Prop :=
  ∀ (ω : Configuration 2) (C : OpenComponent ω) (u ℓ : C → ℝ),
    ℓ ∈ harmonicGrowthSpace C 1 → ∀ x₀ x₁ : C, (componentGraph C).Adj x₀ x₁ →
    u x₁ = u x₀ → ∀ Cχ : ℝ, 0 < Cχ → Cχ ≤ ℓ x₁ - ℓ x₀ →
      (∃ z, IsSensitiveEdge C u ℓ x₁ z) ∨
        ∃ B₀ : ExplorationBlock C u ℓ x₀ x₁, x₁ ∈ B₀.val ∧ Cχ / 4 ≤ outgoingFlux C ℓ x₁ B₀.val

/-- `LeafSensitiveStep` for `ℓ ∈ 𝒜₁` (every slope). -/
def LeafSensitiveHarmonicStep : Prop :=
  ∀ (ω : Configuration 2) (C : OpenComponent ω) (u ℓ : C → ℝ),
    ℓ ∈ harmonicGrowthSpace C 1 → ∀ x₀ x₁ : C, (componentGraph C).Adj x₀ x₁ →
    ℓ x₀ < ℓ x₁ → u x₁ = u x₀ → ∀ B₀ : ExplorationBlock C u ℓ x₀ x₁, x₁ ∈ B₀.val →
      LeafSensitive C u ℓ x₀ x₁ B₀

/-- `FluxBalanceStep` for `ℓ ∈ 𝒜₁` (every slope). -/
def FluxBalanceHarmonicStep : Prop :=
  ∀ (ω : Configuration 2) (C : OpenComponent ω) (u ℓ : C → ℝ),
    ℓ ∈ harmonicGrowthSpace C 1 → ∀ x₀ x₁ : C, (componentGraph C).Adj x₀ x₁ →
    ℓ x₀ < ℓ x₁ → u x₁ = u x₀ → ∀ B₀ : ExplorationBlock C u ℓ x₀ x₁, x₁ ∈ B₀.val →
      FluxBalance C u ℓ x₀ x₁ B₀

/-- Lemma 5.28 for every initial edge and every `ℓ ∈ 𝒜₁` (every slope): the draft
`FiniteBranchesStmt` without the hypotheses `|x₀,₂| ≤ x₀,₁` and `M ≤ x₀,₁` (which its proof does
not use), with the corrected plane of slope `e₁` replaced by `ℓ ∈ 𝒜₁`. -/
def FiniteBranchesHarmonicStmt (p : unitInterval) (f : Vertex 2 → ℤ) : Prop :=
  (Function.support f).Finite → ∃ Cbr : ℕ,
  ∀ᵐ ω ∂latticeBondLaw 2 p, ∃ h : HasUniqueInfiniteOpenComponent ω,
    ∀ u, IsDecayingPotential (uniqueInfiniteComponent h) f u → (Function.support u).Infinite →
    ∀ ℓ, ℓ ∈ harmonicGrowthSpace (uniqueInfiniteComponent h) 1 →
    ∀ x₀ x₁ : uniqueInfiniteComponent h,
      (componentGraph _).Adj x₀ x₁ → ℓ x₀ < ℓ x₁ → u x₁ = u x₀ →
    ∀ B₀ : {S // IsBlock _ (explorationGraph _ u ℓ x₀ x₁) (explorationSet _ u ℓ x₀ x₁) S},
      x₁ ∈ B₀.val →
    ∀ (n : ℕ) (b : Fin n → Set (keptVertices _ u ℓ x₀ x₁ (.inl B₀))),
      (∀ i, IsBranch ((blockCutTree _ _ _).induce (keptVertices _ u ℓ x₀ x₁ (.inl B₀)))
        ⟨.inl B₀, by
          simp only [keptVertices, Set.mem_setOf_eq]
          rintro ⟨B, -, hne, hall⟩
          exact hne (by simpa using hall .nil .nil)⟩ (b i)) →
      Function.Injective b → n ≤ Cbr

/-- `LeafExitStep` for `ℓ ∈ 𝒜₁` (every slope). -/
def LeafExitHarmonicStep : Prop :=
  ∀ (ω : Configuration 2) (C : OpenComponent ω) (u ℓ : C → ℝ),
    ℓ ∈ harmonicGrowthSpace C 1 → ∀ x₀ x₁ : C, (componentGraph C).Adj x₀ x₁ →
    u x₁ = u x₀ → ∀ B₀ : ExplorationBlock C u ℓ x₀ x₁, x₁ ∈ B₀.val →
    ∀ S, IsPrunedFiniteLeafBranch C u ℓ x₀ x₁ B₀ S →
      ∃ z p : C, IsPrunedExit C u ℓ x₀ x₁ B₀ S z ∧ u z = u x₀ ∧ (componentGraph C).Adj z p ∧
        u p ≠ u x₀

/-! ### Proofs of the slope-free steps

Each is the proof of the corresponding step of the `e₁` carving with `hℓ.1.1` (harmonicity of a
corrected plane) replaced by `hℓ.1` (harmonicity of `ℓ ∈ 𝒜₁`); the holes step follows the
lattice half-line `{k w}` instead of `L_-`. -/

section HarmonicSteps

open Classical

/-- `rootBlockStep` for `ℓ ∈ 𝒜₁`: the proof only uses harmonicity. -/
theorem rootBlockHarmonicStep : RootBlockHarmonicStep := by
  intro ω C u ℓ hℓ x₀ x₁ hadj hu Cχ hCχ hgap
  set N := (componentGraph C).neighborFinset x₁ with hN
  have hharm : ∑ y ∈ N, (ℓ y - ℓ x₁) = 0 := hℓ.1 x₁
  have hx₀N : x₀ ∈ N := (SimpleGraph.mem_neighborFinset _ _ _).2 hadj.symm
  -- the flux to the neighbours with `ℓ ≤ ℓ(x₁)` is at most the term of `x₀`
  have hneg : ∑ y ∈ N with ¬ ℓ x₁ < ℓ y, (ℓ y - ℓ x₁) ≤ ℓ x₀ - ℓ x₁ := by
    have hx₀mem : x₀ ∈ N.filter fun y => ¬ ℓ x₁ < ℓ y :=
      Finset.mem_filter.2 ⟨hx₀N, by linarith⟩
    rw [← Finset.add_sum_erase _ _ hx₀mem]
    have hrest : ∑ y ∈ (N.filter fun y => ¬ ℓ x₁ < ℓ y).erase x₀, (ℓ y - ℓ x₁) ≤ 0 :=
      Finset.sum_nonpos fun y hy => by
        have := (Finset.mem_filter.1 (Finset.mem_of_mem_erase hy)).2
        linarith [not_lt.1 this]
    linarith
  have hpos : Cχ ≤ ∑ y ∈ N with ℓ x₁ < ℓ y, (ℓ y - ℓ x₁) := by
    have := Finset.sum_filter_add_sum_filter_not N (fun y => ℓ x₁ < ℓ y) (fun y => ℓ y - ℓ x₁)
    linarith
  -- pigeonhole over the at most four neighbours of `x₁`
  obtain ⟨y, hyN, hy⟩ : ∃ y ∈ N.filter fun y => ℓ x₁ < ℓ y, Cχ / 4 ≤ ℓ y - ℓ x₁ := by
    by_contra! hlt
    have hcard : ((N.filter fun y => ℓ x₁ < ℓ y).card : ℝ) ≤ 4 := by
      have h1 := Finset.card_filter_le N (fun y => ℓ x₁ < ℓ y)
      have h2 : N.card ≤ 2 * 2 := by
        rw [hN, SimpleGraph.card_neighborFinset_eq_degree]
        exact componentGraph_degree_le C x₁
      exact_mod_cast h1.trans h2
    rcases (N.filter fun y => ℓ x₁ < ℓ y).eq_empty_or_nonempty with he | hne
    · rw [he, Finset.sum_empty] at hpos
      linarith
    · have := Finset.sum_lt_sum_of_nonempty hne hlt
      rw [Finset.sum_const, nsmul_eq_mul] at this
      nlinarith
  obtain ⟨hyN', hxy⟩ := Finset.mem_filter.1 hyN
  have hx₁y : (componentGraph C).Adj x₁ y := (SimpleGraph.mem_neighborFinset _ _ _).1 hyN'
  by_cases huy : u y = u x₀
  · right
    have hx₁V := x₁_mem_explorationSet (ℓ := ℓ) hadj hu
    have hyV := mem_explorationSet_of_adj hx₁V hx₁y huy hxy
    obtain ⟨B, hB, hsub⟩ := exists_isBlock_superset
      (biconnectedIn_pair (G := explorationGraph C u ℓ x₀ x₁) hx₁V hyV ⟨hx₁V, hyV, hx₁y, hxy.ne⟩)
    refine ⟨⟨B, hB⟩, hsub (Set.mem_insert _ _), ?_⟩
    have hymem : y ∈ N.filter (· ∈ B) :=
      Finset.mem_filter.2 ⟨hyN', hsub (Set.mem_insert_of_mem _ rfl)⟩
    refine hy.trans (Finset.single_le_sum (f := fun w => ℓ w - ℓ x₁) (fun w hw => ?_) hymem)
    have hwV := hB.1.1 (Finset.mem_filter.1 hw).2
    linarith [le_of_mem_explorationSet C hwV]
  · left
    exact ⟨y, hx₁y, hxy.ne, fun h => huy (h.symm.trans hu)⟩

/-- `leafSensitiveStep` for `ℓ ∈ 𝒜₁`. -/
theorem leafSensitiveHarmonicStep : LeafSensitiveHarmonicStep := by
  intro ω C u ℓ hℓ x₀ x₁ hadj hlt hu B₀ hx₁B₀ B hBk hBfin hcase
  have hx₁V := x₁_mem_explorationSet (ℓ := ℓ) hadj hu
  have hVc := connectedIn_explorationSet hx₁V
  -- a pruning block carries a sensitive edge
  by_cases hBp : IsPruningBlock C u ℓ (u x₀) B.val
  · obtain ⟨y, hyB, z, hzy, hz, hℓzy⟩ := hBp
    have hyu : u y = u x₀ := levelSet_of_mem_explorationSet (B.2.1.1 hyB)
    exact ⟨y, hyB, z, hzy.symm, fun h => hℓzy h.symm, fun h => hz (h.symm.trans hyu)⟩
  have hnochild := hcase.resolve_left hBp
  -- every cut-vertex of `B` is its parent, which is unique
  have hpar : ∀ c : ExplorationCut C u ℓ x₀ x₁, c.val ∈ B.val →
      ∃ W : (blockCutTree C _ _).Walk (.inl B₀) (.inr c), W.IsPath ∧ Sum.inl B ∉ W.support :=
    fun c hc => (isTreeChild_or_parent hx₁V hx₁B₀ hBk hBp c hc).resolve_left (hnochild c)
  have hcut : ∀ c c' : ExplorationCut C u ℓ x₀ x₁, c.val ∈ B.val → c'.val ∈ B.val → c = c' := by
    intro c c' hc hc'
    obtain ⟨W, hW, hBW⟩ := hpar c hc
    obtain ⟨W', hW', hBW'⟩ := hpar c' hc'
    exact eq_of_parent W hW hBW hc W' hW' hBW' hc'
  -- `B` is nonempty, by maximality against `{x₁}`
  have hBne : B.val.Nonempty := by
    by_contra hBe
    rw [Set.not_nonempty_iff_eq_empty] at hBe
    have hbi : BiconnectedIn C (explorationGraph C u ℓ x₀ x₁) (explorationSet C u ℓ x₀ x₁)
        {x₁} :=
      ⟨Set.singleton_subset_iff.2 hx₁V,
        connectedIn_of_reachIn (z := x₁) fun x hx => by
          rw [Set.mem_singleton_iff.1 hx]
          exact .refl rfl,
        fun x hx => connectedIn_of_reachIn (z := x₁) fun y hy =>
          (hy.2 ((Set.mem_singleton_iff.1 hy.1).trans (Set.mem_singleton_iff.1 hx).symm)).elim⟩
    have := B.2.2 {x₁} hbi (hBe ▸ Set.empty_subset _)
    rw [hBe] at this
    exact Set.singleton_ne_empty x₁ this
  -- the maximum `z` of `ℓ` on `B` has a neighbour `p` with `ℓ(p) > ℓ(z)`
  obtain ⟨z, hzB, hzmax⟩ := Set.exists_max_image B.val ℓ hBfin hBne
  have hzV := B.2.1.1 hzB
  have hzu : u z = u x₀ := levelSet_of_mem_explorationSet hzV
  obtain ⟨w, hzw, hwz⟩ := exists_adj_lt_of_mem_explorationSet hadj hlt z hzV
  obtain ⟨⟨p, hzp, hzp'⟩, -⟩ :=
    exists_above_below_of_harmonic (u := ℓ) (hℓ.1 z) rfl hzw hwz.ne
  by_cases hpu : u p = u x₀
  swap
  · exact ⟨z, hzB, p, hzp, hzp'.ne, fun h => hpu (h.symm.trans hzu)⟩
  -- otherwise `z` is a cut-vertex of `B`, its parent
  exfalso
  have hpV := mem_explorationSet_of_adj hzV hzp hpu hzp'
  have hpB : p ∉ B.val := fun h => absurd (hzmax p h) (not_le.2 hzp')
  have hzcut := IsBlock.isCutVertex_of_adj B.2 hzB hpV hpB ⟨hzV, hpV, hzp, hzp'.ne⟩
  obtain ⟨W, -, hBW⟩ := hpar ⟨z, hzcut⟩ hzB
  have hBB₀ : B ≠ B₀ := by
    rintro rfl
    exact hBW W.start_mem_support
  have honly : ∀ y ∈ B.val, IsCutVertex C (explorationGraph C u ℓ x₀ x₁)
      (explorationSet C u ℓ x₀ x₁) y → y = z :=
    fun y hy hcy => congrArg Subtype.val (hcut ⟨y, hcy⟩ ⟨z, hzcut⟩ hy hzB)
  -- `ℓ > ℓ(z)` on `B \ {z}`
  have hmin : ∀ y ∈ explorationSet C u ℓ x₀ x₁, y ∈ B.val → y ≠ z → ℓ z < ℓ y := by
    refine explorationSet_induction ?_ ?_
    · intro hx₁B hx₁z
      exact absurd (honly x₁ hx₁B (IsBlock.isCutVertex B.2 B₀.2
        (fun h => hBB₀ (Subtype.ext h)) hx₁B hx₁B₀)) hx₁z
    · intro y y' hy hy' hyy' hlt' ih hy'B hy'z
      by_cases hyB : y ∈ B.val
      · by_cases hyz : y = z
        · rw [← hyz]
          exact hlt'
        · exact (ih hyB hyz).trans hlt'
      · exact absurd (honly y' hy'B (IsBlock.isCutVertex_of_adj B.2 hy'B hy hyB
          ⟨hy', hy, hyy'.symm, hlt'.ne'⟩)) hy'z
  -- `B` has a point other than `z`, since `z` lies in a second block
  obtain ⟨B', hB', hzB', hB'B⟩ := exists_isBlock_ne hVc hzcut B.2
  obtain ⟨w', hw'B, hw'z⟩ := IsBlock.exists_ne_of_ne B.2 hB' (Ne.symm hB'B) hzB hzB'
  exact absurd (hzmax w' hw'B) (not_le.2 (hmin w' (B.2.1.1 hw'B) hw'B hw'z))

/-- `fluxBalanceStep` for `ℓ ∈ 𝒜₁`. -/
theorem fluxBalanceHarmonicStep : FluxBalanceHarmonicStep := by
  intro ω C u ℓ hℓ x₀ x₁ hadj _ hu B₀ hx₁B₀
  have hx₁V := x₁_mem_explorationSet (ℓ := ℓ) hadj hu
  have hharm : ∀ x, ∑ y ∈ (componentGraph C).neighborFinset x, (ℓ y - ℓ x) = 0 :=
    fun x => hℓ.1 x
  exact ⟨fun hB hBp => outgoingFlux_le_sum_incomingFlux hharm hB hBp hx₁B₀,
    fun B c₀ hc₀ hB hBp => outgoingFlux_le_sum_incomingFlux hharm hB hBp hc₀.2.2.1,
    fun P c hPc => incomingFlux_le_finsum hharm hx₁V hx₁B₀ hPc⟩

/-- `leafExitStep` for `ℓ ∈ 𝒜₁`. -/
theorem leafExitHarmonicStep : LeafExitHarmonicStep := by
  intro ω C u ℓ hℓ x₀ x₁ hadj hu B₀ hx₁B S hS
  obtain ⟨v, hvr, hleaf, ⟨W, hW, rfl⟩, hfin⟩ := hS
  have hx₁V := x₁_mem_explorationSet (ℓ := ℓ) hadj hu
  have hVc := connectedIn_explorationSet hx₁V
  have hWf : (W.map (prunedHom B₀)).IsPath := hW.map (prunedHom_injective B₀)
  have hcv : (prunedTree C u ℓ x₀ x₁ B₀).Adj W.penultimate v :=
    W.adj_penultimate (W.not_nil_of_ne (Ne.symm hvr))
  have hcT : (blockCutTree C _ _).Adj W.penultimate.val v.val := hcv
  rcases hvval : v.val with L | x
  · rw [hvval] at hcT
    rcases hcval : W.penultimate.val with B' | c0
    · rw [hcval] at hcT
      exact hcT.elim
    rw [hcval] at hcT
    have hc0L : c0.val ∈ L.val := hcT
    have hcr : W.penultimate ≠ prunedRoot C u ℓ x₀ x₁ B₀ := fun h => by
      have := congrArg Subtype.val h
      rw [hcval] at this
      exact Sum.inr_ne_inl this
    obtain ⟨b, hbW, hbv, hbc⟩ := exists_adj_penultimate W hW hcr
    have hbT : (blockCutTree C _ _).Adj b.val W.penultimate.val := hbc
    rw [hcval] at hbT
    rcases hbval : b.val with Bpp | b'
    swap
    · rw [hbval] at hbT
      exact hbT.elim
    rw [hbval] at hbT
    have hc0B : c0.val ∈ Bpp.val := hbT
    have hBL : Bpp ≠ L := fun h => hbv (Subtype.ext (hbval.trans (h ▸ hvval.symm)))
    have hexit : ∀ y ∈ L.val, y ≠ c0.val → IsPrunedExit C u ℓ x₀ x₁ B₀ {x | x ∈ W.support} y :=
      fun y hy hyc => isPrunedExit_of_mem hvr hleaf W hW hvval hcval hy hyc
    by_cases hpr : IsPruningBlock C u ℓ (u x₀) L.val
    · obtain ⟨y, hyL, z, hzy, hz, hℓzy⟩ := hpr
      by_cases hyc : y = c0.val
      · exfalso
        apply v.2
        refine ⟨Bpp, ⟨y, hyc ▸ hc0B, z, hzy, hz, hℓzy⟩, isStrictAncestor_of_mem _ hWf ?_ ?_⟩
        · exact (mem_support_map_prunedHom W).2 ⟨b, hbW, hbval⟩
        · show (Sum.inl Bpp : BlockCutVertex C _ _) ≠ v.val
          rw [hvval]
          exact fun h => hBL (Sum.inl_injective h)
      · exact ⟨y, z, hexit y hyL hyc, levelSet_of_mem_explorationSet (L.2.1.1 hyL), hzy.symm, hz⟩
    -- `L` is not a pruning block: `c0` is its only cut-vertex
    have hpar : ∀ w, (blockCutTree C _ _).Adj (.inl L) w → w = .inr c0 := by
      intro w hw
      refine (eq_parent_of_adj_of_not_pruning hvr hleaf W hW ?_ (w := w) ?_).trans hcval
      · intro A hA
        rw [hvval] at hA
        rw [← Sum.inl_injective hA]
        exact hpr
      · rw [hvval]
        exact hw
    have hcut : ∀ y ∈ L.val, IsCutVertex C (explorationGraph C u ℓ x₀ x₁)
        (explorationSet C u ℓ x₀ x₁) y → y = c0.val := fun y hy hcy =>
      congrArg Subtype.val (Sum.inr_injective (hpar (.inr ⟨y, hcy⟩) hy))
    obtain ⟨w0, hw0L, hw0c⟩ :=
      IsBlock.exists_ne_of_ne L.2 Bpp.2 (fun h => hBL (Subtype.ext h).symm) hc0L hc0B
    -- `ℓ` is minimal on `L` exactly at `c0`
    have hmin : ∀ y ∈ explorationSet C u ℓ x₀ x₁, y ∈ L.val → y ≠ c0.val → ℓ c0.val < ℓ y := by
      refine explorationSet_induction ?_ ?_
      · intro hx₁L hx₁c
        refine absurd (hcut x₁ hx₁L (IsBlock.isCutVertex L.2 B₀.2 ?_ hx₁L hx₁B)) hx₁c
        intro h
        apply hvr
        exact Subtype.ext (hvval.trans (congrArg Sum.inl (Subtype.ext h)))
      · intro y y' hy hy' hyy' hlt ih hy'L hy'c
        by_cases hyL : y ∈ L.val
        · by_cases hyc : y = c0.val
          · rw [← hyc]
            exact hlt
          · exact (ih hyL hyc).trans hlt
        · exact absurd (hcut y' hy'L (IsBlock.isCutVertex_of_adj L.2 hy'L hy hyL
            ⟨hy', hy, hyy'.symm, hlt.ne'⟩)) hy'c
    have hfin' : L.val.Finite := by
      change (blockCutCarrier C v.val).Finite at hfin
      rw [hvval] at hfin
      exact hfin
    obtain ⟨z, hzL, hzmax⟩ := Set.exists_max_image L.val ℓ hfin' ⟨c0.val, hc0L⟩
    have hzc : z ≠ c0.val := by
      rintro rfl
      exact absurd (hzmax w0 hw0L) (not_le.2 (hmin w0 (L.2.1.1 hw0L) hw0L hw0c))
    have hzV := L.2.1.1 hzL
    -- a neighbour of `z` in `𝒢`, and harmonicity of `ℓ` at `z`
    obtain ⟨q, -⟩ := connectedIn_iff.1 L.2.1.2.1 z hzL c0.val hc0L
    have hqlen : 0 < q.length :=
      Nat.pos_of_ne_zero fun h => hzc (SimpleGraph.Walk.eq_of_length_eq_zero h)
    have hz1 := q.adj_getVert_succ (i := 0) hqlen
    rw [q.getVert_zero] at hz1
    have hharm : ∀ x, componentLaplacian C ℓ x = 0 := hℓ.1
    obtain ⟨⟨p, hzp, hlt⟩, -⟩ :=
      exists_above_below_of_harmonic (u := ℓ) (hharm z) rfl hz1.2.2.1 hz1.2.2.2.symm
    refine ⟨z, p, hexit z hzL hzc, levelSet_of_mem_explorationSet hzV, hzp, fun hp => hzc ?_⟩
    have hpV := mem_explorationSet_of_adj hzV hzp hp hlt
    have hpL : p ∉ L.val := fun h => absurd (hzmax p h) (not_le.2 hlt)
    exact hcut z hzL (IsBlock.isCutVertex_of_adj L.2 hzL hpV hpL ⟨hzV, hpV, hzp, hlt.ne⟩)
  · -- a leaf cut-vertex lies in a second block, which is kept
    exfalso
    rw [hvval] at hcT
    rcases hcval : W.penultimate.val with Bp | c'
    swap
    · rw [hcval] at hcT
      exact hcT.elim
    obtain ⟨B', hB', hxB', hne⟩ := exists_isBlock_ne hVc x.2 Bp.2
    have hpar := eq_parent_of_adj_of_not_pruning hvr hleaf W hW
      (fun A hA => by rw [hvval] at hA; exact (Sum.inr_ne_inl hA).elim) (w := .inl ⟨B', hB'⟩)
      (by rw [hvval]; exact hxB')
    rw [hcval] at hpar
    exact hne (congrArg Subtype.val (Sum.inl_injective hpar))

variable {ω : Configuration 2}

/-- `branches_card_le` for `ℓ ∈ 𝒜₁`: the corrected plane enters only through `LeafExitStep`. -/
theorem branches_card_le_harmonic (hJ : External.JordanCurveTheoremSphere) (hI : InfiniteBranchesStep)
    (hE : LeafExitHarmonicStep) (hD : ExitsDistinctStep) (hS : LeafSeparatorStep) (hK : NoK33MinorStep)
    {C : OpenComponent ω} {f : Vertex 2 → ℤ} (hf : (Function.support f).Finite) {u : C → ℝ}
    (hu : IsDecayingPotential C f u)
    (h512ω : ∀ T, IsComponentOf C (levelSet u 0) T →
      ¬ HasDisjointInfinitePaths C T ((Function.support f).ncard + 3))
    (hP : ∀ (a : ℝ) T, IsComponentOf C {x | a < u x} T → ∃ y ∈ T, f y.val ≠ 0)
    (hP' : ∀ (a : ℝ) T, IsComponentOf C {x | a < (-u) x} T → ∃ y ∈ T, (-f) y.val ≠ 0)
    {ℓ : C → ℝ} (hℓ : ℓ ∈ harmonicGrowthSpace C 1) {x₀ x₁ : C}
    (hadj : (componentGraph C).Adj x₀ x₁) (hux : u x₁ = u x₀) (B₀ : ExplorationBlock C u ℓ x₀ x₁)
    (hB₀ : x₁ ∈ B₀.val) {n : ℕ} (b : Fin n → Set (PrunedVertex C u ℓ x₀ x₁ B₀))
    (hb : ∀ i, IsPrunedBranch C u ℓ x₀ x₁ B₀ (b i)) (hbinj : Function.Injective b) :
    n ≤ 2 * (Function.support f).ncard ^ 2 + 2 * (Function.support f).ncard + 2 := by
  classical
  set N := (Function.support f).ncard with hN
  -- the branches as a finset, split into finite leaf branches and the others
  set s : Finset (Set (PrunedVertex C u ℓ x₀ x₁ B₀)) := Finset.univ.image b
  have hscard : s.card = n := by
    rw [Finset.card_image_of_injective _ hbinj, Finset.card_univ, Fintype.card_fin]
  have hsb : ∀ S ∈ s, IsPrunedBranch C u ℓ x₀ x₁ B₀ S := by
    intro S hS
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hS
    exact hb i
  set sF := s.filter (IsPrunedFiniteLeafBranch C u ℓ x₀ x₁ B₀)
  set sI := s.filter (fun S => ¬ IsPrunedFiniteLeafBranch C u ℓ x₀ x₁ B₀ S)
  have hsplit : sF.card + sI.card = s.card := Finset.card_filter_add_card_filter_not _
  -- infinite branches: Prop 5.12
  have hcardI : sI.card ≤ N + 2 := by
    by_contra hlt
    push Not at hlt
    obtain ⟨T, hT, hpaths⟩ := hI ω C f u hu ℓ x₀ x₁ hadj hux B₀ hB₀ sI
      (Finset.card_pos.1 (by omega))
      (fun S hS => ⟨hsb S (Finset.mem_filter.1 hS).1, (Finset.mem_filter.1 hS).2⟩)
    exact h512ω T hT (hasDisjointInfinitePaths_mono hpaths (by omega))
  -- exits of the finite leaf branches
  have hex : ∀ S : Set (PrunedVertex C u ℓ x₀ x₁ B₀), ∃ z q : C,
      IsPrunedFiniteLeafBranch C u ℓ x₀ x₁ B₀ S → IsPrunedExit C u ℓ x₀ x₁ B₀ S z ∧
        u z = u x₀ ∧ (componentGraph C).Adj z q ∧ u q ≠ u x₀ := by
    intro S
    by_cases hS : IsPrunedFiniteLeafBranch C u ℓ x₀ x₁ B₀ S
    · obtain ⟨z, q, hz⟩ := hE ω C u ℓ hℓ x₀ x₁ hadj hux B₀ hB₀ S hS
      exact ⟨z, q, fun _ => hz⟩
    · exact ⟨x₀, x₀, fun h => absurd h hS⟩
  choose z q hz using hex
  have hFS : ∀ S ∈ sF, IsPrunedFiniteLeafBranch C u ℓ x₀ x₁ B₀ S :=
    fun S hS => (Finset.mem_filter.1 hS).2
  have hzinj : ∀ S ∈ sF, ∀ S' ∈ sF, z S = z S' → S = S' := by
    intro S hS S' hS' hzz
    by_contra hne
    exact hD ω C u ℓ x₀ x₁ hadj hux B₀ hB₀ S S' (z S) (z S') (hFS S hS) (hFS S' hS')
      (hz S (hFS S hS)).1 (hz S' (hFS S' hS')).1 hne hzz
  -- exits at poles: at most `N`
  set sB := sF.filter (fun S => f (z S).val ≠ 0)
  set sG := sF.filter (fun S => ¬ f (z S).val ≠ 0)
  have hsplitF : sB.card + sG.card = sF.card := Finset.card_filter_add_card_filter_not _
  have hcardB : sB.card ≤ N := by
    rw [hN, Set.ncard_eq_toFinset_card _ hf]
    refine Finset.card_le_card_of_injOn (fun S => (z S).val) (fun S hS => ?_) ?_
    · simpa using (Finset.mem_filter.1 hS).2
    · intro S hS S' hS' hzz
      exact hzinj S (Finset.mem_filter.1 hS).1 S' (Finset.mem_filter.1 hS').1 (Subtype.ext hzz)
  -- harmonic exits: neighbours above and below, and their poles (Lemma 5.17 for `f` and `-f`)
  have hpole : ∀ S : Set (PrunedVertex C u ℓ x₀ x₁ B₀), ∃ qp qn πp πn : C, S ∈ sG →
      (componentGraph C).Adj (z S) qp ∧ (componentGraph C).Adj (z S) qn ∧
      f πp.val ≠ 0 ∧ f πn.val ≠ 0 ∧ JoinedIn C {x | u x₀ < u x} qp πp ∧
      JoinedIn C {x | -u x₀ < (-u) x} qn πn := by
    intro S
    by_cases hSG : S ∈ sG
    · obtain ⟨hSF, hf0⟩ := Finset.mem_filter.1 hSG
      obtain ⟨-, hza, hzq, hq⟩ := hz S (hFS S hSF)
      have hlap : componentLaplacian C u (z S) = 0 := by
        simpa [not_not.1 hf0] using hu.1 (z S)
      obtain ⟨⟨qp, hqp, hqp'⟩, qn, hqn, hqn'⟩ := exists_above_below_of_harmonic hlap hza hzq hq
      obtain ⟨πp, hπp, hfπp⟩ := hP (u x₀) _ ⟨qp, hqp', rfl⟩
      obtain ⟨πn, hπn, hfπn⟩ := hP' (-u x₀) _ ⟨qn, (show -u x₀ < (-u) qn by simp; linarith), rfl⟩
      exact ⟨qp, qn, πp, πn, fun _ => ⟨hqp, hqn, hfπp, by simpa using hfπn, hπp, hπn⟩⟩
    · exact ⟨x₀, x₀, x₀, x₀, fun h => absurd h hSG⟩
  choose qp qn πp πn hπ using hpole
  -- three harmonic exits sharing both poles form a `K_{3,3}` minor
  have hPf : {y : C | f y.val ≠ 0}.Finite := hf.preimage Subtype.val_injective.injOn
  have hPcard : hPf.toFinset.card ≤ N := by
    rw [hN, Set.ncard_eq_toFinset_card _ hf]
    exact Finset.card_le_card_of_injOn Subtype.val (fun y hy => by simpa using hy)
      Subtype.val_injective.injOn
  have hcardG : sG.card ≤ 2 * N ^ 2 := by
    by_contra hlt
    push Not at hlt
    have hmaps : ∀ S ∈ sG, (πp S, πn S) ∈ hPf.toFinset ×ˢ hPf.toFinset := by
      intro S hS
      obtain ⟨-, -, h1, h2, -, -⟩ := hπ S hS
      simp [h1, h2]
    have hlt' : (hPf.toFinset ×ˢ hPf.toFinset).card * 2 < sG.card := by
      rw [Finset.card_product]
      calc hPf.toFinset.card * hPf.toFinset.card * 2 ≤ N * N * 2 := by gcongr
        _ = 2 * N ^ 2 := by ring
        _ < sG.card := hlt
    obtain ⟨y, -, hy⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps hlt'
    obtain ⟨S₁, S₂, S₃, h1, h2, h3, h12, h13, h23⟩ := Finset.two_lt_card_iff.1 hy
    set Sf : Fin 3 → Set (PrunedVertex C u ℓ x₀ x₁ B₀) := ![S₁, S₂, S₃]
    have hSf : ∀ i, Sf i ∈ sG ∧ (πp (Sf i), πn (Sf i)) = y := by
      intro i
      fin_cases i
      exacts [Finset.mem_filter.1 h1, Finset.mem_filter.1 h2, Finset.mem_filter.1 h3]
    have hSfinj : Function.Injective Sf := by
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        first | rfl | exact absurd hij h12 | exact absurd hij h13 | exact absurd hij h23 |
          exact absurd hij.symm h12 | exact absurd hij.symm h13 | exact absurd hij.symm h23
    have hFi : ∀ i, IsPrunedFiniteLeafBranch C u ℓ x₀ x₁ B₀ (Sf i) :=
      fun i => hFS _ (Finset.mem_filter.1 (hSf i).1).1
    obtain ⟨X₀, hX₀a, hX₀c, hX₀z, hX₀adj⟩ := hS ω C u ℓ x₀ x₁ hadj hux B₀ hB₀ Sf
      (fun i => z (Sf i)) hSfinj hFi (fun i => (hz _ (hFi i)).1)
    set Xp := {w | JoinedIn C {x | u x₀ < u x} y.1 w}
    set Xn := {w | JoinedIn C {x | -u x₀ < (-u) x} y.2 w}
    have hqp : ∀ i, qp (Sf i) ∈ Xp := fun i => by
      have h := (hπ _ (hSf i).1).2.2.2.2.1
      rw [show πp (Sf i) = y.1 from congrArg Prod.fst (hSf i).2] at h
      exact joinedIn_symm h
    have hqn : ∀ i, qn (Sf i) ∈ Xn := fun i => by
      have h := (hπ _ (hSf i).1).2.2.2.2.2
      rw [show πn (Sf i) = y.2 from congrArg Prod.snd (hSf i).2] at h
      exact joinedIn_symm h
    obtain ⟨hXpc, hXpa⟩ := isConnectedSet_of_isComponentOf
      (show IsComponentOf C {x | u x₀ < u x} Xp from ⟨y.1, (hqp 0).1, rfl⟩)
    obtain ⟨hXnc, hXna⟩ := isConnectedSet_of_isComponentOf
      (show IsComponentOf C {x | -u x₀ < (-u) x} Xn from ⟨y.2, (hqn 0).1, rfl⟩)
    have hlev : ∀ i, u (z (Sf i)) = u x₀ := fun i => (hz _ (hFi i)).2.1
    -- the three sets lie in the three classes `u = a`, `u > a`, `u < a`
    have hcls : ∀ j, ∀ w ∈ ![X₀, Xp, Xn] j,
        (if u w = u x₀ then (0 : Fin 3) else if u x₀ < u w then 1 else 2) = j := by
      intro j w hw
      fin_cases j
      · simp [show u w = u x₀ from hX₀a hw]
      · have h := hXpa hw
        simp only [Set.mem_setOf_eq] at h
        simp [h.ne', h]
      · have h := hXna hw
        simp only [Set.mem_setOf_eq, Pi.neg_apply, neg_lt_neg_iff] at h
        simp [h.ne, not_lt.2 h.le]
    refine hK hJ ω C ![X₀, Xp, Xn] (fun i => z (Sf i)) (fun j => ?_) (fun j k hjk => ?_)
      (fun i j hij => ?_) (fun i j => ?_) (fun i j => ?_)
    · fin_cases j
      exacts [hX₀c, hXpc, hXnc]
    · exact Set.disjoint_left.2 fun w hj hk => hjk ((hcls j w hj).symm.trans (hcls k w hk))
    · by_contra hne
      exact hD ω C u ℓ x₀ x₁ hadj hux B₀ hB₀ (Sf i) (Sf j) _ _ (hFi i) (hFi j)
        (hz _ (hFi i)).1 (hz _ (hFi j)).1 (fun h => hne (hSfinj h)) hij
    · intro hmem
      have h := hcls j _ hmem
      fin_cases j
      · exact hX₀z i hmem
      · simp [hlev i] at h
      · simp [hlev i] at h
    · fin_cases j
      · exact hX₀adj i
      · exact ⟨qp (Sf i), hqp i, (hπ _ (hSf i).1).1⟩
      · exact ⟨qn (Sf i), hqn i, (hπ _ (hSf i).1).2.1⟩
  omega

/-- Lemma 5.28 for every `ℓ ∈ 𝒜₁`, by the proof of `finiteBranches_of_steps`. -/
theorem finiteBranchesHarmonic_of_steps {p : unitInterval} {f : Vertex 2 → ℤ}
    (hJ : External.JordanCurveTheoremSphere) (h516 : StrongMaxPrincipleStmt p)
    (h512 : InfiniteDisjointPathsStmt p f) (hI : InfiniteBranchesStep)
    (hE : LeafExitHarmonicStep) (hD : ExitsDistinctStep) (hS : LeafSeparatorStep)
    (hK : NoK33MinorStep) : FiniteBranchesHarmonicStmt p f := by
  intro hf
  have hf' : (Function.support (-f)).Finite := by simpa using hf
  refine ⟨2 * (Function.support f).ncard ^ 2 + 2 * (Function.support f).ncard + 2, ?_⟩
  filter_upwards [h512 hf,
    polesSuperLevelSets_of_steps Proofs.Section5.finiteMaxPrinciple h516 f hf,
    polesSuperLevelSets_of_steps Proofs.Section5.finiteMaxPrinciple h516 (-f) hf']
    with ω ⟨h, h512ω⟩ ⟨_, hP⟩ ⟨_, hP'⟩
  exact ⟨h, fun u hu hsupp ℓ hℓ x₀ x₁ hadj _ hux B₀ hB₀ n b hb hbinj =>
    branches_card_le_harmonic hJ hI hE hD hS hK hf hu (h512ω u hu hsupp) (hP u hu hsupp)
      (hP' (-u) (isDecayingPotential_neg hu) (by simpa using hsupp)) hℓ hadj hux B₀ hB₀ b hb
      hbinj⟩

/-! ### The holes step along a lattice ray -/

/-- `x` and `y` are joined by a nearest-neighbour path inside `A` (the relation defining the
connected components of `A` in `IsLatticeComponentOf`). -/
private def RayJoined (A : Set (Vertex 2)) (x y : Vertex 2) : Prop :=
  ∃ hx : x ∈ A, ∃ hy : y ∈ A, ((nearestNeighborGraph 2).induce A).Reachable ⟨x, hx⟩ ⟨y, hy⟩

private theorem RayJoined.trans {A : Set (Vertex 2)} {x y z : Vertex 2}
    (h₁ : RayJoined A x y) (h₂ : RayJoined A y z) : RayJoined A x z := by
  obtain ⟨hx, hy, r₁⟩ := h₁
  obtain ⟨hy', hz, r₂⟩ := h₂
  exact ⟨hx, hz, r₁.trans r₂⟩

private theorem RayJoined.symm {A : Set (Vertex 2)} {x y : Vertex 2}
    (h : RayJoined A x y) : RayJoined A y x := by
  obtain ⟨hx, hy, r⟩ := h
  exact ⟨hy, hx, r.symm⟩

/-- Along a lattice line inside `A`, the endpoints are joined in `A`. -/
private theorem rayJoined_of_line {A : Set (Vertex 2)} (f : ℤ → Vertex 2)
    (hf : ∀ t, (nearestNeighborGraph 2).Adj (f t) (f (t + 1))) {m n : ℤ}
    (hA : ∀ t, (m ≤ t ∧ t ≤ n) ∨ (n ≤ t ∧ t ≤ m) → f t ∈ A) : RayJoined A (f m) (f n) := by
  have key : ∀ a b, a ≤ b → (∀ t, a ≤ t → t ≤ b → f t ∈ A) → RayJoined A (f a) (f b) := by
    intro a b hab
    induction b, hab using Int.leInduction with
    | base => exact fun h => ⟨h a le_rfl le_rfl, h a le_rfl le_rfl, .refl _⟩
    | succ b hab ih =>
      intro h
      have hb : f b ∈ A := h b hab (by omega)
      have hb' : f (b + 1) ∈ A := h (b + 1) (by omega) le_rfl
      refine (ih fun t h1 h2 => h t h1 (by omega)).trans ⟨hb, hb', ?_⟩
      exact (show ((nearestNeighborGraph 2).induce A).Adj ⟨f b, hb⟩ ⟨f (b + 1), hb'⟩ from
        hf b).reachable
  rcases le_total m n with h | h
  · exact key m n h fun t h1 h2 => hA t (Or.inl ⟨h1, h2⟩)
  · exact (key n m h fun t h1 h2 => hA t (Or.inr ⟨h1, h2⟩)).symm

private theorem ray_adj_vertical (a t : ℤ) : (nearestNeighborGraph 2).Adj ![a, t] ![a, t + 1] :=
  show ∃ i : Fin 2, _ = _ + LatticeProb.unit i ∨ _ from
    ⟨1, Or.inl (by funext j; fin_cases j <;> simp [LatticeProb.unit])⟩

private theorem ray_adj_horizontal (t : ℤ) : (nearestNeighborGraph 2).Adj ![t, 0] ![t + 1, 0] :=
  show ∃ i : Fin 2, _ = _ + LatticeProb.unit i ∨ _ from
    ⟨0, Or.inl (by funext j; fin_cases j <;> simp [LatticeProb.unit])⟩

/-- A lattice vector of `ℓ¹`-norm one is a signed unit vector. -/
private theorem exists_unit_of_l1_eq_one {w : Vertex 2} (hw : l1 w = 1) :
    ∃ i : Fin 2, w = LatticeProb.unit i ∨ -w = LatticeProb.unit i := by
  have h : |w 0| + |w 1| = 1 := by
    have : ((|w 0| + |w 1| : ℤ) : ℝ) = 1 := by
      simpa [l1, Fin.sum_univ_two] using hw
    exact_mod_cast this
  have h0 : w 0 = 1 ∧ w 1 = 0 ∨ w 0 = -1 ∧ w 1 = 0 ∨ w 0 = 0 ∧ w 1 = 1 ∨
      w 0 = 0 ∧ w 1 = -1 := by
    rcases abs_cases (w 0) with ⟨a, _⟩ | ⟨a, _⟩ <;> rcases abs_cases (w 1) with ⟨b, _⟩ | ⟨b, _⟩ <;>
      omega
  rcases h0 with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
  · exact ⟨0, Or.inl (by funext j; fin_cases j <;> simp [LatticeProb.unit, a, b])⟩
  · exact ⟨0, Or.inr (by funext j; fin_cases j <;> simp [LatticeProb.unit, a, b])⟩
  · exact ⟨1, Or.inl (by funext j; fin_cases j <;> simp [LatticeProb.unit, a, b])⟩
  · exact ⟨1, Or.inr (by funext j; fin_cases j <;> simp [LatticeProb.unit, a, b])⟩

/-- Consecutive points of the ray are lattice neighbours. -/
private theorem adj_ray {w : Vertex 2} (hw : l1 w = 1) (k : ℕ) :
    (nearestNeighborGraph 2).Adj ((k : ℤ) • w) (((k + 1 : ℕ) : ℤ) • w) := by
  obtain ⟨i, h | h⟩ := exists_unit_of_l1_eq_one hw
  · refine ⟨i, Or.inl ?_⟩
    rw [h]
    simp [add_smul]
  · refine ⟨i, Or.inr ?_⟩
    have : w = -LatticeProb.unit i := by rw [← h]; simp
    rw [this]
    simp [add_smul]

/-- Inside every `A ⊇ Q_r ∪ {k w}`, each point of `Q_r` is joined to each point of the ray. -/
private theorem rayJoined_cube_latticeRay {A : Set (Vertex 2)} {r : ℕ} {w : Vertex 2}
    (hw : l1 w = 1) (hA : cube r ∪ latticeRay w ⊆ A) {x y : Vertex 2} (hx : x ∈ cube r)
    (hy : y ∈ latticeRay w) : RayJoined A x y := by
  obtain ⟨hx0l, hx0r⟩ := abs_le.1 (hx 0)
  obtain ⟨hx1l, hx1r⟩ := abs_le.1 (hx 1)
  obtain ⟨k, rfl⟩ := hy
  have ex : x = ![x 0, x 1] := by funext j; fin_cases j <;> rfl
  have hv : RayJoined A ![x 0, x 1] ![x 0, 0] :=
    rayJoined_of_line (fun t => ![x 0, t]) (ray_adj_vertical (x 0)) fun t ht => hA <| Or.inl <| by
      intro i
      fin_cases i
      · exact hx 0
      · exact abs_le.2 (by simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
                           constructor <;> omega)
  have hh : RayJoined A ![x 0, 0] ![0, 0] :=
    rayJoined_of_line (fun t => ![t, 0]) ray_adj_horizontal fun t ht => hA <| Or.inl <| by
      intro i
      fin_cases i
      · exact abs_le.2 (by simp only [Fin.zero_eta, Matrix.cons_val_zero]
                           constructor <;> omega)
      · simp
  have h0 : (![0, 0] : Vertex 2) = ((0 : ℕ) : ℤ) • w := by
    funext j; fin_cases j <;> simp
  have hray : ∀ n : ℕ, RayJoined A (((0 : ℕ) : ℤ) • w) ((n : ℤ) • w) := by
    intro n
    induction n with
    | zero =>
      have hm : ((0 : ℕ) : ℤ) • w ∈ A := hA (Or.inr ⟨0, rfl⟩)
      exact ⟨hm, hm, .refl _⟩
    | succ n ih =>
      refine ih.trans ⟨hA (Or.inr ⟨n, rfl⟩), hA (Or.inr ⟨n + 1, rfl⟩), ?_⟩
      exact (show ((nearestNeighborGraph 2).induce A).Adj ⟨_, hA (Or.inr ⟨n, rfl⟩)⟩
        ⟨_, hA (Or.inr ⟨n + 1, rfl⟩)⟩ from adj_ray hw n).reachable
  rw [ex]
  exact hv.trans (hh.trans (h0 ▸ hray k))

/-- `explorationHolesStep` with `L_-` replaced by a lattice half-line `{k w}`, `|w|₁ = 1`. -/
theorem explorationHolesRayStep : ExplorationHolesRayStep := by
  intro w hw ω C f r u ℓ x₀ x₁ hf h01 hlow S hS T hT hTfin x hxT
  by_contra hfx
  have hA : cube r ∪ latticeRay w ⊆ (Subtype.val '' S)ᶜ := by
    rintro z hz ⟨y, hyS, rfl⟩
    have h1 := le_of_mem_explorationSet C (hS hyS)
    have h2 := hlow y hz
    linarith
  obtain ⟨x', -, rfl⟩ := hT
  have hxj : RayJoined (Subtype.val '' S)ᶜ x' x := hxT
  have hsub : latticeRay w ⊆ {y | RayJoined (Subtype.val '' S)ᶜ x' y} := fun y hy =>
    hxj.trans (rayJoined_cube_latticeRay hw hA (hf x hfx) hy)
  have hwne : w ≠ 0 := by
    rintro rfl
    simp [l1] at hw
  have hinf : (latticeRay w).Infinite :=
    Set.infinite_of_injective_forall_mem (f := fun k : ℕ => ((k : ℤ) • w : Vertex 2))
      (fun k k' hkk' => by
        obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := by
          by_contra! hall
          exact hwne (funext hall)
        have := congrFun hkk' j
        simp only [Pi.smul_apply, smul_eq_mul] at this
        exact_mod_cast mul_right_cancel₀ hj this)
      fun k => ⟨k, rfl⟩
  exact hinf.mono hsub hTfin

end HarmonicSteps

/-! ### Lemma 5.27 at slope `q`: the minimal scale and the glue

`largeGradientSensitiveAt_of_steps`: Lemma 5.27 at slope `q` from Lemma 5.25 at slope `q`
(`GoodEventPositiveAtStmt`), Lemma 5.28 for `ℓ ∈ 𝒜₁`, the minimal scale on the cone and the steps;
`C_χ = max(1, 32 Λ (2W + 1) e^{C_branches} / c₁)` (`= 128 (2W + 1) e^{C_branches} / c₁` at `Λ = 4`). -/

section SlopeGlue

open Rigidity.External Classical

/-- A unit lattice vector along which `q · x` decreases, for `q ≠ 0`. -/
theorem exists_descentDirection {q : Fin 2 → ℝ} (hq : q ≠ 0) :
    ∃ w : Vertex 2, l1 w = 1 ∧ slopeDot q w < 0 := by
  have hl1 : ∀ w : Vertex 2, l1 w = |(w 0 : ℝ)| + |(w 1 : ℝ)| := fun w => by
    simp [l1, Fin.sum_univ_two]
  by_cases h0 : q 0 = 0
  · have h1 : q 1 ≠ 0 := by
      intro h1
      exact hq (funext fun i => by fin_cases i <;> simp [h0, h1])
    rcases lt_or_gt_of_ne h1 with h | h
    · refine ⟨Pi.single 1 1, ?_, ?_⟩
      · rw [hl1]; simp
      · simp [slopeDot, h0, h]
    · refine ⟨Pi.single 1 (-1), ?_, ?_⟩
      · rw [hl1]; simp
      · simp [slopeDot, h0, h]
  · rcases lt_or_gt_of_ne h0 with h | h
    · refine ⟨Pi.single 0 1, ?_, ?_⟩
      · rw [hl1]; simp
      · simp [slopeDot, h]
    · refine ⟨Pi.single 0 (-1), ?_, ?_⟩
      · rw [hl1]; simp
      · simp [slopeDot, h]

/-- `exists_sensitiveEdge_of_explorationConclusion` with the oscillation bound `Λ R'` in `G_2`
(`Λ > 0`) in place of `4 R'`, and the numeric hypothesis `8 Λ (2 W + 1) ≤ i c₁` in place of
`32 (2 W + 1) ≤ i c₁`. -/
theorem exists_sensitiveEdge_of_explorationConclusion_at {ω : Configuration 2}
    {h : HasUniqueInfiniteOpenComponent ω} {u ℓ : uniqueInfiniteComponent h → ℝ} {x₀ : Vertex 2}
    {X₀ X₁ : uniqueInfiniteComponent h} {Cf W : ℕ} {R c₁ Λ K₀ C₀ i : ℝ} (hX₀ : X₀.val = x₀)
    (h01 : ℓ X₀ < ℓ X₁) (hc₁ : 0 < c₁) (hΛ : 0 < Λ) (hi : 8 * Λ * (2 * W + 1) ≤ i * c₁)
    (hK₀ : K₀ ≤ C₀) (hW : (W : ℝ) + 1 ≤ C₀) (h2 : 2 ≤ C₀)
    (hE : ExplorationConclusion _ u ℓ X₀ X₁ i)
    (hwin : ∀ (n : ℕ) (γ : Fin (n + 1) → uniqueInfiniteComponent h),
      IsExplorationPath _ u ℓ X₀ X₁ γ → (W : ℝ) + 1 ≤ l1 ((γ (Fin.last n)).val - X₀.val) →
      (goodCount ω Cf R γ : ℝ) ≤ (2 * W + 1) * separatorCount _ u ℓ X₀ X₁ γ)
    (hG1 : ∀ (n : ℕ) (γ : Fin (n + 1) → uniqueInfiniteComponent h), IsPathOf _ γ →
      (γ 0).val = x₀ → K₀ ≤ l1 ((γ (Fin.last n)).val - x₀) →
      c₁ * l1 ((γ (Fin.last n)).val - x₀) ≤ (goodCount ω Cf R γ : ℝ))
    (hG2 : ∀ R' : ℕ, K₀ ≤ R' → ∀ y z : uniqueInfiniteComponent h, y.val ∈ Rigidity.Section5.cubeAt x₀ R' →
      z.val ∈ Rigidity.Section5.cubeAt x₀ R' → ℓ y - ℓ z ≤ Λ * R') :
    ∃ a b : uniqueInfiniteComponent h, (componentGraph _).Adj a b ∧ l1 (a.val - x₀) ≤ C₀ ∧
      ℓ a ≠ ℓ b ∧ u a ≠ u b := by
  obtain ⟨E, hEG, hEi, hEii⟩ := hE
  have hnear : ∀ y ∈ E, l1 (y.val - x₀) < C₀ := by
    intro y hy
    by_contra hfar
    replace hfar := not_lt.1 hfar
    obtain ⟨n, hn, γ, hadj, hlev, h0, h1, hlast, hinc⟩ := hEG hy
    have hγ : IsExplorationPath _ u ℓ X₀ X₁ γ := ⟨hn, hadj, hlev, h0, h1, hinc⟩
    have hinj : Function.Injective γ := (hγ.strictMono h01).injective.of_comp
    have hD := l1_nonneg (y.val - x₀)
    have hg1 := hG1 n γ ⟨hinj, hadj⟩ (by rw [h0, hX₀]) (by rw [hlast]; linarith)
    have hw := hwin n γ hγ (by rw [hlast, hX₀]; linarith)
    have hgr := hEi y hy n γ hγ hlast
    rw [hlast] at hg1
    have hDR : l1 (y.val - x₀) ≤ (⌈l1 (y.val - x₀)⌉₊ : ℝ) := Nat.le_ceil _
    have hRD : (⌈l1 (y.val - x₀)⌉₊ : ℝ) < l1 (y.val - x₀) + 1 := Nat.ceil_lt_add_one hD
    have hosc := hG2 ⌈l1 (y.val - x₀)⌉₊ (by linarith) y X₀ (mem_cubeAt_of_l1_le hDR)
      (by rw [hX₀]; intro j; simp)
    have hs0 : (0 : ℝ) ≤ separatorCount _ u ℓ X₀ X₁ γ := Nat.cast_nonneg _
    have hprod := mul_le_mul_of_nonneg_right hi hs0
    have hΛ2 : (0 : ℝ) ≤ 2 * Λ := by positivity
    have k1 := mul_le_mul_of_nonneg_left hg1 hΛ2
    have k2 := mul_le_mul_of_nonneg_left hw hΛ2
    have key : c₁ * (2 * Λ * l1 (y.val - x₀)) ≤ c₁ * (i / 4 * separatorCount _ u ℓ X₀ X₁ γ) := by
      nlinarith
    have key' := le_of_mul_le_mul_left key hc₁
    have hΛR : Λ * (⌈l1 (y.val - x₀)⌉₊ : ℝ) ≤ Λ * (l1 (y.val - x₀) + 1) :=
      mul_le_mul_of_nonneg_left hRD.le hΛ.le
    nlinarith
  rcases hEii with ⟨y, hy, z, hadj, hℓ, hu⟩ | hunb
  · exact ⟨y, z, hadj, (hnear y hy).le, hℓ, hu⟩
  · obtain ⟨y, hy, hD⟩ := hunb C₀
    rw [hX₀] at hD
    exact absurd (hnear y hy) (not_lt.2 hD)

/-- Steps 1-6 of Lemma 5.27 at slope `q` on one cluster: the initial edge is `(x₀, x₀ + v)`,
`|v|₁ = 1`, the plane `ℓ` is a corrected plane of slope `q` (only `ℓ ∈ 𝒜₁` is used by the
exploration steps), the exploration is started above the cube and the lattice ray `{k w}`,
`|w|₁ = 1`, and `G_2` has constant `Λ`. -/
theorem exists_sensitiveEdge_at_of_steps {ω : Configuration 2}
    {h : HasUniqueInfiniteOpenComponent ω}
    (hB : ExplorationBlockStep) (hH : ExplorationHolesRayStep) (hR : RootBlockHarmonicStep)
    (hL : LeafSensitiveHarmonicStep) (hF : FluxBalanceHarmonicStep) (hG : FluxGrowthStep)
    (hX : GreedyExplorationStep) (hA : ExplorationAssemblyStep) (hT : TerminationWindowStep)
    {f : Vertex 2 → ℤ} {r Cf Cbr W : ℕ} {R c₁ Cχ K₀ C₀ Λ : ℝ}
    {u ℓ : uniqueInfiniteComponent h → ℝ} {q : Fin 2 → ℝ}
    {x₀ v w : Vertex 2} {X₀ X₁ : uniqueInfiniteComponent h} (hf : ∀ x, f x ≠ 0 → x ∈ cube r)
    (hR1 : 1 ≤ R) (hRW : 4 * R ^ 2 ≤ W) (hc₁ : 0 < c₁) (hCχ : 0 < Cχ) (hΛ : 0 < Λ)
    (hχ : 32 * Λ * (2 * W + 1) * Real.exp Cbr ≤ Cχ * c₁) (hK₀ : K₀ ≤ C₀) (hW : (W : ℝ) + 1 ≤ C₀)
    (h2 : 2 ≤ C₀) (hℓ : IsCorrectedPlane _ q ℓ) (hX₀ : X₀.val = x₀)
    (hX₁ : X₁.val = x₀ + v) (hv : l1 v = 1) (hw : l1 w = 1) (hadj : (componentGraph _).Adj X₀ X₁)
    (hΔ : Cχ ≤ ℓ X₁ - ℓ X₀) (hu01 : u X₁ = u X₀) (hMh : ∀ y : uniqueInfiniteComponent h,
      (y.val ∈ cube r ∨ y.val ∈ latticeRay w) → ℓ y < ℓ X₀)
    (h520 : ∀ S ⊆ levelSet u (u X₀), IsBiconnected _ S →
      (∀ T, IsLatticeComponentOf (Subtype.val '' S)ᶜ T → T.Finite → ∀ x ∈ T, f x = 0) →
      ¬ HasDisjointPathsToInfinity _ S (Cf + 1))
    (h528 : ∀ B₀ : ExplorationBlock _ u ℓ X₀ X₁, X₁ ∈ B₀.val →
      ∀ (n : ℕ) (b : Fin n → Set (PrunedVertex _ u ℓ X₀ X₁ B₀)),
        (∀ k, IsPrunedBranch _ u ℓ X₀ X₁ B₀ (b k)) → Function.Injective b → n ≤ Cbr)
    (hG1 : ∀ (n : ℕ) (γ : Fin (n + 1) → uniqueInfiniteComponent h), IsPathOf _ γ →
      (γ 0).val = x₀ → K₀ ≤ l1 ((γ (Fin.last n)).val - x₀) →
      c₁ * l1 ((γ (Fin.last n)).val - x₀) ≤ (goodCount ω Cf R γ : ℝ))
    (hG2 : ∀ R' : ℕ, K₀ ≤ R' → ∀ y z : uniqueInfiniteComponent h,
      y.val ∈ Rigidity.Section5.cubeAt x₀ R' →
      z.val ∈ Rigidity.Section5.cubeAt x₀ R' → ℓ y - ℓ z ≤ Λ * R') :
    ∃ a b : uniqueInfiniteComponent h, (componentGraph _).Adj a b ∧ l1 (a.val - x₀) ≤ C₀ ∧
      ℓ a ≠ ℓ b ∧ u a ≠ u b := by
  have h01 : ℓ X₀ < ℓ X₁ := by linarith
  have holes := hH w hw ω _ f r u ℓ X₀ X₁ hf h01 hMh
  have hfew : ∀ S, IsBlock _ (explorationGraph _ u ℓ X₀ X₁) (explorationSet _ u ℓ X₀ X₁) S →
      ¬ HasDisjointPathsToInfinity _ S (Cf + 1) := fun S hS =>
    h520 S (hB ω _ u ℓ X₀ X₁ S hS).1 (hB ω _ u ℓ X₀ X₁ S hS).2 (holes S hS.1.1)
  rcases hR ω _ u ℓ hℓ.1 X₀ X₁ hadj hu01 Cχ hCχ hΔ with ⟨z, hz⟩ | ⟨B₀, hB₀, hflux⟩
  · refine ⟨X₁, z, hz.1, ?_, hz.2.1, hz.2.2⟩
    rw [hX₁, add_sub_cancel_left, hv]
    linarith
  have hgreedy := hX ω _ u ℓ X₀ X₁ hadj h01 hu01 B₀ hB₀ Cbr (Cχ / 4) (by positivity) hflux
    (hF ω _ u ℓ hℓ.1 X₀ X₁ hadj h01 hu01 B₀ hB₀) (h528 B₀ hB₀)
  have hconc := hA ω _ u ℓ X₀ X₁ hadj h01 hu01 B₀ hB₀ _ hgreedy
    (hG ω _ u ℓ X₀ X₁ hadj h01 hu01 B₀ hB₀) (hL ω _ u ℓ hℓ.1 X₀ X₁ hadj h01 hu01 B₀ hB₀)
  have he : Real.exp (Cbr : ℝ) * Real.exp (-(Cbr : ℝ)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hi : 8 * Λ * (2 * W + 1) ≤ Cχ / 4 * Real.exp (-(Cbr : ℝ)) * c₁ := by
    have h1 := mul_le_mul_of_nonneg_right hχ (Real.exp_pos (-(Cbr : ℝ))).le
    have h2 : 32 * Λ * (2 * W + 1) * Real.exp Cbr * Real.exp (-(Cbr : ℝ)) =
        32 * Λ * (2 * W + 1) := by
      rw [mul_assoc _ (Real.exp (Cbr : ℝ)), he, mul_one]
    linarith
  exact exists_sensitiveEdge_of_explorationConclusion_at hX₀ h01 hc₁ hΛ hi hK₀ hW h2 hconc
    (hT ω h u ℓ X₀ X₁ Cf R W h01 hR1 hRW hfew) hG1 hG2

/-- Lemma 5.27 at slope `q ≠ 0` from Lemma 5.25 at slope `q` with constant `Λ`, Lemma 5.28 for
`ℓ ∈ 𝒜₁` and the proved steps of the carving of Lemma 5.27. Constants: `R = max R₁ 1`,
`W = ⌈4 R²⌉`, `C_χ = max 1 (32 Λ (2 W + 1) e^{C_br} / c₁)`, `C₀ = max (max K₀ (W + 1)) 2`; the
minimal scale is `hM` at the ray `w` (`|w|₁ = 1`, `q · w < 0`) and the cube `Q_{C_f / 2}`. -/
theorem largeGradientSensitiveAt_of_steps {p : unitInterval} {f : Vertex 2 → ℤ}
    {q : Fin 2 → ℝ} {Λ : ℝ} (hq : q ≠ 0) (hΛ : 0 < Λ)
    (hQ : CorrectorQuantitativeInput) (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (h520 : BoundarySizeStmt p f) (h524 : LongPathRenormalizedStmt p)
    (h525 : GoodEventPositiveAtStmt p q Λ) (h528 : FiniteBranchesHarmonicStmt p f)
    (hM : CorrectedPlaneMinimalScaleAtStep) (hB : ExplorationBlockStep)
    (hH : ExplorationHolesRayStep) (hR : RootBlockHarmonicStep) (hL : LeafSensitiveHarmonicStep)
    (hF : FluxBalanceHarmonicStep) (hG : FluxGrowthStep) (hX : GreedyExplorationStep)
    (hA : ExplorationAssemblyStep) (hT : TerminationWindowStep) :
    LargeGradientSensitiveAtStmt p f q := by
  intro hfin
  obtain ⟨Cf, hCf, h520ae⟩ := h520 hfin
  obtain ⟨Cbr, h528ae⟩ := h528 hfin
  obtain ⟨R₁, hR₁⟩ := h524 Cf
  obtain ⟨c₁, hc₁, hLP⟩ := hR₁ (max R₁ 1) (le_max_left _ _)
  set R := max R₁ 1 with hR_def
  set W := ⌈4 * R ^ 2⌉₊ with hW_def
  set Cχ := max 1 (32 * Λ * (2 * W + 1) * Real.exp Cbr / c₁) with hCχ_def
  obtain ⟨v, hv, h25⟩ := h525
  obtain ⟨K₀, hK₀⟩ := h25 Cχ (le_max_left _ _) Cf R c₁ hLP
  set C₀ := max (max K₀ (W + 1)) 2 with hC₀_def
  obtain ⟨w, hw1, hwq⟩ := exists_descentDirection hq
  refine ⟨Cf, R, c₁, Λ, Cχ, K₀, C₀, v, hK₀ K₀ le_rfl, ?_⟩
  intro κ hκ
  filter_upwards [hM hQ p hpc hp1 q w hwq κ hκ (Cf / 2), h528ae, h520ae] with ω hMω h528ω h520ω
  obtain ⟨h, h528c⟩ := h528ω
  obtain ⟨M₁, hM₁⟩ := hMω h
  obtain ⟨_, h520c⟩ := h520ω
  refine ⟨h, M₁, fun u hu hsupp ℓ hℓ x₀ hcone hMx hGω => ?_⟩
  obtain ⟨⟨⟨_, hG1⟩, ⟨_, hG2⟩⟩, ⟨_, hx, hx', hadj, hΔ⟩⟩ := hGω
  set X₀ : uniqueInfiniteComponent h := ⟨x₀, hx⟩
  set X₁ : uniqueInfiniteComponent h := ⟨x₀ + v, hx'⟩
  have hΔ' : Cχ ≤ ℓ X₁ - ℓ X₀ := hΔ ℓ hℓ
  have hCχ1 : 1 ≤ Cχ := le_max_left _ _
  by_cases hu01 : u X₁ = u X₀
  · have hχ : 32 * Λ * (2 * W + 1) * Real.exp Cbr ≤ Cχ * c₁ :=
      (div_le_iff₀ hc₁).1 (le_max_right _ _)
    exact exists_sensitiveEdge_at_of_steps hB hH hR hL hF hG hX hA hT hCf
      (le_max_right _ _) (Nat.le_ceil _) hc₁ (by linarith) hΛ hχ
      ((le_max_left _ _).trans (le_max_left _ _)) ((le_max_right _ _).trans (le_max_left _ _))
      (le_max_right _ _) hℓ rfl rfl hv hw1 hadj hΔ' hu01
      (fun y hy => hM₁ ℓ hℓ X₀ y hcone hMx hy)
      (h520c u hu hsupp (u X₀))
      (h528c u hu hsupp ℓ hℓ.1 X₀ X₁ hadj (by linarith) hu01)
      hG1 (hG2 ℓ hℓ)
  · refine ⟨X₀, X₁, hadj, ?_, ?_, fun e => hu01 e.symm⟩
    · simp only [X₀, sub_self]
      have : l1 0 = 0 := by simp [l1]
      rw [this]
      exact (zero_le_two).trans (le_max_right _ _)
    · intro e
      linarith

/-! ### The minimal scale of the corrected plane at slope `q` -/

/-- The Euclidean norm of a vertex of `ℤ²` is at most its `ℓ¹` norm. -/
private theorem norm_latticeEuclideanEmbedding_le_abs_add_abs' (v : Vertex 2) :
    ‖latticeEuclideanEmbedding v‖ ≤ |(v 0 : ℝ)| + |(v 1 : ℝ)| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  have h0 : ‖latticeEuclideanEmbedding v 0‖ = |(v 0 : ℝ)| := Real.norm_eq_abs _
  have h1 : ‖latticeEuclideanEmbedding v 1‖ = |(v 1 : ℝ)| := Real.norm_eq_abs _
  rw [h0, h1, Real.sqrt_le_left (by positivity)]
  nlinarith [mul_nonneg (abs_nonneg (v 0 : ℝ)) (abs_nonneg (v 1 : ℝ))]

/-- Every vertex of an infinite open component has a neighbour in it. -/
private theorem exists_adj_of_supp_infinite' {ω : Configuration 2} {C : OpenComponent ω}
    (hC : C.supp.Infinite) (y : C) : ∃ y' : C, (componentGraph C).Adj y y' := by
  obtain ⟨w, hw, hwy⟩ := hC.nontrivial.exists_ne y.val
  have hreach : (openGraph ω).Reachable y.val w :=
    SimpleGraph.ConnectedComponent.exact
      (((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 y.2).trans
        ((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 hw).symm)
  obtain ⟨q⟩ := hreach
  cases q with
  | nil => exact absurd rfl hwy
  | @cons _ v _ hadj _ =>
    have hv : v ∈ C.supp := C.mem_supp_of_adj_mem_supp y.2 hadj
    exact ⟨⟨v, hv⟩, (C.toSimpleGraph_adj y.2 hv).2 hadj⟩

/-- The coordinates of neighbours in `𝒞_∞` differ by at most one. -/
private theorem abs_coord_le_of_adj' {ω : Configuration 2} {C : OpenComponent ω} {a b : C}
    (hab : (componentGraph C).Adj a b) (j : Fin 2) :
    |(b.val j : ℝ)| ≤ |(a.val j : ℝ)| + 1 := by
  have hu : ∀ i : Fin 2, |((LatticeProb.unit i : Vertex 2) j : ℝ)| ≤ 1 := by
    intro i
    simp only [LatticeProb.unit, Pi.single_apply]
    split_ifs <;> simp
  obtain ⟨i, hi | hi⟩ := openGraph_le ω ((C.toSimpleGraph_adj a.2 b.2).1 hab)
  · have hb : (b.val j : ℝ) = (a.val j : ℝ) + ((LatticeProb.unit i : Vertex 2) j : ℝ) := by
      rw [hi]; push_cast [Pi.add_apply]; ring
    rw [hb]
    exact (abs_add_le _ _).trans (by linarith [hu i])
  · have hb : (b.val j : ℝ) = (a.val j : ℝ) - ((LatticeProb.unit i : Vertex 2) j : ℝ) := by
      rw [hi]; push_cast [Pi.add_apply]; ring
    rw [hb]
    exact (abs_sub _ _).trans (by linarith [hu i])

/-- `K √ρ ≤ ε ρ + K² / (4 ε)` for `ρ ≥ 0`, `ε > 0`. -/
private theorem mul_rpow_half_le_add_div {K ρ ε : ℝ} (hρ : 0 ≤ ρ) (hε : 0 < ε) :
    K * ρ ^ (1 / 2 : ℝ) ≤ ε * ρ + K ^ 2 / (4 * ε) := by
  obtain ⟨t, ht0, rfl⟩ : ∃ t : ℝ, 0 ≤ t ∧ ρ = t ^ 2 := ⟨Real.sqrt ρ, Real.sqrt_nonneg _,
    (Real.sq_sqrt hρ).symm⟩
  rw [← Real.sqrt_eq_rpow, Real.sqrt_sq ht0]
  have h4 : 0 < 4 * ε := by positivity
  have : K * t - ε * t ^ 2 ≤ K ^ 2 / (4 * ε) := by
    rw [le_div_iff₀ h4]
    nlinarith [sq_nonneg (2 * ε * t - K)]
  linarith

/-- **step:5.27-Mh at slope `q`** (eq. `def-Mh`, L2457-2462): the proof of
`correctedPlaneMinimalScaleStep` with the cone `κ |x|₁ ≤ q · x` and the lattice ray `{k w}`,
`q · w < 0`. With `A = C |q|₁` (`C` from Theorem 2.5 with `α = 1/2`) and
`ε = min (κ / 2) (-(q · w) / (|w|₁ + 1))`, the scale is
`M = (2 / κ) (|q|₁ r + ε (2 r + M₀ + 3) + A² / (4 ε)) + 1`. -/
theorem correctedPlaneMinimalScaleAtStep : CorrectedPlaneMinimalScaleAtStep := by
  intro hQ p hpc hp1 q w hqw κ hκ r
  obtain ⟨s, K, -, -, hM⟩ := hQ 2 le_rfl p hpc hp1 (1 / 2) one_half_pos
  obtain ⟨M₀, -, hM₀, -, hae⟩ := hM 0
  filter_upwards [hae] with ω hω h
  have hl1 : ∀ v : Vertex 2, l1 v = |(v 0 : ℝ)| + |(v 1 : ℝ)| := fun v => by
    simp [l1, Fin.sum_univ_two]
  set Q : ℝ := |q 0| + |q 1| with hQdef
  have hQ0 : 0 ≤ Q := by positivity
  set A : ℝ := K * Q with hAdef
  set a : ℝ := -(slopeDot q w) with hadef
  have ha : 0 < a := by linarith
  set Wn : ℝ := |(w 0 : ℝ)| + |(w 1 : ℝ)| with hWn
  have hWn0 : 0 ≤ Wn := by positivity
  set ε : ℝ := min (κ / 2) (a / (Wn + 1)) with hεdef
  have hε : 0 < ε := lt_min (by linarith) (by positivity)
  have hε1 : ε ≤ κ / 2 := min_le_left _ _
  have hε2 : ε * Wn ≤ a := by
    have h1 : ε ≤ a / (Wn + 1) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  set T : ℝ := Q * r + ε * (2 * r + M₀ ω + 3) + A ^ 2 / (4 * ε) with hT
  have hM₀ω := hM₀ ω
  have hr : (0 : ℝ) ≤ r := r.cast_nonneg
  have hT0 : 0 ≤ T := by
    have : 0 ≤ A ^ 2 / (4 * ε) := by positivity
    have : 0 ≤ ε * (2 * r + M₀ ω + 3) := by positivity
    have : 0 ≤ Q * r := by positivity
    linarith
  refine ⟨2 / κ * T + 1, fun ℓ hℓ x y hcone hx hy => ?_⟩
  obtain ⟨x', hxx'⟩ := exists_adj_of_supp_infinite' (uniqueInfiniteComponent_infinite h) x
  have e0 : latticeEuclideanEmbedding (0 : Vertex 2) = 0 := by
    ext i
    change ((0 : ℤ) : ℝ) = 0
    simp
  set ρ : ℝ := (|(x.val 0 : ℝ)| + |(x.val 1 : ℝ)|) + (|(y.val 0 : ℝ)| + |(y.val 1 : ℝ)|) +
    M₀ ω + 3 with hρ
  have hax := abs_nonneg (x.val 0 : ℝ)
  have hbx := abs_nonneg (x.val 1 : ℝ)
  have hay := abs_nonneg (y.val 0 : ℝ)
  have hby := abs_nonneg (y.val 1 : ℝ)
  have hball : ∀ v : Vertex 2, |(v 0 : ℝ)| + |(v 1 : ℝ)| < ρ →
      ‖latticeEuclideanEmbedding v - latticeEuclideanEmbedding 0‖ < ρ := fun v hv => by
    rw [e0, sub_zero]
    exact (norm_latticeEuclideanEmbedding_le_abs_add_abs' v).trans_lt hv
  have hx'0 := abs_coord_le_of_adj' hxx' 0
  have hx'1 := abs_coord_le_of_adj' hxx' 1
  have key := hω h q ℓ hℓ ρ (by linarith) x y x x'
    (hball _ (by linarith)) (hball _ (by linarith)) (hball _ (by linarith))
    (hball _ (by linarith)) hxx'
  simp only [Fin.sum_univ_two] at key
  rw [← hQdef, ← hAdef] at key
  have hosc := (abs_le.1 (le_trans (le_add_of_nonneg_right (abs_nonneg _)) key)).1
  have hsq := mul_rpow_half_le_add_div (K := A) (ε := ε) (by linarith : (0 : ℝ) ≤ ρ) hε
  have hcone' : κ * (|(x.val 0 : ℝ)| + |(x.val 1 : ℝ)|) ≤
      q 0 * (x.val 0 : ℝ) + q 1 * (x.val 1 : ℝ) := by
    have := hcone
    rwa [hl1, slopeDot] at this
  have hx' : 2 / κ * T + 1 ≤ |(x.val 0 : ℝ)| + |(x.val 1 : ℝ)| := by
    have := hx
    rwa [hl1] at this
  have hXT : T + κ / 2 ≤ κ / 2 * (|(x.val 0 : ℝ)| + |(x.val 1 : ℝ)|) := by
    have := mul_le_mul_of_nonneg_left hx' (by linarith : 0 ≤ κ / 2)
    have e : κ / 2 * (2 / κ * T + 1) = T + κ / 2 := by field_simp
    linarith
  have hεX := mul_le_mul_of_nonneg_right hε1 (by positivity :
    0 ≤ |(x.val 0 : ℝ)| + |(x.val 1 : ℝ)|)
  have hερ : ε * ρ = ε * (|(x.val 0 : ℝ)| + |(x.val 1 : ℝ)|) +
      ε * (|(y.val 0 : ℝ)| + |(y.val 1 : ℝ)|) + ε * (M₀ ω + 3) := by rw [hρ]; ring
  have hfin : (q 0 * (x.val 0 : ℝ) + q 1 * (x.val 1 : ℝ)) -
      (q 0 * (y.val 0 : ℝ) + q 1 * (y.val 1 : ℝ)) - ε * ρ - A ^ 2 / (4 * ε) ≤ ℓ x - ℓ y := by
    linarith
  rcases hy with hy | ⟨k, hk⟩
  · have hy0 : |(y.val 0 : ℝ)| ≤ r := by exact_mod_cast hy 0
    have hy1 : |(y.val 1 : ℝ)| ≤ r := by exact_mod_cast hy 1
    have hq0 : q 0 * (y.val 0 : ℝ) ≤ |q 0| * r :=
      (le_abs_self _).trans (by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left hy0 (abs_nonneg _))
    have hq1 : q 1 * (y.val 1 : ℝ) ≤ |q 1| * r :=
      (le_abs_self _).trans (by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left hy1 (abs_nonneg _))
    have hεY := mul_le_mul_of_nonneg_left (by linarith : |(y.val 0 : ℝ)| + |(y.val 1 : ℝ)| ≤ 2 * r)
      hε.le
    have hQr : Q * r = |q 0| * r + |q 1| * r := by rw [hQdef]; ring
    simp only [hT] at hXT
    have hε2r : ε * (2 * r + M₀ ω + 3) = ε * (2 * r) + ε * (M₀ ω + 3) := by ring
    linarith
  · have hk0 : (y.val 0 : ℝ) = k * (w 0 : ℝ) := by rw [hk]; simp
    have hk1 : (y.val 1 : ℝ) = k * (w 1 : ℝ) := by rw [hk]; simp
    have hkn : (0 : ℝ) ≤ k := k.cast_nonneg
    have hYk : |(y.val 0 : ℝ)| + |(y.val 1 : ℝ)| = k * Wn := by
      rw [hk0, hk1, abs_mul, abs_mul, abs_of_nonneg hkn, hWn]; ring
    have hqy : q 0 * (y.val 0 : ℝ) + q 1 * (y.val 1 : ℝ) = -(k * a) := by
      rw [hk0, hk1, hadef, slopeDot]; ring
    have hεk := mul_le_mul_of_nonneg_left hε2 hkn
    have hεY : ε * (|(y.val 0 : ℝ)| + |(y.val 1 : ℝ)|) ≤ k * a := by
      rw [hYk]; linarith
    simp only [hT] at hXT
    have hεr : 0 ≤ ε * (2 * r) := by positivity
    have hQr : 0 ≤ Q * r := by positivity
    have hε2r : ε * (2 * r + M₀ ω + 3) = ε * (2 * r) + ε * (M₀ ω + 3) := by ring
    linarith

end SlopeGlue

/-! ### Proposition 5.11 at every slope -/

open LatticeProb.External Rigidity.External in
/-- Eq. `PG2goesto1` at slope `q` (step, same proof as `secondGoodEventStep`, Theorem 2.5 being
stated for every slope): for some `Λ > 0`, `G_2^q(0, K)` fails with outer probability at most
`C exp(-c K^s)`. -/
def SecondGoodEventAtStep : Prop :=
  SupercriticalBondUniqueness → CorrectorQuantitativeInput → ∀ p : unitInterval,
    criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 → ∀ q : Fin 2 → ℝ, ∃ Λ : ℝ, 0 < Λ ∧
    ∃ C c s : ℝ, 0 < C ∧ 0 < c ∧ 0 < s ∧ ∀ K : ℝ, 1 ≤ K →
      latticeBondLaw 2 p (eventG2At q Λ 0 K)ᶜ ≤ ENNReal.ofReal (C * Real.exp (-(c * K ^ s)))

section SecondGoodEventAt

open Rigidity.External LatticeProb.External Rigidity.Proofs.Section5 Classical

/-- The second good event at slope `q` with `Λ = 4 |q|₁ + 1` holds when the cluster is unique, the
conclusion of Theorem 2.5 holds and the minimal scale is at most `5K`, for `K ≥ 2C²`. -/
theorem mem_eventG2At_of_minimalScale_le {C : ℝ} (hC : 0 < C) {x : Vertex 2} {K : ℝ}
    (hK : 2 * C ^ 2 ≤ K) (hK1 : 1 ≤ K) {M : ℝ} {ω : Configuration 2} (q : Fin 2 → ℝ)
    (hω : ∀ h : HasUniqueInfiniteOpenComponent ω,
        ∀ (q : Fin 2 → ℝ) (ℓ : uniqueInfiniteComponent h → ℝ),
          IsCorrectedPlane (uniqueInfiniteComponent h) q ℓ →
        ∀ r : ℝ, M ≤ r →
        ∀ a b a' b' : uniqueInfiniteComponent h,
          ‖latticeEuclideanEmbedding a.val - latticeEuclideanEmbedding x‖ < r →
          ‖latticeEuclideanEmbedding b.val - latticeEuclideanEmbedding x‖ < r →
          ‖latticeEuclideanEmbedding a'.val - latticeEuclideanEmbedding x‖ < r →
          ‖latticeEuclideanEmbedding b'.val - latticeEuclideanEmbedding x‖ < r →
          (componentGraph (uniqueInfiniteComponent h)).Adj a' b' →
          |(ℓ a - ∑ i, q i * a.val i) - (ℓ b - ∑ i, q i * b.val i)| +
              |(ℓ a' - ∑ i, q i * a'.val i) - (ℓ b' - ∑ i, q i * b'.val i)|
            ≤ C * (∑ i, |q i|) * r ^ (1 / 2 : ℝ))
    (hh : HasUniqueInfiniteOpenComponent ω) (hM : M ≤ 5 * K) :
    ω ∈ eventG2At q (4 * (|q 0| + |q 1|) + 1) x K := by
  refine ⟨hh, fun ℓ hℓ R' hR' y z hy hz => ?_⟩
  have hR'1 : (1 : ℝ) ≤ R' := hK1.trans hR'
  obtain ⟨y', hyy'⟩ := exists_adj_of_infinite (uniqueInfiniteComponent_infinite hh) y
  have hy1 := abs_sub_add_abs_sub_eq_one_of_adj hyy'
  have hyb : ∀ i, |((y.val i - x i : ℤ) : ℝ)| ≤ (R' : ℝ) + 1 := fun i =>
    (abs_sub_le_of_mem_cubeAt hy i).trans (by linarith)
  have hzb : ∀ i, |((z.val i - x i : ℤ) : ℝ)| ≤ (R' : ℝ) + 1 := fun i =>
    (abs_sub_le_of_mem_cubeAt hz i).trans (by linarith)
  have hy'b : ∀ i, |((y'.val i - x i : ℤ) : ℝ)| ≤ (R' : ℝ) + 1 := by
    intro i
    have hi : |y.val i - y'.val i| ≤ 1 := by
      fin_cases i
      · exact le_of_le_of_eq (le_add_of_nonneg_right (abs_nonneg _)) hy1
      · exact le_of_le_of_eq (le_add_of_nonneg_left (abs_nonneg _)) hy1
    have hi' : |((y.val i - y'.val i : ℤ) : ℝ)| ≤ 1 := by
      rw [← Int.cast_abs]
      exact_mod_cast hi
    have hyx := abs_sub_le_of_mem_cubeAt hy i
    push_cast at hi' hyx ⊢
    calc |(y'.val i : ℝ) - x i| ≤ |(y'.val i : ℝ) - y.val i| + |(y.val i : ℝ) - x i| :=
          abs_sub_le _ _ _
      _ ≤ 1 + R' := by rw [abs_sub_comm]; exact add_le_add hi' hyx
      _ = R' + 1 := add_comm _ _
  have hosc := hω hh q ℓ hℓ (5 * R') (hM.trans (by linarith)) y z y y'
    (norm_embedding_sub_lt hR'1 hyb) (norm_embedding_sub_lt hR'1 hzb)
    (norm_embedding_sub_lt hR'1 hyb) (norm_embedding_sub_lt hR'1 hy'b) hyy'
  simp only [Fin.sum_univ_two] at hosc
  have hroot := mul_rpow_half_le hC (show 2 * C ^ 2 ≤ (R' : ℝ) by linarith)
  have hS : 0 ≤ |q 0| + |q 1| := by positivity
  have hmul : C * (|q 0| + |q 1|) * (5 * (R' : ℝ)) ^ (1 / 2 : ℝ) ≤ (|q 0| + |q 1|) * (2 * R') := by
    calc C * (|q 0| + |q 1|) * (5 * (R' : ℝ)) ^ (1 / 2 : ℝ)
        = (|q 0| + |q 1|) * (C * (5 * (R' : ℝ)) ^ (1 / 2 : ℝ)) := by ring
      _ ≤ (|q 0| + |q 1|) * (2 * R') := mul_le_mul_of_nonneg_left hroot hS
  have hy0 := abs_sub_le_of_mem_cubeAt hy 0
  have hz0 := abs_sub_le_of_mem_cubeAt hz 0
  have hy1' := abs_sub_le_of_mem_cubeAt hy 1
  have hz1 := abs_sub_le_of_mem_cubeAt hz 1
  push_cast at hy0 hz0 hy1' hz1
  have hd0 : |(y.val 0 : ℝ) - z.val 0| ≤ 2 * R' := by
    calc |(y.val 0 : ℝ) - z.val 0| = |((y.val 0 : ℝ) - x 0) - ((z.val 0 : ℝ) - x 0)| := by ring_nf
      _ ≤ |(y.val 0 : ℝ) - x 0| + |(z.val 0 : ℝ) - x 0| := abs_sub _ _
      _ ≤ 2 * R' := by linarith
  have hd1 : |(y.val 1 : ℝ) - z.val 1| ≤ 2 * R' := by
    calc |(y.val 1 : ℝ) - z.val 1| = |((y.val 1 : ℝ) - x 1) - ((z.val 1 : ℝ) - x 1)| := by ring_nf
      _ ≤ |(y.val 1 : ℝ) - x 1| + |(z.val 1 : ℝ) - x 1| := abs_sub _ _
      _ ≤ 2 * R' := by linarith
  have hq0 : q 0 * (y.val 0 : ℝ) - q 0 * z.val 0 ≤ |q 0| * (2 * R') := by
    calc q 0 * (y.val 0 : ℝ) - q 0 * z.val 0 = q 0 * ((y.val 0 : ℝ) - z.val 0) := by ring
      _ ≤ |q 0 * ((y.val 0 : ℝ) - z.val 0)| := le_abs_self _
      _ = |q 0| * |(y.val 0 : ℝ) - z.val 0| := abs_mul _ _
      _ ≤ |q 0| * (2 * R') := mul_le_mul_of_nonneg_left hd0 (abs_nonneg _)
  have hq1 : q 1 * (y.val 1 : ℝ) - q 1 * z.val 1 ≤ |q 1| * (2 * R') := by
    calc q 1 * (y.val 1 : ℝ) - q 1 * z.val 1 = q 1 * ((y.val 1 : ℝ) - z.val 1) := by ring
      _ ≤ |q 1 * ((y.val 1 : ℝ) - z.val 1)| := le_abs_self _
      _ = |q 1| * |(y.val 1 : ℝ) - z.val 1| := abs_mul _ _
      _ ≤ |q 1| * (2 * R') := mul_le_mul_of_nonneg_left hd1 (abs_nonneg _)
  have h1 := le_abs_self ((ℓ y - (q 0 * (y.val 0 : ℝ) + q 1 * (y.val 1 : ℝ))) -
    (ℓ z - (q 0 * (z.val 0 : ℝ) + q 1 * (z.val 1 : ℝ))))
  have h2 := abs_nonneg ((ℓ y - (q 0 * (y.val 0 : ℝ) + q 1 * (y.val 1 : ℝ))) -
    (ℓ y' - (q 0 * (y'.val 0 : ℝ) + q 1 * (y'.val 1 : ℝ))))
  have hR'0 : (0 : ℝ) ≤ R' := by linarith
  nlinarith [mul_nonneg hS hR'0]

/-- Eq. `PG2goesto1` at slope `q`: under uniqueness of the infinite cluster, the second good event
at slope `q` with `Λ = 4 |q|₁ + 1` fails with probability at most `C exp(-c K^s)`. -/
theorem secondGoodEventAt_bound (hQ : CorrectorQuantitativeInput) {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hUae : UniqueClusterAe p)
    (q : Fin 2 → ℝ) :
    ∃ C c s : ℝ, 0 < C ∧ 0 < c ∧ 0 < s ∧ ∀ (x : Vertex 2) (K : ℝ), 1 ≤ K →
      latticeBondLaw 2 p (eventG2At q (4 * (|q 0| + |q 1|) + 1) x K)ᶜ ≤
        ENNReal.ofReal (C * Real.exp (-(c * K ^ s))) := by
  obtain ⟨s, C, hs, hC, hQx⟩ := hQ 2 le_rfl p hpc hp1 (1 / 2) (by norm_num)
  set c := (5 / C) ^ s with hc_def
  have hc : 0 < c := Real.rpow_pos_of_pos (by positivity) s
  set K₁ := 2 * C ^ 2 with hK₁
  have hK₁0 : 0 ≤ K₁ := by positivity
  refine ⟨2 * Real.exp (c * K₁ ^ s), c, s, by positivity, hc, hs, fun x K hK => ?_⟩
  obtain ⟨M, -, -, hMos, hMae⟩ := hQx x
  set μ := latticeBondLaw 2 p
  have hexp1 : 1 ≤ Real.exp (c * K₁ ^ s) :=
    Real.one_le_exp (mul_nonneg hc.le (Real.rpow_nonneg hK₁0 s))
  rcases lt_or_ge K K₁ with hKK | hKK
  · refine prob_le_one.trans ?_
    rw [ENNReal.one_le_ofReal]
    have hKs : K ^ s ≤ K₁ ^ s := Real.rpow_le_rpow (by linarith) hKK.le hs.le
    have h1 : 1 ≤ Real.exp (c * K₁ ^ s - c * K ^ s) :=
      Real.one_le_exp (by nlinarith)
    calc (1 : ℝ) ≤ 2 * Real.exp (c * K₁ ^ s - c * K ^ s) := by linarith
      _ = 2 * Real.exp (c * K₁ ^ s) * Real.exp (-(c * K ^ s)) := by
        rw [mul_assoc, ← Real.exp_add, sub_eq_add_neg]
  · have hbad := ae_iff.mp (hMae.and hUae)
    have hsub : (eventG2At q (4 * (|q 0| + |q 1|) + 1) x K)ᶜ ⊆ {ω | ¬ ((∀ h : HasUniqueInfiniteOpenComponent ω,
        ∀ (q : Fin 2 → ℝ) (ℓ : uniqueInfiniteComponent h → ℝ),
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
            ≤ C * (∑ i, |q i|) * r ^ (1 / 2 : ℝ)) ∧ HasUniqueInfiniteOpenComponent ω)} ∪
        {ω | 5 * K < M ω} := by
      intro ω hω
      by_contra hn
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not, not_lt] at hn
      exact hω (mem_eventG2At_of_minimalScale_le hC hKK hK q hn.1.1 hn.1.2 hn.2)
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
    rw [hbad, zero_add]
    refine (measure_lt_minimalScale_le hs hC (by linarith) hMos).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have hpow : (5 * K / C) ^ s = c * K ^ s := by
      rw [hc_def, ← Real.mul_rpow (by positivity) (by linarith)]
      ring_nf
    rw [hpow, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (le_mul_of_one_le_left (Real.exp_pos _).le hexp1) (by norm_num)

/-- `SecondGoodEventAtStep` (eq. `PG2goesto1` at every slope `q`), with `Λ = 4 |q|₁ + 1`: from the
quantitative part of Theorem 2.5, applied at slope `q`. -/
theorem secondGoodEventAtStep : SecondGoodEventAtStep := by
  intro hUq hQ p hpc hp1 q
  obtain ⟨C, c, s, hC, hc, hs, hb⟩ := secondGoodEventAt_bound hQ hpc hp1
    ((mem_ae_iff_prob_eq_one (measurableSet_uniqueInfiniteComponentEvent 2)).mpr
      (hUq.2 2 le_rfl p hpc hp1)) q
  exact ⟨4 * (|q 0| + |q 1|) + 1, by positivity, C, c, s, hC, hc, hs, hb 0⟩

end SecondGoodEventAt

open LatticeProb.External Rigidity.External in
/-- **Proposition 5.11 at every slope** (the draft `LevelSetDensityStmt`) from Proposition 3.2 at
every slope (`NotLipschitzAtStep`, proved by `Rigidity.Steps.S3.notLipschitzAt`) and
`SecondGoodEventAtStep`, with Lemma 5.16, Props 5.12, 5.20, 5.24, Theorem 2.5 and the external
inputs; every other step of Lemmas 5.25-5.28 at slope `q` is proved. -/
theorem levelSetDensity_of_notLipschitzAt (hU : SupercriticalBondUniqueness)
    (hQ : CorrectorQuantitativeInput) (hC : SupercriticalBondCorrectorInput)
    (hJ : JordanCurveTheoremSphere) {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) {f : Vertex 2 → ℤ}
    (h32 : ∀ q : Fin 2 → ℝ, q ≠ 0 → NotLipschitzAtStep p q)
    (h512 : InfiniteDisjointPathsStmt p f) (h516 : StrongMaxPrincipleStmt p)
    (h520 : BoundarySizeStmt p f) (h524 : LongPathRenormalizedStmt p) :
    LevelSetDensityStmt p f :=
  levelSetDensity_of_largeGradientSensitiveAt fun q hq => by
    obtain ⟨Λ, hΛ, h2q⟩ := secondGoodEventAtStep hU hQ p hpc hp1 q
    exact largeGradientSensitiveAt_of_steps hq hΛ hQ hpc hp1 h520 h524
      (goodEventPositiveAt_of_steps (exists_eventG3At_of_notLipschitzAt hC hpc hp1 (h32 q hq)) h2q)
      (finiteBranchesHarmonic_of_steps hJ h516 h512 Proofs.Section5.infiniteBranchesStep
        leafExitHarmonicStep Proofs.Section5.exitsDistinctStep Proofs.Section5.leafSeparatorStep
        Proofs.Section5.noK33MinorStep)
      correctedPlaneMinimalScaleAtStep Proofs.Section5.explorationBlockStep
      explorationHolesRayStep rootBlockHarmonicStep leafSensitiveHarmonicStep
      fluxBalanceHarmonicStep Proofs.Section5.fluxGrowthStep Proofs.Section5.greedyExplorationStep
      Proofs.Section5.explorationAssemblyStep Proofs.Section5.terminationWindowStep

end Rigidity.Steps.Section5
