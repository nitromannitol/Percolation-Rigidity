import Rigidity.Steps.Section5.LevelSetDensity
import Rigidity.Steps.Section5.Common

/-!
# Proposition 5.7: the steps of the gradient trichotomy

Proposition 5.7 (`prop:gradient-trichotomy`, corrected draft L1645-1651, proof L1739-1836) is carved
as follows. Fix `f` finitely supported and a slope `q ≠ 0`. The event `E` of L1741 is
`trichotomyFailure f q`: the cluster is unique, `Σ f = 0`, `Σ f ℓ_q = 0` and `u_f - lim u_f` has
infinite support. Its part on which the oriented edge `(x, y)` is sensitive (`∇u_f ≠ 0`, `∇ℓ_q ≠ 0`)
is `sensitiveFailure f q x y`, and `ω^e` is `flipAt e ω`.

* `FlipInfluenceStep` (`step:5.7-martingale`, eq. `event-not-dependent`): for `0 < p < 1` and a
  null-measurable event `E`, `P[E ∆ {ω^e ∈ E}] → 0` along the edges `e`.
* `step:5.7-flip` (eq. `flip-edge-implication`): almost surely, if `ω ∈ E` and `(x, y)` is
  sensitive then `ω^{xy} ∉ E`; proved (`ae_flipAt_not_mem_of_steps`) from three deterministic
  steps and two almost sure inputs (Liouville at order zero, symmetry of `H`):
  - `FlipShrinkStep`: if closing the edge changes the vertex set of `𝒞_∞`, the mass of `f` on the
    new cluster is nonzero;
  - `FlipIdentityStep`: otherwise `Σ f ℓ - Σ f ℓ' = ∇ℓ'(e) ∇u_f(e)` (L1806-1812);
  - `FlipGradientStep`: `∇ℓ(e) ≠ 0` implies `∇ℓ'(e) ≠ 0` (L1801-1803).
* `DensityConclusionStep` (`step:5.7-conclusion`, abstract): if `P[A_e] → 0` along the edges and,
  almost surely on `E`, the edges `e` of `B_{2^k}` with `ω ∈ A_e` have density `≥ c > 0` for all
  large `k`, then `P[E] = 0` (Markov's inequality and a countable union).
* `TrichotomyEventMeasurableStep`: `E` is null-measurable (implicit in the paper).

`gradientTrichotomyAt_of_steps` proves the conclusion of Proposition 5.7 for one slope `q` from
these steps and Proposition 5.11 for the same slope `q`; `gradientTrichotomy_of_steps` proves
Proposition 5.7. Prop 5.7 at the slope `q` uses Prop 5.11 at the slope `q` only.

Issues in the printed proof.
* `lim sup` versus `lim inf`. Step 3 (L1833-1836) derives `E[1_E N_k] / |B_{2^k}| → 0` for the
  number `N_k` of sensitive edges of `B_{2^k}`, and claims a contradiction with eq.
  `level-set-of-harmonic-function`, a `lim sup`. Convergence to `0` in `L¹` does not contradict a
  positive `lim sup` (a typewriter sequence of events `{U ∈ I_k}`, `|I_k| → 0`, covering each point
  infinitely often). The argument needs Proposition 5.11 with `lim inf`
  (`LevelSetDensityEventuallyAt`), which its proof gives: the ergodic theorem on the triangles
  (`TriangleDensityStep`) yields a limit, not a `lim sup`. The draft `LevelSetDensityStmt` states
  the `lim inf` form ([C29], gap G8).
* Vertex sets (L1797-1799). If closing `e` disconnects a finite piece `F` meeting `supp f`, then
  `∇u_f(e) = ±Σ_F f` need not vanish; the conclusion `ω^e ∉ E` still holds, since the mass of `f`
  on the new cluster is `∓∇u_f(e) ≠ 0` (`FlipShrinkStep`).
* Symmetry. The identity of L1806-1812 needs `Σ_y f(y) (G(y, a) - G(y, b)) = u_f(a) - u_f(b)`
  for `Σ f = 0`, i.e. the symmetry of `H(x, y) = G(x, y) - κ(y)` (corrected draft L459, from
  Dario-Gu Section 5). `GreenSymmetry` is proved from the asymptotics of the Green function
  (`Rigidity.Proofs.Section5.greenSymmetry`, from `SupercriticalBondGreenQuantitative`).
* Measurability of `E` (`TrichotomyEventMeasurableStep`) is used by the martingale argument and is
  not addressed in the paper; it is proved in `Rigidity/Proofs/Section5/TrichotomyMeasurable.lean`
  (`trichotomyEventMeasurable`).
* `0 < p < 1` is needed: for `p = 1`, `𝒞_∞ = ℤ²`, `ℓ_{e₁}(x) = x₁`, and `f = δ_{e₂} - δ₀` has
  `Σ f = Σ f ℓ_{e₁} = 0` while `u_f` has infinite support.
-/

open MeasureTheory LatticeProb.Percolation Classical Filter Topology
open scoped symmDiff

namespace Rigidity.Steps.Section5

open Rigidity.Section5

variable {ω : Configuration 2}

/-- The configuration `ω^e`: the status of the bond `e` is flipped (no change if `e` is not a
bond). -/
def flipAt (e : Sym2 (Vertex 2)) (ω : Configuration 2) : Configuration 2 :=
  fun b => if b.val = e then !ω b else ω b

/-- Witnesses of the event `E` of L1741 at `ω`: `Σ f = 0`, a Green family `G`, a corrected plane
`ℓ` of slope `q` with `Σ f ℓ = 0`, and a limit `L` of `u_f` at infinity such that `u_f - L` has
infinite support. -/
def IsTrichotomyFailure (f : Vertex 2 → ℤ) (q : Fin 2 → ℝ) (h : HasUniqueInfiniteOpenComponent ω)
    (G : uniqueInfiniteComponent h → uniqueInfiniteComponent h → ℝ)
    (ℓ : uniqueInfiniteComponent h → ℝ) (L : ℝ) : Prop :=
  mass (uniqueInfiniteComponent h) f = 0 ∧ IsGreenFamily (uniqueInfiniteComponent h) G ∧
    IsCorrectedPlane (uniqueInfiniteComponent h) q ℓ ∧ pairing _ f ℓ = 0 ∧
    Tendsto (potential _ G f) cofinite (𝓝 L) ∧
    (Function.support fun x => potential _ G f x - L).Infinite

/-- The event `E` of L1741. -/
def trichotomyFailure (f : Vertex 2 → ℤ) (q : Fin 2 → ℝ) : Set (Configuration 2) :=
  {ω | ∃ (h : HasUniqueInfiniteOpenComponent ω)
    (G : uniqueInfiniteComponent h → uniqueInfiniteComponent h → ℝ)
    (ℓ : uniqueInfiniteComponent h → ℝ) (L : ℝ), IsTrichotomyFailure f q h G ℓ L}

/-- The part of `E` on which the oriented edge `(x, y)` is an edge of `𝒞_∞` with `∇u_f ≠ 0` and
`∇ℓ_q ≠ 0`, for the same witnesses. -/
def sensitiveFailure (f : Vertex 2 → ℤ) (q : Fin 2 → ℝ) (x y : Vertex 2) :
    Set (Configuration 2) :=
  {ω | ∃ (h : HasUniqueInfiniteOpenComponent ω)
    (G : uniqueInfiniteComponent h → uniqueInfiniteComponent h → ℝ)
    (ℓ : uniqueInfiniteComponent h → ℝ) (L : ℝ), IsTrichotomyFailure f q h G ℓ L ∧
    ∃ a b : uniqueInfiniteComponent h, a.val = x ∧ b.val = y ∧ (componentGraph _).Adj a b ∧
      potential _ G f a ≠ potential _ G f b ∧ ℓ a ≠ ℓ b}

/-- Liouville at order zero on a component: harmonic functions of sublinear growth are
constant. -/
def HasSublinearLiouville (C : OpenComponent ω) : Prop :=
  ∀ v : C → ℝ, (∀ x, componentLaplacian C v x = 0) →
    (∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ x : C, R ≤ eucl x.val → |v x| ≤ ε * eucl x.val) →
    ∃ c : ℝ, ∀ x, v x = c

/-- `step:5.7-martingale` (Step 1, eq. `event-not-dependent`): for `0 < p < 1` and a
null-measurable event `E`, `E[(1_E(ω) - 1_E(ω^e))²] → 0` along the edges `e = {x, y}`. -/
def FlipInfluenceStep (p : unitInterval) : Prop :=
  0 < (p : ℝ) → (p : ℝ) < 1 →
    ∀ E : Set (Configuration 2), NullMeasurableSet E (latticeBondLaw 2 p) →
      Tendsto (fun e : Vertex 2 × Vertex 2 =>
        latticeBondLaw 2 p (E ∆ (flipAt s(e.1, e.2) ⁻¹' E))) cofinite (𝓝 0)

/-- Step 2, vertex sets (L1797-1799, deterministic): let `-Δu = f` on `𝒞_∞` with `Σ f = 0` and
`u(a) ≠ u(b)` on an edge `ab` of `𝒞_∞`. If closing `ab` changes the vertex set of the infinite
cluster, it disconnects a finite piece `F` with `Σ_F f = ±(u(a) - u(b))`, so the mass of `f` on the
new cluster is nonzero. -/
def FlipShrinkStep (f : Vertex 2 → ℤ) : Prop :=
  (Function.support f).Finite →
  ∀ (ω : Configuration 2) (h : HasUniqueInfiniteOpenComponent ω)
    (u : uniqueInfiniteComponent h → ℝ), (∀ x, -componentLaplacian _ u x = f x.val) →
    ∀ a b : uniqueInfiniteComponent h, (componentGraph _).Adj a b → u a ≠ u b →
    mass (uniqueInfiniteComponent h) f = 0 →
    ∀ h' : HasUniqueInfiniteOpenComponent (flipAt s(a.val, b.val) ω),
      (uniqueInfiniteComponent h').supp ≠ (uniqueInfiniteComponent h).supp →
      mass (uniqueInfiniteComponent h') f ≠ 0

/-- Step 2, the identity of L1806-1812 (deterministic): if closing the edge `ab` of `𝒞_∞` keeps
its vertex set, `ℓ, ℓ'` are corrected planes of slope `q` before and after, and `Σ f = 0`, then
`Σ f ℓ - Σ f ℓ' = (ℓ'(b) - ℓ'(a)) (u_f(a) - u_f(b))`. Proof: `ℓ - ℓ' - ∇ℓ'(ab) (G(·, a) - G(·, b))`
is harmonic and sublinear on `𝒞_∞`, hence constant; then the symmetry of `H = G - κ` and
`Σ f = 0`. -/
def FlipIdentityStep (f : Vertex 2 → ℤ) (q : Fin 2 → ℝ) : Prop :=
  (Function.support f).Finite →
  ∀ (ω : Configuration 2) (h : HasUniqueInfiniteOpenComponent ω),
    HasSublinearLiouville (uniqueInfiniteComponent h) →
    ∀ G, IsGreenFamily (uniqueInfiniteComponent h) G →
    (∃ κ : uniqueInfiniteComponent h → ℝ, ∀ x y, G x y - κ y = G y x - κ x) →
    mass (uniqueInfiniteComponent h) f = 0 →
    ∀ ℓ, IsCorrectedPlane (uniqueInfiniteComponent h) q ℓ →
    ∀ a b : uniqueInfiniteComponent h, (componentGraph _).Adj a b →
    ∀ h' : HasUniqueInfiniteOpenComponent (flipAt s(a.val, b.val) ω),
      (uniqueInfiniteComponent h').supp = (uniqueInfiniteComponent h).supp →
    ∀ ℓ', IsCorrectedPlane (uniqueInfiniteComponent h') q ℓ' →
    ∀ a' b' : uniqueInfiniteComponent h', a'.val = a.val → b'.val = b.val →
      pairing _ f ℓ - pairing _ f ℓ' = (ℓ' b' - ℓ' a') * (potential _ G f a - potential _ G f b)

/-- Step 2, gradients (L1801-1803, deterministic): if closing the edge `ab` of `𝒞_∞` keeps its
vertex set and `ℓ'(a) = ℓ'(b)`, then `ℓ'` is harmonic on `𝒞_∞` and `ℓ - ℓ'` is constant; hence
`∇ℓ(ab) ≠ 0` implies `∇ℓ'(ab) ≠ 0`. -/
def FlipGradientStep (q : Fin 2 → ℝ) : Prop :=
  ∀ (ω : Configuration 2) (h : HasUniqueInfiniteOpenComponent ω),
    HasSublinearLiouville (uniqueInfiniteComponent h) →
    ∀ ℓ, IsCorrectedPlane (uniqueInfiniteComponent h) q ℓ →
    ∀ a b : uniqueInfiniteComponent h, (componentGraph _).Adj a b →
    ∀ h' : HasUniqueInfiniteOpenComponent (flipAt s(a.val, b.val) ω),
      (uniqueInfiniteComponent h').supp = (uniqueInfiniteComponent h).supp →
    ∀ ℓ', IsCorrectedPlane (uniqueInfiniteComponent h') q ℓ' →
    ∀ a' b' : uniqueInfiniteComponent h', a'.val = a.val → b'.val = b.val →
      ℓ a ≠ ℓ b → ℓ' a' ≠ ℓ' b'

/-- Step (corrected draft L459, Dario-Gu Section 5): almost surely the normalized Green function
`H(x, y) = G(x, y) - κ(y)` is symmetric. Proved in `Rigidity/Proofs/Section5/GreenSymmetry.lean`
(`greenSymmetry`, from `SupercriticalBondGreenQuantitative`). -/
def GreenSymmetry (p : unitInterval) : Prop :=
  ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω,
    ∀ G, IsGreenFamily (uniqueInfiniteComponent h) G →
      ∃ κ : uniqueInfiniteComponent h → ℝ, ∀ x y, G x y - κ y = G y x - κ x

/-- The event `E` is null-measurable (used by Step 1, implicit in the paper). -/
def TrichotomyEventMeasurableStep (p : unitInterval) (f : Vertex 2 → ℤ) (q : Fin 2 → ℝ) :
    Prop :=
  NullMeasurableSet (trichotomyFailure f q) (latticeBondLaw 2 p)

/-- `step:5.7-conclusion` (Step 3, abstract): let `A_e` be events indexed by the oriented
nearest-neighbour edges with `P[A_e] → 0`. If, almost surely on `E`, the edges `e` of `B_{2^k}`
with `ω ∈ A_e` number at least `c |B_{2^k}|` for all large `k`, then `P[E] = 0`. -/
def DensityConclusionStep : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] (E : Set Ω)
    (A : Vertex 2 × Vertex 2 → Set Ω),
    (∀ e, (A e).Nonempty → (nearestNeighborGraph 2).Adj e.1 e.2) →
    Tendsto (fun e => μ (A e)) cofinite (𝓝 0) →
    (∀ᵐ z ∂μ, z ∈ E → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k : ℕ in atTop,
      c ≤ ({e : Vertex 2 × Vertex 2 | eucl e.1 < 2 ^ k ∧ eucl e.2 < 2 ^ k ∧ z ∈ A e}.ncard : ℝ) /
        (Real.pi * 4 ^ k)) →
    μ E = 0

/-- The conclusion of Proposition 5.11 for the slope `q` in the draft form ([C29], lower limit): the
density of the edges of `B_{2^k}` with `∇u_f ≠ 0` and `∇ℓ_q ≠ 0` is at least `c > 0` for all
large `k`. -/
def LevelSetDensityEventuallyAt (p : unitInterval) (f : Vertex 2 → ℤ) (q : Fin 2 → ℝ) : Prop :=
  ∀ᵐ ω ∂latticeBondLaw 2 p, ∃ h : HasUniqueInfiniteOpenComponent ω,
    mass (uniqueInfiniteComponent h) f = 0 →
    ∀ G, IsGreenFamily (uniqueInfiniteComponent h) G →
    ∀ ℓ, IsCorrectedPlane (uniqueInfiniteComponent h) q ℓ →
    ∀ L : ℝ, Tendsto (potential _ G f) cofinite (𝓝 L) →
      (Function.support (fun x => potential _ G f x - L)).Infinite →
      ∃ c : ℝ, 0 < c ∧ ∀ᶠ k : ℕ in atTop,
        c ≤ ((activeEdges _ (potential _ G f) ℓ (2 ^ k)).ncard : ℝ) / (Real.pi * 4 ^ k)

/-- The draft `LevelSetDensityStmt` is `LevelSetDensityEventuallyAt` at every slope `q ≠ 0`. -/
theorem levelSetDensityStmt_iff {p : unitInterval} {f : Vertex 2 → ℤ} :
    LevelSetDensityStmt p f ↔
      ((Function.support f).Finite → ∀ q : Fin 2 → ℝ, q ≠ 0 → LevelSetDensityEventuallyAt p f q) :=
  Iff.rfl

/-- The `lim inf` form of Proposition 5.11 implies its `lim sup` form. -/
theorem levelSetDensityAt_of_eventually {p : unitInterval} {f : Vertex 2 → ℤ}
    {q : Fin 2 → ℝ} (h : LevelSetDensityEventuallyAt p f q) : LevelSetDensityAt p f q := by
  filter_upwards [h] with ω ⟨hh, hω⟩
  refine ⟨hh, fun hm G hG ℓ hℓ L hL hs => ?_⟩
  obtain ⟨c, hc, hev⟩ := hω hm G hG ℓ hℓ L hL hs
  refine ⟨c, hc, fun K => ?_⟩
  obtain ⟨k, hk, hK⟩ := (hev.and (eventually_ge_atTop K)).exists
  exact ⟨k, hK, hk⟩

/-- The conclusion of Proposition 5.7 for the slope `q`. -/
def GradientTrichotomyAt (p : unitInterval) (f : Vertex 2 → ℤ) (q : Fin 2 → ℝ) : Prop :=
  ∀ᵐ ω ∂latticeBondLaw 2 p, ∃ h : HasUniqueInfiniteOpenComponent ω,
    mass (uniqueInfiniteComponent h) f = 0 →
    ∀ G, IsGreenFamily (uniqueInfiniteComponent h) G →
    ∀ ℓ, IsCorrectedPlane (uniqueInfiniteComponent h) q ℓ →
      pairing _ f ℓ ≠ 0 ∨ ∃ L : ℝ, Tendsto (potential _ G f) cofinite (𝓝 L) ∧
        (Function.support (fun x => potential _ G f x - L)).Finite

theorem gradientTrichotomyStmt_iff {p : unitInterval} {f : Vertex 2 → ℤ} :
    GradientTrichotomyStmt p f ↔
      ((Function.support f).Finite → ∀ q : Fin 2 → ℝ, q ≠ 0 → GradientTrichotomyAt p f q) :=
  Iff.rfl

theorem sensitiveFailure_subset {f : Vertex 2 → ℤ} {q : Fin 2 → ℝ} {x y : Vertex 2} :
    sensitiveFailure f q x y ⊆ trichotomyFailure f q :=
  fun _ ⟨h, G, ℓ, L, hw, _⟩ => ⟨h, G, ℓ, L, hw⟩

theorem adj_of_mem_sensitiveFailure {f : Vertex 2 → ℤ} {q : Fin 2 → ℝ} {x y : Vertex 2}
    (hω : ω ∈ sensitiveFailure f q x y) : (nearestNeighborGraph 2).Adj x y := by
  obtain ⟨h, G, ℓ, L, -, a, b, rfl, rfl, hab, -⟩ := hω
  exact openGraph_le ω hab

/-- `step:5.7-flip` (eq. `flip-edge-implication`): almost surely, if `ω ∈ E` and the oriented
edge `(x, y)` is sensitive, then `ω^{xy} ∉ E`. -/
theorem ae_flipAt_not_mem_of_steps {p : unitInterval} {f : Vertex 2 → ℤ} {q : Fin 2 → ℝ}
    (hf : (Function.support f).Finite) (hLiou : SublinearLiouville p) (hsym : GreenSymmetry p)
    (hshrink : FlipShrinkStep f) (hid : FlipIdentityStep f q) (hgrad : FlipGradientStep q)
    (x y : Vertex 2) :
    ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ sensitiveFailure f q x y →
      flipAt s(x, y) ω ∉ trichotomyFailure f q := by
  filter_upwards [hLiou, hsym] with ω hL hS
  rintro ⟨h, G, ℓ, L, ⟨hm, hG, hℓ, hp, -, -⟩, a, b, rfl, rfl, hab, hu, hℓab⟩
    ⟨h', G', ℓ', L', ⟨hm', -, hℓ', hp', -, -⟩⟩
  by_cases hsupp : (uniqueInfiniteComponent h').supp = (uniqueInfiniteComponent h).supp
  · have ha : a.val ∈ uniqueInfiniteComponent h' := by
      show a.val ∈ (uniqueInfiniteComponent h').supp
      rw [hsupp]
      exact a.prop
    have hb : b.val ∈ uniqueInfiniteComponent h' := by
      show b.val ∈ (uniqueInfiniteComponent h').supp
      rw [hsupp]
      exact b.prop
    have hI := hid hf ω h (hL h) G hG (hS h G hG) hm ℓ hℓ a b hab h' hsupp ℓ' hℓ'
      ⟨a.val, ha⟩ ⟨b.val, hb⟩ rfl rfl
    have hgr := hgrad ω h (hL h) ℓ hℓ a b hab h' hsupp ℓ' hℓ' ⟨a.val, ha⟩ ⟨b.val, hb⟩ rfl rfl
      hℓab
    rw [hp, hp', sub_zero] at hI
    exact mul_ne_zero (sub_ne_zero.2 (Ne.symm hgr)) (sub_ne_zero.2 hu) hI.symm
  · exact hshrink hf ω h (potential _ G f)
      (fun z => Rigidity.Proofs.Section5.potentialLaplacian ω _ G hG f hf z) a b hab hu hm h'
      hsupp hm'

/-- Steps 1 and 2: `P[E ∩ {(x, y) sensitive}] → 0` along the oriented edges. -/
theorem tendsto_measure_sensitiveFailure {p : unitInterval} {f : Vertex 2 → ℤ} {q : Fin 2 → ℝ}
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hmeas : TrichotomyEventMeasurableStep p f q)
    (h1 : FlipInfluenceStep p)
    (hflip : ∀ x y : Vertex 2, ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ sensitiveFailure f q x y →
      flipAt s(x, y) ω ∉ trichotomyFailure f q) :
    Tendsto (fun e : Vertex 2 × Vertex 2 => latticeBondLaw 2 p (sensitiveFailure f q e.1 e.2))
      cofinite (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h1 hp0 hp1 _ hmeas)
    (fun _ => zero_le) fun e => ?_
  set E := trichotomyFailure f q
  set A := sensitiveFailure f q e.1 e.2
  have hnull : latticeBondLaw 2 p (A ∩ flipAt s(e.1, e.2) ⁻¹' E) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hflip e.1 e.2] with ω hω hmem using hω hmem.1 hmem.2
  calc latticeBondLaw 2 p A
      ≤ latticeBondLaw 2 p ((A ∩ flipAt s(e.1, e.2) ⁻¹' E) ∪ (E ∆ (flipAt s(e.1, e.2) ⁻¹' E))) :=
        measure_mono fun ω hω => by
          by_cases hfl : flipAt s(e.1, e.2) ω ∈ E
          · exact Or.inl ⟨hω, hfl⟩
          · exact Or.inr (Set.mem_symmDiff.2 (Or.inl ⟨sensitiveFailure_subset hω, hfl⟩))
    _ ≤ latticeBondLaw 2 p (A ∩ flipAt s(e.1, e.2) ⁻¹' E) +
          latticeBondLaw 2 p (E ∆ (flipAt s(e.1, e.2) ⁻¹' E)) := measure_union_le _ _
    _ = latticeBondLaw 2 p (E ∆ (flipAt s(e.1, e.2) ⁻¹' E)) := by rw [hnull, zero_add]

/-- The lattice points of a Euclidean ball around the origin form a finite set. -/
theorem finite_eucl_lt_vertex (R : ℝ) : {x : Vertex 2 | eucl x < R}.Finite := by
  have h0 : latticeEuclideanEmbedding (0 : Vertex 2) = 0 := by
    ext i; simp [latticeEuclideanEmbedding]
  refine (finite_latticeEuclideanBall (0 : Vertex 2) R).subset fun x hx => ?_
  simp only [Set.mem_setOf_eq, h0, dist_zero_right]
  exact hx

/-- The sensitive oriented edges of `𝒞_∞` in `B_r` for the witnesses of `E` are among the
oriented edges `(x, y)` of `B_r` with `ω ∈ sensitiveFailure f q x y`. -/
theorem ncard_activeEdges_le {f : Vertex 2 → ℤ} {q : Fin 2 → ℝ}
    {h : HasUniqueInfiniteOpenComponent ω}
    {G : uniqueInfiniteComponent h → uniqueInfiniteComponent h → ℝ}
    {ℓ : uniqueInfiniteComponent h → ℝ} {L : ℝ} (hw : IsTrichotomyFailure f q h G ℓ L) (r : ℝ) :
    (activeEdges (uniqueInfiniteComponent h) (potential _ G f) ℓ r).ncard ≤
      {e : Vertex 2 × Vertex 2 | eucl e.1 < r ∧ eucl e.2 < r ∧
        ω ∈ sensitiveFailure f q e.1 e.2}.ncard := by
  refine Set.ncard_le_ncard_of_injOn (fun e => (e.1.val, e.2.val)) ?_ ?_ ?_
  · rintro ⟨a, b⟩ ⟨hab, ha, hb, hu, hℓ⟩
    exact ⟨ha, hb, h, G, ℓ, L, hw, a, b, rfl, rfl, hab, hu, hℓ⟩
  · rintro ⟨a, b⟩ - ⟨a', b'⟩ - he
    simp only [Prod.mk.injEq] at he
    exact Prod.ext (Subtype.ext he.1) (Subtype.ext he.2)
  · exact ((finite_eucl_lt_vertex r).prod (finite_eucl_lt_vertex r)).subset
      fun e he => ⟨he.1, he.2.1⟩

/-- Step 3: `P[E] = 0`, from `P[E ∩ {e sensitive}] → 0` and the `lim inf` form of
Proposition 5.11. -/
theorem measure_trichotomyFailure_eq_zero {p : unitInterval} {f : Vertex 2 → ℤ}
    {q : Fin 2 → ℝ} (h3 : DensityConclusionStep)
    (hT : Tendsto (fun e : Vertex 2 × Vertex 2 =>
      latticeBondLaw 2 p (sensitiveFailure f q e.1 e.2)) cofinite (𝓝 0))
    (h511 : LevelSetDensityEventuallyAt p f q) :
    latticeBondLaw 2 p (trichotomyFailure f q) = 0 := by
  refine h3 (latticeBondLaw 2 p) _ (fun e => sensitiveFailure f q e.1 e.2)
    (fun _ he => adj_of_mem_sensitiveFailure he.some_mem) hT ?_
  filter_upwards [h511] with ω hω
  rintro ⟨h, G, ℓ, L, hw⟩
  obtain ⟨_, hω⟩ := hω
  obtain ⟨c, hc, hev⟩ := hω hw.1 G hw.2.1 ℓ hw.2.2.1 L hw.2.2.2.2.1 hw.2.2.2.2.2
  refine ⟨c, hc, hev.mono fun k hk => hk.trans ?_⟩
  have hpos : (0 : ℝ) < Real.pi * 4 ^ k := by positivity
  exact div_le_div_of_nonneg_right (by exact_mod_cast ncard_activeEdges_le hw _) hpos.le

/-- The conclusion of Proposition 5.7 for a slope `q`, from Steps 1-3, the uniqueness of the
infinite cluster, the limit of `u_f` at infinity, Liouville at order zero, the symmetry of `H`,
and Proposition 5.11 (`lim inf` form) for the same slope `q`. -/
theorem gradientTrichotomyAt_of_steps {p : unitInterval} {f : Vertex 2 → ℤ} {q : Fin 2 → ℝ}
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hf : (Function.support f).Finite)
    (huniq : UniqueClusterAe p) (hlim : PotentialLimit p) (hLiou : SublinearLiouville p)
    (hsym : GreenSymmetry p) (hmeas : TrichotomyEventMeasurableStep p f q)
    (h1 : FlipInfluenceStep p) (hshrink : FlipShrinkStep f) (hid : FlipIdentityStep f q)
    (hgrad : FlipGradientStep q) (h3 : DensityConclusionStep)
    (h511 : LevelSetDensityEventuallyAt p f q) : GradientTrichotomyAt p f q := by
  have hE := measure_trichotomyFailure_eq_zero h3
    (tendsto_measure_sensitiveFailure hp0 hp1 hmeas h1
      (ae_flipAt_not_mem_of_steps hf hLiou hsym hshrink hid hgrad)) h511
  filter_upwards [huniq, hlim f hf, measure_eq_zero_iff_ae_notMem.1 hE] with ω hu hL hnE
  refine ⟨hu, fun hm G hG ℓ hℓ => ?_⟩
  by_contra hcon
  rw [not_or, not_ne_iff, not_exists] at hcon
  obtain ⟨L, hL⟩ := hL hu hm
  exact hnE ⟨hu, G, ℓ, L, hm, hG, hℓ, hcon.1, hL G hG, fun hfin => hcon.2 L ⟨hL G hG, hfin⟩⟩

/-- Proposition 5.7 from Steps 1-3 and Proposition 5.11 (`lim inf` form) for every slope
`q ≠ 0`. -/
theorem gradientTrichotomy_of_steps {p : unitInterval} {f : Vertex 2 → ℤ}
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (huniq : UniqueClusterAe p)
    (hlim : PotentialLimit p) (hLiou : SublinearLiouville p) (hsym : GreenSymmetry p)
    (hmeas : ∀ q : Fin 2 → ℝ, q ≠ 0 → TrichotomyEventMeasurableStep p f q)
    (h1 : FlipInfluenceStep p) (hshrink : FlipShrinkStep f)
    (hid : ∀ q, FlipIdentityStep f q) (hgrad : ∀ q, FlipGradientStep q)
    (h3 : DensityConclusionStep)
    (h511 : ∀ q : Fin 2 → ℝ, q ≠ 0 → LevelSetDensityEventuallyAt p f q) :
    GradientTrichotomyStmt p f := fun hf q hq =>
  gradientTrichotomyAt_of_steps hp0 hp1 hf huniq hlim hLiou hsym (hmeas q hq) h1 hshrink
    (hid q) (hgrad q) h3 (h511 q hq)

end Rigidity.Steps.Section5
