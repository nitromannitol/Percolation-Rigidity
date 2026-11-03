import Rigidity.Draft.Section3Statements
import Rigidity.External.WellConnected
import Rigidity.Support.MixedGreenResult
import LatticeProb.External.SupercriticalBondUniquenessInput
import Rigidity.Steps.S3.NotLipschitzInner

/-!
# Proposition 3.2, carved into its steps

Proposition 3.2 (`prop:not-lipschitz`, corrected draft L864-1112): for every `L ≥ 1`, with positive
probability the corrected plane `ℓ_{e₁}` has `|∇ℓ_{e₁}(0)| > L`. The proof argues by contradiction:
if `|∇ℓ_{e₁}(0)| ≤ L` almost surely, then `ℓ_{e₁}` and (by finite energy) the corrected plane of any
finitely modified environment are `L`-Lipschitz. On the event `E_N` (well-connected cube `Q_N`,
small minimal scales of the mixed derivative of the Green function, flux of `ℓ_{e₁}` of order
`ā N^{d-1}` through the left face and `o(N^{d-1})` through the sides) one removes the horizontal
edges of the centre plane that are not bridges; Lemma 3.3 and Proposition 2.8 show that the flux of
the new corrected plane `ℓ'` through the left face and the sides is still of order `N^{d-1}`, the
divergence identity on `L(Q_N)` transfers it to the centre plane, where only
`C N^{d-1-1/(10d)+1/(10d)²}` edges carry a nonzero gradient of `ℓ'`, each bounded by `L`.

Steps (one per step of the proof of Proposition 3.2):
* `EdgeGradientStep`, `FiniteEnergyStep`, `ClosedBondsUniqueStep`: the preamble of the proof
  (L952): stationarity, and Lemma 2.1 (finite energy) for the modified environments.
* `WellConnectedEventStep`, `GreenScaleEventStep`, `FluxEventStep`: `step:3.2-event` (L954-984),
  split into its three parts.
* `RemovalStep`: `step:3.2-removal` (L986-1022).
* `ShortPathsStep`: `step:3.2-short-paths` (L1023-1062), together with the choice of the removable
  horizontal edges and the count of the remaining ones (eq. (horizontal-flux-small)).
* `DivergenceStep`: `step:3.2-divergence` (eq. (divergence-theorem-flux)).
* `BridgeFluxStep`: `step:3.2-bridge-flux` (L1074-1080).
* `GreenKernelSumStep`: the lattice sum of `step:3.2-contradiction` (eqs. (altered-grad-left-bound)
  and (altered-grad-top-and-bottom-bound)).

The final arithmetic and the assembly (`notLipschitz_of_steps`) are proved here.

Deviations from the printed proof:
* the flux through the left face is the outward flux of `L(Q_N)`, over the edges `(x, x - e₁)`,
  `x ∈ left(Q_N)`; the printed `(x, x + e₁)` is not a boundary edge of `L(Q_N)` and the printed
  expectation `E[(ℓ_{e₁}(x) - ℓ_{e₁}(x + e₁)) 1] = ā > 0` has the wrong sign;
* the bound on the side fluxes of `ℓ_{e₁} - ℓ'` ("Similarly") needs the lattice sum
  `GreenKernelSumStep`, since the removed edges come within `N^{1/d}` of the sides;
* the zero gradient across a non-removed horizontal edge uses that one side of the bridge is
  finite, i.e. the uniqueness of the infinite cluster of the modified environment
  (`ClosedBondsUniqueStep`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Topology LatticeProb LatticeProb.Percolation Rigidity.Section3 Classical
open scoped BigOperators ENNReal

namespace Rigidity.Steps.S3

variable {d : ℕ}

/-! ### The cube `Q_N` and its faces, eq. (box-decomp) -/

/-- The cube `Q_N = {x ∈ ℤᵈ : |xᵢ| ≤ N for every i}`. -/
noncomputable def latticeCube (d N : ℕ) : Finset (Vertex d) :=
  Fintype.piFinset fun _ => Finset.Icc (-(N : ℤ)) N

section Faces

variable [NeZero d]

/-- `L(Q_N) = {x ∈ Q_N : x₁ ≤ 0}`. -/
noncomputable def halfCube (d N : ℕ) [NeZero d] : Finset (Vertex d) :=
  (latticeCube d N).filter fun x => x 0 ≤ 0

/-- `left(Q_N) = {x ∈ Q_N : x₁ = -N}`. -/
noncomputable def leftFace (d N : ℕ) [NeZero d] : Finset (Vertex d) :=
  (latticeCube d N).filter fun x => x 0 = -(N : ℤ)

/-- `center(Q_N) = {x ∈ Q_N : x₁ = 0}`. -/
noncomputable def centerFace (d N : ℕ) [NeZero d] : Finset (Vertex d) :=
  (latticeCube d N).filter fun x => x 0 = 0

/-- The side of `L(Q_N)` where `x_j = N`. -/
noncomputable def upperSide (j : Fin d) (N : ℕ) : Finset (Vertex d) :=
  (halfCube d N).filter fun x => x j = N

/-- The side of `L(Q_N)` where `x_j = -N`. -/
noncomputable def lowerSide (j : Fin d) (N : ℕ) : Finset (Vertex d) :=
  (halfCube d N).filter fun x => x j = -(N : ℤ)

/-- The centre points of `Q_{N - N^{1/d}}`: the centre points at distance at least `N^{1/d}` from
the sides of `Q_N`. The removed horizontal edges start at these points. -/
noncomputable def centerInner (d N : ℕ) [NeZero d] : Finset (Vertex d) :=
  (centerFace d N).filter fun x =>
    ∀ i : Fin d, i ≠ 0 → ((|x i| : ℤ) : ℝ) + (N : ℝ) ^ (1 / (d : ℝ)) ≤ N

/-- The sum of `f x y` over the outward edges `(x, x - e₁)` of `L(Q_N)` through `left(Q_N)`. -/
noncomputable def leftSum (f : Vertex d → Vertex d → ℝ) (N : ℕ) : ℝ :=
  ∑ x ∈ leftFace d N, f x (x - unit 0)

/-- The sum of `f x y` over the outward edges `(x, x ± e_j)`, `j ≠ 1`, of `L(Q_N)` through
`sides(Q_N)`. -/
noncomputable def sidesSum (f : Vertex d → Vertex d → ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.univ.erase (0 : Fin d),
    (∑ x ∈ upperSide j N, f x (x + unit j) + ∑ x ∈ lowerSide j N, f x (x - unit j))

/-- The sum of `f x y` over the horizontal edges `(x, x + e₁)`, `x ∈ center(Q_N)`, the outward
edges of `L(Q_N)` through the centre plane. -/
noncomputable def centerSum (f : Vertex d → Vertex d → ℝ) (N : ℕ) : ℝ :=
  ∑ x ∈ centerFace d N, f x (x + unit 0)

/-- The horizontal edge `{x, x + e₁}`. -/
def centerBond (x : Vertex d) : Bond d :=
  bondOfAdjacent (show (nearestNeighborGraph d).Adj x (x + unit 0) from ⟨0, Or.inl rfl⟩)

end Faces

/-- The discrete normal derivative along `(x, y)` on the cluster `C`:
`(u(x) - u(y)) 1_{(x, y) ∈ E(C)}`. -/
noncomputable def edgeDifference {ω : Configuration d} (C : OpenComponent ω) (u : C → ℝ)
    (x y : Vertex d) : ℝ :=
  if x ∈ C.supp ∧ (openGraph ω).Adj x y then extend C u x - extend C u y else 0

section Fluxes

variable [NeZero d] {ω : Configuration d}

/-- The flux of `u` out of `L(Q_N)` through `left(Q_N)`, eq. (left-side-large). -/
noncomputable def leftFlux (C : OpenComponent ω) (u : C → ℝ) (N : ℕ) : ℝ :=
  leftSum (edgeDifference C u) N

/-- The flux of `u` out of `L(Q_N)` through `sides(Q_N)`, eq. (other-sides-small). -/
noncomputable def sideFlux (C : OpenComponent ω) (u : C → ℝ) (N : ℕ) : ℝ :=
  sidesSum (edgeDifference C u) N

/-- The flux of `u` out of `L(Q_N)` through `center(Q_N)`. -/
noncomputable def centerFlux (C : OpenComponent ω) (u : C → ℝ) (N : ℕ) : ℝ :=
  centerSum (edgeDifference C u) N

end Fluxes

/-- The decay `|e - e'|^{-(d - 1/4)}` of the mixed derivative of the Green function
(Proposition 2.8 with `δ = 1/4`) between an edge `(x, y)` and a point `z`, at the smaller of the
two `ℓ¹` distances. -/
noncomputable def pairKernel (x y z : Vertex d) : ℝ :=
  1 / Real.rpow (min (latticeL1Dist x z : ℝ) (latticeL1Dist y z : ℝ)) ((d : ℝ) - 1 / 4)

/-! ### The steps -/

section Steps

variable (d) [NeZero d]

/-- Preamble of the proof (L952), stationarity: if `|∇ℓ_{e₁}(0)| ≤ L` almost surely, then
almost surely every corrected plane of slope `e₁` is `L`-Lipschitz on the infinite cluster (the
law of the gradient along any edge is a translate of the law at the origin). -/
def EdgeGradientStep (p : unitInterval) : Prop :=
  ∀ L : ℝ, latticeBondLaw d p {ω | ∃ h : HasUniqueInfiniteOpenComponent ω,
      ∃ ho : (0 : Vertex d) ∈ (uniqueInfiniteComponent h).supp,
      ∃ u, IsCorrectedPlane (uniqueInfiniteComponent h) (slopeE1 d) u ∧
        L < originGradientNorm (uniqueInfiniteComponent h) ho u} = 0 →
    ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω,
      ∀ u, IsCorrectedPlane (uniqueInfiniteComponent h) (slopeE1 d) u →
        IsLipschitzWith (uniqueInfiniteComponent h) L u

/-- Preamble of the proof (L952), Lemma 2.1 (finite energy): if almost surely every corrected
plane of slope `e₁` is `L`-Lipschitz, then almost surely, for every finite set `B` of bonds, every
corrected plane of slope `e₁` of the environment in which the bonds of `B` are closed is
`L`-Lipschitz. -/
def FiniteEnergyStep (p : unitInterval) : Prop :=
  (p : ℝ) < 1 → ∀ L : ℝ,
    (∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω,
      ∀ u, IsCorrectedPlane (uniqueInfiniteComponent h) (slopeE1 d) u →
        IsLipschitzWith (uniqueInfiniteComponent h) L u) →
    ∀ᵐ ω ∂latticeBondLaw d p, ∀ B : Finset (Bond d),
      ∀ h' : HasUniqueInfiniteOpenComponent (closeBonds B ω),
      ∀ u', IsCorrectedPlane (uniqueInfiniteComponent h') (slopeE1 d) u' →
        IsLipschitzWith (uniqueInfiniteComponent h') L u'

/-- Lemma 2.1 (finite energy) applied to the uniqueness of the infinite cluster: almost surely,
for every finite set `B` of bonds, the environment in which the bonds of `B` are closed has a
unique infinite cluster. (Used in `step:3.2-bridge-flux`: one side of a bridge is finite.) -/
def ClosedBondsUniqueStep (p : unitInterval) : Prop :=
  (p : ℝ) < 1 → latticeBondLaw d p (uniqueInfiniteComponentEvent d) = 1 →
    ∀ᵐ ω ∂latticeBondLaw d p, ∀ B : Finset (Bond d),
      HasUniqueInfiniteOpenComponent (closeBonds B ω)

/-- `step:3.2-event`, well-connected part (L982, Proposition 2.3): the cube `Q_N` is
well-connected with probability tending to one. -/
def WellConnectedEventStep (p : unitInterval) : Prop :=
  Rigidity.External.WellConnectedInput → 2 ≤ d → criticalProbability d < (p : ℝ) →
    (p : ℝ) < 1 →
    Tendsto (fun N : ℕ =>
      latticeBondLaw d p {ω | ¬ Rigidity.External.IsWellConnected ω 0 N}) atTop (𝓝 0)

/-- `step:3.2-event`, mixed-Green-scale part (L982-983, stochastic integrability (stoch.estMdecay)
of Proposition 2.8): minimal scales `M_y ≤ O_s(c)` are all at most `N^{1/(10d²)}` on `Q_N` with
probability tending to one. -/
def GreenScaleEventStep (p : unitInterval) : Prop :=
  ∀ s c : ℝ, 0 < s → 0 < c → ∀ M : Vertex d → Configuration d → ℝ,
    (∀ y, Measurable (M y)) →
    (∀ y, Integrable (fun ω => Real.exp (Real.rpow (M y ω / c) s)) (latticeBondLaw d p)) →
    (∀ y, (∫ ω, Real.exp (Real.rpow (M y ω / c) s) ∂latticeBondLaw d p) ≤ 2) →
    Tendsto (fun N : ℕ => latticeBondLaw d p
      {ω | ∃ y ∈ latticeCube d N, (N : ℝ) ^ (1 / (10 * (d : ℝ) ^ 2)) < M y ω}) atTop (𝓝 0)

/-- `step:3.2-event`, flux part (eqs. (left-side-large), (other-sides-small), L974-982): there is
`a > 0` such that for every `ε > 0`, with probability tending to one, the corrected plane `ℓ_{e₁}`
has flux at least `a N^{d-1}` out of `L(Q_N)` through `left(Q_N)` and at most `ε N^{d-1}` in absolute
value through `sides(Q_N)`.

Cited in the paper: the ergodic theorem, with ergodicity from [Berger-Biskup, Thm 3.2]; the
identity `E[(ℓ_{e₁}(x + e₁) - ℓ_{e₁}(x)) 1_{(x, x+e₁) ∈ E(𝒞_∞)}] = ā > 0` (`ā` the homogenized
coefficient); `E[(ℓ_{e₁}(x) - ℓ_{e₁}(x + e_j)) 1_{(x, x+e_j) ∈ E(𝒞_∞)}] = 0` for `j ≠ 1` by symmetry
(`step:3.1-reflection`). Convergence in probability of the face averages only needs the `L²`
(von Neumann) ergodic theorem along one direction of the face and the ergodicity of a single
lattice translation (`ergodic_configurationTranslation`).

Proved in `Rigidity/Proofs/S3/FluxEvent.lean` (`fluxEventStep`); the positivity `ā > 0` is
`HomogenizedCoefficientProposed`, proved from literature inputs in
`Rigidity/Proofs/S3/HomogenizedCoefficient.lean` (`homogenizedCoefficientProposed`). -/
def FluxEventStep (p : unitInterval) : Prop :=
  2 ≤ d → criticalProbability d < (p : ℝ) → (p : ℝ) < 1 → ∃ a : ℝ, 0 < a ∧ ∀ ε : ℝ, 0 < ε →
    Tendsto (fun N : ℕ => latticeBondLaw d p {ω | ¬ ∃ h : HasUniqueInfiniteOpenComponent ω,
      ∃ u, IsCorrectedPlane (uniqueInfiniteComponent h) (slopeE1 d) u ∧
        a * (N : ℝ) ^ ((d : ℝ) - 1) ≤ leftFlux (uniqueInfiniteComponent h) u N ∧
        |sideFlux (uniqueInfiniteComponent h) u N| ≤ ε * (N : ℝ) ^ ((d : ℝ) - 1)}) atTop (𝓝 0)

/-- `step:3.2-removal` (L986-1022): processing a finite list `H` of open edges of the cluster and
removing each edge whose removal does not disconnect the current cluster yields `B ⊆ H` whose
removal does not disconnect the cluster, and such that removing any further edge of `H` disconnects
its endpoints. -/
def RemovalStep : Prop :=
  ∀ (ω : Configuration d) (C : OpenComponent ω) (H : Finset (Bond d)),
    (∀ e ∈ H, ω e = true ∧ ∀ z ∈ (e : Sym2 (Vertex d)), z ∈ C.supp) →
    ∃ B ⊆ H, (∀ x ∈ C.supp, ∀ y ∈ C.supp, (openGraph (closeBonds B ω)).Reachable x y) ∧
      ∀ e ∈ H, e ∉ B → ∀ x y : Vertex d, (e : Sym2 (Vertex d)) = s(x, y) →
        ¬ (openGraph (closeBonds (insert e B) ω)).Reachable x y

/-- `step:3.2-short-paths` (L1023-1062, eq. (short-paths)), with the choice of the removable
horizontal edges `H_N` (the horizontal edges of the medium cubes adjacent to `center(Q_N)`, outside
their boundary layers of small blue cubes and inside `Q_{N - N^{1/d}}`) and the count of the
remaining horizontal edges (eq. (horizontal-flux-small)): if `Q_N` is well-connected, removing any
non-disconnecting set `B ⊆ H_N` of open edges of the infinite cluster leaves every removed edge
`(x, x + e₁)` with `dist_{𝒞'}(x, x + e₁) ≤ C N^{1/2}`. -/
def ShortPathsStep : Prop :=
  2 ≤ d → ∃ K : ℝ, 0 < K ∧ ∃ H : ℕ → Finset (Bond d), ∀ᶠ N : ℕ in atTop,
    (∀ e ∈ H N, ∃ x ∈ centerInner d N, e = centerBond x) ∧
    ((((centerFace d N).filter fun x => centerBond x ∉ H N).card : ℕ) : ℝ) ≤
      K * (N : ℝ) ^ ((d : ℝ) - 1 - 1 / (10 * (d : ℝ)) + 1 / (10 * (d : ℝ)) ^ 2) ∧
    ∀ ω : Configuration d, Rigidity.External.IsWellConnected ω 0 N →
      ∀ (C : OpenComponent ω), C.supp.Infinite → ∀ B ⊆ H N,
        (∀ e ∈ B, ω e = true ∧ ∀ z ∈ (e : Sym2 (Vertex d)), z ∈ C.supp) →
        (∀ x ∈ C.supp, ∀ y ∈ C.supp, (openGraph (closeBonds B ω)).Reachable x y) →
        ∀ x : Vertex d, centerBond x ∈ B → ∀ (C' : OpenComponent (closeBonds B ω))
          (hx : x ∈ C'.supp) (hy : x + unit 0 ∈ C'.supp),
          (((componentGraph C').dist ⟨x, hx⟩ ⟨x + unit 0, hy⟩ : ℕ) : ℝ) ≤
            K * (N : ℝ) ^ (1 / 2 : ℝ)

/-- `step:3.2-divergence` (eq. (divergence-theorem-flux)): the total flux of a harmonic function
out of `L(Q_N)`, through `left(Q_N)`, `sides(Q_N)` and `center(Q_N)`, vanishes. -/
def DivergenceStep : Prop :=
  ∀ (ω : Configuration d) (C : OpenComponent ω) (u : C → ℝ),
    (∀ x, componentLaplacian C u x = 0) →
    ∀ N : ℕ, leftFlux C u N + sideFlux C u N + centerFlux C u N = 0

/-- `step:3.2-bridge-flux` (L1074-1080): a harmonic function on a cluster has zero gradient across
an open edge whose removal disconnects its endpoints, when the environment without that edge has a
unique infinite cluster (so that one side of the bridge is finite). -/
def BridgeFluxStep : Prop :=
  ∀ (ω : Configuration d) (C : OpenComponent ω) (u : C → ℝ),
    (∀ x, componentLaplacian C u x = 0) →
    ∀ (e : Bond d) (x y : C), (e : Sym2 (Vertex d)) = s(x.val, y.val) → ω e = true →
      HasUniqueInfiniteOpenComponent (closeBonds {e} ω) →
      ¬ (openGraph (closeBonds {e} ω)).Reachable x.val y.val → u x = u y

/-- `step:3.2-contradiction`, the lattice sum behind eqs. (altered-grad-left-bound) and
(altered-grad-top-and-bottom-bound): summing the decay `|e - e'|^{-(d - 1/4)}` of the mixed
derivative of the Green function over the centre points `e` of `Q_{N - N^{1/d}}` and the outward
edges `e'` of `L(Q_N)` through the left face and the sides gives `O(N^{d - 2 + 1/4})`. -/
def GreenKernelSumStep : Prop :=
  2 ≤ d → ∃ K : ℝ, ∀ᶠ N : ℕ in atTop,
    leftSum (fun x y => ∑ z ∈ centerInner d N, pairKernel x y z) N +
        sidesSum (fun x y => ∑ z ∈ centerInner d N, pairKernel x y z) N ≤
      K * (N : ℝ) ^ ((d : ℝ) - 2 + 1 / 4)

end Steps

/-! ### Auxiliary lemmas -/

section Aux

variable {ω : Configuration d}

theorem adj_of_adj_closeBonds {B : Finset (Bond d)} {x y : Vertex d}
    (h : (openGraph (closeBonds B ω)).Adj x y) : (openGraph ω).Adj x y := by
  obtain ⟨hn, ho⟩ := h
  refine ⟨hn, ?_⟩
  unfold closeBonds at ho
  by_cases hB : bondOfAdjacent hn ∈ B
  · rw [if_pos hB] at ho
    exact absurd ho (by decide)
  · rwa [if_neg hB] at ho

theorem adj_closeBonds_of_adj {B : Finset (Bond d)} {x y : Vertex d}
    (h : (openGraph ω).Adj x y) (hB : ∀ e ∈ B, (e : Sym2 (Vertex d)) ≠ s(x, y)) :
    (openGraph (closeBonds B ω)).Adj x y := by
  obtain ⟨hn, ho⟩ := h
  refine ⟨hn, ?_⟩
  have hnot : bondOfAdjacent hn ∉ B := fun hm => hB _ hm rfl
  unfold closeBonds
  rw [if_neg hnot]
  exact ho

theorem not_adj_closeBonds {B : Finset (Bond d)} {e : Bond d} (he : e ∈ B) {x y : Vertex d}
    (hxy : (e : Sym2 (Vertex d)) = s(x, y)) : ¬ (openGraph (closeBonds B ω)).Adj x y := by
  rintro ⟨hn, ho⟩
  have heq : bondOfAdjacent hn = e := Subtype.ext hxy.symm
  unfold closeBonds at ho
  rw [if_pos (heq ▸ he)] at ho
  exact absurd ho (by decide)

theorem closeBonds_singleton_closeBonds (B : Finset (Bond d)) (e : Bond d) :
    closeBonds {e} (closeBonds B ω) = closeBonds (insert e B) ω := by
  funext f
  simp only [closeBonds, Finset.mem_singleton, Finset.mem_insert]
  by_cases h1 : f = e <;> by_cases h2 : f ∈ B <;> simp [h1, h2]

theorem edgeDifference_of_adj (C : OpenComponent ω) (u : C → ℝ) {x y : Vertex d}
    (hx : x ∈ C.supp) (hxy : (openGraph ω).Adj x y) :
    edgeDifference C u x y = u ⟨x, hx⟩ - u ⟨y, C.mem_supp_of_adj_mem_supp hx hxy⟩ := by
  have hy := C.mem_supp_of_adj_mem_supp hx hxy
  simp only [edgeDifference, if_pos (And.intro hx hxy), Section3.extend, dif_pos hx, dif_pos hy]

theorem abs_edgeDifference_le (C : OpenComponent ω) {u : C → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hu : IsLipschitzWith C L u) (x y : Vertex d) : |edgeDifference C u x y| ≤ L := by
  by_cases h : x ∈ C.supp ∧ (openGraph ω).Adj x y
  · obtain ⟨hx, hxy⟩ := h
    have hy := C.mem_supp_of_adj_mem_supp hx hxy
    rw [edgeDifference_of_adj C u hx hxy]
    have hadj : (componentGraph C).Adj ⟨x, hx⟩ ⟨y, hy⟩ := (C.toSimpleGraph_adj hx hy).2 hxy
    have hd : (componentGraph C).dist ⟨x, hx⟩ ⟨y, hy⟩ = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.2 hadj
    have := hu ⟨x, hx⟩ ⟨y, hy⟩
    rw [hd] at this
    simpa using this
  · rw [edgeDifference, if_neg h, abs_zero]
    exact hL

theorem compareSummand_swap (g : Vertex d → Vertex d → ℝ) (w : Vertex d → ℝ) (a b : Vertex d)
    (e : Sym2 (Vertex d)) : compareSummand g w b a e = -compareSummand g w a b e := by
  induction e using Sym2.ind with
  | _ x y => simp only [compareSummand, Sym2.lift_mk]; ring

variable [NeZero d]

theorem centerBond_injective : Function.Injective (centerBond (d := d)) := by
  intro z z' h
  have h' : s(z, z + unit 0) = s(z', z' + unit 0) := congrArg Subtype.val h
  rcases Sym2.eq_iff.1 h' with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact h1
  · exfalso
    have e1 := congrFun h1 0
    have e2 := congrFun h2 0
    simp only [Pi.add_apply, unit, Pi.single_eq_same] at e1 e2
    omega

theorem centerBond_ne {x y z : Vertex d} (hz : z 0 = 0) (hxy : x 0 = y 0 ∨ y 0 < 0) :
    ((centerBond z : Bond d) : Sym2 (Vertex d)) ≠ s(x, y) := by
  intro h
  have h' : s(z, z + unit 0) = s(x, y) := h
  have hu : (z + unit 0 : Vertex d) 0 = 1 := by simp [unit, hz]
  rcases Sym2.eq_iff.1 h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have e1 : y 0 = 1 := by rw [← h2, hu]
    have e2 : x 0 = 0 := by rw [← h1, hz]
    rcases hxy with h3 | h3 <;> omega
  · have e1 : y 0 = 0 := by rw [← h1, hz]
    have e2 : x 0 = 1 := by rw [← h2, hu]
    rcases hxy with h3 | h3 <;> omega

/-- A sum over a set of horizontal edges starting at centre points is bounded by the sum over
those centre points. -/
theorem sum_le_sum_centerInner {N : ℕ} {B : Finset (Bond d)}
    (hB : ∀ e ∈ B, ∃ x ∈ centerInner d N, e = centerBond x) (f : Bond d → ℝ)
    (g : Vertex d → ℝ) (hg : ∀ z ∈ centerInner d N, 0 ≤ g z)
    (hfg : ∀ z ∈ centerInner d N, centerBond z ∈ B → f (centerBond z) ≤ g z) :
    ∑ e ∈ B, f e ≤ ∑ z ∈ centerInner d N, g z := by
  have hBeq : B = ((centerInner d N).filter fun z => centerBond z ∈ B).image centerBond := by
    ext e
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · intro he
      obtain ⟨z, hz, rfl⟩ := hB e he
      exact ⟨z, ⟨hz, he⟩, rfl⟩
    · rintro ⟨z, ⟨-, hz⟩, rfl⟩
      exact hz
  rw [hBeq, Finset.sum_image (fun z _ z' _ hzz' => centerBond_injective hzz')]
  calc _ ≤ ∑ z ∈ (centerInner d N).filter (fun z => centerBond z ∈ B), g z :=
        Finset.sum_le_sum fun z hz =>
          hfg z (Finset.mem_filter.1 hz).1 (Finset.mem_filter.1 hz).2
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun z hz _ => hg z hz

omit [NeZero d] in
theorem le_latticeL1Dist (w z : Vertex d) (i : Fin d) :
    ((|w i - z i| : ℤ) : ℝ) ≤ (latticeL1Dist w z : ℝ) := by
  unfold latticeL1Dist
  exact_mod_cast Finset.single_le_sum (f := fun i => |w i - z i|) (fun _ _ => abs_nonneg _)
    (Finset.mem_univ i)

omit [NeZero d] in
theorem latticeL1Dist_nonneg (w z : Vertex d) : (0 : ℝ) ≤ (latticeL1Dist w z : ℝ) := by
  unfold latticeL1Dist
  exact_mod_cast Finset.sum_nonneg fun i _ => abs_nonneg (w i - z i)

/-- Points of the left face or of the sides are at distance at least `N^{1/d}` from the centre
points of `Q_{N - N^{1/d}}`. -/
theorem rpow_le_latticeL1Dist {N : ℕ} (hN : 1 ≤ N) {z : Vertex d} (hz : z ∈ centerInner d N)
    {w : Vertex d} (hw : w 0 ≤ -(N : ℤ) ∨ ∃ i, i ≠ 0 ∧ (N : ℤ) ≤ |w i|) :
    (N : ℝ) ^ (1 / (d : ℝ)) ≤ (latticeL1Dist w z : ℝ) := by
  have hz' := Finset.mem_filter.1 hz
  have hz0 : z 0 = 0 := (Finset.mem_filter.1 hz'.1).2
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
  have hNd : (N : ℝ) ^ (1 / (d : ℝ)) ≤ N := by
    calc (N : ℝ) ^ (1 / (d : ℝ)) ≤ (N : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN)
            ((div_le_one (by linarith)).2 hd1)
      _ = N := Real.rpow_one _
  rcases hw with hw | ⟨i, hi, hw⟩
  · calc _ ≤ (N : ℝ) := hNd
      _ ≤ ((|w 0 - z 0| : ℤ) : ℝ) := by
          have : (N : ℤ) ≤ |w 0 - z 0| := by
            rw [hz0, sub_zero, abs_of_nonpos (by omega)]
            omega
          exact_mod_cast this
      _ ≤ _ := le_latticeL1Dist w z 0
  · have h2 := hz'.2 i hi
    calc _ ≤ (N : ℝ) - ((|z i| : ℤ) : ℝ) := by linarith
      _ ≤ ((|w i - z i| : ℤ) : ℝ) := by
          have : (N : ℤ) - |z i| ≤ |w i - z i| := by
            have := abs_sub_abs_le_abs_sub (w i) (z i)
            omega
          exact_mod_cast this
      _ ≤ _ := le_latticeL1Dist w z i

omit [NeZero d] in
theorem pairKernel_nonneg (x y z : Vertex d) : 0 ≤ pairKernel x y z :=
  div_nonneg zero_le_one (Real.rpow_nonneg
    (le_min (latticeL1Dist_nonneg x z) (latticeL1Dist_nonneg y z)) _)

/-- The decay of Proposition 2.8 at either endpoint of an edge is bounded by `pairKernel`. -/
theorem div_rpow_le_pairKernel {c : ℝ} (hc : 0 ≤ c) {x y z w : Vertex d} (hw : w = x ∨ w = y)
    (hpos : 0 < min (latticeL1Dist x z : ℝ) (latticeL1Dist y z : ℝ)) :
    c / Real.rpow (latticeL1Dist w z : ℝ) ((d : ℝ) - 1 / 4) ≤ c * pairKernel x y z := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
  have hmin : min (latticeL1Dist x z : ℝ) (latticeL1Dist y z : ℝ) ≤ (latticeL1Dist w z : ℝ) := by
    rcases hw with rfl | rfl
    · exact min_le_left _ _
    · exact min_le_right _ _
  rw [pairKernel, mul_one_div]
  simp only [Real.rpow_eq_pow]
  exact div_le_div_of_nonneg_left hc (Real.rpow_pos_of_pos hpos _)
    (Real.rpow_le_rpow hpos.le hmin (by linarith))

/-- The summand of Lemma 3.3 for a removed horizontal edge `(z, z + e₁)` and an edge
`(b, b + e_j)` is a mixed derivative of the Green function times the gradient of `w`. -/
theorem abs_compareSummand_le (C : OpenComponent ω) (G : C → C → ℝ) (w : Vertex d → ℝ)
    {b z : Vertex d} (hb : b ∈ C.supp) (hz : z ∈ C.supp) (j : Fin d)
    (hbj : (openGraph ω).Adj b (b + unit j)) (hz0 : (openGraph ω).Adj z (z + unit 0)) :
    |compareSummand (fun x z => extend C (fun y => if hx : x ∈ C.supp then G ⟨x, hx⟩ y else 0) z)
        w b (b + unit j) s(z, z + unit 0)| ≤
      (∑ i : Fin d, ∑ k : Fin d, |mixedEntry C G ⟨b, hb⟩ ⟨z, hz⟩ i k|) *
        |w (z + unit 0) - w z| := by
  have hb' := C.mem_supp_of_adj_mem_supp hb hbj
  have hz' := C.mem_supp_of_adj_mem_supp hz hz0
  have heq : compareSummand
      (fun x z => extend C (fun y => if hx : x ∈ C.supp then G ⟨x, hx⟩ y else 0) z)
        w b (b + unit j) s(z, z + unit 0) =
      mixedEntry C G ⟨b, hb⟩ ⟨z, hz⟩ j 0 * (w (z + unit 0) - w z) := by
    simp only [compareSummand, Sym2.lift_mk, mixedEntry, Section3.extend, dif_pos hb, dif_pos hb',
      dif_pos hz, dif_pos hz', dif_pos hbj, dif_pos hz0]
    ring
  rw [heq, abs_mul]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  calc |mixedEntry C G ⟨b, hb⟩ ⟨z, hz⟩ j 0|
      ≤ ∑ k : Fin d, |mixedEntry C G ⟨b, hb⟩ ⟨z, hz⟩ j k| :=
        Finset.single_le_sum (f := fun k => |mixedEntry C G ⟨b, hb⟩ ⟨z, hz⟩ j k|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ 0)
    _ ≤ _ := Finset.single_le_sum
        (f := fun i => ∑ k : Fin d, |mixedEntry C G ⟨b, hb⟩ ⟨z, hz⟩ i k|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ j)

theorem abs_leftSum_sub_le {f g k : Vertex d → Vertex d → ℝ} {N : ℕ}
    (h : ∀ x ∈ leftFace d N, |f x (x - unit 0) - g x (x - unit 0)| ≤ k x (x - unit 0)) :
    |leftSum f N - leftSum g N| ≤ leftSum k N := by
  unfold leftSum
  rw [← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum h)

theorem abs_sidesSum_sub_le {f g k : Vertex d → Vertex d → ℝ} {N : ℕ}
    (h : ∀ j ∈ Finset.univ.erase (0 : Fin d),
      (∀ x ∈ upperSide j N, |f x (x + unit j) - g x (x + unit j)| ≤ k x (x + unit j)) ∧
      (∀ x ∈ lowerSide j N, |f x (x - unit j) - g x (x - unit j)| ≤ k x (x - unit j))) :
    |sidesSum f N - sidesSum g N| ≤ sidesSum k N := by
  unfold sidesSum
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
  obtain ⟨h1, h2⟩ := h j hj
  rw [add_sub_add_comm, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum h1)
  · exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum h2)

theorem leftSum_const_mul (c : ℝ) (k : Vertex d → Vertex d → ℝ) (N : ℕ) :
    leftSum (fun x y => c * k x y) N = c * leftSum k N := by
  simp only [leftSum, Finset.mul_sum]

theorem sidesSum_const_mul (c : ℝ) (k : Vertex d → Vertex d → ℝ) (N : ℕ) :
    sidesSum (fun x y => c * k x y) N = c * sidesSum k N := by
  simp only [sidesSum, Finset.mul_sum, mul_add]

end Aux

/-! ### Assembly -/

section Assembly

/-- The conclusion of Lemma 3.3 at a configuration `ω` with a unique infinite cluster. -/
def CompareDifferentPlanesAt (hd : 2 ≤ d) {ω : Configuration d}
    (h : HasUniqueInfiniteOpenComponent ω) : Prop :=
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
              (u a - u b) - (Section3.extend _ u' a.val - Section3.extend _ u' b.val) =
                ∑ e ∈ B, compareSummand
                  (fun x z => Section3.extend _ (fun y => if hx : x ∈ (uniqueInfiniteComponent h).supp
                    then G ⟨x, hx⟩ y else 0) z)
                  (Section3.extend _ u') a.val b.val e.val

variable [NeZero d]

/-- `step:3.2-contradiction` (L1082-1112), the deterministic part: on the event `E_N`, with the
removal, the short paths, Lemma 3.3, Proposition 2.8, the divergence identity and the zero flux
across bridges, the flux of the new corrected plane through the centre plane is both of order
`N^{d-1}` and `O(L N^{d-1-1/(10d)+1/(10d)²})`. -/
theorem false_of_steps_at (hd : 2 ≤ d) (hRem : RemovalStep d) (hDiv : DivergenceStep d)
    (hBr : BridgeFluxStep d) {L a ε CG Ksp Kker : ℝ} (hL : 0 ≤ L) (hCG : 0 < CG) (hKsp : 0 < Ksp)
    {N : ℕ} (hN : 1 ≤ N) (H : Finset (Bond d))
    (hHc : ∀ e ∈ H, ∃ x ∈ centerInner d N, e = centerBond x)
    (hHct : ((((centerFace d N).filter fun x => centerBond x ∉ H).card : ℕ) : ℝ) ≤
      Ksp * (N : ℝ) ^ ((d : ℝ) - 1 - 1 / (10 * (d : ℝ)) + 1 / (10 * (d : ℝ)) ^ 2))
    (hker : leftSum (fun x y => ∑ z ∈ centerInner d N, pairKernel x y z) N +
        sidesSum (fun x y => ∑ z ∈ centerInner d N, pairKernel x y z) N ≤
      Kker * (N : ℝ) ^ ((d : ℝ) - 2 + 1 / 4))
    (harith : L * (Ksp * (N : ℝ) ^ ((d : ℝ) - 1 - 1 / (10 * (d : ℝ)) + 1 / (10 * (d : ℝ)) ^ 2)) +
        CG * (L * (Ksp * (N : ℝ) ^ (1 / 2 : ℝ))) * (Kker * (N : ℝ) ^ ((d : ℝ) - 2 + 1 / 4)) <
      a * (N : ℝ) ^ ((d : ℝ) - 1) - ε * (N : ℝ) ^ ((d : ℝ) - 1))
    {ω : Configuration d} (h : HasUniqueInfiniteOpenComponent ω)
    (hSP : ∀ B ⊆ H,
      (∀ e ∈ B, ω e = true ∧ ∀ z ∈ (e : Sym2 (Vertex d)), z ∈ (uniqueInfiniteComponent h).supp) →
      (∀ x ∈ (uniqueInfiniteComponent h).supp, ∀ y ∈ (uniqueInfiniteComponent h).supp,
        (openGraph (closeBonds B ω)).Reachable x y) →
      ∀ x : Vertex d, centerBond x ∈ B → ∀ (C' : OpenComponent (closeBonds B ω))
        (hx : x ∈ C'.supp) (hy : x + unit 0 ∈ C'.supp),
        (((componentGraph C').dist ⟨x, hx⟩ ⟨x + unit 0, hy⟩ : ℕ) : ℝ) ≤
          Ksp * (N : ℝ) ^ (1 / 2 : ℝ))
    (hUq : ∀ B : Finset (Bond d), HasUniqueInfiniteOpenComponent (closeBonds B ω))
    (hLip : ∀ (B : Finset (Bond d)) (h' : HasUniqueInfiniteOpenComponent (closeBonds B ω)) u',
      IsCorrectedPlane (uniqueInfiniteComponent h') (slopeE1 d) u' →
        IsLipschitzWith (uniqueInfiniteComponent h') L u')
    (h33 : CompareDifferentPlanesAt hd h)
    (M : Vertex d → ℝ) (hM : ∀ y ∈ latticeCube d N, M y ≤ (N : ℝ) ^ (1 / (10 * (d : ℝ) ^ 2)))
    (hMG : ∀ (y : Vertex d) (hy : y ∈ (uniqueInfiniteComponent h).supp)
      (g : uniqueInfiniteComponent h → uniqueInfiniteComponent h → ℝ),
      (∀ z, IsGreenColumn d hd (uniqueInfiniteComponent h) z (g z)) →
      ∀ x : uniqueInfiniteComponent h, M y ≤ (latticeL1Dist x.val y : ℝ) →
        (∑ i : Fin d, ∑ j : Fin d, |mixedEntry (uniqueInfiniteComponent h) g x ⟨y, hy⟩ i j|) ≤
          CG / Real.rpow (latticeL1Dist x.val y : ℝ) ((d : ℝ) - 1 / 4))
    (u0 : uniqueInfiniteComponent h → ℝ)
    (hu0 : IsCorrectedPlane (uniqueInfiniteComponent h) (slopeE1 d) u0)
    (hleft : a * (N : ℝ) ^ ((d : ℝ) - 1) ≤ leftFlux (uniqueInfiniteComponent h) u0 N)
    (hside : |sideFlux (uniqueInfiniteComponent h) u0 N| ≤ ε * (N : ℝ) ^ ((d : ℝ) - 1)) :
    False := by
  set H' := H.filter (fun e => ω e = true ∧ ∀ z ∈ (e : Sym2 (Vertex d)), z ∈ (uniqueInfiniteComponent h).supp) with hH'
  obtain ⟨B, hBH', hBconn, hBbr⟩ := hRem ω (uniqueInfiniteComponent h) H' (fun e he => (Finset.mem_filter.1 he).2)
  have hBH : B ⊆ H := hBH'.trans (Finset.filter_subset _ _)
  have hBopen : ∀ e ∈ B, ω e = true ∧ ∀ z ∈ (e : Sym2 (Vertex d)), z ∈ (uniqueInfiniteComponent h).supp :=
    fun e he => (Finset.mem_filter.1 (hBH' he)).2
  obtain ⟨h', hsupp, ⟨G, hG⟩, hq⟩ := h33 B hBopen hBconn
  set C' := uniqueInfiniteComponent h' with hC'def
  obtain ⟨-, -, ⟨u', hu'⟩, -, hId⟩ := hq (slopeE1 d)
  have hLip' : IsLipschitzWith C' L u' := hLip B h' u' hu'
  have hharm' : ∀ x, componentLaplacian C' u' x = 0 := hu'.1.1
  have hsupp' : ∀ x, x ∈ C'.supp ↔ x ∈ (uniqueInfiniteComponent h).supp := fun x => by rw [hsupp]
  set D := L * (Ksp * (N : ℝ) ^ (1 / 2 : ℝ)) with hDdef
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hD0 : 0 ≤ D := mul_nonneg hL (mul_nonneg hKsp.le (Real.rpow_nonneg hNpos.le _))
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
  -- the gradient of `ℓ'` across a removed edge, by the short paths and the Lipschitz bound
  have hDz : ∀ z, centerBond z ∈ B →
      |Section3.extend C' u' (z + unit 0) - Section3.extend C' u' z| ≤ D := by
    intro z hz
    have hzC' : z ∈ C'.supp := (hsupp' z).2 ((hBopen _ hz).2 z (Sym2.mem_mk_left _ _))
    have hz1C' : z + unit 0 ∈ C'.supp :=
      (hsupp' _).2 ((hBopen _ hz).2 _ (Sym2.mem_mk_right _ _))
    have hdist := hSP B hBH hBopen hBconn z hz C' hzC' hz1C'
    simp only [Section3.extend, dif_pos hzC', dif_pos hz1C']
    calc |u' ⟨z + unit 0, hz1C'⟩ - u' ⟨z, hzC'⟩|
        ≤ L * ((componentGraph C').dist ⟨z + unit 0, hz1C'⟩ ⟨z, hzC'⟩ : ℝ) := hLip' _ _
      _ = L * ((componentGraph C').dist ⟨z, hzC'⟩ ⟨z + unit 0, hz1C'⟩ : ℝ) := by
          rw [SimpleGraph.dist_comm]
      _ ≤ D := mul_le_mul_of_nonneg_left hdist hL
  -- the minimal scales are below the distance from the sides to the removed edges
  have hzM : ∀ z ∈ centerInner d N, ∀ w : Vertex d,
      (N : ℝ) ^ (1 / (d : ℝ)) ≤ (latticeL1Dist w z : ℝ) → M z ≤ (latticeL1Dist w z : ℝ) := by
    intro z hz w hw
    have hzQ : z ∈ latticeCube d N := (Finset.mem_filter.1 (Finset.mem_filter.1 hz).1).1
    refine (hM z hzQ).trans (le_trans ?_ hw)
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN)
      (one_div_le_one_div_of_le (by positivity) (by nlinarith))
  -- Lemma 3.3 and Proposition 2.8 along an edge of the left face or of the sides
  have hpair : ∀ x y : Vertex d, (∀ e ∈ B, (e : Sym2 (Vertex d)) ≠ s(x, y)) →
      (∃ j : Fin d, y = x + unit j ∨ x = y + unit j) →
      (∀ z ∈ centerInner d N, (N : ℝ) ^ (1 / (d : ℝ)) ≤ (latticeL1Dist x z : ℝ) ∧
        (N : ℝ) ^ (1 / (d : ℝ)) ≤ (latticeL1Dist y z : ℝ)) →
      |edgeDifference (uniqueInfiniteComponent h) u0 x y - edgeDifference C' u' x y| ≤
        CG * D * ∑ z ∈ centerInner d N, pairKernel x y z := by
    intro x y hout horient hfar
    by_cases hc : x ∈ (uniqueInfiniteComponent h).supp ∧ (openGraph ω).Adj x y
    · obtain ⟨hx, hxy⟩ := hc
      have hy := (uniqueInfiniteComponent h).mem_supp_of_adj_mem_supp hx hxy
      have hx' : x ∈ C'.supp := (hsupp' x).2 hx
      have hxy' : (openGraph (closeBonds B ω)).Adj x y := adj_closeBonds_of_adj hxy hout
      have hadj : (componentGraph (uniqueInfiniteComponent h)).Adj ⟨x, hx⟩ ⟨y, hy⟩ := ((uniqueInfiniteComponent h).toSimpleGraph_adj hx hy).2 hxy
      have e1 : edgeDifference C' u' x y =
          Section3.extend C' u' x - Section3.extend C' u' y := if_pos ⟨hx', hxy'⟩
      have hIdxy : u0 ⟨x, hx⟩ - u0 ⟨y, hy⟩ -
          (Section3.extend C' u' x - Section3.extend C' u' y) =
          ∑ e ∈ B, compareSummand (fun x z => Section3.extend (uniqueInfiniteComponent h)
            (fun y => if hx : x ∈ (uniqueInfiniteComponent h).supp then G ⟨x, hx⟩ y else 0) z)
            (Section3.extend C' u') x y e.val :=
        hId u0 u' hu0 hu' G hG ⟨x, hx⟩ ⟨y, hy⟩ hadj
      rw [edgeDifference_of_adj (uniqueInfiniteComponent h) u0 hx hxy, e1, hIdxy]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.mul_sum]
      refine sum_le_sum_centerInner (fun e he => hHc e (hBH he)) _ _
        (fun z _ => mul_nonneg (mul_nonneg hCG.le hD0) (pairKernel_nonneg x y z)) ?_
      intro z hz hzB
      have hzC : z ∈ (uniqueInfiniteComponent h).supp := (hBopen _ hzB).2 z (Sym2.mem_mk_left _ _)
      have hzadj : (openGraph ω).Adj z (z + unit 0) := ⟨⟨0, Or.inl rfl⟩, (hBopen _ hzB).1⟩
      obtain ⟨hfx, hfy⟩ := hfar z hz
      have hNd : 0 < (N : ℝ) ^ (1 / (d : ℝ)) := Real.rpow_pos_of_pos hNpos _
      have hpos : 0 < min (latticeL1Dist x z : ℝ) (latticeL1Dist y z : ℝ) :=
        lt_min (hNd.trans_le hfx) (hNd.trans_le hfy)
      have key : ∀ (b : Vertex d) (j : Fin d) (hb : b ∈ (uniqueInfiniteComponent h).supp), (b = x ∨ b = y) →
          (openGraph ω).Adj b (b + unit j) →
          |compareSummand (fun x z => Section3.extend (uniqueInfiniteComponent h)
            (fun y => if hx : x ∈ (uniqueInfiniteComponent h).supp then G ⟨x, hx⟩ y else 0) z)
            (Section3.extend C' u') b (b + unit j) s(z, z + unit 0)| ≤
            CG * D * pairKernel x y z := by
        intro b j hb hbxy hbj
        have hfb : (N : ℝ) ^ (1 / (d : ℝ)) ≤ (latticeL1Dist b z : ℝ) := by
          rcases hbxy with rfl | rfl
          · exact hfx
          · exact hfy
        refine (abs_compareSummand_le (uniqueInfiniteComponent h) G _ hb hzC j hbj hzadj).trans ?_
        have hmix := hMG z hzC G hG ⟨b, hb⟩ (hzM z hz b hfb)
        have hk := div_rpow_le_pairKernel (w := b) hCG.le hbxy hpos
        calc _ ≤ (CG * pairKernel x y z) * D :=
              mul_le_mul (hmix.trans hk) (hDz z hzB) (abs_nonneg _)
                (mul_nonneg hCG.le (pairKernel_nonneg x y z))
          _ = CG * D * pairKernel x y z := by ring
      obtain ⟨j, hj | hj⟩ := horient
      · subst hj
        exact key x j hx (Or.inl rfl) hxy
      · subst hj
        rw [compareSummand_swap, abs_neg]
        exact key y j hy (Or.inr rfl) hxy.symm
    · have e0 : edgeDifference (uniqueInfiniteComponent h) u0 x y = 0 := if_neg hc
      have e1 : edgeDifference C' u' x y = 0 :=
        if_neg fun hc' => hc ⟨(hsupp' x).1 hc'.1, adj_of_adj_closeBonds hc'.2⟩
      rw [e0, e1, sub_zero, abs_zero]
      exact mul_nonneg (mul_nonneg hCG.le hD0)
        (Finset.sum_nonneg fun z _ => pairKernel_nonneg x y z)
  have hcenterB : ∀ e ∈ B, ∀ x y : Vertex d, (x 0 = y 0 ∨ y 0 < 0) →
      (e : Sym2 (Vertex d)) ≠ s(x, y) := by
    intro e he x y hxy
    obtain ⟨z, hz, rfl⟩ := hHc e (hBH he)
    exact centerBond_ne (Finset.mem_filter.1 (Finset.mem_filter.1 hz).1).2 hxy
  -- the left face
  have hleftb : |leftFlux (uniqueInfiniteComponent h) u0 N - leftFlux C' u' N| ≤
      CG * D * leftSum (fun x y => ∑ z ∈ centerInner d N, pairKernel x y z) N := by
    unfold leftFlux
    rw [← leftSum_const_mul]
    refine abs_leftSum_sub_le fun x hx => ?_
    have hx0 : x 0 = -(N : ℤ) := (Finset.mem_filter.1 hx).2
    have hy0 : (x - unit 0 : Vertex d) 0 = x 0 - 1 := by simp [unit]
    refine hpair x (x - unit 0) (fun e he => hcenterB e he _ _ (Or.inr (by omega)))
      ⟨0, Or.inr (sub_add_cancel x _).symm⟩ fun z hz => ⟨?_, ?_⟩
    · exact rpow_le_latticeL1Dist hN hz (Or.inl hx0.le)
    · exact rpow_le_latticeL1Dist hN hz (Or.inl (by omega))
  -- the sides
  have hsideb : |sideFlux (uniqueInfiniteComponent h) u0 N - sideFlux C' u' N| ≤
      CG * D * sidesSum (fun x y => ∑ z ∈ centerInner d N, pairKernel x y z) N := by
    unfold sideFlux
    rw [← sidesSum_const_mul]
    refine abs_sidesSum_sub_le fun j hj => ⟨fun x hx => ?_, fun x hx => ?_⟩
    · have hj0 : j ≠ 0 := Finset.ne_of_mem_erase hj
      have hxj : x j = N := (Finset.mem_filter.1 hx).2
      have hu0j : (x + unit j : Vertex d) 0 = x 0 := by simp [unit, hj0.symm]
      have hujj : (x + unit j : Vertex d) j = x j + 1 := by simp [unit]
      refine hpair x (x + unit j) (fun e he => hcenterB e he _ _ (Or.inl hu0j.symm))
        ⟨j, Or.inl rfl⟩ fun z hz => ⟨?_, ?_⟩
      · exact rpow_le_latticeL1Dist hN hz (Or.inr ⟨j, hj0, by rw [hxj, abs_of_nonneg (by omega)]⟩)
      · exact rpow_le_latticeL1Dist hN hz
          (Or.inr ⟨j, hj0, by rw [hujj, hxj, abs_of_nonneg (by omega)]; omega⟩)
    · have hj0 : j ≠ 0 := Finset.ne_of_mem_erase hj
      have hxj : x j = -(N : ℤ) := (Finset.mem_filter.1 hx).2
      have hu0j : (x - unit j : Vertex d) 0 = x 0 := by simp [unit, hj0.symm]
      have hujj : (x - unit j : Vertex d) j = x j - 1 := by simp [unit]
      refine hpair x (x - unit j) (fun e he => hcenterB e he _ _ (Or.inl hu0j.symm))
        ⟨j, Or.inr (sub_add_cancel x _).symm⟩ fun z hz => ⟨?_, ?_⟩
      · exact rpow_le_latticeL1Dist hN hz (Or.inr ⟨j, hj0, by rw [hxj, abs_of_nonpos (by omega)]; omega⟩)
      · exact rpow_le_latticeL1Dist hN hz
          (Or.inr ⟨j, hj0, by rw [hujj, hxj, abs_of_nonpos (by omega)]; omega⟩)
  -- the centre plane: removed edges and bridges carry no flux, the others at most `L`
  have hcenter : |centerFlux C' u' N| ≤
      L * ((((centerFace d N).filter fun x => centerBond x ∉ H).card : ℕ) : ℝ) := by
    unfold centerFlux centerSum
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ x ∈ centerFace d N, |edgeDifference C' u' x (x + unit 0)|
        ≤ ∑ x ∈ centerFace d N, (if centerBond x ∉ H then L else 0) :=
          Finset.sum_le_sum fun x _ => ?_
      _ = L * ((((centerFace d N).filter fun x => centerBond x ∉ H).card : ℕ) : ℝ) := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    split_ifs with hxH
    swap
    · exact abs_edgeDifference_le C' hL hLip' x _
    · by_cases hc : x ∈ C'.supp ∧ (openGraph (closeBonds B ω)).Adj x (x + unit 0)
      · obtain ⟨hx', hadj'⟩ := hc
        have hadj := adj_of_adj_closeBonds hadj'
        have hxC : x ∈ (uniqueInfiniteComponent h).supp := (hsupp' x).1 hx'
        have hx1C : x + unit 0 ∈ (uniqueInfiniteComponent h).supp := (uniqueInfiniteComponent h).mem_supp_of_adj_mem_supp hxC hadj
        have hωe : ω (centerBond x) = true := hadj.2
        have hnB : centerBond x ∉ B := fun hB => not_adj_closeBonds hB rfl hadj'
        have hH'mem : centerBond x ∈ H' := Finset.mem_filter.2 ⟨hxH, hωe, fun w hw => by
          rcases Sym2.mem_iff.1 hw with rfl | rfl
          · exact hxC
          · exact hx1C⟩
        have hsep := hBbr _ hH'mem hnB x (x + unit 0) rfl
        have hx1' : x + unit 0 ∈ C'.supp := C'.mem_supp_of_adj_mem_supp hx' hadj'
        have hωe' : closeBonds B ω (centerBond x) = true := by
          unfold closeBonds
          rw [if_neg hnB]
          exact hωe
        have heq := hBr (closeBonds B ω) C' u' hharm' (centerBond x) ⟨x, hx'⟩ ⟨x + unit 0, hx1'⟩
          rfl hωe' (by rw [closeBonds_singleton_closeBonds]; exact hUq _)
          (by rw [closeBonds_singleton_closeBonds]; exact hsep)
        rw [edgeDifference_of_adj C' u' hx' hadj', heq, sub_self, abs_zero]
      · rw [edgeDifference, if_neg hc, abs_zero]
  -- the divergence identity and the final count
  have hdiv := hDiv (closeBonds B ω) C' u' hharm' N
  have hCGD : 0 ≤ CG * D := mul_nonneg hCG.le hD0
  have hker' := mul_le_mul_of_nonneg_left hker hCGD
  rw [mul_add] at hker'
  have hct' := mul_le_mul_of_nonneg_left hHct hL
  have h1 := abs_le.1 hleftb
  have h2 := abs_le.1 hsideb
  have h3 := abs_le.1 hcenter
  have h4 := abs_le.1 hside
  linarith

/-- The final arithmetic of `step:3.2-contradiction`: the error terms are `o(N^{d-1})`. -/
theorem eventually_flux_arith (a c₁ c₂ : ℝ) (ha : 0 < a) :
    ∀ᶠ N : ℕ in atTop,
      c₁ * (N : ℝ) ^ ((d : ℝ) - 1 - 1 / (10 * (d : ℝ)) + 1 / (10 * (d : ℝ)) ^ 2) +
        c₂ * ((N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ ((d : ℝ) - 2 + 1 / 4)) <
      a * (N : ℝ) ^ ((d : ℝ) - 1) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
  set η : ℝ := 1 / (10 * (d : ℝ)) - 1 / (10 * (d : ℝ)) ^ 2 with hη
  have hηpos : 0 < η := by
    rw [hη, sub_pos]
    exact one_div_lt_one_div_of_lt (by positivity) (by nlinarith)
  have hlim : Tendsto (fun N : ℕ => c₁ * (N : ℝ) ^ (-η) + c₂ * (N : ℝ) ^ (-(1 / 4 : ℝ))) atTop
      (𝓝 (c₁ * 0 + c₂ * 0)) :=
    (((tendsto_rpow_neg_atTop hηpos).comp tendsto_natCast_atTop_atTop).const_mul c₁).add
      (((tendsto_rpow_neg_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop).const_mul c₂)
  rw [mul_zero, mul_zero, add_zero] at hlim
  filter_upwards [hlim.eventually_lt_const ha, eventually_ge_atTop 1] with N hN hN1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have e1 : (N : ℝ) ^ ((d : ℝ) - 1 - 1 / (10 * (d : ℝ)) + 1 / (10 * (d : ℝ)) ^ 2) =
      (N : ℝ) ^ ((d : ℝ) - 1) * (N : ℝ) ^ (-η) := by
    rw [← Real.rpow_add hNpos, hη]
    congr 1
    ring
  have e2 : (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ ((d : ℝ) - 2 + 1 / 4) =
      (N : ℝ) ^ ((d : ℝ) - 1) * (N : ℝ) ^ (-(1 / 4 : ℝ)) := by
    rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
    congr 1
    ring
  have hP : 0 < (N : ℝ) ^ ((d : ℝ) - 1) := Real.rpow_pos_of_pos hNpos _
  have hN' : c₁ * (N : ℝ) ^ (-η) + c₂ * (N : ℝ) ^ (-(1 / 4 : ℝ)) < a := hN
  rw [e1, e2]
  nlinarith

/-- A point outside three sets whose measures sum to less than one, at which an almost sure
property holds. -/
theorem exists_notMem_of_measure_lt {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {A₁ A₂ A₃ : Set α} {q : α → Prop} (h : μ A₁ + μ A₂ + μ A₃ < 1)
    (hq : ∀ᵐ x ∂μ, q x) : ∃ x, x ∉ A₁ ∧ x ∉ A₂ ∧ x ∉ A₃ ∧ q x := by
  by_contra hcon
  have hsub : (Set.univ : Set α) ⊆ A₁ ∪ A₂ ∪ A₃ ∪ {x | ¬ q x} := by
    intro x _
    by_cases h1 : x ∈ A₁
    · exact Or.inl (Or.inl (Or.inl h1))
    by_cases h2 : x ∈ A₂
    · exact Or.inl (Or.inl (Or.inr h2))
    by_cases h3 : x ∈ A₃
    · exact Or.inl (Or.inr h3)
    exact Or.inr fun hqx => hcon ⟨x, h1, h2, h3, hqx⟩
  have hq0 : μ {x | ¬ q x} = 0 := ae_iff.1 hq
  have : (1 : ℝ≥0∞) < 1 := calc
    (1 : ℝ≥0∞) = μ Set.univ := measure_univ.symm
    _ ≤ μ (A₁ ∪ A₂ ∪ A₃ ∪ {x | ¬ q x}) := measure_mono hsub
    _ ≤ μ A₁ + μ A₂ + μ A₃ + μ {x | ¬ q x} := by
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        exact measure_union_le _ _
    _ = μ A₁ + μ A₂ + μ A₃ := by rw [hq0, add_zero]
    _ < 1 := h
  exact lt_irrefl _ this

/-- The first assertion of Proposition 3.2, by contradiction: if `|∇ℓ_{e₁}(0)| ≤ L` almost surely,
some configuration of the event `E_N` satisfies the hypotheses of `false_of_steps_at`. -/
theorem originGradient_of_steps (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hW : Rigidity.External.WellConnectedInput)
    (hginput : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hreg : LatticeProb.External.ArmstrongDarioOrderZero)
    (hclassical : LatticeProb.External.SupercriticalBondUniqueness)
    (h33 : Section3.CompareDifferentPlanesStmt d hd p)
    (hEdge : EdgeGradientStep d p) (hFE : FiniteEnergyStep d p) (hCU : ClosedBondsUniqueStep d p)
    (hWC : WellConnectedEventStep d p) (hGS : GreenScaleEventStep d p)
    (hFlux : FluxEventStep d p) (hRem : RemovalStep d) (hSP : ShortPathsStep d)
    (hDiv : DivergenceStep d) (hBr : BridgeFluxStep d) (hKer : GreenKernelSumStep d)
    (L : ℝ) (hL : 0 ≤ L) :
    latticeBondLaw d p {ω | ∃ h : HasUniqueInfiniteOpenComponent ω,
        ∃ ho : (0 : Vertex d) ∈ (uniqueInfiniteComponent h).supp,
        ∃ u, IsCorrectedPlane (uniqueInfiniteComponent h) (slopeE1 d) u ∧
          L < originGradientNorm (uniqueInfiniteComponent h) ho u} ≠ 0 := by
  intro h0
  have hLipae := hFE hp1 L (hEdge L h0)
  have hUqae := hCU hp1 (hclassical.2 d hd p hpc hp1)
  obtain ⟨s, CG, hs, hCG, hMG⟩ :=
    Rigidity.Support.mixed_green hginput hreg d hd p hpc hp1 (1 / 4) (by norm_num)
  choose M hMmeas _hM1 hMint hMle hMae using hMG
  have hMae' := ae_all_iff.2 hMae
  obtain ⟨a, ha, hfl⟩ := hFlux hd hpc hp1
  obtain ⟨Ksp, hKsp, H, hH⟩ := hSP hd
  obtain ⟨Kker, hKker⟩ := hKer hd
  have hsum := ((hWC hW hd hpc hp1).add (hGS s CG hs hCG M hMmeas hMint hMle)).add
    (hfl (a / 2) (by positivity))
  rw [add_zero, add_zero] at hsum
  obtain ⟨N, hN1, hNprob, hNH, hNker, hNarith⟩ := ((eventually_ge_atTop 1).and
    ((hsum.eventually_lt_const zero_lt_one).and (hH.and (hKker.and
      (eventually_flux_arith (d := d) (a / 2) (L * Ksp) (CG * L * Ksp * Kker)
        (by positivity)))))).exists
  obtain ⟨ω, hω1, hω2, hω3, hLipω, hUqω, ⟨h1, h33ω⟩, hMω⟩ :=
    exists_notMem_of_measure_lt hNprob (hLipae.and (hUqae.and (h33.and hMae')))
  obtain ⟨h, u0, hu0, hleft, hside⟩ := not_not.1 hω3
  obtain ⟨hNHc, hNHct, hNHsp⟩ := hNH
  have hgr : ∀ y ∈ latticeCube d N, M y ω ≤ (N : ℝ) ^ (1 / (10 * (d : ℝ) ^ 2)) :=
    fun y hy => not_lt.1 fun hlt => hω2 ⟨y, hy, hlt⟩
  refine false_of_steps_at hd hRem hDiv hBr (ε := a / 2) hL hCG hKsp hN1 (H N) hNHc hNHct
    hNker ?_ h (hNHsp ω (not_not.1 hω1) _ (uniqueInfiniteComponent_infinite h)) hUqω hLipω h33ω
    (fun y => M y ω) hgr (fun y hy g hg x hx => (hMω y).elim fun _ hall => hall h hy g hg x hx)
    u0 hu0 hleft hside
  linarith

/-- **Proposition 3.2** from its steps, Lemma 3.3 and the cited inputs: Proposition 2.3
(well-connected cubes), the two cited inputs of Proposition 2.8 (mixed derivative of the Green
function), the existence and uniqueness of the infinite cluster, and the first-order correctors
(`SupercriticalBondCorrectorInput`), which turn the positive outer measure given by the
contradiction argument into the inner-measure form of the draft statement
(`notLipschitzStmt_of_originGradient`). -/
theorem notLipschitz_of_steps (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hW : Rigidity.External.WellConnectedInput)
    (hginput : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hreg : LatticeProb.External.ArmstrongDarioOrderZero)
    (hclassical : LatticeProb.External.SupercriticalBondUniqueness)
    (hcorrector : LatticeProb.External.SupercriticalBondCorrectorInput)
    (h33 : Section3.CompareDifferentPlanesStmt d hd p)
    (hEdge : EdgeGradientStep d p) (hFE : FiniteEnergyStep d p) (hCU : ClosedBondsUniqueStep d p)
    (hWC : WellConnectedEventStep d p) (hGS : GreenScaleEventStep d p)
    (hFlux : FluxEventStep d p) (hRem : RemovalStep d) (hSP : ShortPathsStep d)
    (hDiv : DivergenceStep d) (hBr : BridgeFluxStep d) (hKer : GreenKernelSumStep d) :
    Section3.NotLipschitzStmt d p :=
  notLipschitzStmt_of_originGradient hclassical hcorrector hd hpc hp1 fun L hL =>
    originGradient_of_steps hd p hpc hp1 hW hginput hreg hclassical h33 hEdge hFE hCU hWC hGS
      hFlux hRem hSP hDiv hBr hKer L (by linarith)

end Assembly

end Rigidity.Steps.S3
