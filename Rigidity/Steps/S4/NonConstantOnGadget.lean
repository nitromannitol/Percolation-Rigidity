import Rigidity.Draft.Section4Statements
import Rigidity.External.WellConnected
import LatticeProb.Prob.Percolation.LatticeHarmonicGrowth

/-!
# Lemma 4.8: the steps of the attachment of a gadget

Lemma 4.8 (paper L1358-1366, proof L1398-1418 of the corrected draft) is carved into the
following steps, for a deterministic slope `q ≠ 0`.

* `step:4.8-event` (`EventStep`): the event `E_R` (`Q_R` is well-connected, Proposition 2.3, and
  every nonconstant function of `A₁(𝒞_∞)` takes more than one value on `Q_R ∩ 𝒞_∞`, Theorem 2.4)
  has probability at least `1/2` for every large `R`.
* `step:4.8-closed-boundary` (`ClosedBoundaryStep`): on `E_R`, after closing every bond meeting
  `Q_R`, the infinite cluster `𝒞̃_∞` carries a corrected plane `ℓ̃_q` separating two sites `x̃, ỹ`
  which share an edge with two distinct sites `x, y` of `Q_R`.
* `step:4.8-attach` (`AttachGeometryStep`, `AttachStep`, Figure `attach-gadget`): a deterministic
  bond set `H R x y` of `Q_R` (paths `P₁, P₂` from `x, y` and a translated copy of the gadget of
  height `R` as an induced subgraph, isolated: inside `Q_{R-1}` and attached at its terminals only,
  `IsIsolatedGadget`) such that opening exactly `H R x y` and the bonds `x x̃`,
  `y ỹ` near `Q_R` gives `𝒞_∞ ∩ Q_R = H R x y` with `ℓ_q` not constant on the gadget.
* `step:4.8-union` (`PlacementCountStep`): there are at most `C R^{d-1}` boundary placements
  `(x, x̃)`, hence at most `C² R^{2d-2}` pairs; the union bound is made in
  `nonConstantOnGadget_of_steps`.

GAP (`ConditioningStep`). The last sentence of the proof (L1417, "by taking a union bound ... we
have the desired claim") identifies the conditional law given `𝒞_∞ ∩ Q_R = H` with the law in
which the bonds near `Q_R` are fixed and the outside bonds are free. The union bound gives a
placement whose attachment event `W` (an event of the outside bonds) has `P[W] ≥ c R^{-2d+2}`, and
`P[𝒞_∞ ∩ Q_R = H, ℓ_q not constant on the gadget] ≥ P[bonds near Q_R as in the attachment] P[W]`.
Conditioning on `𝒞_∞ ∩ Q_R = H` reweights the outside bonds by the probability of the inner
configurations compatible with `H`, which ranges over a factor `(1 - p)^{-O(R^d)}`; the paper does
not compare the two laws. `ConditioningStep` states the comparison needed for the uniform constant
of Lemma 4.8; it is not proved in the paper. Lemma 4.7 only uses the joint lower bound.
The draft statement `Rigidity.Section4.NonConstantOnGadgetStmt` is Lemma 4.8 as printed (the
conditional form). It is proved without `ConditioningStep`, by averaging over `H`
(`Rigidity.Proofs.S4.OuterNonConstant.nonConstantOnGadget`); `ConditioningStep` and
`nonConstantOnGadget_of_steps` are not used in that proof. The joint form with the isolated gadget
is the proved support result `NonConstantOnGadgetJointStmt` (`NonConstantOnGadgetJoint.lean`).

The cited inputs are used in the proofs of the steps, not in the assembly:
`Rigidity.External.WellConnectedInput` (Proposition 2.3) and
`LatticeProb.External.ArmstrongDarioOrderZero` (Theorem 2.4) for `EventStep`, Theorem 2.4 and
`LatticeProb.External.SupercriticalBondCorrectorInput` (corrected planes) for the Liouville
arguments of `ClosedBoundaryStep` and `AttachStep`, on the finitely modified environments.
-/

namespace Rigidity.Steps.S4

open MeasureTheory LatticeProb.Percolation LatticeProb.Network Rigidity.Section4

variable {d : ℕ}

/-- The bonds with an endpoint in `Q_R`. -/
def bondsNear (d R : ℕ) : Set (Bond d) :=
  {e | ∃ z ∈ (e : Sym2 (Vertex d)), z ∈ cube d R}

open scoped Classical in
/-- The environment `ω` with every bond meeting `Q_R` closed. The paper closes the bonds containing
a site of `∂Q_R`; the two environments have the same clusters outside `Q_R`. -/
noncomputable def closedNear (R : ℕ) (ω : Configuration d) : Configuration d :=
  fun e => if e ∈ bondsNear d R then false else ω e

open scoped Classical in
/-- The environment `ω` with the bonds meeting `Q_R` open exactly on `F`. -/
noncomputable def attachConfig (R : ℕ) (F : Set (Bond d)) (ω : Configuration d) : Configuration d :=
  fun e => if e ∈ bondsNear d R then decide (e ∈ F) else ω e

/-- The boundary placements `(x, x̃)`: a site `x ∈ Q_R` and a lattice neighbour `x̃ ∉ Q_R`. -/
def boundaryPairs (d R : ℕ) : Set (Vertex d × Vertex d) :=
  {z | z.1 ∈ cube d R ∧ z.2 ∉ cube d R ∧ (nearestNeighborGraph d).Adj z.1 z.2}

/-- The conditioning event `𝒞_∞ ∩ Q_R = H` of Lemma 4.8, in terms of the bonds of the cluster. -/
def conditioningEvent (d R : ℕ) (H : Set (Bond d)) : Set (Configuration d) :=
  {ω | ∃ h : HasUniqueInfiniteOpenComponent ω,
    componentBondsIn (uniqueInfiniteComponent h) (cube d R) = H}

/-- The event that a corrected plane `ℓ_q` of the unique infinite cluster is not constant on the
gadget of height `R` translated by `τ`. -/
def gadgetNonconstantEvent (hd : 2 ≤ d) (q : Fin d → ℝ) (R : ℕ) (τ : Vertex d) :
    Set (Configuration d) :=
  {ω | ∃ h : HasUniqueInfiniteOpenComponent ω,
    ∃ u, IsCorrectedPlane (uniqueInfiniteComponent h) q u ∧
      ∃ x ∈ OpenLadder.Embedding.ambientSites hd (R : ℤ),
      ∃ y ∈ OpenLadder.Embedding.ambientSites hd (R : ℤ),
      ∃ hx : τ + x ∈ (uniqueInfiniteComponent h).supp,
      ∃ hy : τ + y ∈ (uniqueInfiniteComponent h).supp,
        u ⟨τ + x, hx⟩ ≠ u ⟨τ + y, hy⟩}

/-- `H` is a bond set of `Q_R` containing the gadget of height `R` translated by `τ` inside `Q_R`,
as an induced subgraph. -/
def IsGadgetPlacement (hd : 2 ≤ d) (R : ℕ) (H : Set (Bond d)) (τ : Vertex d) : Prop :=
  (∀ e ∈ H, ∀ z ∈ (e : Sym2 (Vertex d)), z ∈ cube d R) ∧
    (∀ x ∈ OpenLadder.Embedding.ambientSites hd (R : ℤ), τ + x ∈ cube d R) ∧
    ∀ x (hx : x ∈ OpenLadder.Embedding.ambientSites hd (R : ℤ))
      y (hy : y ∈ OpenLadder.Embedding.ambientSites hd (R : ℤ))
      (hxy : (nearestNeighborGraph d).Adj (τ + x) (τ + y)),
      bondOfAdjacent hxy ∈ H ↔
        (OpenLadder.Embedding.ambientGraph hd (R : ℤ)).Adj ⟨x, hx⟩ ⟨y, hy⟩

/-- The event `E_R`: `Q_R` is well-connected (Proposition 2.3), and every nonconstant function of
`A₁(𝒞_∞)` takes more than one value on `Q_R ∩ 𝒞_∞`. -/
def goodCubeEvent (d R : ℕ) : Set (Configuration d) :=
  {ω | External.IsWellConnected ω 0 R ∧ ∃ h : HasUniqueInfiniteOpenComponent ω,
    ∀ u ∈ harmonicGrowthSpace (uniqueInfiniteComponent h) 1, (∃ x y, u x ≠ u y) →
      ∃ x y : uniqueInfiniteComponent h, x.1 ∈ cube d R ∧ y.1 ∈ cube d R ∧ u x ≠ u y}

/-- The sites `x', y'` lie in the unique infinite cluster `𝒞̃_∞` of the environment `closedNear R ω`
and a corrected plane `ℓ̃_q` of `𝒞̃_∞` separates them. -/
def IsClosedBoundaryWitness (R : ℕ) (q : Fin d → ℝ) (ω : Configuration d) (x' y' : Vertex d) :
    Prop :=
  ∃ h : HasUniqueInfiniteOpenComponent (closedNear R ω),
    ∃ hx : x' ∈ (uniqueInfiniteComponent h).supp, ∃ hy : y' ∈ (uniqueInfiniteComponent h).supp,
    ∃ u, IsCorrectedPlane (uniqueInfiniteComponent h) q u ∧ u ⟨x', hx⟩ ≠ u ⟨y', hy⟩

/-- The bonds opened near `Q_R` by the attachment: `H` and the two bonds `x x'`, `y y'`. -/
def attachBonds (H : Set (Bond d)) (x x' y y' : Vertex d) : Set (Bond d) :=
  H ∪ {e | (e : Sym2 (Vertex d)) = s(x, x') ∨ (e : Sym2 (Vertex d)) = s(y, y')}

/-- The attachment event `W` of the placement `(x, x'), (y, y')`, an event of the bonds away from
`Q_R`: opening exactly `attachBonds (H R x y) x x' y y'` near `Q_R` gives `𝒞_∞ ∩ Q_R = H R x y`
and a corrected plane `ℓ_q` not constant on the gadget translated by `τ R`. -/
def attachEvent (hd : 2 ≤ d) (q : Fin d → ℝ) (H : ℕ → Vertex d → Vertex d → Set (Bond d))
    (τ : ℕ → Vertex d) (R : ℕ) (x x' y y' : Vertex d) : Set (Configuration d) :=
  {ω | attachConfig R (attachBonds (H R x y) x x' y y') ω ∈
    conditioningEvent d R (H R x y) ∩ gadgetNonconstantEvent hd q R (τ R)}

/-- Step `step:4.8-event` (paper L1399-1404): by Proposition 2.3 and Theorem 2.4 the event `E_R`
has probability at least `1/2` for every large `R`. -/
def EventStep (d : ℕ) (p : unitInterval) : Prop :=
  ∃ R₁ : ℕ, ∀ R : ℕ, R₁ ≤ R → (1 / 2 : ℝ) ≤ (latticeBondLaw d p (goodCubeEvent d R)).toReal

/-- Step `step:4.8-closed-boundary` (paper L1406-1411): almost surely on `E_R`, closing every bond
meeting `Q_R` leaves a unique infinite cluster `𝒞̃_∞ ⊆ 𝒞_∞` whose corrected plane `ℓ̃_q` is not
constant on the sites of `𝒞̃_∞` next to `Q_R ∩ 𝒞_∞` (else `ℓ_q - ℓ̃_q`, with `ℓ̃_q` extended by a
constant, is a nonconstant sublinear harmonic function, against Theorem 2.4): there are boundary
placements `(x, x̃), (y, ỹ)` with `x ≠ y` and `ℓ̃_q(x̃) ≠ ℓ̃_q(ỹ)`. -/
def ClosedBoundaryStep (d : ℕ) (p : unitInterval) (q : Fin d → ℝ) : Prop :=
  ∀ R : ℕ, ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ goodCubeEvent d R →
    ∃ x x' y y' : Vertex d, (x, x') ∈ boundaryPairs d R ∧ (y, y') ∈ boundaryPairs d R ∧
      x ≠ y ∧ IsClosedBoundaryWitness R q ω x' y'

/-- The gadget of height `R` translated by `τ` is isolated in `H`: it lies in `Q_{R-1}`, and every
bond of `H` at a gadget site other than the terminals `s = (1, 1)`, `t = (4, 1)` joins two gadget
sites. This is what Proposition 4.1 ([C9]: harmonic for the graph induced on the gadget at every
non-terminal site) needs of `ℓ_q` restricted to the gadget, when `𝒞_∞ ∩ Q_R = H` (Lemma 4.8). -/
def IsIsolatedGadget (hd : 2 ≤ d) (R : ℕ) (H : Set (Bond d)) (τ : Vertex d) : Prop :=
  (∀ x ∈ OpenLadder.Embedding.ambientSites hd (R : ℤ), τ + x ∈ cube d (R - 1)) ∧
    ∀ e ∈ H, ∀ x ∈ OpenLadder.Embedding.ambientSites hd (R : ℤ),
      x ≠ OpenLadder.Embedding.zeroPad d (1, 1) → x ≠ OpenLadder.Embedding.zeroPad d (4, 1) →
      τ + x ∈ (e : Sym2 (Vertex d)) → ∀ z ∈ (e : Sym2 (Vertex d)),
        ∃ y ∈ OpenLadder.Embedding.ambientSites hd (R : ℤ), z = τ + y

/-- Step `step:4.8-attach`, geometry (paper L1411-1413, Figure `attach-gadget`): for large `R` and
boundary placements `(x, x̃), (y, ỹ)` with `x ≠ y`, the bond set `H R x y` of `Q_R` contains the
gadget of height `R` translated by `τ R`, as an induced subgraph, and the gadget is isolated in
`H R x y` (inside `Q_{R-1}`, the paths `P₁, P₂` attached at the terminals only). -/
def AttachGeometryStep (hd : 2 ≤ d) (H : ℕ → Vertex d → Vertex d → Set (Bond d))
    (τ : ℕ → Vertex d) : Prop :=
  ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → ∀ x x' y y' : Vertex d, (x, x') ∈ boundaryPairs d R →
    (y, y') ∈ boundaryPairs d R → x ≠ y →
      IsGadgetPlacement hd R (H R x y) (τ R) ∧ IsIsolatedGadget hd R (H R x y) (τ R)

/-- Step `step:4.8-attach`, Liouville argument (paper L1415): almost surely, for every pair of
boundary placements with `x ≠ y` separated by a corrected plane `ℓ̃_q` of the closed environment,
the attachment of `H R x y` through the bonds `x x̃`, `y ỹ` has `𝒞'_∞ ∩ Q_R = H R x y`, and its
corrected plane `ℓ'_q` is not constant on the gadget (else `ℓ'_q(x) = ℓ'_q(y)`, and `ℓ'_q - ℓ̃_q`
on `𝒞̃_∞` is a nonconstant sublinear harmonic function, against Theorem 2.4). -/
def AttachStep (hd : 2 ≤ d) (p : unitInterval) (q : Fin d → ℝ)
    (H : ℕ → Vertex d → Vertex d → Set (Bond d)) (τ : ℕ → Vertex d) : Prop :=
  ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → ∀ᵐ ω ∂latticeBondLaw d p, ∀ x x' y y' : Vertex d,
    (x, x') ∈ boundaryPairs d R → (y, y') ∈ boundaryPairs d R → x ≠ y →
      IsClosedBoundaryWitness R q ω x' y' → ω ∈ attachEvent hd q H τ R x x' y y'

/-- Step `step:4.8-union` (paper L1417): there are at most `C R^{d-1}` boundary placements
`(x, x̃)` of `Q_R`, hence at most `C² R^{2d-2}` pairs of them. -/
def PlacementCountStep (d : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ R : ℕ, 1 ≤ R →
    (boundaryPairs d R).Finite ∧ ((boundaryPairs d R).ncard : ℝ) ≤ C * (R : ℝ) ^ (d - 1)

/-- Not used in the proof of Lemma 4.8, which averages over `H`
(`Rigidity.Proofs.S4.OuterNonConstant.nonConstantOnGadget`).
GAP, not proved in the paper (see the module docstring): conditioning on
`𝒞_∞ ∩ Q_R = H R x y` costs at most a constant factor `c₀` against the probability of the
attachment event, an event of the bonds away from `Q_R`. The paper's last sentence (L1417)
identifies the two laws. -/
def ConditioningStep (hd : 2 ≤ d) (p : unitInterval) (q : Fin d → ℝ)
    (H : ℕ → Vertex d → Vertex d → Set (Bond d)) (τ : ℕ → Vertex d) : Prop :=
  ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → ∀ x x' y y' : Vertex d,
    (x, x') ∈ boundaryPairs d R → (y, y') ∈ boundaryPairs d R → x ≠ y →
      c₀ * (latticeBondLaw d p (attachEvent hd q H τ R x x' y y')).toReal ≤
        (latticeBondLaw d p
            (conditioningEvent d R (H R x y) ∩ gadgetNonconstantEvent hd q R (τ R)) /
          latticeBondLaw d p (conditioningEvent d R (H R x y))).toReal

/-- The zpow `R^{-2d+2}` of Lemma 4.8 is the inverse of `R^{2d-2}`. -/
theorem zpow_neg_two_mul_add_two (hd : 2 ≤ d) (R : ℝ) :
    R ^ (-(2 * (d : ℤ)) + 2) = (R ^ (2 * d - 2))⁻¹ := by
  have h : -(2 * (d : ℤ)) + 2 = -((2 * d - 2 : ℕ) : ℤ) := by omega
  rw [h, zpow_neg, zpow_natCast]

/-- **Lemma 4.8** (`Rigidity.Section4.NonConstantOnGadgetStmt`, the printed conditional form) from
its steps, for a construction `H, τ` of the attached gadget, through the unproved comparison
`ConditioningStep`. Lemma 4.8 itself is proved without `ConditioningStep` in
`Rigidity.Proofs.S4.OuterNonConstant`. -/
theorem nonConstantOnGadget_of_steps [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (_hpc : criticalProbability d < (p : ℝ)) (_hp1 : (p : ℝ) < 1)
    (H : ℕ → Vertex d → Vertex d → Set (Bond d)) (τ : ℕ → Vertex d)
    (hevent : EventStep d p) (hclosed : ∀ q : Fin d → ℝ, q ≠ 0 → ClosedBoundaryStep d p q)
    (hgeom : AttachGeometryStep hd H τ)
    (hattach : ∀ q : Fin d → ℝ, q ≠ 0 → AttachStep hd p q H τ)
    (hcount : PlacementCountStep d)
    (hcond : ∀ q : Fin d → ℝ, q ≠ 0 → ConditioningStep hd p q H τ) :
    NonConstantOnGadgetStmt d hd p := by
  intro q hq
  obtain ⟨R₁, hR₁⟩ := hevent
  obtain ⟨R₂, hR₂⟩ := hgeom
  obtain ⟨R₃, hR₃⟩ := hattach q hq
  obtain ⟨C, hC, hCR⟩ := hcount
  obtain ⟨c₀, hc₀, R₄, hR₄⟩ := hcond q hq
  refine ⟨c₀ / (2 * C ^ 2), by positivity, max (max R₁ R₂) (max (max R₃ R₄) 1),
    fun R hR => ?_⟩
  simp only [max_le_iff] at hR
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩ := hR
  obtain ⟨hfin, hcard⟩ := hCR R h5
  set μ := latticeBondLaw d p with hμ
  -- the finite set of placements, and the union bound
  obtain ⟨s, hs⟩ : ∃ s : Finset ((Vertex d × Vertex d) × (Vertex d × Vertex d)),
      s = ((hfin.prod hfin).toFinset).filter (fun i => i.1.1 ≠ i.2.1) := ⟨_, rfl⟩
  let W : (Vertex d × Vertex d) × (Vertex d × Vertex d) → Set (Configuration d) :=
    fun i => attachEvent hd q H τ R i.1.1 i.1.2 i.2.1 i.2.2
  have hsub : ∀ᵐ ω ∂μ, ω ∈ goodCubeEvent d R → ω ∈ ⋃ i ∈ s, W i := by
    filter_upwards [hclosed q hq R, hR₃ R h3] with ω hω hω' hE
    obtain ⟨x, x', y, y', hx, hy, hxy, hwit⟩ := hω hE
    refine Set.mem_iUnion₂.mpr ⟨((x, x'), (y, y')), ?_, hω' x x' y y' hx hy hxy hwit⟩
    rw [hs, Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨Set.mk_mem_prod hx hy, hxy⟩
  have hhalf : (1 / 2 : ℝ) ≤ ∑ i ∈ s, (μ (W i)).toReal :=
    calc (1 / 2 : ℝ) ≤ (μ (goodCubeEvent d R)).toReal := hR₁ R h1
      _ ≤ (μ (⋃ i ∈ s, W i)).toReal :=
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae (hsub.mono fun _ h => h))
      _ ≤ ∑ i ∈ s, (μ (W i)).toReal := measureReal_biUnion_finset_le s W
  have hsne : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro hempty
    rw [hempty, Finset.sum_empty] at hhalf
    norm_num at hhalf
  obtain ⟨⟨⟨x, x'⟩, ⟨y, y'⟩⟩, his, himax⟩ :=
    Finset.exists_max_image s (fun i => (μ (W i)).toReal) hsne
  have hW : (1 / 2 : ℝ) ≤ s.card * (μ (W ((x, x'), (y, y')))).toReal := by
    have := Finset.sum_le_card_nsmul s (fun i => (μ (W i)).toReal) _ himax
    rw [nsmul_eq_mul] at this
    exact hhalf.trans this
  have hcard_s : (s.card : ℝ) ≤ C ^ 2 * (R : ℝ) ^ (2 * d - 2) := by
    have hle : s.card ≤ hfin.toFinset.card * hfin.toFinset.card := by
      calc s.card ≤ (hfin.prod hfin).toFinset.card := hs ▸ Finset.card_filter_le _ _
        _ = hfin.toFinset.card * hfin.toFinset.card := by
          rw [← Set.Finite.toFinset_prod, Finset.card_product]
    have hC' : (hfin.toFinset.card : ℝ) ≤ C * (R : ℝ) ^ (d - 1) := by
      rwa [← Set.ncard_eq_toFinset_card _ hfin]
    have hpow : (R : ℝ) ^ (2 * d - 2) = ((R : ℝ) ^ (d - 1)) ^ 2 := by
      rw [← pow_mul]
      congr 1
      omega
    calc (s.card : ℝ) ≤ (hfin.toFinset.card : ℝ) * hfin.toFinset.card := by exact_mod_cast hle
      _ ≤ (C * (R : ℝ) ^ (d - 1)) * (C * (R : ℝ) ^ (d - 1)) :=
        mul_le_mul hC' hC' (by positivity) (by positivity)
      _ = C ^ 2 * (R : ℝ) ^ (2 * d - 2) := by rw [hpow]; ring
  rw [hs, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_prod] at his
  obtain ⟨⟨hx, hy⟩, hxy⟩ := his
  have hcondi := hR₄ R h4 x x' y y' hx hy hxy
  obtain ⟨⟨hHQ, hτQ, hind⟩, -⟩ := hR₂ R h2 x x' y y' hx hy hxy
  have hWnn : 0 ≤ (μ (W ((x, x'), (y, y')))).toReal := ENNReal.toReal_nonneg
  have hWpos : 0 < (μ (W ((x, x'), (y, y')))).toReal := by
    by_contra hneg
    have h0 : (μ (W ((x, x'), (y, y')))).toReal = 0 := le_antisymm (not_lt.mp hneg) hWnn
    rw [h0, mul_zero] at hW
    norm_num at hW
  have hApos : 0 < μ (conditioningEvent d R (H R x y)) := by
    rw [pos_iff_ne_zero]
    intro hA0
    have hAG : μ (conditioningEvent d R (H R x y) ∩ gadgetNonconstantEvent hd q R (τ R)) = 0 :=
      measure_mono_null Set.inter_subset_left hA0
    rw [hAG, hA0, ENNReal.zero_div, ENNReal.toReal_zero] at hcondi
    exact absurd hcondi (not_le.mpr (mul_pos hc₀ hWpos))
  refine ⟨H R x y, τ R, hHQ, hτQ, hind, hApos, ?_⟩
  have hR0 : (0 : ℝ) < (R : ℝ) ^ (2 * d - 2) := by
    have : (1 : ℝ) ≤ R := by exact_mod_cast h5
    positivity
  have hkey : 1 ≤ 2 * C ^ 2 * (R : ℝ) ^ (2 * d - 2) * (μ (W ((x, x'), (y, y')))).toReal := by
    nlinarith
  calc c₀ / (2 * C ^ 2) * (R : ℝ) ^ (-(2 * (d : ℤ)) + 2)
      = c₀ / (2 * C ^ 2 * (R : ℝ) ^ (2 * d - 2)) := by
        rw [zpow_neg_two_mul_add_two hd]
        field_simp
    _ ≤ c₀ * (μ (W ((x, x'), (y, y')))).toReal := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith
    _ ≤ _ := hcondi

end Rigidity.Steps.S4
