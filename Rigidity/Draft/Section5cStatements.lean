import Rigidity.Draft.Section5bStatements
import LatticeProb.Prob.Strassen.Defs
import LatticeProb.Prob.Percolation.LSSThinIsIncreasing

/-! Statements of the numbered results of Sections 5.3.2-5.3.3 (percolation estimates and the
good events, d = 2). They follow the corrected draft `paper/percolation-harmonic-corrected.tex`
(each correction is marked `% CORRECTION [Cn]` there).

* Convention: the statements (`…Stmt`) omit the regime `p_c(2) < p < 1`; the composed theorems
  (`Rigidity/Proofs/Assembly`) carry it as hypotheses `criticalProbability 2 < p` and `p < 1`.

* The event `E_R(x)` uses the constant `C_f` of Proposition 5.20; it is a parameter here, and the
  estimates on `E_R(x)` are stated for every value of it. Likewise the good event `G_1` depends on
  the constants `R`, `c_1` of Proposition 5.24, which are parameters.
* "Very good" boxes (Section 5.3.2): `x + Q_r` is well-connected (the definition before
  Proposition 2.3, with "side length `M`" read as radius `M`, as `size(Q_r) := r`) and contains
  horizontal and vertical Kesten channels, read as: with `w = ⌈√r⌉`, each of the `⌊(2r+1)/w⌋`
  consecutive bands of `w` rows (resp. columns) contains an open path, inside the band, that joins
  the two short end faces of the band (the sides of `x + Q_r` crossed in direction `i`). Ties for
  the largest cluster `𝒞_*` are left to the existential.
* [C23, C31] `G_1(x, K)` is universal over the paths `γ` of `𝒞_∞` from `x`: every such path with
  `|γ(end) - x| ≥ K` has `Σ 1_{E_R(γ(i))} ≥ c_1 |γ(end) - x|`.
* [C24] `G_2(x, K)` bounds `osc ℓ_{e₁}` on `Q_{R'}(x)` by `4R'`.
* [C32] `G_3(x, C_χ)` is direction-free: some edge `(x, y)` of `𝒞_∞` at `x` (not necessarily
  `(x, x + e₁)`) across which every corrected plane `ℓ_{e₁}` increases by at least `C_χ`.
* [C1] The triangle is `T_L = {x : x₁ ≥ |x₂|, x₁ ≤ L}`.
* Lemma 5.26 is stated for all parameters with `NullMeasurableSet` (the good event quantifies over
  the corrected planes of every environment; null-measurability is what the ergodic theorem uses).
* Lower bounds on probabilities of events not shown measurable are stated for a measurable subset;
  upper bounds bound the outer measure. -/

open MeasureTheory LatticeProb.Percolation Classical Filter Topology

namespace Rigidity.Section5

/-- The cube `x + Q_r`. -/
def cubeAt (x : Vertex 2) (r : ℕ) : Set (Vertex 2) := {y | ∀ i, |y i - x i| ≤ (r : ℤ)}

/-- The open edges with both endpoints in `B`. -/
def openIn (ω : Configuration 2) (B : Set (Vertex 2)) : SimpleGraph (Vertex 2) where
  Adj y z := (openGraph ω).Adj y z ∧ y ∈ B ∧ z ∈ B
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => (openGraph ω).loopless.irrefl _ h.1⟩

/-- `V` is a largest open cluster of the finite set `B`. -/
def IsLargestClusterIn (ω : Configuration 2) (B V : Set (Vertex 2)) : Prop :=
  (∃ x ∈ B, V = {y | (openIn ω B).Reachable x y}) ∧
    ∀ x ∈ B, {y | (openIn ω B).Reachable x y}.ncard ≤ V.ncard

/-- `V` meets both faces of `z + Q_r` in each coordinate direction. -/
def CrossesCube (z : Vertex 2) (r : ℕ) (V : Set (Vertex 2)) : Prop :=
  ∀ i : Fin 2, (∃ y ∈ V, y i = z i - r) ∧ (∃ y ∈ V, y i = z i + r)

/-- `z + Q_r` is crossing: some largest cluster `𝒞_*` of it crosses it. -/
def IsCrossingCube (ω : Configuration 2) (z : Vertex 2) (r : ℕ) : Prop :=
  ∃ V, IsLargestClusterIn ω (cubeAt z r) V ∧ CrossesCube z r V

/-- `z + Q_M` is crossing by a largest cluster `𝒞_*` to which every open path of length at least
`M/100` in the cube is connected inside the cube. -/
def IsGoodSubcube (ω : Configuration 2) (z : Vertex 2) (M : ℕ) : Prop :=
  ∃ V, IsLargestClusterIn ω (cubeAt z M) V ∧ CrossesCube z M V ∧
    ∀ (n : ℕ) (γ : Fin (n + 1) → Vertex 2), Function.Injective γ →
      (∀ i : Fin n, (openIn ω (cubeAt z M)).Adj (γ i.castSucc) (γ i.succ)) →
      (M : ℝ) / 100 ≤ n → ∃ y ∈ V, (openIn ω (cubeAt z M)).Reachable (γ 0) y

/-- `x + Q_R` is well-connected (the definition before Proposition 2.3, d = 2). -/
def IsWellConnected (ω : Configuration 2) (x : Vertex 2) (R : ℕ) : Prop :=
  (R : ℝ) ^ (1 / 400 : ℝ) ≤ R / 100 ∧ IsCrossingCube ω x R ∧
    ∀ (z : Vertex 2) (M : ℕ), (R : ℝ) ^ (1 / 400 : ℝ) / 2 ≤ M → (M : ℝ) ≤ R / 10 →
      (cubeAt z M ∩ cubeAt x R).Nonempty → IsGoodSubcube ω z M

/-- The band `j` of rows of `x + Q_r` (coordinate `k` restricted, the other free in the cube). -/
def band (x : Vertex 2) (r w j : ℕ) (k : Fin 2) : Set (Vertex 2) :=
  {y | y ∈ cubeAt x r ∧ x k - r + j * w ≤ y k ∧ y k ≤ x k - r + (j + 1) * w - 1}

/-- Kesten channels of `x + Q_r` across direction `i` (bands in the other coordinate `k`). -/
def HasKestenChannels (ω : Configuration 2) (x : Vertex 2) (r : ℕ) (i k : Fin 2) : Prop :=
  let w := Nat.ceil (Real.sqrt r)
  ∀ j : ℕ, j < (2 * r + 1) / w → ∃ y z, y ∈ band x r w j k ∧ z ∈ band x r w j k ∧
    y i = x i - r ∧ z i = x i + r ∧ (openIn ω (band x r w j k)).Reachable y z

/-- `x + Q_r` is very good: well-connected, with horizontal and vertical Kesten channels. -/
def IsVeryGood (ω : Configuration 2) (x : Vertex 2) (r : ℕ) : Prop :=
  IsWellConnected ω x r ∧ HasKestenChannels ω x r 0 1 ∧ HasKestenChannels ω x r 1 0

/-- The centre `(2R + 1) z` of the renormalized site `z`. -/
def renormCentre (R : ℕ) (z : ℤ × ℤ) : Vertex 2 := ![(2 * R + 1 : ℤ) * z.1, (2 * R + 1 : ℤ) * z.2]

/-- The renormalized percolation process of size `R`: the site `z` is open when
`(2R + 1) z + Q_{11R/10}` is very good. -/
noncomputable def renormField (R : ℕ) (ω : Configuration 2) : PlanarCarrier → Bool :=
  fun z => decide (IsVeryGood ω (renormCentre R z) (11 * R / 10))

/-- Lemma 5.23: there are `C, c, s > 0` such that for every `R ≥ 1` the renormalized percolation
process of size `R` stochastically dominates Bernoulli site percolation of parameter
`1 - C exp(-c R^s)`: it gives every measurable increasing event at least the Bernoulli
probability. -/
def RenormalizedDominationStmt (p : unitInterval) : Prop :=
  ∃ C c s : ℝ, 0 < C ∧ 0 < c ∧ 0 < s ∧ ∀ R : ℕ, 1 ≤ R →
    ∀ A : Set (PlanarCarrier → Bool), MeasurableSet A → LatticeProb.StrassenAux.IsIncreasingSet A →
      bernoulliFieldPlanar (min 1 (Real.toNNReal (1 - C * Real.exp (-(c * (R : ℝ) ^ s)))))
          (min_le_left _ _) A ≤ (latticeBondLaw 2 p).map (renormField R) A

/-- The event `E_R(x)` (eq. `def.eventE`): every finite connected `S ⊆ 𝒞_∞` with `x ∈ S` and
`diam S ≥ R` is connected to infinity by at least `C_f + 1` disjoint paths. It holds when
`x ∉ 𝒞_∞`. -/
def eventE (Cf : ℕ) (R : ℝ) (x : Vertex 2) : Set (Configuration 2) :=
  {ω | ∀ h : HasUniqueInfiniteOpenComponent ω, ∀ S : Set (uniqueInfiniteComponent h),
    S.Finite → IsConnectedSet _ S → (∃ y ∈ S, y.val = x) →
    (∃ y ∈ S, ∃ z ∈ S, R ≤ l1 (y.val - z.val)) → HasDisjointPathsToInfinity _ S (Cf + 1)}

/-- Proposition 5.21: there is an exponent `s > 0` such that for every value of `C_f` there are
`C, c > 0` with `P(E_R(x)) ≥ 1 - C exp(-c R^s)` for all `x` and `R ≥ 1`. -/
def DisjointPathsToInfinityStmt (p : unitInterval) : Prop :=
  ∃ s : ℝ, 0 < s ∧ ∀ Cf : ℕ, ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (x : Vertex 2) (R : ℝ), 1 ≤ R →
    latticeBondLaw 2 p (eventE Cf R x)ᶜ ≤ ENNReal.ofReal (C * Real.exp (-(c * R ^ s)))

/-- The number of indices `1 ≤ i ≤ n` with `ω ∈ E_R(γ(i))`. -/
noncomputable def goodCount (ω : Configuration 2) (Cf : ℕ) (R : ℝ) {C : OpenComponent ω}
    {n : ℕ} (γ : Fin (n + 1) → C) : ℕ :=
  (Finset.univ.filter (fun i : Fin (n + 1) => i ≠ 0 ∧ ω ∈ eventE Cf R (γ i).val)).card

/-- `γ` is a path of `𝒞_∞`: injective, consecutive vertices adjacent. -/
def IsPathOf {ω : Configuration 2} (C : OpenComponent ω) {n : ℕ} (γ : Fin (n + 1) → C) : Prop :=
  Function.Injective γ ∧ ∀ i : Fin n, (componentGraph C).Adj (γ i.castSucc) (γ i.succ)

/-- The event of Proposition 5.24: a path of `𝒞_∞` from the origin reaching `|γ(end)| ≥ K` with
at most `c₁ |γ(end)|` of its sites in `E_R`. -/
def badPathEvent (Cf : ℕ) (R c₁ K : ℝ) : Set (Configuration 2) :=
  {ω | ∃ h : HasUniqueInfiniteOpenComponent ω, ∃ n : ℕ,
    ∃ γ : Fin (n + 1) → uniqueInfiniteComponent h, IsPathOf _ γ ∧ (γ 0).val = 0 ∧
      K ≤ l1 (γ (Fin.last n)).val ∧ (goodCount ω Cf R γ : ℝ) ≤ c₁ * l1 (γ (Fin.last n)).val}

/-- The conclusion of Proposition 5.24 for given `R` and `c₁`. -/
def LongPathBound (p : unitInterval) (Cf : ℕ) (R c₁ : ℝ) : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ K : ℝ, 1 ≤ K →
    latticeBondLaw 2 p (badPathEvent Cf R c₁ K) ≤ ENNReal.ofReal (C * Real.exp (-(c * K)))

/-- Proposition 5.24: for every value of `C_f` there is `R₁` such that for each `R ≥ R₁` some
`c₁ > 0` satisfies the bound `P(badPathEvent) ≤ C exp(-c K)` for all `K ≥ 1`. -/
def LongPathRenormalizedStmt (p : unitInterval) : Prop :=
  ∀ Cf : ℕ, ∃ R₁ : ℝ, ∀ R : ℝ, R₁ ≤ R → ∃ c₁ : ℝ, 0 < c₁ ∧ LongPathBound p Cf R c₁

/-- The first good event `G_1(x, K)` (eq. `defG1`, [C23], [C31]): every path `γ` of `𝒞_∞` from `x`
with `|γ(end) - x| ≥ K` has at least `c₁ |γ(end) - x|` of its sites in `E_R`. -/
def eventG1 (Cf : ℕ) (R c₁ : ℝ) (x : Vertex 2) (K : ℝ) : Set (Configuration 2) :=
  {ω | ∃ h : HasUniqueInfiniteOpenComponent ω, ∀ (n : ℕ)
    (γ : Fin (n + 1) → uniqueInfiniteComponent h), IsPathOf _ γ → (γ 0).val = x →
      K ≤ l1 ((γ (Fin.last n)).val - x) →
      c₁ * l1 ((γ (Fin.last n)).val - x) ≤ (goodCount ω Cf R γ : ℝ)}

/-- The unit vector `e₁`. -/
def e1 : Vertex 2 := Pi.single 0 1

/-- The second good event `G_2(x, K)` (eq. `corrector-oscillation`): for every `R' ≥ K`, the
oscillation of `ℓ_{e₁}` on `Q_{R'}(x) ∩ 𝒞_∞` is at most `4R'`. -/
def eventG2 (x : Vertex 2) (K : ℝ) : Set (Configuration 2) :=
  {ω | ∃ h : HasUniqueInfiniteOpenComponent ω, ∀ ℓ,
    IsCorrectedPlane (uniqueInfiniteComponent h) (Pi.single 0 1) ℓ →
    ∀ R' : ℕ, K ≤ R' → ∀ y z : uniqueInfiniteComponent h, y.val ∈ cubeAt x R' →
      z.val ∈ cubeAt x R' → ℓ y - ℓ z ≤ 4 * R'}

/-- The third good event `G_3(x, C_χ)` (eq. `not-lipschitz`, [C32]): `x` lies in `𝒞_∞` and has a
neighbour `y` in `𝒞_∞` across which every corrected plane `ℓ_{e₁}` increases by at least `C_χ`. -/
def eventG3 (x : Vertex 2) (Cχ : ℝ) : Set (Configuration 2) :=
  {ω | ∃ h : HasUniqueInfiniteOpenComponent ω, ∃ hx : x ∈ (uniqueInfiniteComponent h).supp,
    ∃ y : uniqueInfiniteComponent h, (componentGraph _).Adj ⟨x, hx⟩ y ∧
      ∀ ℓ, IsCorrectedPlane (uniqueInfiniteComponent h) (Pi.single 0 1) ℓ →
        Cχ ≤ ℓ y - ℓ ⟨x, hx⟩}

/-- The good event `G(x, C_χ, K) = G_1(x, K) ∩ G_2(x, K) ∩ G_3(x, C_χ)` (eq. `def-good-event`). -/
def eventG (Cf : ℕ) (R c₁ : ℝ) (x : Vertex 2) (Cχ K : ℝ) : Set (Configuration 2) :=
  eventG1 Cf R c₁ x K ∩ eventG2 x K ∩ eventG3 x Cχ

/-- Lemma 5.25: for every `C_χ ≥ 1` there is `c > 0` such that, for parameters `R, c₁` satisfying
the bound of Proposition 5.24, `P[G(x, C_χ, K)] ≥ c` for all `x` and all large `K`. -/
def GoodEventLowerBoundStmt (p : unitInterval) : Prop :=
  ∀ Cχ : ℝ, 1 ≤ Cχ → ∃ c : ℝ, 0 < c ∧ ∀ (Cf : ℕ) (R c₁ : ℝ), LongPathBound p Cf R c₁ →
    ∃ K₀ : ℝ, ∀ K : ℝ, K₀ ≤ K → ∀ x : Vertex 2, ∃ A ⊆ eventG Cf R c₁ x Cχ K,
      MeasurableSet A ∧ ENNReal.ofReal c ≤ latticeBondLaw 2 p A

/-- The triangle `T_L = {x : x₁ ≥ |x₂|, x₁ ≤ L}`. -/
def triangle (L : ℕ) : Set (Vertex 2) := {x | |x 1| ≤ x 0 ∧ x 0 ≤ L}

/-- Lemma 5.26: for all parameters, the good event `G(0, C_χ, K)` is null-measurable and almost
surely `liminf_L L⁻² |{y ∈ T_L : G(y, C_χ, K)}| = P[G(0, C_χ, K)]` (null-measurable form, all
parameters). -/
def GoodEventDensityStmt (p : unitInterval) : Prop :=
  ∀ (Cf : ℕ) (R c₁ Cχ K : ℝ),
    NullMeasurableSet (eventG Cf R c₁ 0 Cχ K) (latticeBondLaw 2 p) ∧
    ∀ᵐ ω ∂latticeBondLaw 2 p,
      liminf (fun L : ℕ => ({y | y ∈ triangle L ∧ ω ∈ eventG Cf R c₁ y Cχ K}.ncard : ℝ) /
          (L : ℝ) ^ 2) atTop = (latticeBondLaw 2 p (eventG Cf R c₁ 0 Cχ K)).toReal

/-- Lemma 5.27: there are parameters and constants `C_χ, K₀, C₀` with `P[G(0, C_χ, K₀)] > 0` and,
almost surely, a scale `M_h` such that on the standing event, for every `x₀` with
`x₀,₁ ≥ |x₀,₂|` and `x₀,₁ ≥ M_h` at which `G(x₀, C_χ, K₀)` holds, some edge of `𝒞_∞` within
distance `C₀` of `x₀` has `∇ℓ_{e₁} ≠ 0` and `∇u_f ≠ 0`. -/
def LargeGradientSensitiveStmt (p : unitInterval) (f : Vertex 2 → ℤ) : Prop :=
  (Function.support f).Finite →
  ∃ (Cf : ℕ) (R c₁ Cχ K₀ C₀ : ℝ),
    (∃ A ⊆ eventG Cf R c₁ 0 Cχ K₀, MeasurableSet A ∧ 0 < latticeBondLaw 2 p A) ∧
    ∀ᵐ ω ∂latticeBondLaw 2 p, ∃ h : HasUniqueInfiniteOpenComponent ω, ∃ M : ℝ,
      ∀ u, IsDecayingPotential (uniqueInfiniteComponent h) f u → (Function.support u).Infinite →
      ∀ ℓ, IsCorrectedPlane (uniqueInfiniteComponent h) (Pi.single 0 1) ℓ →
      ∀ x₀ : Vertex 2, |x₀ 1| ≤ x₀ 0 → M ≤ x₀ 0 → ω ∈ eventG Cf R c₁ x₀ Cχ K₀ →
        ∃ a b : uniqueInfiniteComponent h, (componentGraph _).Adj a b ∧
          l1 (a.val - x₀) ≤ C₀ ∧ ℓ a ≠ ℓ b ∧ u a ≠ u b

end Rigidity.Section5
