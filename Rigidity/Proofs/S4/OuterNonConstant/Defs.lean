import Rigidity.Proofs.S4.Conditioning
import Rigidity.Proofs.S4.Attach

/-!
# Lemma 4.8, conditional form: definitions

Lemma 4.8 (`paper/percolation-harmonic.tex` L1340-1347, printed conditional form
`Rigidity.Section4.NonConstantOnGadgetStmt`) bounds
`P[ℓ_q not constant on the gadget | 𝒞_∞ ∩ Q_R = H]` from below for some deterministic `H`. The
route of `Rigidity/Proofs/S4/OuterNonConstant.lean`:

* **Averaging over `H`.** Reset a finite set `D` of bonds of `Q_R` to a pattern `π`. If every
  environment of the gadget event, after the reset, has `H = 𝒞_∞ ∩ Q_R` with `A_H ⊆ {ω_D = π}`,
  then some `H` has `P[G | A_H] ≥ P[reset⁻¹ G]` (the conditional probabilities given the disjoint
  events `A_H` average to at most their maximum).
* **The reset.** On the face sites of `Q_R` (exactly one coordinate at `± R`) all bonds between face
  sites are opened, all bonds from face sites into `Q_{R-1}` are closed, and the faces are joined by
  `connectorBonds` through sites of the `(d-2)`-skeleton. The bonds at the other skeleton sites and
  the outer bonds keep their values: they are not fixed by `A_H`.
* **Comparison** with the environment `ω` itself (no skeleton bond is changed), on the event that the
  connector bonds of `ω` are open: the corrected plane of the reset environment is not constant on
  the face sites.
* **Attachment** of the gadget at a face site `w` and at the reference site `z₀ = (1, -R, 0, …)`.
-/

namespace Rigidity.Proofs.S4.OuterNonConstant

open MeasureTheory ProbabilityTheory LatticeProb.Percolation LatticeProb.Network
  LatticeProb.Network.OpenLadder.Embedding Rigidity.Section4 Rigidity.Steps.S4

variable {d : ℕ}

/-! ### Resetting a finite set of bonds -/

open scoped Classical in
/-- The environment `ω` with the bonds of `D` reset to the values `π`. -/
noncomputable def resetConfig (D : Set (Bond d)) (π : Bond d → Bool) (ω : Configuration d) :
    Configuration d :=
  fun e => if e ∈ D then π e else ω e

/-- The event that the bonds of `D` take the values `π`. -/
def resetEvent (D : Set (Bond d)) (π : Bond d → Bool) : Set (Configuration d) :=
  {ω | ∀ e ∈ D, ω e = π e}

/-! ### Regions of `Q_R` -/

/-- The face sites of `Q_R`: exactly one coordinate equals `± R`, the others lie in `(-R, R)`. -/
def faceSites (d R : ℕ) : Set (Vertex d) :=
  {x | ∃ i, |x i| = R ∧ ∀ j, j ≠ i → |x j| < R}

/-- The bonds between two face sites of `Q_R`. -/
def faceBonds (d R : ℕ) : Set (Bond d) :=
  {e | ∀ z ∈ (e : Sym2 (Vertex d)), z ∈ faceSites d R}

/-- The bonds of `Q_R` with no endpoint on the `(d-2)`-skeleton: both endpoints are face sites or
sites of `Q_{R-1}`. -/
def coreBonds (d R : ℕ) : Set (Bond d) :=
  {e | ∀ z ∈ (e : Sym2 (Vertex d)), z ∈ faceSites d R ∨ z ∈ cube d (R - 1)}

/-- The site `σ R e_i + τ R e_j` of the `(d-2)`-skeleton of `Q_R`. -/
def edgeSite (R : ℕ) (i j : Fin d) (σ τ : ℤ) : Vertex d :=
  fun l => if l = i then σ * R else if l = j then τ * R else 0

/-- The connector bonds: at each skeleton site `z = σ R e_i + τ R e_j` (`i ≠ j`, `σ, τ = ± 1`), the
bonds from `z` to the face sites `z - τ e_j` (face `x_i = σ R`) and `z - σ e_i` (face `x_j = τ R`).
They join every two non-opposite faces of `Q_R`. -/
def connectorBonds (d R : ℕ) : Set (Bond d) :=
  {e | ∃ i j : Fin d, i ≠ j ∧ ∃ σ τ : ℤ, (σ = 1 ∨ σ = -1) ∧ (τ = 1 ∨ τ = -1) ∧
    ((e : Sym2 (Vertex d)) =
        s(edgeSite R i j σ τ, Function.update (edgeSite R i j σ τ) j (τ * ((R : ℤ) - 1))) ∨
      (e : Sym2 (Vertex d)) =
        s(edgeSite R i j σ τ, Function.update (edgeSite R i j σ τ) i (σ * ((R : ℤ) - 1))))}

open scoped Classical in
/-- The comparison environment `ρ₀`: bonds between face sites and connector bonds open, the other
bonds of `Q_R` with no skeleton endpoint closed. -/
noncomputable def compareEnv (d R : ℕ) (ω : Configuration d) : Configuration d :=
  resetConfig (coreBonds d R ∪ connectorBonds d R)
    (fun e => decide (e ∈ faceBonds d R ∨ e ∈ connectorBonds d R)) ω

/-! ### The attachment of the gadget -/

/-- The neighbour in `Q_{R-1}` of a face site: its coordinate at `± R` moves to `± (R - 1)`. -/
def innerNeighbor (R : ℕ) (x : Vertex d) : Vertex d :=
  fun i => if |x i| = R then x i - Int.sign (x i) else x i

/-- The reference face site `z₀ = (1, -R, 0, …)`. -/
def refSite (d R : ℕ) : Vertex d := zeroPad d (1, -(R : ℤ))

/-- The path `P₂` from the inner neighbour `(1, -(R-1))` of `z₀` straight up to the terminal
`t = (1, -m-1)` of the gadget. -/
def highWaypoints (d R : ℕ) : List (Vertex d) :=
  [zeroPad d (1, -((R : ℤ) - 1)), zeroPad d (1, -halfSide R - 1)]

/-- The first leg of `P₁` on the shell `∂Q_{R-1}`: from a site of the face `x_1 = -(R-1)`, move the
coordinate `0` to `± (R-1)`, away from the column `x_0 = 1` of `P₂`; from any other site stay. -/
def preWaypoint (hd : 2 ≤ d) (R : ℕ) (w : Vertex d) : Vertex d :=
  if w ⟨1, by omega⟩ = -(R : ℤ) then
    Function.update (innerNeighbor R w) ⟨0, by omega⟩
      (if 1 ≤ w ⟨0, by omega⟩ then (R : ℤ) - 1 else -((R : ℤ) - 1))
  else innerNeighbor R w

/-- The path `P₁` from the inner neighbour `w¹` of the face site `w` to the terminal
`s = (-2, -m-1)` of the gadget: on the shell `∂Q_{R-1}` move the coordinate `1` to `R - 1`, the
coordinate `0` to `-(R-1)`, the coordinate `1` to `-(R-1)`, the other coordinates to `0`, the
coordinate `0` to `-2`; then up the column `x_0 = -2` to `s`. It avoids the site `(1, -(R-1))`. -/
def lowWaypoints (hd : 2 ≤ d) (R : ℕ) (w : Vertex d) : List (Vertex d) :=
  let p₀ := preWaypoint hd R w
  let p₁ := Function.update p₀ ⟨1, by omega⟩ ((R : ℤ) - 1)
  let p₂ := Function.update p₁ ⟨0, by omega⟩ (-((R : ℤ) - 1))
  let p₃ := Function.update p₂ ⟨1, by omega⟩ (-((R : ℤ) - 1))
  [innerNeighbor R w, p₀, p₁, p₂, p₃, zeroPad d (-((R : ℤ) - 1), -((R : ℤ) - 1)),
    zeroPad d (-2, -((R : ℤ) - 1)), zeroPad d (-2, -halfSide R - 1)]

/-- The bonds of the branch: the gadget of height `R` translated by `τ_R`, the paths `P₁`, `P₂`,
and the attachment bonds `w w¹`, `z₀ z₀¹`. -/
def branchBonds (hd : 2 ≤ d) (R : ℕ) (w : Vertex d) : Set (Bond d) :=
  gadgetBonds hd R ∪ chainBonds (lowWaypoints hd R w) ∪ chainBonds (highWaypoints d R) ∪
    {e | (e : Sym2 (Vertex d)) = s(w, innerNeighbor R w) ∨
      (e : Sym2 (Vertex d)) = s(refSite d R, innerNeighbor R (refSite d R))}

/-- The bonds reset for the attachment at `w`: the bonds of `Q_R` with no skeleton endpoint and an
endpoint at a face site or at a site of the branch, and the connector bonds. -/
def attachResetBonds (hd : 2 ≤ d) (R : ℕ) (w : Vertex d) : Set (Bond d) :=
  {e | e ∈ coreBonds d R ∧ ∃ z ∈ (e : Sym2 (Vertex d)),
      z ∈ faceSites d R ∨ z ∈ bondSites (branchBonds hd R w)} ∪ connectorBonds d R

open scoped Classical in
/-- The values of the attachment reset: open exactly on face bonds, connector bonds and the
branch. -/
noncomputable def attachPattern (hd : 2 ≤ d) (R : ℕ) (w : Vertex d) : Bond d → Bool :=
  fun e => decide (e ∈ faceBonds d R ∨ e ∈ connectorBonds d R ∨ e ∈ branchBonds hd R w)

/-- The environment `ω^♮_w` with the gadget attached at `w` and `z₀`. -/
noncomputable def attachEnv (hd : 2 ≤ d) (R : ℕ) (w : Vertex d) (ω : Configuration d) :
    Configuration d :=
  resetConfig (attachResetBonds hd R w) (attachPattern hd R w) ω

end Rigidity.Proofs.S4.OuterNonConstant
