import Rigidity.Draft.Section5cStatements

/-!
# The good events as printed

The draft good events `eventG1` and `eventG3` (`Rigidity/Draft/Section5cStatements.lean`) follow the
corrections [C31] (universal `G_1`) and [C32] (direction-free `G_3`). This file keeps the events as
printed, for the results stated with them (among them Lemma 5.25 as printed):

* `eventG1Exists`: the printed `G_1(x, K)` with an existential over the path `γ` ([C31]: it lies in
  `{x ∈ 𝒞_∞}`, so eq. `PG1goesto1` fails for it);
* `eventG3Edge`: the printed `G_3(x, C_χ)` on the edge `(x, x + e₁)` ([C32]: Proposition 3.2 does
  not show that it has positive probability; it needs the signed variant `HorizontalIncrementStep`);
* `eventGPrinted = eventG1Exists ∩ eventG2 ∩ eventG3Edge`.
-/

open MeasureTheory LatticeProb.Percolation

namespace Rigidity.Steps.Section5

open Rigidity.Section5

/-- The first good event `G_1(x, K)` as printed (corrected by [C31]): some path `γ` of
`𝒞_∞` from `x` with `|γ(end) - x| ≥ K` has at least `c₁ |γ(end) - x|` of its sites in `E_R`. -/
def eventG1Exists (Cf : ℕ) (R c₁ : ℝ) (x : Vertex 2) (K : ℝ) : Set (Configuration 2) :=
  {ω | ∃ h : HasUniqueInfiniteOpenComponent ω, ∃ n : ℕ,
    ∃ γ : Fin (n + 1) → uniqueInfiniteComponent h, IsPathOf _ γ ∧ (γ 0).val = x ∧
      K ≤ l1 ((γ (Fin.last n)).val - x) ∧
      c₁ * l1 ((γ (Fin.last n)).val - x) ≤ (goodCount ω Cf R γ : ℝ)}

/-- The third good event `G_3(x, C_χ)` as printed (corrected by [C32]): `(x, x + e₁)` is
an edge of `𝒞_∞` across which every corrected plane `ℓ_{e₁}` increases by at least `C_χ`. -/
def eventG3Edge (x : Vertex 2) (Cχ : ℝ) : Set (Configuration 2) :=
  {ω | ∃ h : HasUniqueInfiniteOpenComponent ω, ∃ hx : x ∈ (uniqueInfiniteComponent h).supp,
    ∃ hx' : x + e1 ∈ (uniqueInfiniteComponent h).supp,
      (componentGraph _).Adj ⟨x, hx⟩ ⟨x + e1, hx'⟩ ∧
      ∀ ℓ, IsCorrectedPlane (uniqueInfiniteComponent h) (Pi.single 0 1) ℓ →
        Cχ ≤ ℓ ⟨x + e1, hx'⟩ - ℓ ⟨x, hx⟩}

/-- The good event as printed: `eventG1Exists ∩ eventG2 ∩ eventG3Edge`. -/
def eventGPrinted (Cf : ℕ) (R c₁ : ℝ) (x : Vertex 2) (Cχ K : ℝ) : Set (Configuration 2) :=
  eventG1Exists Cf R c₁ x K ∩ eventG2 x K ∩ eventG3Edge x Cχ

/-- The printed third good event implies the direction-free one. -/
theorem eventG3Edge_subset (x : Vertex 2) (Cχ : ℝ) : eventG3Edge x Cχ ⊆ eventG3 x Cχ := by
  rintro ω ⟨h, hx, hx', hadj, hG⟩
  exact ⟨h, hx, ⟨x + e1, hx'⟩, hadj, hG⟩

end Rigidity.Steps.Section5
