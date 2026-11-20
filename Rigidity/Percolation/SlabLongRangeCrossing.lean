import Rigidity.Percolation.TargetConnectionHarris

/-!
# Rooted crossings from long-range connections

Uniform two-point connection probabilities inside a slab imply a uniform
probability that a fixed root connects to all marked faces. The proof uses
positive association of the individual face-connection events.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory Rigidity.External

/-- If a root connects to one prescribed point on each marked face with
probability at least `ρ`, then its component meets every face with probability
at least `ρ ^ (2 * d)`. -/
theorem pow_le_measureReal_crossingRoot_of_twoPoint {d : ℕ} (p : unitInterval)
    (B : Set (Vertex d)) (lower upper : Fin d → Set (Vertex d))
    (x : Vertex d) (hx : x ∈ B) (point : Fin d × Bool → Vertex d)
    (hpointB : ∀ face, point face ∈ B)
    (hpointFace : ∀ face, point face ∈ (if face.2 then upper face.1 else lower face.1))
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hprob : ∀ face, ρ ≤ (latticeBondLaw d p).real
      {ω | (openIn ω B).Reachable x (point face)}) :
    ρ ^ (2 * d) ≤ (latticeBondLaw d p).real
      {ω | IsCrossingRoot ω B lower upper x} := by
  have hface : ∀ face : Fin d × Bool, ρ ≤ (latticeBondLaw d p).real
      (targetConnection B (if face.2 then upper face.1 else lower face.1) x) := by
    intro face
    apply (hprob face).trans
    apply measureReal_mono _ (measure_ne_top _ _)
    intro ω hω
    exact ⟨point face, hpointB face, hpointFace face, hω⟩
  calc
    ρ ^ (2 * d) = ∏ _face : Fin d × Bool, ρ := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_prod,
        Fintype.card_fin, Fintype.card_bool, Nat.mul_comm]
    _ ≤ ∏ face : Fin d × Bool, (latticeBondLaw d p).real
        (targetConnection B (if face.2 then upper face.1 else lower face.1) x) := by
      exact Finset.prod_le_prod (fun _ _ => hρ) (fun face _ => hface face)
    _ ≤ _ := prod_measure_faceConnection_le_crossingRoot p B lower upper x hx

end Rigidity.Percolation
