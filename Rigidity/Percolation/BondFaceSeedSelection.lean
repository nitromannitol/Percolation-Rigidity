import Rigidity.Percolation.BondFaceSeedTrials
import Rigidity.Percolation.BondSeedBatch

/-!
# Face seed trials selected by the base field

A finite family of face contacts selected from a base configuration retains a
geometric success bound for independent added-layer seed trials.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External
open scoped MeasureTheory

/-- Base-measurably selected contacts in distinct face cells give a geometric
lower bound for finding an open added-layer trial. -/
theorem condExp_indicator_lower_of_base_faceSeedTrials {d k : ℕ} {ι : Type*}
    [Countable ι] (hk : 0 < k) (q r : unitInterval) (m : ℕ)
    (j : Fin d) (n : ℤ) (x : ι → Fin m → Vertex d)
    (hface : ∀ a t, x a t j = n)
    (hinj : ∀ a, Function.Injective (fun t => seedGridIndex k (x a t)))
    (A : ι → Set (Bond d → Bool × Bool)) {G C : Set (Bond d → Bool × Bool)}
    (hA : ∀ a, MeasurableSet[baseBondSigma d] (A a))
    (hG : MeasurableSet G) (hC : MeasurableSet C) (hcover : G ⊆ ⋃ a, A a)
    (hsubset : ∀ a, A a ∩ (addedBondConfiguration ⁻¹'
      (⋃ t, fullyOpenRegion (faceSeedTrial k j n (x a t)))) ⊆ C) :
    ∀ᵐ ω ∂(bondPairLaw d q r).restrict G,
      1 - (1 - (r : ℝ) ^ ((k ^ d + 1) ^ 2)) ^ m ≤
        (bondPairLaw d q r)[C.indicator (fun _ => (1 : ℝ)) | baseBondSigma d] ω := by
  apply condExp_indicator_lower_of_base_seed_batch q r m ((k ^ d + 1) ^ 2)
    (fun a t => faceSeedTrial k j n (x a t))
    (fun a t => finite_faceSeedTrial hk j n (x a t))
    (fun a t u htu => disjoint_faceSeedTrial j n (hface a t) (hface a u)
      (fun h => htu (hinj a h)))
    (fun a t => card_localBonds_faceSeedTrial_le hk j n (x a t))
    A hA hG hC hcover hsubset

end Rigidity.Percolation
