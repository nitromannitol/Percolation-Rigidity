import Rigidity.Percolation.EquivariantConditionalSeed
import Rigidity.Percolation.SteeredFacePad

/-!
# Transport of steered seed targets

The outward-pad seed targets transport under lattice symmetries. Steering is
implemented by reflecting transverse coordinates and translating by the seed
center.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External
open scoped unitInterval

/-- Reflect transverse coordinates toward the axes and translate by the seed
center. -/
def steeringVertexEquiv {d : ℕ} (i : Fin d) (b : Vertex d) : Vertex d ≃ Vertex d :=
  (coordinateSignFlip (steeringSigns i b)).trans (latticeVertexTranslation b)

/-- Steering preserves lattice distance. -/
theorem latticeL1Dist_steeringVertexEquiv {d : ℕ} (i : Fin d) (b x y : Vertex d) :
    latticeL1Dist (steeringVertexEquiv i b x) (steeringVertexEquiv i b y) = latticeL1Dist x y := by
  exact (latticeL1Dist_latticeVertexTranslation b _ _).trans
    (latticeL1Dist_coordinateSignFlip (steeringSigns i b) x y)

/-- The transformed positive pad is the translated steered pad. -/
theorem steeringVertexEquiv_image_orthantFaceSeedPad {d : ℕ} (M n : ℕ)
    (i : Fin d) (b : Vertex d) :
    steeringVertexEquiv i b '' orthantFaceSeedPad n (2 * M + 1) i =
      (fun x : Vertex d => x + b) '' steeredFacePad M n i b := by
  rw [← image_orthantFaceSeedPad_coordinateSignFlip M n i b, Set.image_image]
  rfl

/-- Coordinate sign reversal is additive. -/
theorem coordinateSignFlip_add {d : ℕ} (s : Fin d → Bool) (x y : Vertex d) :
    coordinateSignFlip s (x + y) = coordinateSignFlip s x + coordinateSignFlip s y := by
  funext i
  change (if s i then -(x i + y i) else x i + y i) =
    (if s i then -(x i) else x i) + (if s i then -(y i) else y i)
  cases h : s i <;> simp only [Bool.false_eq_true, ↓reduceIte, neg_add]

/-- Coordinate sign reversal preserves each centered cube. -/
theorem coordinateSignFlip_image_centeredBondCube {d : ℕ} (s : Fin d → Bool) (M : ℕ) :
    coordinateSignFlip s '' centeredBondCube M = centeredBondCube M := by
  have h := signedCoordinateEquiv_image_centeredBondCube (Equiv.refl (Fin d)) s M
  exact h

/-- Steering carries every translate of a centered seed cube to another
translate of the same seed cube. -/
theorem steeringVertexEquiv_image_translatedSeed {d : ℕ} (M : ℕ) (i : Fin d)
    (b c : Vertex d) :
    steeringVertexEquiv i b '' ((fun z : Vertex d => z + c) '' centeredBondCube M) =
      (fun z : Vertex d => z + steeringVertexEquiv i b c) '' centeredBondCube M := by
  let s := steeringSigns i b
  calc
    _ = (fun z : Vertex d => coordinateSignFlip s z + steeringVertexEquiv i b c) ''
        centeredBondCube M := by
      rw [Set.image_image]
      congr 1
      funext z
      change coordinateSignFlip s (z + c) + b =
        coordinateSignFlip s z + (coordinateSignFlip s c + b)
      rw [coordinateSignFlip_add, add_assoc]
    _ = (fun z : Vertex d => z + steeringVertexEquiv i b c) ''
        (coordinateSignFlip s '' centeredBondCube M) := by
      rw [Set.image_image]
    _ = _ := by rw [coordinateSignFlip_image_centeredBondCube]

/-- A transported pad-seed target is the corresponding transformed seed
family, transformed pad and transformed outward step. -/
theorem latticeTransportTargets_padSeedTargets {d : ℕ} (f : Vertex d ≃ Vertex d)
    (hf : ∀ x y, latticeL1Dist (f x) (f y) = latticeL1Dist x y)
    (M n : ℕ) (i : Fin d) (η : Configuration d) :
    latticeTransportTargets f hf (padSeedTargets M n i) η =
      seedFamilyTargets ((centeredCubeOrthantFace n i (fun _ => true)).image f)
        (fun c : Vertex d => f '' ((fun z : Vertex d => z + c) '' centeredBondCube M))
        (f '' orthantFaceSeedPad n (2 * M + 1) i)
        (fun x => f (fun j => if j = i then (f.symm x) j + 1 else (f.symm x) j)) η := by
  classical
  have h := seedFamilyTargets_latticeEquiv f hf (centeredCubeOrthantFace n i (fun _ => true))
    (fun c : Vertex d => (fun z : Vertex d => z + c) '' centeredBondCube M)
    (orthantFaceSeedPad n (2 * M + 1) i)
    (fun x j => if j = i then x j + 1 else x j) ((latticeConfigurationEquiv f hf).symm η)
  rw [MeasurableEquiv.apply_symm_apply] at h
  change _ = (padSeedTargets M n i ((latticeConfigurationEquiv f hf).symm η)).image f at h
  exact h.symm

/-- Under the standard block-radius bounds, the translated steered pad lies
inside the neighboring block. -/
theorem steeringVertexEquiv_image_pad_subset_neighborBlock {d : ℕ} (M n : ℕ)
    (i : Fin d) (b : Vertex d) (hb : ∀ j, |b j| ≤ ((M + n + 1 : ℕ) : ℤ))
    (hbi : (M : ℤ) ≤ b i) :
    ∀ x ∈ steeringVertexEquiv i b '' orthantFaceSeedPad n (2 * M + 1) i, ∀ j,
      |x j - (if j = i then (2 * (M + n + 1 : ℕ) : ℤ) else 0)| ≤
        ((M + n + 1 : ℕ) : ℤ) := by
  intro x hx j
  rw [steeringVertexEquiv_image_orthantFaceSeedPad] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  simpa only [Pi.add_apply, add_comm] using
    steeredFacePad_subset_neighborBlock M n i b hb hbi y hy j

end Rigidity.Percolation
