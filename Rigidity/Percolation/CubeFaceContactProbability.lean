import Rigidity.Percolation.CubeOrthantFaces

/-!
# Boundary and orthant-face contact probabilities

For a centered cube seed, signed symmetries make all orthant-face contact
counts equidistributed. Positive association then bounds the probability of
few contacts on one face in terms of the corresponding boundary event.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External

/-- The finite vertex set of a centered cube. -/
noncomputable def centeredBondCubeFinset {d : ℕ} (n : ℕ) : Finset (Vertex d) :=
  (finite_centeredBondCube n).toFinset

/-- Signed permutations preserve the finite vertex set of a centered cube. -/
theorem image_centeredBondCubeFinset_signedCoordinateEquiv {d : ℕ}
    (σ : Equiv.Perm (Fin d)) (s : Fin d → Bool) (n : ℕ) :
    (centeredBondCubeFinset n).image (signedCoordinateEquiv σ s) =
      centeredBondCubeFinset n := by
  classical
  apply Finset.coe_injective
  simpa only [Finset.coe_image, centeredBondCubeFinset, Set.Finite.coe_toFinset] using
    signedCoordinateEquiv_image_centeredBondCube σ s n

/-- All orthant faces have the same small-contact probability when the region
and the seed are concentric centered cubes. -/
theorem measureReal_fewSeedContacts_orthantFace_eq {d : ℕ} (p : unitInterval)
    (M n m : ℕ) (i j : Fin d) (s : Fin d → Bool) :
    (latticeBondLaw d p).real (fewSeedContacts (centeredBondCube n)
      (centeredBondCubeFinset M) (centeredCubeOrthantFace n i s) m) =
    (latticeBondLaw d p).real (fewSeedContacts (centeredBondCube n)
      (centeredBondCubeFinset M) (centeredCubeOrthantFace n j (fun _ => true)) m) := by
  classical
  let σ : Equiv.Perm (Fin d) := Equiv.swap i j
  let t : Fin d → Bool := fun k => !s k
  have h := measureReal_fewSeedContacts_latticeEquiv p (signedCoordinateEquiv σ t)
    (latticeL1Dist_signedCoordinateEquiv σ t) (centeredBondCube n)
    (centeredBondCubeFinset M) (centeredCubeOrthantFace n j (fun _ => true)) m
  have hσ : σ i = j := Equiv.swap_apply_left i j
  have hface : (centeredCubeOrthantFace n j (fun _ => true)).image
      (signedCoordinateEquiv σ t) = centeredCubeOrthantFace n i s := by
    simpa only [hσ, t] using image_centeredCubeOrthantFace_signedCoordinateEquiv σ s n i
  rw [signedCoordinateEquiv_image_centeredBondCube,
    image_centeredBondCubeFinset_signedCoordinateEquiv, hface] at h
  exact h

/-- For a centered cube seed, the probability of few contacts on an orthant
face to the power `d * 2 ^ d` is bounded by the probability of fewer than
`d * 2 ^ d * m` contacts on the whole cube boundary. -/
theorem pow_measureReal_orthantFace_contacts_le_boundary {d : ℕ} (p : unitInterval)
    (M n m : ℕ) (i : Fin d) :
    (latticeBondLaw d p).real (fewSeedContacts (centeredBondCube n)
      (centeredBondCubeFinset M) (centeredCubeOrthantFace n i (fun _ => true)) m) ^
        (d * 2 ^ d) ≤
    (latticeBondLaw d p).real (fewSeedContacts (centeredBondCube n)
      (centeredBondCubeFinset M) (centeredBondCubeBoundary n) ((d * 2 ^ d) * m)) := by
  classical
  let pieces : Fin d × (Fin d → Bool) → Finset (Vertex d) :=
    fun a => centeredCubeOrthantFace n a.1 a.2
  have hs : (Finset.univ : Finset (Fin d × (Fin d → Bool))).Nonempty :=
    ⟨(i, fun _ => true), Finset.mem_univ _⟩
  have h := pow_measureReal_fewSeedContacts_le p (centeredBondCube n)
    (centeredBondCubeFinset M) (centeredBondCubeBoundary n) pieces m Finset.univ hs
    (centeredBondCubeBoundary_subset_biUnion_orthantFace n) (i, fun _ => true) (by
      intro a _
      exact measureReal_fewSeedContacts_orthantFace_eq p M n m a.1 i a.2)
  simpa only [pieces, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_fun, Fintype.card_bool] using h

end Rigidity.Percolation
