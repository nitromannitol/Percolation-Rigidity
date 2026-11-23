import Rigidity.Proofs.Regularity.PlanarCorrectorOsc
import Rigidity.Proofs.Regularity.PlanarCorrectorHolds
import Rigidity.Proofs.Cluster.PlanarSubaddOsMain

/-!
# (1.18) and (1.22) in dimension two with no hypothesis

The inputs of `planarCorrectorOscSublinearTwo_of_subaddOs` are proved for `p > p_c(2)`:
Proposition 5.2 for `ν` in the form `O_s` (`PlanarNuSubaddOsTwo p`) is the part on `ν` of
`Rigidity.Proofs.Cluster.planar_subadd_os` (`planarNuSubaddOsTwo_holds`), the minimal scales are
`planarMinimalScalesTwo_holds` (Proposition 2.4) and the order-zero regularity is
`armstrongDarioOrderZeroTwo_holds`. Hence, with no hypothesis beyond `p_c(2) < p < 1`:

* `planarAffineApproximationTwo_holds`: the approximation of affine functions by harmonic functions
  on the balls `B_{3^m}` of the cluster, above a minimal scale of class `O_s`;
* `planarCorrectorSublinearL2Two_holds`: (1.18) of Armstrong and Dario in dimension two, with a
  minimal scale of class `O_s`;
* `planarCorrectorOscSublinearTwo_holds`: (1.22) in dimension two in the oscillation form.

`planarCorrectorOscSublinearTwo_iff`: the statement `PlanarCorrectorOscSublinearTwo` is the
statement `Rigidity.Corrector.CorrectorOscSublinearTwo` of the proof of Lemma 3.2 of Dario.
-/

namespace Rigidity.Proofs.Regularity

open LatticeProb.Percolation Rigidity.External

/-- **Armstrong–Dario, Proposition 5.2 for `ν` in the form `O_s`, in dimension two**, for
`p > p_c(2)`: the part on `ν` of `planar_subadd_os`, with `Z_V` the error `planarSubaddErr p V`. -/
theorem planarNuSubaddOsTwo_holds {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) :
    PlanarNuSubaddOsTwo p := by
  obtain ⟨r, α, C, hr, hα, hC, h⟩ := Rigidity.Proofs.Cluster.planar_subadd_os hpc
  exact ⟨r, α, C, hr, hα, hC, fun V => ⟨Rigidity.Proofs.Cluster.planarSubaddErr p V, (h V).1,
    (h V).2.1, (h V).2.2.1, fun ω ξ => ((h V).2.2.2 ω 0 ξ).2⟩⟩

/-- The statement (1.22) in the oscillation form is the statement `CorrectorOscSublinearTwo` used
in the proof of Lemma 3.2 of Dario. -/
theorem planarCorrectorOscSublinearTwo_iff :
    PlanarCorrectorOscSublinearTwo ↔ Rigidity.Corrector.CorrectorOscSublinearTwo :=
  Iff.rfl

/-- **The approximation of affine functions on the balls of the planar cluster**, above a minimal
scale of class `O_s`, with no hypothesis. -/
theorem planarAffineApproximationTwo_holds : PlanarAffineApproximationTwo :=
  planarAffineApproximationTwo_of_subaddOs (fun _ hpc _ => planarNuSubaddOsTwo_holds hpc)
    fun _ hpc _ => planarMinimalScalesTwo_holds hpc

/-- **Armstrong–Dario, (1.18), in dimension two**, with a minimal scale of class `O_s` and no
hypothesis. -/
theorem planarCorrectorSublinearL2Two_holds : PlanarCorrectorSublinearL2Two :=
  planarCorrectorSublinearL2Two_of_subaddOs (fun _ hpc _ => planarNuSubaddOsTwo_holds hpc)
    (fun _ hpc _ => planarMinimalScalesTwo_holds hpc) armstrongDarioOrderZeroTwo_holds

/-- **Armstrong–Dario, (1.22), in dimension two**, in the oscillation form, with no hypothesis. -/
theorem planarCorrectorOscSublinearTwo_holds : PlanarCorrectorOscSublinearTwo :=
  planarCorrectorOscSublinearTwo_of_subaddOs (fun _ hpc _ => planarNuSubaddOsTwo_holds hpc)
    (fun _ hpc _ => planarMinimalScalesTwo_holds hpc) armstrongDarioOrderZeroTwo_holds

end Rigidity.Proofs.Regularity
