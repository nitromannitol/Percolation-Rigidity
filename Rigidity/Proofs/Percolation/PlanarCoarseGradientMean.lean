import Rigidity.Proofs.Percolation.PlanarMuEnergyDefect
import Rigidity.Proofs.Percolation.PlanarMuQuadratic

/-!
# The spatial average of the coarsened gradient of the minimizer of `μ`

For a resolved cube `U` and slopes `p, q`, the coarse pairing `ℓ_p(u_q) = ∑ p · ∇[u_q]` of the
minimizer `u_q` of `μ(U, q)` is the polarization of `-|U| μ(U, ·)`:

`ℓ_p(u_q) = -|U| (μ(U, p + q) - μ(U, p) - μ(U, q))`.

In other words, the spatial average of the coarsened gradient of `u(·, U, q)` is `-∇μ(U, ·)(q)`;
this is the identity behind the definition of the finite-volume matrices `ā_{□_n}⁻¹` used in
Lemmas 5.6 and 5.8 of Armstrong and Dario.
-/

open LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped Classical

namespace Rigidity.Percolation

variable {ω : Configuration 2}

/-- **The coarse pairing of the minimizer of `μ` is the polarization of `-|U| μ`.** -/
theorem coarsePairing_planarMuMinimizer (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) (p q : Fin 2 → ℝ) :
    coarsePairing ω U p (planarMuMinimizer ω U q) =
      -((planarMu ω U (p + q) - planarMu ω U p - planarMu ω U q) * U.volume) := by
  obtain ⟨hup, hvp⟩ := planarMuMinimizer_spec hP hU p
  obtain ⟨huq, hvq⟩ := planarMuMinimizer_spec hP hU q
  set up := planarMuMinimizer ω U p
  set uq := planarMuMinimizer ω U q
  have hpair : ∀ w, coarsePairing ω U (p + q) w = coarsePairing ω U p w + coarsePairing ω U q w :=
    fun w => by
      have h := coarsePairing_smul_add_smul (ω := ω) (U := U) p q 1 1 w
      simpa only [one_smul, one_mul] using h
  have hsum : up + uq ∈ clusterHarmonic ω U := (clusterHarmonic ω U).add_mem hup huq
  have hvar : ∀ w ∈ clusterHarmonic ω U,
      clusterForm ω U w (up + uq) = coarsePairing ω U (p + q) w := fun w hw => by
    rw [map_add, hvp w hw, hvq w hw, hpair]
  have e1 := planarMu_mul_volume_eq hP hU (p + q) hsum hvar
  have e2 := planarMu_mul_volume_eq hP hU p hup hvp
  have e3 := planarMu_mul_volume_eq hP hU q huq hvq
  have e4 : clusterForm ω U (up + uq) (up + uq) =
      clusterForm ω U up up + 2 * clusterForm ω U uq up + clusterForm ω U uq uq := by
    simp only [map_add, LinearMap.add_apply]
    rw [clusterForm_symm up uq]
    ring
  have e5 := hvp uq huq
  rw [← e5]
  have : (planarMu ω U (p + q) - planarMu ω U p - planarMu ω U q) * U.volume =
      planarMu ω U (p + q) * U.volume - planarMu ω U p * U.volume -
        planarMu ω U q * U.volume := by ring
  rw [this, e1, e2, e3, e4]
  ring

end Rigidity.Percolation
