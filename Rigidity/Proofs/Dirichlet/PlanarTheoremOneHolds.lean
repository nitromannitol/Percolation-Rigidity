import Rigidity.Proofs.Dirichlet.PlanarTheoremOne
import Rigidity.Proofs.Cluster.PlanarScaleForms

/-!
# Theorem 1 of Armstrong and Dario in dimension two, with no hypothesis

`planarHomogenizationError_holds` is `planarHomogenizationError_of_inputs` with its two inputs
supplied by the theorems `planarMesoscopicConvergence_holds` (Proposition 5.13 on the triadic
subcubes of scale `⌈m/8⌉`) and `planarMinimalScales_partition_holds` (both bounds of (2.13) for the
planar partition), which are proved for `p > p_c(2)`. Theorem 1 therefore holds in dimension two,
for every `p' > 2`, with the discrete homogenized solution and `ā = σ I`.
-/

open LatticeProb.Percolation Rigidity.Percolation

namespace Rigidity.Dirichlet

/-- **Armstrong and Dario, Theorem 1, in dimension two, with the discrete homogenized solution**,
for every `𝔭_c(2) < p` and every exponent `p' > 2`, with no further hypothesis. -/
theorem planarHomogenizationError_holds {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) {p' : ℝ} (hp' : 2 < p') :
    PlanarHomogenizationError p p' :=
  planarHomogenizationError_of_inputs hpc
    (Rigidity.Proofs.Cluster.planarMesoscopicConvergence_holds hpc)
    (Rigidity.Proofs.Cluster.planarMinimalScales_partition_holds hpc) hp'

end Rigidity.Dirichlet
