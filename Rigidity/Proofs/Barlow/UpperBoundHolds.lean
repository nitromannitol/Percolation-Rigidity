import Rigidity.Proofs.Barlow.GaussianHolds
import Rigidity.Proofs.WeakPoincare.PlanarVeryGood

/-!
# Barlow's Gaussian upper bound on the planar infinite cluster, with no hypothesis

The very good balls of the planar infinite cluster (`ClusterVeryGoodBallsTwo`: Barlow 2004,
Theorem 2.18 (c) with Lemma 2.19, for Euclidean balls) are the case `d = 2` of
`Rigidity.WeakPoincare.clusterVeryGoodBalls_holds`, written with the planar distance, balls and
averages in `Rigidity.WeakPoincare.planarVeryGoodBalls_holds`
(`clusterVeryGoodBallsTwo_holds`). With `barlowGaussianUpperBoundTwo_of_veryGood` they give the
input `BarlowGaussianUpperBoundTwo` (Theorem 4 of Dario and Gu = Barlow 2004, Theorem 1, upper
bound with the tail (0.5)) for `𝔭_c(2) < p < 1` with no hypothesis
(`barlowGaussianUpperBoundTwo_holds`).
-/

namespace Rigidity.Barlow

/-- **Very good balls of the planar infinite cluster** (Barlow 2004, Theorem 2.18 (c) and
Lemma 2.19, for Euclidean balls): for every `θ ∈ (0, 1]`, above a random scale `S(y) ≤ O_s(C)`
every ball `B(z, r)` of the infinite cluster with `|z - y| ≤ R` and `r ≥ R^θ` is good. -/
theorem clusterVeryGoodBallsTwo_holds : ClusterVeryGoodBallsTwo :=
  Rigidity.WeakPoincare.planarVeryGoodBalls_holds

/-- **Barlow 2004, Theorem 1** (upper bound with the tail (0.5)) in the form of Dario and Gu,
Theorem 4, with no hypothesis: `BarlowGaussianUpperBoundTwo`. -/
theorem barlowGaussianUpperBoundTwo_holds : Rigidity.Green.BarlowGaussianUpperBoundTwo :=
  barlowGaussianUpperBoundTwo_of_veryGood clusterVeryGoodBallsTwo_holds

end Rigidity.Barlow
