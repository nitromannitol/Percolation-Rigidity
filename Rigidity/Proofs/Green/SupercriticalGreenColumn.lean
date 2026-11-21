import Rigidity.Proofs.Green.ClusterIsoperimetryWellConnected
import Rigidity.Proofs.Green.LatticeIsoperimetry

/-!
# Green columns of the supercritical cluster in dimension at least three

For `d ≥ 3` and `p_c(d) < p < 1`, almost surely the infinite cluster has, for each pole `y` in it,
a unique Green column (`greenColumnExistence_of_three_le`). The proof chains

* the isoperimetric inequality of `ℤ^d` (`LatticeIsoperimetry.lean`);
* the coarse graining by good subcubes of radius `⌈(2R)^{1/(10d)²}⌉` of a well-connected cube
  `y + Q_{2R}`, which gives the isoperimetric inequality of the cluster in `y + Q_R` with constant
  `κ R^{-1/(100d)}` (`ClusterIsoperimetryWellConnected.lean`);
* the discrete Cheeger inequality, the local Nash inequality and the on-diagonal heat kernel bound,
  which give the summable bound `p_n(x, y) ≤ K n^{-(d/2)(1 - 1/(50d))}`, and the Green function
  `∑_n p_n(·, y)/deg(y)` (`ClusterIsoperimetry.lean`, `ClusterFaberKrahn.lean`).

With the planar statement this is the Green-column input
`LatticeProb.External.SupercriticalBondGreenColumnExistence`
(`supercriticalBondGreenColumnExistence_of_two`).
-/

open MeasureTheory LatticeProb.Percolation

namespace Rigidity.Green

variable {d : ℕ}

/-- **Green columns of the infinite cluster in dimension `d ≥ 3`**: almost surely, for a pole `y`
in the infinite cluster, there is exactly one Green column with pole `y`. -/
theorem greenColumnExistence_of_three_le [NeZero d] (hd : 3 ≤ d) (hd2 : 2 ≤ d)
    (p : unitInterval) (hp : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (y : Vertex d) :
    ∀ᵐ ω ∂latticeBondLaw d p,
      ∀ h : HasUniqueInfiniteOpenComponent ω,
        ∀ hy : y ∈ (uniqueInfiniteComponent h).supp,
          ∃! g : uniqueInfiniteComponent h → ℝ,
            IsGreenColumn d hd2 (uniqueInfiniteComponent h) ⟨y, hy⟩ g :=
  greenColumnExistence_of_clusterIsoperimetry hd hd2 p le_rfl (by positivity)
    (one_lt_exponent_of_le (by rw [zero_add]; exact coarseLoss_le (by omega)) hd)
    (clusterIsoperimetry_of_latticeIsoperimetry hd2 hp hp1 (latticeIsoperimetry hd2)) y

/-- **The Green-column input** from its planar statement. -/
theorem supercriticalBondGreenColumnExistence_of_two
    (hTwo : Rigidity.External.SupercriticalBondGreenColumnExistenceTwo) :
    LatticeProb.External.SupercriticalBondGreenColumnExistence :=
  supercriticalBondGreenColumnExistence_of_latticeIsoperimetry hTwo fun _ hd =>
    latticeIsoperimetry (by omega)

end Rigidity.Green
