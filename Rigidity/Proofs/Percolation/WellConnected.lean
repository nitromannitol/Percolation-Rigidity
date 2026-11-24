import PercolationClusterHomogenization.Percolation.Pisztora.WellConnected
import Rigidity.Proofs.Percolation.PlanarWellConnected

/-!
# Well-connected cubes in every dimension

Proposition 2.3 of the paper, the literature input `Rigidity.External.WellConnectedInput`: for
`d ≥ 2` and `p_c(d) < p < 1`, every cube `x + Q_N` is well-connected outside an event of
probability at most `C exp(-c N^s)`. The case `d = 2` is `wellConnected_input_two`, from
supercritical rectangle crossings of strips of width of order `√N`, and the cases `d ≥ 3` are
`wellConnected_of_three_le`, from slab connectivity above the critical point.
-/

namespace Rigidity.Percolation

/-- **Proposition 2.3** (`Rigidity.External.WellConnectedInput`): for `d ≥ 2` and
`p_c(d) < p < 1` there are `c, C, s > 0` such that every cube `x + Q_N` is well-connected outside
an event of probability at most `C exp(-c N^s)`. -/
theorem wellConnected_input : Rigidity.External.WellConnectedInput :=
  wellConnectedInput_of_planar wellConnected_input_two

end Rigidity.Percolation
