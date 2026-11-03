import LatticeProb.Prob.Percolation.GreenColumn

open LatticeProb.Percolation
open scoped Classical

namespace Rigidity

/-- The two masked forward differences of a scalar kernel on an open component. -/
-- FROZEN-STATEMENT-BEGIN
noncomputable def mixedEntry {d : ℕ} {ω : Configuration d} (C : OpenComponent ω)
    (g : C → C → ℝ) (x y : C) (i j : Fin d) : ℝ :=
  if hx : (openGraph ω).Adj x.val (x.val + LatticeProb.unit i) then
    if hy : (openGraph ω).Adj y.val (y.val + LatticeProb.unit j) then
      let xp : C := ⟨x.val + LatticeProb.unit i, C.mem_supp_of_adj_mem_supp x.property hx⟩
      let yp : C := ⟨y.val + LatticeProb.unit j, C.mem_supp_of_adj_mem_supp y.property hy⟩
      g y x - g y xp - g yp x + g yp xp
    else 0
  else 0
-- FROZEN-STATEMENT-END

end Rigidity
