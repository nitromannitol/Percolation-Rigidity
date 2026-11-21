/-
Copied from Lattice-High-Contrast-Homogenization (https://github.com/nitromannitol/Lattice-High-Contrast-Homogenization),
commit f47a932a9f7a07e1692bfe4aae564d02e8ca0944, file `LatticeHC/Model/Lattice.lean` (Apache License 2.0,
Copyright 2026 Ahmed Bou-Rabee and Yuval Peres).
Changes: imports `LatticeHC.*` renamed to `Rigidity.Vendor.LHCH.*`; namespace `LatticeHC` kept.
-/
import LatticeProb.Site
import LatticeProb.Walk.Ball
import LatticeProb.Walk.Energy
import LatticeProb.Walk.Lazy
import LatticeProb.Walk.SRW

/-!
# The lattice, its cubes and its edges

The sets of `ℤ^d` that Appendix A names: the open box `U_L = (0,L)^d ∩ ℤ^d` (§1.1), the lattice
cubes `z + {0,…,L}^d` and the triadic cubes `□_n`.

It also defines the oriented edge `(x, j) = {x, x + e_j}` and the embedding of the lattice in
`EuclideanSpace ℝ (Fin d)`.

Sites, unit vectors, neighbours and norms are those of `LatticeProb`.
-/

namespace LatticeHC

open LatticeProb

noncomputable section

variable {d : ℕ}

/-- Nearest neighbours `x ∼ y` (§1.1): the sites differ by a unit vector. -/
def IsNbr (x y : Site d) : Prop := (lattice d).Adj x y

/-- The open box `U_L = (0, L)^d ∩ ℤ^d` (§1.1). -/
def openBox (d L : ℕ) : Finset (Site d) :=
  Fintype.piFinset fun _ : Fin d => Finset.Ioo (0 : ℤ) (L : ℤ)

/-- The lattice cube `z + {0, …, L}^d` of side `L` (§1.1). -/
def latticeCube (z : Site d) (L : ℕ) : Finset (Site d) := qbox z L

/-- The triadic cube `□_n = {0, …, 3^n}^d` (Appendix A, before `(e:matrix-sandwich)`). -/
def triadicCube (d n : ℕ) : Finset (Site d) := qbox 0 (3 ^ n)

/-- An oriented nearest-neighbour edge: `(x, j)` is the edge `{x, x + e_j}`, oriented from `x` to
`x + e_j` (§4.1). -/
abbrev Edge (d : ℕ) := Site d × Fin d

/-- The initial endpoint `x` of the edge `(x, j)`. -/
def Edge.src (e : Edge d) : Site d := e.1

/-- The final endpoint `x + e_j` of the edge `(x, j)`. -/
def Edge.tgt (e : Edge d) : Site d := e.1 + unit e.2

/-- The embedding of `ℤ^d` in `EuclideanSpace ℝ (Fin d)`. -/
def toEuc (x : Site d) : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 fun i => ((x i : ℤ) : ℝ)

end

end LatticeHC
