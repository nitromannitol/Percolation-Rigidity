/-
Copied from Lattice-High-Contrast-Homogenization (https://github.com/nitromannitol/Lattice-High-Contrast-Homogenization),
commit f47a932a9f7a07e1692bfe4aae564d02e8ca0944, file `LatticeHC/Model/Symmetry.lean` (Apache License 2.0,
Copyright 2026 Ahmed Bou-Rabee and Yuval Peres).
Changes: imports `LatticeHC.*` renamed to `Rigidity.Vendor.LHCH.*`; namespace `LatticeHC` kept.
-/
import Rigidity.Vendor.LHCH.Model.Lattice

/-!
# Lattice symmetries of random fields

The translations and the point symmetries (coordinate permutations and reflections) of `ℤ^d`, acting
on fields of sites and on fields of edges. This module defines the invariance of a law under them,
and the finite range of dependence of a random field of edges.
* The shift of a field of sites is `(τ_x v)_z = v_{x+z}` (subsection `ss:thmB`). A law on fields is
  stationary if it is invariant under every shift, and ergodic if moreover every shift-invariant
  event has probability zero or one.
* A permutation `σ` of the coordinates maps the edge `{x, x+e_j}` to `{σx, σx+e_{σj}}`. The
  reflection in coordinate `k` maps `{x, x+e_j}` to `{r_k x, r_k x + e_j}` for `j ≠ k`, and to
  `{r_k x - e_k, r_k x}` for `j = k`.
* Sets of edges are far apart when all their endpoints are at pairwise `ℓ^∞` distance greater than
  `r`. A field has range of dependence `r` when its restrictions to finitely many such sets are
  independent (`p:hypotheses` (ii), (H2), `p:finite-range`).
-/

namespace LatticeHC

open MeasureTheory ProbabilityTheory LatticeProb

noncomputable section

variable {d : ℕ}

/-- The shift `(τ_x v)_z = v_{x+z}` of a field of sites (subsection `ss:thmB`). -/
def shiftField {α : Type*} (x : Site d) (v : Site d → α) : Site d → α := fun z => v (x + z)

/-- A law on fields of sites is stationary: invariant under every shift. -/
def IsShiftStationary {α : Type*} [MeasurableSpace α] (ν : Measure (Site d → α)) : Prop :=
  ∀ x : Site d, ν.map (shiftField x) = ν

/-- A law on fields of sites is ergodic for the shifts: every measurable event invariant under every
shift has probability zero or one. -/
def IsShiftErgodic {α : Type*} [MeasurableSpace α] (ν : Measure (Site d → α)) : Prop :=
  ∀ A : Set (Site d → α), MeasurableSet A → (∀ x : Site d, shiftField x ⁻¹' A = A) →
    ν A = 0 ∨ ν A = 1

/-- The shift `(τ_x c)_e = c_{x+e}` of a field of edges. -/
def shiftEdgeField {α : Type*} (x : Site d) (c : Edge d → α) : Edge d → α :=
  fun e => c (x + e.1, e.2)

/-- A law on fields of edges is invariant under the translations of `ℤ^d`. -/
def IsEdgeShiftStationary {α : Type*} [MeasurableSpace α] (ν : Measure (Edge d → α)) : Prop :=
  ∀ x : Site d, ν.map (shiftEdgeField x) = ν

/-- The action of a permutation `σ` of the coordinates on sites: `(σ x)_{σ i} = x_i`. -/
def permuteSite (σ : Equiv.Perm (Fin d)) (x : Site d) : Site d := fun i => x (σ.symm i)

/-- The action of a permutation of the coordinates on edges: `{x, x+e_j} ↦ {σx, σx+e_{σj}}`. -/
def permuteEdge (σ : Equiv.Perm (Fin d)) (e : Edge d) : Edge d := (permuteSite σ e.1, σ e.2)

/-- The reflection of sites in coordinate `k`. -/
def reflectSite (k : Fin d) (x : Site d) : Site d := fun i => if i = k then -x i else x i

/-- Reflecting in the coordinate `k` twice is the identity on sites. -/
theorem reflectSite_reflectSite_eq_self (k : Fin d) (x : Site d) :
    reflectSite k (reflectSite k x) = x := by
  funext i
  by_cases h : i = k <;> simp [reflectSite, h]

/-- The reflection of edges in coordinate `k`: `{x, x+e_j} ↦ {r_k x, r_k x+e_j}` for `j ≠ k`, and
`{x, x+e_k} ↦ {r_k x - e_k, r_k x}`. -/
def reflectEdge (k : Fin d) (e : Edge d) : Edge d :=
  if e.2 = k then (reflectSite k e.1 - unit k, k) else (reflectSite k e.1, e.2)

/-- A law on fields of edges is invariant under the coordinate permutations and reflections of
`ℤ^d`. -/
def IsPointSymmetric {α : Type*} [MeasurableSpace α] (ν : Measure (Edge d → α)) : Prop :=
  (∀ σ : Equiv.Perm (Fin d), ν.map (fun c e => c (permuteEdge σ e)) = ν) ∧
    ∀ k : Fin d, ν.map (fun c e => c (reflectEdge k e)) = ν

/-- The `ℓ^∞` distance between two sites. -/
def supDist (x y : Site d) : ℝ := (supNorm (x - y) : ℝ)

/-- The families `E k` of edges are far apart at range `r`: endpoints of edges in distinct families
are at `ℓ^∞` distance greater than `r`. -/
def PairwiseFar {n : ℕ} (r : ℝ) (E : Fin n → Set (Edge d)) : Prop :=
  ∀ k l, k ≠ l → ∀ e ∈ E k, ∀ e' ∈ E l, ∀ x ∈ ({e.src, e.tgt} : Set (Site d)),
    ∀ y ∈ ({e'.src, e'.tgt} : Set (Site d)), r < supDist x y

/-- A random field of edges has range of dependence `r`: its restrictions to finitely many sets of
edges whose endpoints are at pairwise `ℓ^∞` distance greater than `r` are independent. -/
def FiniteRange {Ω : Type*} [MeasurableSpace Ω] (r : ℝ) (μ : Measure Ω) (c : Ω → Edge d → ℝ) :
    Prop :=
  ∀ (n : ℕ) (E : Fin n → Set (Edge d)), PairwiseFar r E →
    iIndepFun (fun k ω (e : E k) => c ω e) μ

end

end LatticeHC
