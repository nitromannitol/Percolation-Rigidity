/-
Copied from Lattice-High-Contrast-Homogenization (https://github.com/nitromannitol/Lattice-High-Contrast-Homogenization),
commit f47a932a9f7a07e1692bfe4aae564d02e8ca0944, file `LatticeHC/Support/WeakNorm/Reflection.lean` (Apache License 2.0,
Copyright 2026 Ahmed Bou-Rabee and Yuval Peres).
Changes: imports `LatticeHC.*` renamed to `Rigidity.Vendor.LHCH.*`; namespace `LatticeHC` kept.
-/
import Rigidity.Vendor.LHCH.Model.Coarse

/-!
# Reflection of functions and edge fields from a cube to the periodic lattice

Step 3 of the proof of `p:finite-range` uses this reflection:
"the weak norm of edge fields on `□_n` is the normalized `L²` norm, on the torus of side `2·3^n`,
of `(Id + 9^n ∇*∇)^{-1/4}` applied to their reflection to that torus, the `j`th component oddly in
the `j`th coordinate and evenly in the others".

For `N ≥ 1`, `foldCoord N` folds an integer into `[0, N]` by the even reflection of period `2N`.
A function `u` on the cube `{0, …, N}^d` is reflected evenly in every coordinate; an edge field
`F` is reflected with the sign `−1` in its own direction, so that the reflection of a gradient is
the gradient of the reflection (`edgeGrad_reflectFun`). Both reflections are `2N`-periodic. No
analytic fact is proved here.
-/

namespace LatticeHC

open LatticeProb

noncomputable section

variable {d : ℕ}

/-- The even fold of period `2N` of an integer into `[0, N]`: `a mod 2N` if it is at most `N`,
and `2N − (a mod 2N)` otherwise. -/
def foldCoord (N : ℕ) (a : ℤ) : ℤ :=
  if a % (2 * N) ≤ N then a % (2 * N) else 2 * N - a % (2 * N)

/-- The fold of a site, coordinatewise. -/
def foldSite (N : ℕ) (x : Site d) : Site d := fun i => foldCoord N (x i)

/-- The even reflection `ũ(x) = u(fold x)` of a function on the cube `{0, …, N}^d`. -/
def reflectFun (N : ℕ) (u : Site d → ℝ) : Site d → ℝ := fun x => u (foldSite N x)

/-- The reflection of an edge field: the edge `(x, j)` with `x_j mod 2N < N` carries `F` of the
folded edge, and otherwise minus `F` of the folded edge, which then starts at the fold of
`x + e_j`. -/
def reflectEdgeField (N : ℕ) (F : Edge d → ℝ) : Edge d → ℝ := fun e =>
  if e.1 e.2 % (2 * N) < N then F (foldSite N e.1, e.2)
  else -F (foldSite N (e.1 + unit e.2), e.2)

/-- The gradient `∇u(e) = u(x + e_j) − u(x)` of a function along the edge `e = (x, j)`. -/
def edgeGrad (u : Site d → ℝ) (e : Edge d) : ℝ := u e.tgt - u e.src

/-- The successor modulo `2N`: `(a + 1) mod 2N` is `a mod 2N + 1`, unless that is `2N`, in which
case it is `0`. -/
theorem add_one_emod_two_mul_eq_ite (N : ℕ) (hN : 0 < N) (a : ℤ) :
    (a + 1) % (2 * N) = if a % (2 * N) + 1 < 2 * N then a % (2 * N) + 1 else 0 := by
  have hm : (0 : ℤ) < 2 * N := by positivity
  have hdec := Int.mul_ediv_add_emod a (2 * N)
  have h0 := Int.emod_nonneg a hm.ne'
  have h1 := Int.emod_lt_of_pos a hm
  split_ifs with h
  · have : a + 1 = (a % (2 * N) + 1) + (2 * N) * (a / (2 * N)) := by linarith
    rw [this, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by linarith) h]
  · have : a + 1 = 0 + (2 * N) * (a / (2 * N) + 1) := by nlinarith
    rw [this, Int.add_mul_emod_self_left]
    simp

/-- Below the midpoint, the fold is the identity on the edge: `fold(a + 1) = fold(a) + 1`. -/
theorem foldCoord_add_one_of_lt (N : ℕ) (hN : 0 < N) (a : ℤ) (h : a % (2 * N) < N) :
    foldCoord N (a + 1) = foldCoord N a + 1 := by
  have h0 := Int.emod_nonneg a (by positivity : (2 * (N : ℤ)) ≠ 0)
  have hs : (a + 1) % (2 * N) = a % (2 * N) + 1 := by
    rw [add_one_emod_two_mul_eq_ite N hN, if_pos (by linarith)]
  unfold foldCoord
  rw [hs, if_pos (by linarith), if_pos (by linarith)]

/-- At or above the midpoint, the fold reverses the edge: `fold(a) = fold(a + 1) + 1`. -/
theorem foldCoord_eq_add_one_of_le (N : ℕ) (hN : 0 < N) (a : ℤ) (h : (N : ℤ) ≤ a % (2 * N)) :
    foldCoord N a = foldCoord N (a + 1) + 1 := by
  have h1 := Int.emod_lt_of_pos a (by positivity : (0 : ℤ) < 2 * N)
  have hN' : (1 : ℤ) ≤ N := by exact_mod_cast hN
  unfold foldCoord
  by_cases hlt : a % (2 * N) + 1 < 2 * N
  · have hs : (a + 1) % (2 * N) = a % (2 * N) + 1 :=
      by rw [add_one_emod_two_mul_eq_ite N hN, if_pos hlt]
    rw [hs]
    generalize a % (2 * (N : ℤ)) = r at *
    split_ifs <;> omega
  · have hs : (a + 1) % (2 * N) = 0 := by rw [add_one_emod_two_mul_eq_ite N hN, if_neg hlt]
    rw [hs]
    generalize a % (2 * (N : ℤ)) = r at *
    split_ifs <;> omega

/-- The fold leaves the coordinates other than `j` of `x + e_j` unchanged. -/
theorem foldSite_add_unit_of_ne (N : ℕ) (x : Site d) (j i : Fin d) (hij : i ≠ j) :
    foldSite N (x + unit j) i = foldSite N x i := by
  simp [foldSite, unit, hij]

/-- **The reflection of a gradient is the gradient of the reflection**: for `N ≥ 1`,
`∇ũ = (∇u)~`. Below the midpoint of the period in direction `j` the fold maps the edge
`(x, j)` to `(fold x, j)`; above it, to `(fold (x + e_j), j)` with the orientation reversed. -/
theorem edgeGrad_reflectFun (N : ℕ) (hN : 0 < N) (u : Site d → ℝ) :
    edgeGrad (reflectFun N u) = reflectEdgeField N (edgeGrad u) := by
  funext e
  obtain ⟨x, j⟩ := e
  simp only [edgeGrad, reflectFun, reflectEdgeField, Edge.tgt, Edge.src]
  split_ifs with h
  · have hfold : foldSite N (x + unit j) = foldSite N x + unit j := by
      funext i
      by_cases hij : i = j
      · subst hij
        simp only [Pi.add_apply, foldSite, unit, Pi.single_eq_same]
        exact foldCoord_add_one_of_lt N hN (x i) h
      · rw [foldSite_add_unit_of_ne N x j i hij]
        simp [unit, hij]
    rw [hfold]
  · have hfold : foldSite N x = foldSite N (x + unit j) + unit j := by
      funext i
      by_cases hij : i = j
      · subst hij
        simp only [Pi.add_apply, foldSite, unit, Pi.single_eq_same]
        exact foldCoord_eq_add_one_of_le N hN (x i) (not_lt.mp h)
      · rw [Pi.add_apply, foldSite_add_unit_of_ne N x j i hij]
        simp [unit, hij]
    rw [hfold]
    ring

end

end LatticeHC
