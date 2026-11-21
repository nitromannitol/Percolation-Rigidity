/-
Copied from Lattice-High-Contrast-Homogenization (https://github.com/nitromannitol/Lattice-High-Contrast-Homogenization),
commit f47a932a9f7a07e1692bfe4aae564d02e8ca0944, file `LatticeHC/Support/WeakNorm/ReflectPeriodic.lean` (Apache License 2.0,
Copyright 2026 Ahmed Bou-Rabee and Yuval Peres).
Changes: imports `LatticeHC.*` renamed to `Rigidity.Vendor.LHCH.*`; namespace `LatticeHC` kept.
-/
import Rigidity.Vendor.LHCH.Model.Symmetry
import Rigidity.Vendor.LHCH.Support.WeakNorm.TorusH2

/-!
# Periodicity and evenness of the reflection

The even reflection `reflectFun N f` has period `2N` and is invariant under every coordinate
reflection `x_k ↦ −x_k`; conversely an even `2N`-periodic function is the reflection of its
restriction to `{0, …, N}^d`, since the fold of a site is reached from it by coordinate reflections
and shifts by multiples of `2N`.
-/

open LatticeProb

noncomputable section

namespace LatticeHC

variable {d : ℕ}

/-- The fold of an integer has period `2N`. -/
theorem foldCoord_add_two_mul (N : ℕ) (a : ℤ) : foldCoord N (a + 2 * N) = foldCoord N a := by
  unfold foldCoord
  rw [Int.add_emod_right]

/-- The fold of an integer is invariant under negation. -/
theorem foldCoord_neg (N : ℕ) (hN : 0 < N) (a : ℤ) : foldCoord N (-a) = foldCoord N a := by
  have hm : (0 : ℤ) < 2 * N := by positivity
  have hdec := Int.mul_ediv_add_emod a (2 * N)
  have h0 := Int.emod_nonneg a hm.ne'
  have h1 := Int.emod_lt_of_pos a hm
  by_cases hr : a % (2 * N) = 0
  · have h : -a = 0 + (2 * N) * (-(a / (2 * N))) := by linarith
    have hneg : (-a) % (2 * N) = 0 := by
      rw [h, Int.add_mul_emod_self_left]
      simp
    unfold foldCoord
    rw [hneg, hr]
  · have h : -a = (2 * N - a % (2 * N)) + (2 * N) * (-(a / (2 * N)) - 1) := by linarith
    have hneg : (-a) % (2 * N) = 2 * N - a % (2 * N) := by
      rw [h, Int.add_mul_emod_self_left]
      exact Int.emod_eq_of_lt (by omega) (by omega)
    unfold foldCoord
    rw [hneg]
    generalize a % (2 * (N : ℤ)) = r at *
    split_ifs <;> omega

/-- The fold of a site is unchanged by a shift by `2N` in one coordinate. -/
theorem foldSite_add_smul_unit (N : ℕ) (x : Site d) (i : Fin d) :
    foldSite N (x + (2 * (N : ℤ)) • unit i) = foldSite N x := by
  funext j
  by_cases hji : j = i
  · subst hji
    simp only [foldSite, Pi.add_apply, Pi.smul_apply, unit, Pi.single_eq_same, smul_eq_mul,
      mul_one]
    exact foldCoord_add_two_mul N (x j)
  · simp [foldSite, unit, hji]

/-- The fold of a site is invariant under the coordinate reflection `x_k ↦ −x_k`. -/
theorem foldSite_reflectSite (N : ℕ) (hN : 0 < N) (k : Fin d) (x : Site d) :
    foldSite N (reflectSite k x) = foldSite N x := by
  funext i
  by_cases hik : i = k
  · subst hik
    simp only [foldSite, reflectSite, if_true]
    exact foldCoord_neg N hN (x i)
  · simp [foldSite, reflectSite, hik]

/-- The even reflection of a function on `{0, …, N}^d` has period `2N` in every coordinate. -/
theorem isTorusPeriodic_reflectFun (N : ℕ) (f : Site d → ℝ) :
    IsTorusPeriodic N (reflectFun N f) := by
  intro x i
  simp only [reflectFun]
  rw [foldSite_add_smul_unit]

/-- The even reflection is invariant under every coordinate reflection `x_k ↦ −x_k`. -/
theorem reflectFun_reflectSite (N : ℕ) (hN : 0 < N) (f : Site d → ℝ) (k : Fin d) (x : Site d) :
    reflectFun N f (reflectSite k x) = reflectFun N f x := by
  simp only [reflectFun]
  rw [foldSite_reflectSite N hN]

/-- An even `2N`-periodic function takes the same value at `z` and at `z` with its `j`th
coordinate replaced by the fold of that coordinate. -/
theorem eq_update_foldCoord_of_even (N : ℕ) (hN : 0 < N) (w : Site d → ℝ)
    (hw : IsTorusPeriodic N w) (heven : ∀ x (k : Fin d), w (reflectSite k x) = w x)
    (j : Fin d) (z : Site d) : w z = w (Function.update z j (foldCoord N (z j))) := by
  have hm : (0 : ℤ) < 2 * N := by positivity
  have h1 : w z = w (Function.update z j (z j % (2 * N))) := by
    have h := isTorusPeriodic_add_smul N w hw (Pi.single j (z j / (2 * N)))
      (Function.update z j (z j % (2 * N)))
    rw [← h]
    congr 1
    ext i
    by_cases hij : i = j
    · subst hij
      simp only [Pi.add_apply, Pi.smul_apply, Function.update_self, Pi.single_eq_same,
        smul_eq_mul]
      exact (Int.emod_add_mul_ediv (z i) _).symm
    · simp [hij]
  rw [h1]
  unfold foldCoord
  have h0 := Int.emod_nonneg (z j) hm.ne'
  have h2 := Int.emod_lt_of_pos (z j) hm
  by_cases hle : z j % (2 * N) ≤ N
  · rw [if_pos hle]
  · rw [if_neg hle]
    set u := Function.update z j (z j % (2 * N)) with hu
    have h3 : u j = z j % (2 * N) := by simp [hu]
    have h4 := isTorusPeriodic_add_smul N w hw (unit j) (reflectSite j u)
    rw [← heven u j, ← h4]
    congr 1
    ext i
    by_cases hij : i = j
    · subst hij
      simp only [Pi.add_apply, reflectSite, if_true, Pi.smul_apply, unit, Pi.single_eq_same,
        smul_eq_mul, mul_one, Function.update_self, h3]
      ring
    · simp [reflectSite, hij, unit, hu]

/-- An even `2N`-periodic function takes the same value at `y` and at `y` with the coordinates in
`S` replaced by their folds. -/
theorem eq_partial_fold_of_even (N : ℕ) (hN : 0 < N) (w : Site d → ℝ)
    (hw : IsTorusPeriodic N w) (heven : ∀ x (k : Fin d), w (reflectSite k x) = w x)
    (S : Finset (Fin d)) :
    ∀ y : Site d, w y = w (fun i => if i ∈ S then foldCoord N (y i) else y i) := by
  induction S using Finset.induction_on with
  | empty => intro y; simp
  | insert j S hj ih =>
    intro y
    rw [ih y]
    refine (eq_update_foldCoord_of_even N hN w hw heven j _).trans ?_
    congr 1
    ext i
    by_cases hij : i = j
    · subst hij
      simp [hj]
    · simp [hij]

/-- **An even periodic function is the reflection of its restriction**: if `w` has period `2N` and
is invariant under every coordinate reflection, then `w = reflectFun N w` (the fold of `x` is
obtained from `x` by coordinate reflections and shifts by multiples of `2N`). -/
theorem eq_reflectFun_of_even (N : ℕ) (hN : 0 < N) (w : Site d → ℝ) (hw : IsTorusPeriodic N w)
    (heven : ∀ x (k : Fin d), w (reflectSite k x) = w x) (x : Site d) :
    w x = reflectFun N w x := by
  have h := eq_partial_fold_of_even N hN w hw heven Finset.univ x
  simp only [Finset.mem_univ, if_true] at h
  exact h

end LatticeHC

end
